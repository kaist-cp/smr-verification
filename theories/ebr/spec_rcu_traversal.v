From stdpp Require Export namespaces gmultiset.
From iris.algebra Require Import list.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr Require Export smr_common ebr.spec_rcu_common.
From iris.prelude Require Import options.

From smr Require Import helpers.


Definition InactiveT Σ : Type :=
  ∀ (γd : gname) (g : loc), iProp Σ.

Definition GuardT Σ (N : namespace) : Type :=
  ∀ (γd : gname) (γg : gname)
    (g : loc),
    iProp Σ.

Definition ManagedT Σ (N : namespace) : Type :=
  ∀ (γd : gname)
    (p : blk) (i : positive) (ty : type Σ)
    (B : gmultiset positive),
    iProp Σ.

Definition DeletedT Σ (N : namespace) : Type :=
  ∀ (γd : gname)
    (p : blk) (i : positive) (ty : type Σ),
    iProp Σ.

(* Logical ownership of [p +ₗ o]. If [to] is [Some], it points to a node
governed by RCU. If [None], [p +ₗ o] points to something uninteresting. *)
Definition RCUPointsToT Σ (N : namespace) : Type :=
  ∀ (γd : gname)
    (p : blk) (i : positive) (o : nat)
    (to : option (blk * positive * type Σ)),
    iProp Σ.

Definition RCUNodeInfoT Σ (N : namespace) : Type :=
  ∀ (γd : gname) (γg : gname)
    (p : blk) (i : positive)
    (ty : type Σ),
    iProp Σ.

Section spec.
Context {Σ} `{!heapGS Σ} (N : namespace).
Variables
  (rcu_domain_new : val)
  (rcu_domain_retire : val)
  (rcu_domain_do_reclamation : val)
  (guard_new : val)
  (guard_activate : val)
  (guard_deactivate : val)
  (guard_drop : val).
Variables
  (IsRCUDomain : DomainT Σ N)
  (Inactive : InactiveT Σ)
  (Guard : GuardT Σ N)
  (Managed : ManagedT Σ N)
  (Deleted : DeletedT Σ N)
  (RCUPointsTo : RCUPointsToT Σ N)
  (RCUNodeInfo : RCUNodeInfoT Σ N)
  .

Definition rcu_domain_new_spec' : Prop :=
  ∀ E,
  {{{ True }}}
    rcu_domain_new #() @ E
  {{{ γd d, RET #d; IsRCUDomain γd d }}}.

Implicit Types (succs : list (option (blk * positive * type Σ * gmultiset positive))).

Definition RCUNodeSuccManageds γd succs : iProp Σ :=
  [∗ list] field ∈ succs,
    match field with
    | Some (p', i', ty', B') => Managed γd p' i' ty' B'
    | _ => True
    end.
Global Arguments RCUNodeSuccManageds _ !_ / : assert.

Definition succs_add_pred succs (i : positive) :=
  (λ field, match field with Some (p', i', ty', B') => Some (p', i', ty', B' ⊎ {[+i+]}) | None => None end)
  <$> succs.

Definition rcu_domain_register' : Prop :=
  ∀ (I : gset positive) ty succs (R : positive → iProp Σ) E' E (p : blk) lv γd d,
  E' ## ↑(mgmtN N) →
  E' ⊆ E →
  ↑(mgmtN N) ⊆ E →
  ty.(ty_sz) = length lv →
  ty.(ty_sz) = length succs →
  ty.(ty_sz) > 0 →
  IsRCUDomain γd d -∗
  p ↦∗ lv -∗ †p…(length lv) -∗
  (* NOTE: Can't let client modify the link, because that requires opening
  [IsRCUDomain], which is already open in the proof of this rule. So this rule
  itself should modify the links (which requires the [Managed]s of link
  targets) and pass the [RCUPointsTo]s to the client. *)
  RCUNodeSuccManageds γd succs -∗
  ( ∀ i, ⌜i ∉ I⌝ -∗
    ([∗ list] o ↦ field ∈ succs, RCUPointsTo γd p i o (fst <$> field)) ={E'}=∗
    ty.(ty_res) p lv i ∗ R i) ={E}=∗
  ∃ i, ⌜i ∉ I⌝ ∗
    Managed γd p i ty ∅ ∗ RCUNodeSuccManageds γd (succs_add_pred succs i) ∗ R i.

Definition guard_new_spec' : Prop :=
  ∀ E γd d,
  ↑(mgmtN N) ⊆ E →
  IsRCUDomain γd d -∗
  {{{ True }}}
    guard_new #d @ E
  {{{ g, RET #g; Inactive γd g }}}.

Definition guard_activate_spec' : Prop :=
  ∀ E γd d g,
  ↑(mgmtN N) ⊆ E →
  IsRCUDomain γd d -∗
  {{{ Inactive γd g }}}
    guard_activate #g @ E
  {{{ γg, RET #(); Guard γd γg g }}}.

Definition guard_deactivate_spec' : Prop :=
  ∀ E γd d γg g,
  ↑(mgmtN N) ⊆ E →
  IsRCUDomain γd d -∗
  {{{ Guard γd γg g }}}
    guard_deactivate #g @ E
  {{{ RET #(); Inactive γd g }}}.

Definition guard_drop_spec' : Prop :=
  ∀ E γd d γg g,
  ↑(mgmtN N) ⊆ E →
  IsRCUDomain γd d -∗
  {{{ Guard γd γg g }}}
    guard_drop #g @ E
  {{{ RET #(); True }}}.

Definition guard_drop_inactive_spec' : Prop :=
  ∀ E γd d g,
  ↑(mgmtN N) ⊆ E →
  IsRCUDomain γd d -∗
  {{{ Inactive γd g }}}
    guard_drop #g @ E
  {{{ RET #(); True }}}.

Definition guard_protect_managed' :=
  ∀ E γd d p i ty B γg g,
  ↑(mgmtN N) ⊆ E →
  IsRCUDomain γd d -∗
  Managed γd p i ty B -∗
  Guard γd γg g ={E}=∗
  Managed γd p i ty B ∗
  Guard γd γg g ∗
  RCUNodeInfo γd γg p i ty.

Definition guard_protect_rcu_points_to' :=
  ∀ E γd d p1 i1 o1 p2 i2 ty1 ty2 γg g,
  ↑(mgmtN N) ⊆ E →
  IsRCUDomain γd d -∗
  RCUNodeInfo γd γg p1 i1 ty1 -∗
  RCUPointsTo γd p1 i1 o1 (Some (p2, i2, ty2)) -∗
  Guard γd γg g ={E}=∗
  RCUPointsTo γd p1 i1 o1 (Some (p2, i2, ty2)) ∗
  Guard γd γg g ∗
  RCUNodeInfo γd γg p2 i2 ty2.

Definition guard_acc' : Prop :=
  ∀ ty E γd γg g p i,
  ↑(ptrN N p) ⊆ E →
  RCUNodeInfo γd γg p i ty -∗
  Guard γd γg g ={E,E∖↑(ptrN N p)}=∗
  ∃ lv, p ↦∗ lv ∗ ▷ ty.(ty_res) p lv i ∗ Guard γd γg g ∗
  (∀ lv', p ↦∗ lv' ∗ ▷ ty.(ty_res) p lv' i ={E∖↑(ptrN N p),E}=∗ True).

Definition managed_acc' : Prop :=
  ∀ E γd ty p i B,
  ↑(ptrN N p) ⊆ E →
  Managed γd p i ty B ={E,E∖↑(ptrN N p)}=∗
  ∃ lv, p ↦∗ lv ∗ ▷ ty.(ty_res) p lv i ∗ Managed γd p i ty B ∗
  (∀ lv', p ↦∗ lv' ∗ ▷ ty.(ty_res) p lv' i ={E∖↑(ptrN N p),E}=∗ True).

Definition deleted_acc' : Prop :=
  ∀ E γd ty p i,
  ↑(ptrN N p) ⊆ E →
  Deleted γd p i ty ={E,E∖↑(ptrN N p)}=∗
  ∃ lv, p ↦∗ lv ∗ ▷ ty.(ty_res) p lv i ∗ Deleted γd p i ty ∗
  (∀ lv', p ↦∗ lv' ∗ ▷ ty.(ty_res) p lv' i ={E∖↑(ptrN N p),E}=∗ True).

Definition managed_exclusive' : Prop :=
  ∀ γd p i i' ty ty' B B',
  Managed γd p i ty B -∗ Managed γd p i' ty' B' -∗ False.

Definition guard_managed_agree' : Prop :=
  ∀ γd γg g p i1 i2 ty1 ty2 B,
  RCUNodeInfo γd γg p i1 ty1 -∗
  Guard γd γg g -∗
  Managed γd p i2 ty2 B -∗
  ⌜i1 = i2⌝.

Definition rcu_points_to_link' : Prop :=
  ∀ E γd d p1 i1 o1 p2 i2 ty2 B2,
  ↑(mgmtN N) ⊆ E →
  IsRCUDomain γd d -∗
  RCUPointsTo γd p1 i1 o1 None -∗
  Managed γd p2 i2 ty2 B2 ={E}=∗
  RCUPointsTo γd p1 i1 o1 (Some (p2,i2,ty2)) ∗
  Managed γd p2 i2 ty2 (B2 ⊎ {[+ i1 +]}).

Definition rcu_points_to_unlink' : Prop :=
  ∀ E γd d p1 i1 o1 p2 i2 ty2 B2,
  ↑(mgmtN N) ⊆ E →
  IsRCUDomain γd d -∗
  RCUPointsTo γd p1 i1 o1 (Some (p2,i2,ty2)) -∗
  Managed γd p2 i2 ty2 B2 ={E}=∗
  RCUPointsTo γd p1 i1 o1 None ∗
  Managed γd p2 i2 ty2 (B2 ∖ {[+ i1 +]}).

Definition rcu_points_to_update' : Prop :=
  ∀ E γd d p1 i1 o1 p2 i2 ty2 B2 p3 i3 ty3 B3,
  ↑(mgmtN N) ⊆ E →
  IsRCUDomain γd d -∗
  RCUPointsTo γd p1 i1 o1 (Some (p2,i2,ty2)) -∗
  Managed γd p2 i2 ty2 B2 -∗
  Managed γd p3 i3 ty3 B3 ={E}=∗
  RCUPointsTo γd p1 i1 o1 (Some (p3,i3,ty3)) ∗
  Managed γd p2 i2 ty2 (B2 ∖ {[+ i1 +]}) ∗
  Managed γd p3 i3 ty3 (B3 ⊎ {[+ i1 +]}).

(* Delayed cleanup of predecessor set using over-approximating predecessor set.
Alternative: No delayed cleanup. Require [Managed]s here. This make deletion
rule more complicated, but enables reference counting (instead of predecessor
multiset). *)
Definition managed_delete' : Prop :=
  ∀ E γd d p i ty,
  ↑(mgmtN N) ⊆ E →
  IsRCUDomain γd d -∗
  Managed γd p i ty ∅ ={E}=∗
  Deleted γd p i ty.

Definition deleted_clean' : Prop :=
  ∀ E γd d p1 p2 i1 i2 ty1 ty2 B,
  ↑(mgmtN N) ⊆ E →
  IsRCUDomain γd d -∗
  Deleted γd p1 i1 ty1 -∗
  Managed γd p2 i2 ty2 B ={E}=∗
  Deleted γd p1 i1 ty1 ∗
  Managed γd p2 i2 ty2 (B ∖ {[+ i1 +]}).

(* NOTE: variant of retire that makes guard internally. *)
Definition rcu_domain_retire_spec' : Prop :=
  ∀ E γd d p i ty s,
  ↑N ⊆ E →
  s = ty.(ty_sz) →
  IsRCUDomain γd d -∗
  {{{ Deleted γd p i ty }}}
    rcu_domain_retire #d #p #s @ E
  {{{ RET #(); True }}}.

Definition rcu_domain_do_reclamation_spec' : Prop :=
  ∀ E γd d,
  ↑N ⊆ E →
  IsRCUDomain γd d -∗
  {{{ True }}}
    rcu_domain_do_reclamation #d @ E
  {{{ RET #(); True }}}.

End spec.

Record rcu_traversal_spec {Σ} `{!heapGS Σ} {N : namespace} : Type := RCUTraversalSpec {
  rcu_spec_code :> rcu_code;

  IsRCUDomain : DomainT Σ N;
  Inactive : InactiveT Σ;
  Guard : GuardT Σ N;
  Managed : ManagedT Σ N;
  Deleted : DeletedT Σ N;
  RCUPointsTo : RCUPointsToT Σ N;
  RCUNodeInfo : RCUNodeInfoT Σ N;

  IsRCUDomain_Persistent : ∀ γd d, Persistent (IsRCUDomain γd d);
  RCUNodeInfo_Persistent : ∀ γd γg p i ty, Persistent (RCUNodeInfo γd γg p i ty);
  RCUPointsTo_Some_Contractive : ∀ γd p1 i1 o1 p2 i2 n, Proper (type_dist2 n ==> dist n) (λ ty2, RCUPointsTo γd p1 i1 o1 (Some (p2,i2,ty2)));

  rcu_domain_new_spec : rcu_domain_new_spec' N rcu_spec_code.(rcu_domain_new) IsRCUDomain;
  rcu_domain_register : rcu_domain_register' N IsRCUDomain Managed RCUPointsTo;
  guard_new_spec : guard_new_spec' N rcu_spec_code.(guard_new) IsRCUDomain Inactive;
  guard_activate_spec : guard_activate_spec' N rcu_spec_code.(guard_activate) IsRCUDomain Inactive Guard;
  guard_deactivate_spec : guard_deactivate_spec' N rcu_spec_code.(guard_deactivate) IsRCUDomain Inactive Guard;
  guard_drop_spec : guard_drop_spec' N rcu_spec_code.(guard_drop) IsRCUDomain Guard;
  guard_drop_inactive_spec : guard_drop_inactive_spec' N rcu_spec_code.(guard_drop) IsRCUDomain Inactive;
  guard_protect_managed : guard_protect_managed' N IsRCUDomain Guard Managed RCUNodeInfo;
  guard_protect_rcu_points_to : guard_protect_rcu_points_to' N IsRCUDomain Guard RCUPointsTo RCUNodeInfo;
  guard_acc : guard_acc' N Guard RCUNodeInfo;
  managed_acc : managed_acc' N Managed;
  deleted_acc : deleted_acc' N Deleted;
  managed_exclusive : managed_exclusive' N Managed;
  guard_managed_agree : guard_managed_agree' N Guard Managed RCUNodeInfo;
  rcu_points_to_link : rcu_points_to_link' N IsRCUDomain Managed RCUPointsTo;
  rcu_points_to_unlink : rcu_points_to_unlink' N IsRCUDomain Managed RCUPointsTo;
  rcu_points_to_update : rcu_points_to_update' N IsRCUDomain Managed RCUPointsTo;
  managed_delete : managed_delete' N IsRCUDomain Managed Deleted;
  deleted_clean : deleted_clean' N IsRCUDomain Managed Deleted;
  rcu_domain_retire_spec : rcu_domain_retire_spec' N rcu_spec_code.(rcu_domain_retire) IsRCUDomain Deleted;
  rcu_domain_do_reclamation_spec : rcu_domain_do_reclamation_spec' N rcu_spec_code.(rcu_domain_do_reclamation) IsRCUDomain
}.

Global Arguments rcu_traversal_spec _ {_} _ : assert.
Global Existing Instances IsRCUDomain_Persistent RCUNodeInfo_Persistent RCUPointsTo_Some_Contractive.

Section helpers.
Context {Σ} `{!heapGS Σ} {N : namespace} {rcu : rcu_traversal_spec Σ N}.

Global Instance into_inv_guard γd γg p i_p ty : IntoInv (rcu.(RCUNodeInfo) γd γg p i_p ty) (ptrN N p) := {}.

Global Instance into_acc_guard E γd γg g p i_p ty :
  IntoAcc (rcu.(RCUNodeInfo) γd γg p i_p ty) (↑(ptrN N p) ⊆ E) (rcu.(Guard) γd γg g)%I
          (fupd E (E∖↑(ptrN N p))) (fupd (E∖↑(ptrN N p)) E)
          (λ lv, p ↦∗ lv ∗ ▷ ty.(ty_res) p lv i_p ∗ rcu.(Guard) γd γg g)%I
          (λ lv, ∃ lv', p ↦∗ lv' ∗ ▷ ty.(ty_res) p lv' i_p)%I (λ _, None)%I.
Proof.
  rewrite /IntoAcc /accessor. iIntros (?) "#Info_p G".
  iMod (rcu.(guard_acc) with "Info_p G") as (lv) "(p↦ & R & G & CloseG)"; [solve_ndisj|].
  iExists lv. iFrame.
  iIntros "!> (% & p↦ & R)".
  by iMod ("CloseG" with "[$p↦ $R]").
Qed.

Global Instance into_inv_managed γd p i_p ty B : IntoInv (rcu.(Managed) γd p i_p ty B) (ptrN N p) := {}.

Global Instance into_acc_managed E γd p i_p ty B :
  IntoAcc (rcu.(Managed) γd p i_p ty B) (↑(ptrN N p) ⊆ E) (True%I)
          (fupd E (E∖↑(ptrN N p))) (fupd (E∖↑(ptrN N p)) E)
          (λ lv, p ↦∗ lv ∗ ▷ ty.(ty_res) p lv i_p ∗ rcu.(Managed) γd p i_p ty B)%I
          (λ lv, ∃ lv', p ↦∗ lv' ∗ ▷ ty.(ty_res) p lv' i_p)%I (λ _, None)%I.
Proof.
  rewrite /IntoAcc /accessor. iIntros (?) "M _".
  iMod (rcu.(managed_acc) with "M") as (lv) "(p↦ & R & M & CloseM)"; [solve_ndisj|].
  iExists lv. iFrame.
  iIntros "!> (% & p↦ & R)".
  by iMod ("CloseM" with "[$p↦ $R]").
Qed.

Global Instance into_inv_deleted γd p i_p ty : IntoInv (rcu.(Deleted) γd p i_p ty) (ptrN N p) := {}.

Global Instance into_acc_deleted E γd p i_p ty :
  IntoAcc (rcu.(Deleted) γd p i_p ty) (↑(ptrN N p) ⊆ E) (True%I)
          (fupd E (E∖↑(ptrN N p))) (fupd (E∖↑(ptrN N p)) E)
          (λ lv, p ↦∗ lv ∗ ▷ ty.(ty_res) p lv i_p ∗ rcu.(Deleted) γd p i_p ty)%I
          (λ lv, ∃ lv', p ↦∗ lv' ∗ ▷ ty.(ty_res) p lv' i_p)%I (λ _, None)%I.
Proof.
  rewrite /IntoAcc /accessor. iIntros (?) "D _".
  iMod (rcu.(deleted_acc) with "D") as (lv) "(p↦ & R & D & CloseD)"; [solve_ndisj|].
  iExists lv. iFrame.
  iIntros "!> (% & p↦ & R)".
  by iMod ("CloseD" with "[$p↦ $R]").
Qed.

End helpers.
