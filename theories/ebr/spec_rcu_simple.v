From stdpp Require Export namespaces.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr Require Export smr_common ebr.spec_rcu_common.
From smr Require  ebr.spec_rcu_common.
From iris.prelude Require Import options.

From smr Require Import helpers.


Inductive guard_state :=
  | Deactivated
  | Activated (γg : gname).

Definition GuardT Σ (N : namespace) : Type :=
  ∀ (γd : gname) (g : loc) (gt : guard_state), iProp Σ.

Definition NodeInfoT Σ (N : namespace) : Type :=
  ∀ (γd : gname) (γg : gname) (p : blk) (γ_p : gname) (size_i : nat) (R : resource Σ), iProp Σ.

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
  (Managed : ManagedT Σ N)
  (Guard : GuardT Σ N)
  (NodeInfo : NodeInfoT Σ N)
  .

Implicit Types (R : resource Σ) (γ_p : gname).

Definition rcu_domain_new_spec' : Prop :=
  ∀ E,
  {{{ True }}}
    rcu_domain_new #() @ E
  {{{ γd d, RET #d; IsRCUDomain γd d }}}.

(* Register a owned resource to the domain. *)
Definition rcu_domain_register' : Prop :=
  ∀ R E (p : blk) lv γ_p γd d,
  ↑(mgmtN N) ⊆ E →
  IsRCUDomain γd d -∗
  p ↦∗ lv ∗ †p…(length lv) ∗ R p lv γ_p ={E}=∗
  Managed γd p γ_p (length lv) R.

Definition guard_new_spec' : Prop :=
  ∀ E γd d,
  ↑(mgmtN N) ⊆ E →
  IsRCUDomain γd d -∗
  {{{ True }}}
    guard_new #d @ E
  {{{ g, RET #g; Guard γd g Deactivated }}}.

Definition guard_activate_spec' : Prop :=
  ∀ E γd d g,
  ↑(mgmtN N) ⊆ E →
  IsRCUDomain γd d -∗
  {{{ Guard γd g Deactivated }}}
    guard_activate #g @ E
  {{{ γg, RET #(); Guard γd g (Activated γg) }}}.

Definition guard_protect' :=
  ∀ E γd d R p γ_p γg g size_i,
  ↑(mgmtN N) ⊆ E →
  IsRCUDomain γd d -∗
  Managed γd p γ_p size_i R-∗
  Guard γd g (Activated γg) ={E}=∗
  Managed γd p γ_p size_i R ∗ Guard γd g (Activated γg) ∗
  NodeInfo γd γg p γ_p size_i R.

Definition guard_acc' : Prop :=
  ∀ R E γd γg g p γ_p size_i,
  ↑(ptrN N p) ⊆ E →
  NodeInfo γd γg p γ_p size_i R -∗
  Guard γd g (Activated γg) ={E,E∖↑(ptrN N p)}=∗
  ∃ lv, ⌜length lv = size_i⌝ ∗ p ↦∗ lv ∗ ▷ R p lv γ_p ∗ Guard γd g (Activated γg) ∗
  (∀ lv', ⌜length lv = length lv'⌝ ∗ p ↦∗ lv' ∗ ▷ R p lv' γ_p ={E∖↑(ptrN N p),E}=∗ True).

Definition managed_acc' : Prop :=
  ∀ E γd R p γ_p size_i,
  ↑(ptrN N p) ⊆ E →
  Managed γd p γ_p size_i R ={E,E∖↑(ptrN N p)}=∗
  ∃ lv, ⌜length lv = size_i⌝ ∗ p ↦∗ lv ∗ ▷ R p lv γ_p ∗ Managed γd p γ_p size_i R ∗
  (∀ lv', ⌜length lv = length lv'⌝ ∗ p ↦∗ lv' ∗ ▷ R p lv' γ_p ={E∖↑(ptrN N p),E}=∗ True).

Definition managed_exclusive' : Prop :=
  ∀ γd p γ_p γ_p' size_i size_i' R R',
  Managed γd p γ_p size_i R -∗ Managed γd p γ_p' size_i' R' -∗ False.

Definition guard_managed_agree' : Prop :=
  ∀ γd γg g p γ_p1 γ_p2 R1 R2 size_i1 size_i2,
  NodeInfo γd γg p γ_p1 size_i1 R1 -∗
  Guard γd g (Activated γg) -∗
  Managed γd p γ_p2 size_i2 R2 -∗
  ⌜γ_p1 = γ_p2⌝.

Definition guard_deactivate_spec' : Prop :=
  ∀ E γd d g γg,
  ↑(mgmtN N) ⊆ E →
  IsRCUDomain γd d -∗
  {{{ Guard γd g (Activated γg) }}}
    guard_deactivate #g @ E
  {{{ RET #(); Guard γd g Deactivated }}}.

Definition guard_drop_spec' : Prop :=
  ∀ E γd d g gs,
  ↑(mgmtN N) ⊆ E →
  IsRCUDomain γd d -∗
  {{{ Guard γd g gs }}}
    guard_drop #g @ E
  {{{ RET #(); True }}}.

Definition rcu_domain_retire_spec' : Prop :=
  ∀ E γd d R s p γ_p,
  ↑N ⊆ E →
  IsRCUDomain γd d -∗
  {{{ Managed γd p γ_p s R }}}
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

Record rcu_simple_spec {Σ} `{!heapGS Σ} {N : namespace} : Type := RCUSimpleSpec {
  rcu_spec_code :> rcu_code;

  IsRCUDomain : DomainT Σ N;
  Managed : ManagedT Σ N;
  Guard : GuardT Σ N;
  NodeInfo : NodeInfoT Σ N;

  IsRCUDomain_Persistent : ∀ γd d, Persistent (IsRCUDomain γd d);
  NodeInfo_Persistent : ∀ γd γg p γ_p size_p R, Persistent (NodeInfo γd γg p γ_p size_p R);

  rcu_domain_new_spec : rcu_domain_new_spec' N rcu_spec_code.(rcu_domain_new) IsRCUDomain;
  rcu_domain_register : rcu_domain_register' N IsRCUDomain Managed;
  guard_new_spec : guard_new_spec' N rcu_spec_code.(guard_new) IsRCUDomain Guard;
  guard_protect : guard_protect' N IsRCUDomain Managed Guard NodeInfo;
  guard_activate_spec : guard_activate_spec' N rcu_spec_code.(guard_activate) IsRCUDomain Guard;
  guard_deactivate_spec : guard_deactivate_spec' N rcu_spec_code.(guard_deactivate) IsRCUDomain Guard;
  guard_drop_spec : guard_drop_spec' N rcu_spec_code.(guard_drop) IsRCUDomain Guard;
  guard_acc : guard_acc' N Guard NodeInfo;
  managed_acc : managed_acc' N Managed;
  managed_exclusive : managed_exclusive' N Managed;
  guard_managed_agree : guard_managed_agree' N Managed Guard NodeInfo;
  rcu_domain_retire_spec : rcu_domain_retire_spec' N rcu_spec_code.(rcu_domain_retire) IsRCUDomain Managed;
  rcu_domain_do_reclamation_spec : rcu_domain_do_reclamation_spec' N rcu_spec_code.(rcu_domain_do_reclamation) IsRCUDomain
}.

Global Arguments rcu_simple_spec _ {_} _ : assert.
Global Existing Instances IsRCUDomain_Persistent NodeInfo_Persistent.

Section helpers.
Context {Σ} `{!heapGS Σ} {N : namespace} {rcu : rcu_simple_spec Σ N}.

Global Instance into_inv_guard γd γg p γ_p size_i R : IntoInv (rcu.(NodeInfo) γd γg p γ_p size_i R) (ptrN N p) := {}.

Global Instance into_acc_guard R E γd γg g (p : blk) γ_p size_i :
  IntoAcc (rcu.(NodeInfo) γd γg p γ_p size_i R) (↑(ptrN N p) ⊆ E) (rcu.(Guard) γd g (Activated γg))%I
          (fupd E (E∖↑(ptrN N p))) (fupd (E∖↑(ptrN N p)) E)
          (λ lv, ⌜length lv = size_i⌝ ∗ p ↦∗ lv ∗ ▷ R p lv γ_p ∗ rcu.(Guard) γd g (Activated γg))%I
          (λ lv, ∃ lv', ⌜length lv = length lv'⌝ ∗ p ↦∗ lv' ∗ ▷ R p lv' γ_p)%I (λ _, None)%I.
Proof.
  rewrite /IntoAcc /accessor. iIntros (?) "#Info_p G".
  iMod (rcu.(guard_acc) with "Info_p G") as (lv) "(% & p↦ & R & G & CloseG)"; [solve_ndisj|].
  iExists lv. iSplitL "p↦ R G"; [by iFrame|].
  iIntros "!> (% & % & p↦ & R)".
  by iMod ("CloseG" with "[$p↦ $R]").
Qed.

Global Instance into_inv_managed γd p γ_p size_i R : IntoInv (rcu.(Managed) γd p γ_p size_i R) (ptrN N p) := {}.

Global Instance into_acc_managed E γd p γ_p size_i R :
  IntoAcc (rcu.(Managed) γd p γ_p size_i R) (↑(ptrN N p) ⊆ E) (True%I)
          (fupd E (E∖↑(ptrN N p))) (fupd (E∖↑(ptrN N p)) E)
          (λ lv, ⌜length lv = size_i⌝ ∗ p ↦∗ lv ∗ ▷ R p lv γ_p ∗ rcu.(Managed) γd p γ_p size_i R)%I
          (λ lv, ∃ lv', ⌜length lv = length lv'⌝ ∗ p ↦∗ lv' ∗ ▷ R p lv' γ_p)%I (λ _, None)%I.
Proof.
  rewrite /IntoAcc /accessor. iIntros (?) "M _".
  iMod (rcu.(managed_acc) with "M") as (lv) "(% & p↦ & R & M & CloseM)"; [solve_ndisj|].
  iExists lv. iSplitL "p↦ R M"; [by iFrame|].
  iIntros "!> (% & % & p↦ & R)".
  by iMod ("CloseM" with "[$p↦ $R]").
Qed.

Lemma guard_read R o E γd γg g p γ_p size_i :
  ↑(ptrN N p) ⊆ E →
  o < size_i →
  (∀ p lv γ_p, Persistent (R p lv γ_p)) →
  {{{ rcu.(NodeInfo) γd γg p γ_p size_i R ∗ rcu.(Guard) γd g (Activated γg) }}}
    !#(p +ₗ o) @ E
  {{{ lv v, RET v; rcu.(Guard) γd g (Activated γg) ∗ R p lv γ_p ∗ ⌜lv !! o = Some v⌝ }}}.
Proof.
  intros ???.
  iIntros (Φ) "[#Info_p G] HΦ".
  iInv "Info_p" as (lv <-) "(p↦ & #R & Syn)".
  have [v ?] : (is_Some (lv !! o)) by (apply lookup_lt_is_Some; lia).
  wp_apply (wp_load_offset with "p↦") as "p↦"; [done|].
  iModIntro. iSplitL "p↦".
  { iExists _. by iFrame "∗#". }
  iApply "HΦ". iFrame "∗#%".
Qed.

Lemma managed_read R o E γd p γ_p size_i :
  ↑(ptrN N p) ⊆ E →
  o < size_i →
  (∀ p lv γ_p, Persistent (R p lv γ_p)) →
  {{{ rcu.(Managed) γd p γ_p size_i R }}}
    !#(p +ₗ o) @ E
  {{{ lv v, RET v; rcu.(Managed) γd p γ_p size_i R ∗ R p lv γ_p ∗ ⌜lv !! o = Some v⌝ }}}.
Proof.
  intros ???.
  iIntros (Φ) "M HΦ".
  iInv "M" as (lv <-) "(p↦ & #R & M)".
  have [v ?] : is_Some (lv !! o) by apply lookup_lt_is_Some.
  wp_apply (wp_load_offset with "p↦") as "p↦"; [done|].
  iModIntro. iSplitL "p↦".
  { iExists _. by iFrame "∗#%". }
  iApply "HΦ". iFrame "∗#%".
Qed.

End helpers.
