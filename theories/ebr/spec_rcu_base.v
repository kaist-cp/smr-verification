From stdpp Require Export namespaces.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr Require Export smr_common ebr.spec_rcu_common.
From iris.prelude Require Import options.

From smr Require Import helpers.

Definition BaseDomainT Σ (mgmtN ptrsN : namespace) : Type :=
  ∀ (γd : gname) (d : loc), iProp Σ.

Definition BaseManagedT Σ (mgmtN ptrsN : namespace) : Type :=
  ∀ (γd : gname) (p : blk) (γ_p : gname) (size_p : nat) (R : resource Σ), iProp Σ.

Definition InactiveT Σ : Type :=
  ∀ (γe : gname) (g : loc), iProp Σ.

Definition BaseGuardT Σ (ptrsN : namespace) : Type :=
  ∀ (γe : gname)
    (γg : gname)
    (g : loc)
    (Syn : gset positive)
    (G : gmap blk positive),
    iProp Σ.

Definition BaseGuardedNodeInfoT Σ (ptrsN : namespace) : Type :=
  ∀ (γe : gname)
    (γg : gname)
    (p : blk)
    (γ_p : positive)
    (size_p : nat)
    (R : resource Σ),
    iProp Σ.

Definition RCUAuthT Σ : Type :=
  ∀ (γe : gname) (Im : gmap positive alloc) (Rs : gset positive), iProp Σ.

Definition to_baseN (N : namespace) := N .@ "base".

Section spec.
Context {Σ} `{!heapGS Σ} (mgmtN ptrsN : namespace) (DISJ : mgmtN ## ptrsN).
Variables
  (rcu_domain_new : val)
  (rcu_domain_retire : val)
  (rcu_domain_do_reclamation : val)
  (guard_new : val)
  (guard_activate : val)
  (guard_deactivate : val)
  (guard_drop : val).
Variables
  (IsRCUDomain : BaseDomainT Σ mgmtN ptrsN)
  (RCUAuth : RCUAuthT Σ)
  (BaseManaged : BaseManagedT Σ mgmtN ptrsN)
  (BaseInactive : InactiveT Σ)
  (BaseGuard : BaseGuardT Σ ptrsN)
  (BaseNodeInfo : NodeInfoT Σ ptrsN)
  (BaseGuardedNodeInfo : BaseGuardedNodeInfoT Σ ptrsN).

Implicit Types
  (R : resource Σ) (Im : gmap positive alloc) (Rs : gset positive)
  (Syn : gset positive)
  (d : loc) (E : coPset) (p : blk).

Definition rcu_domain_new_spec' : Prop :=
  ∀ E,
  ⊢ {{{ True }}}
    rcu_domain_new #() @ E
  {{{ (γe : gname) d, RET #d; IsRCUDomain γe d ∗ RCUAuth γe ∅ ∅ }}}.

(* Register a owned resource to the domain. *)
Definition rcu_domain_register' : Prop :=
  ∀ R (I : gset positive) (Ms : positive → iProp Σ) E (p : blk) lv γe Im Rs d,
  ↑(to_baseN mgmtN) ⊆ E →
  IsRCUDomain γe d -∗
  RCUAuth γe Im Rs -∗
  p ↦∗ lv -∗ †p…(length lv) -∗
  (∀ (i_p : positive), ⌜i_p ∉ I⌝ ={E}=∗ (R p lv i_p ∗ Ms i_p)) ={E}=∗
  ∃ (i_p : positive), ⌜i_p ∉ (dom Im ∪ I)⌝ ∗
    RCUAuth γe (<[i_p := {| addr := p; len := length lv; |}]> Im) Rs ∗
    BaseManaged γe p i_p (length lv) R ∗ Ms i_p
  .

Definition guard_new_spec' : Prop :=
  ∀ E γe d,
  ↑(to_baseN mgmtN) ⊆ E →
  ⊢ IsRCUDomain γe d -∗
  {{{ True }}}
    guard_new #d @ E
  {{{ (g : loc), RET #g; BaseInactive γe g }}}.

Definition guard_activate_spec' : Prop :=
  ∀ E γe d g,
  ↑(to_baseN mgmtN) ⊆ E →
  ⊢ IsRCUDomain γe d -∗
  {{{ BaseInactive γe g }}}
    guard_activate #g @ E
  {{{ γg Syn, RET #(); BaseGuard γe γg g Syn ∅ }}}.

Definition guard_protect' :=
  ∀ E γe d p i_p size_p R γg g Syn G,
  ↑(to_baseN mgmtN) ⊆ E →
  IsRCUDomain γe d -∗
  BaseManaged γe p i_p size_p R -∗
  BaseGuard γe γg g Syn G ={E}=∗
  BaseManaged γe p i_p size_p R ∗
  BaseGuard γe γg g Syn (<[ p := i_p ]> G) ∗
  ⌜i_p ∉ Syn⌝ ∗
  ⌜is_Some (G !! p) → G !! p = Some i_p⌝
  .

Definition guard_protect_node_info' :=
  ∀ E γe d p i_p size_p R γg g Syn G,
  ↑(to_baseN mgmtN) ⊆ E →
  i_p ∉ Syn →
  IsRCUDomain γe d -∗
  BaseNodeInfo γe p i_p size_p R -∗
  BaseGuard γe γg g Syn G ={E}=∗
  BaseGuard γe γg g Syn (<[ p := i_p ]> G) ∗
  BaseGuardedNodeInfo γe γg p i_p size_p R ∗
  ⌜is_Some (G !! p) → G !! p = Some i_p⌝
  .

Definition rcu_auth_guard_subset' :=
  ∀ E γe d Im Rs γg g Syn G,
  ↑(to_baseN mgmtN) ⊆ E →
  ⊢ IsRCUDomain γe d -∗
    RCUAuth γe Im Rs -∗
    BaseGuard γe γg g Syn G ={E}=∗
    RCUAuth γe Im Rs ∗ BaseGuard γe γg g Syn G ∗ ⌜Syn ⊆ Rs⌝.

Definition guard_acc' : Prop :=
  ∀ R E γe γg g Syn G p i_p size_p,
  ↑(to_baseN (ptrsN.@p)) ⊆ E →
  BaseGuardedNodeInfo γe γg p i_p size_p R -∗
  BaseGuard γe γg g Syn G ={E,E∖↑(to_baseN (ptrsN.@p))}=∗
  ∃ lv, ⌜length lv = size_p⌝ ∗ p ↦∗ lv ∗ ▷ R p lv i_p ∗ BaseGuard γe γg g Syn G ∗
  (∀ lv', ⌜length lv = length lv'⌝ ∗ p ↦∗ lv' ∗ ▷ R p lv' i_p ={E∖↑(to_baseN (ptrsN.@p)),E}=∗ True).

Definition managed_acc' : Prop :=
  ∀ E γe R p i_p size_p,
  ↑(to_baseN (ptrsN.@p)) ⊆ E →
  BaseManaged γe p i_p size_p R ={E,E∖↑(to_baseN (ptrsN.@p))}=∗
  ∃ lv, ⌜length lv = size_p⌝ ∗ p ↦∗ lv ∗ ▷ R p lv i_p ∗ BaseManaged γe p i_p size_p R ∗
  (∀ lv', ⌜length lv = length lv'⌝ ∗ p ↦∗ lv' ∗ ▷ R p lv' i_p ={E∖↑(to_baseN (ptrsN.@p)),E}=∗ True).

Definition managed_exclusive' : Prop :=
  ∀ γe p i_p i_p' size_p size_p' R R',
  BaseManaged γe p i_p size_p R -∗ BaseManaged γe p i_p' size_p' R' -∗ False.

Definition managed_get_node_info' : Prop :=
  ∀ γe p i_p size_p R,
  BaseManaged γe p i_p size_p R -∗ BaseNodeInfo γe p i_p size_p R.

Definition guard_managed_agree' : Prop :=
  ∀ γe γg g Syn G p i_p1 i_p2 R1 R2 size_p1 size_p2,
  BaseGuardedNodeInfo γe γg p i_p1 size_p1 R1 -∗
  BaseGuard γe γg g Syn G -∗
  BaseManaged γe p i_p2 size_p2 R2 -∗
  ⌜i_p1 = i_p2⌝.

Definition guard_deactivate_spec' : Prop :=
  ∀ E γe d γg g Syn G,
  ↑(to_baseN mgmtN) ⊆ E →
  ⊢ IsRCUDomain γe d -∗
  {{{ BaseGuard γe γg g Syn G }}}
    guard_deactivate #g @ E
  {{{ RET #(); BaseInactive γe g }}}.

Definition guard_drop_spec' : Prop :=
  ∀ E γe d γg g Syn G,
  ↑(to_baseN mgmtN) ⊆ E →
  ⊢ IsRCUDomain γe d -∗
  {{{ BaseGuard γe γg g Syn G }}}
    guard_drop #g @ E
  {{{ RET #(); True }}}.

Definition guard_drop_inactive_spec' : Prop :=
  ∀ E γe d g,
  ↑(to_baseN mgmtN) ⊆ E →
  ⊢ IsRCUDomain γe d -∗
  {{{ BaseInactive γe g }}}
    guard_drop #g @ E
  {{{ RET #(); True }}}.

Definition rcu_domain_retire_spec' : Prop :=
  ∀ E γe d R size_p p i_p,
  ↑(to_baseN mgmtN) ⊆ E →
  ⊢IsRCUDomain γe d -∗
  BaseManaged γe p i_p size_p R -∗
  <<{ ∀∀ Im Rs, RCUAuth γe Im Rs }>>
    rcu_domain_retire #d #p #size_p @ E,↑(to_baseN mgmtN),∅
  <<{ RCUAuth γe Im ({[i_p]} ∪ Rs) | RET #() }>>.

Definition rcu_domain_do_reclamation_spec' : Prop :=
  ∀ E γe d,
  ↑(to_baseN mgmtN) ∪ ↑ptrsN ⊆ E →
  ⊢ IsRCUDomain γe d -∗
  {{{ True }}}
    rcu_domain_do_reclamation #d @ E
  {{{ RET #(); True }}}.

End spec.

Record rcu_base_spec {Σ} `{!heapGS Σ} {mgmtN ptrsN : namespace} : Type := RCUBaseSpec {
  rcu_spec_code :> rcu_code;

  RCUAuth : RCUAuthT Σ;
  IsRCUDomain : BaseDomainT Σ mgmtN ptrsN;
  BaseManaged : ManagedT Σ ptrsN;
  BaseInactive : InactiveT Σ;
  BaseGuard : BaseGuardT Σ ptrsN;
  BaseNodeInfo : NodeInfoT Σ ptrsN;
  BaseGuardedNodeInfo : BaseGuardedNodeInfoT Σ ptrsN;

  RCUAuth_timeless : ∀ γe Im Rs, Timeless (RCUAuth γe Im Rs);
  IsRCUDomain_persistent : ∀ γe d, Persistent (IsRCUDomain γe d);
  BaseNodeInfo_persistent : ∀ γe p i_p size_p R, Persistent (BaseNodeInfo γe p i_p size_p R);
  BaseNodeInfo_contractive : ∀ γe p i_p size_p, Contractive (λ (R : blk -d> list val -d> gname -d> iPropO Σ), BaseNodeInfo γe p i_p size_p R);
  BaseGuardedNodeInfo_persistent : ∀ γe γg p i_p size_p R, Persistent (BaseGuardedNodeInfo γe γg p i_p size_p R);

  rcu_domain_new_spec : rcu_domain_new_spec' mgmtN ptrsN rcu_spec_code.(rcu_domain_new) IsRCUDomain RCUAuth;
  rcu_domain_register : rcu_domain_register' mgmtN ptrsN IsRCUDomain RCUAuth BaseManaged;
  guard_new_spec : guard_new_spec' mgmtN ptrsN rcu_spec_code.(guard_new) IsRCUDomain BaseInactive;
  guard_protect : guard_protect' mgmtN ptrsN IsRCUDomain BaseManaged BaseGuard;
  guard_protect_node_info : guard_protect_node_info' mgmtN ptrsN IsRCUDomain BaseGuard BaseNodeInfo BaseGuardedNodeInfo;
  rcu_auth_guard_subset: rcu_auth_guard_subset' mgmtN ptrsN IsRCUDomain RCUAuth BaseGuard;
  guard_activate_spec : guard_activate_spec' mgmtN ptrsN rcu_spec_code.(guard_activate) IsRCUDomain BaseInactive BaseGuard;
  guard_deactivate_spec : guard_deactivate_spec' mgmtN ptrsN rcu_spec_code.(guard_deactivate) IsRCUDomain BaseInactive BaseGuard;
  guard_drop_spec : guard_drop_spec' mgmtN ptrsN rcu_spec_code.(guard_drop) IsRCUDomain BaseGuard;
  guard_drop_inactive_spec : guard_drop_inactive_spec' mgmtN ptrsN rcu_spec_code.(guard_drop) IsRCUDomain BaseInactive;
  guard_acc : guard_acc' ptrsN BaseGuard BaseGuardedNodeInfo;
  managed_acc : managed_acc' mgmtN ptrsN BaseManaged;
  managed_exclusive : managed_exclusive' mgmtN ptrsN BaseManaged;
  managed_get_node_info: managed_get_node_info' mgmtN ptrsN BaseManaged BaseNodeInfo;
  guard_managed_agree : guard_managed_agree' mgmtN ptrsN BaseManaged BaseGuard BaseGuardedNodeInfo;
  rcu_domain_retire_spec : rcu_domain_retire_spec' mgmtN ptrsN rcu_spec_code.(rcu_domain_retire) IsRCUDomain RCUAuth BaseManaged;
  rcu_domain_do_reclamation_spec : rcu_domain_do_reclamation_spec' mgmtN ptrsN rcu_spec_code.(rcu_domain_do_reclamation) IsRCUDomain
}.

Global Arguments rcu_base_spec _ {_} _ _ : assert.
Global Existing Instances RCUAuth_timeless IsRCUDomain_persistent BaseNodeInfo_persistent BaseNodeInfo_contractive BaseGuardedNodeInfo_persistent.
