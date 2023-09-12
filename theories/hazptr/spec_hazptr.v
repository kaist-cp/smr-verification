From stdpp Require Export namespaces.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr Require Export smr_common.
From iris.prelude Require Import options.

From smr Require Import helpers.


Inductive shield_state {Σ} :=
  | Deactivated
  | NotValidated (p : blk)
  | Validated (p : blk) (γ_p : gname) (R : resource Σ) (size_i : nat).

Global Arguments shield_state : clear implicits.

Definition ShieldT Σ (N : namespace) : Type :=
  ∀ (γd : gname) (s : loc) (st : shield_state Σ), iProp Σ.


Section spec.
Context {Σ} `{!heapGS Σ} (N : namespace).
Variables
  (hazard_domain_new : val)
  (hazard_domain_retire : val)
  (hazard_domain_do_reclamation : val)
  (shield_new : val)
  (shield_set : val)
  (shield_protect : val)
  (shield_unset : val)
  (shield_drop : val).
Variables
  (IsHazardDomain : DomainT Σ N)
  (Managed : ManagedT Σ N)
  (Shield : ShieldT Σ N).

Implicit Types (R : resource Σ).

(* NOTE
- Take [E] for Hoare triples and updates to avoid using [fupd_mask_subseteq].
  For LAT, use the exact [↑N].
- Put easily inferred (by unification with precondition) parameters at the back.
*)

Definition hazard_domain_new_spec' : Prop :=
  ∀ E,
  {{{ True }}}
    hazard_domain_new #() @ E
  {{{ γd d, RET #d; IsHazardDomain γd d }}}.

(* Register a owned resource to the domain. *)
Definition hazard_domain_register' : Prop :=
  ∀ R E (p : blk) lv γ_p γd d,
  ↑(mgmtN N) ⊆ E →
  IsHazardDomain γd d -∗
  p ↦∗ lv ∗ †p…(length lv) ∗ R p lv γ_p ={E}=∗
  Managed γd p γ_p (length lv) R.

Definition shield_new_spec' : Prop :=
  ∀ E γd d,
  ↑(mgmtN N) ⊆ E →
  IsHazardDomain γd d -∗
  {{{ True }}}
    shield_new #d @ E
  {{{ s, RET #s; Shield γd s Deactivated }}}.

Definition shield_set_spec' : Prop :=
  ∀ p E γd d s s_st,
  ↑(mgmtN N) ⊆ E →
  IsHazardDomain γd d -∗
  {{{ Shield γd s s_st }}}
    shield_set #s #(oblk_to_lit p) @ E (* NOTE: oblk_to_lit makes it a bit annoying to use (should specify p) *)
  {{{ RET #(); Shield γd s (if p is Some p then NotValidated p else Deactivated) }}}.

(* [Shield] is validated by proving that the resource is reachable. *)
Definition shield_validate' : Prop :=
  ∀ E γd d R p γ_p s size_i,
  ↑(mgmtN N) ⊆ E →
  IsHazardDomain γd d -∗
  Managed γd p γ_p size_i R -∗
  Shield γd s (NotValidated p) ={E}=∗
  Managed γd p γ_p size_i R ∗ Shield γd s (Validated p γ_p R size_i).

(* NOTE: To use this spec, the client's invariant should be inspected before
proving AACC. In [None] case, [γ_p] can be any dummy value. *)
Definition shield_protect_spec' : Prop :=
  ∀ E γd d s s_st (a : loc) dq,
  ↑(mgmtN N) ⊆ E →
  IsHazardDomain γd d -∗
  Shield γd s s_st -∗
  (* TODO: this create a hole for size_i and R when pa is None. This blocks automation with diaframe *)
  <<< ∀∀ (pa : option blk) γ_p size_i R,
      a ↦{dq} #(oblk_to_lit pa) ∗
      if pa is Some p then
        ▷ Managed γd p γ_p size_i R
      else True >>>
    shield_protect #s #a @ E,∅,↑(mgmtN N)
  <<< a ↦{dq} #(oblk_to_lit pa) ∗
      if pa is Some p then
        Managed γd p γ_p size_i R ∗ Shield γd s (Validated p γ_p R size_i)
      else
        Shield γd s Deactivated,
      RET #(oblk_to_lit pa) >>>.

(* Access the protected pointer. *)
Definition shield_acc' : Prop :=
  ∀ E γd R s p γ_p size_i,
  ↑(ptrN N p) ⊆ E →
  Shield γd s (Validated p γ_p R size_i) ={E,E∖↑(ptrN N p)}=∗
  ∃ lv, ⌜length lv = size_i⌝ ∗ p ↦∗ lv ∗ ▷ R p lv γ_p ∗ Shield γd s (Validated p γ_p R size_i) ∗
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

Definition shield_managed_agree' : Prop :=
  ∀ γd s p γ_p1 γ_p2 R1 R2 size_i1 size_i2,
  Shield γd s (Validated p γ_p1 R1 size_i1) -∗
  Managed γd p γ_p2 size_i2 R2 -∗
  ⌜γ_p1 = γ_p2⌝.

Definition shield_unset_spec' : Prop :=
  ∀ E γd d s s_st,
  ↑(mgmtN N) ⊆ E →
  IsHazardDomain γd d -∗
  {{{ Shield γd s s_st }}}
    shield_unset #s @ E
  {{{ RET #(); Shield γd s Deactivated }}}.

Definition shield_drop_spec' : Prop :=
  ∀ E γd d s s_st,
  ↑(mgmtN N) ⊆ E →
  IsHazardDomain γd d -∗
  {{{ Shield γd s s_st }}}
    shield_drop #s @ E
  {{{ RET #(); True }}}.

(* Detach a registered pointer and request deallocation. *)
Definition hazard_domain_retire_spec' : Prop :=
  ∀ E γd d R p γ_p (s : nat),
  ↑N ⊆ E →
  IsHazardDomain γd d -∗
  {{{ Managed γd p γ_p s R }}}
    hazard_domain_retire #d #p #s @ E
  {{{ RET #(); True }}}.

Definition hazard_domain_do_reclamation_spec' : Prop :=
  ∀ E γd d,
  ↑N ⊆ E →
  IsHazardDomain γd d -∗
  {{{ True }}}
    hazard_domain_do_reclamation #d @ E
  {{{ RET #(); True }}}.

End spec.

Record hazard_pointer_code : Type := HazardPointerCode {
  hazard_domain_new : val;
  hazard_domain_retire : val;
  hazard_domain_do_reclamation: val;
  shield_new : val;
  shield_set : val;
  shield_protect : val;
  shield_unset : val;
  shield_drop : val;
}.

Record hazard_pointer_spec {Σ} `{!heapGS Σ} {N : namespace} : Type := HazardPointerSpec {
  hazard_pointer_spec_code :> hazard_pointer_code;

  IsHazardDomain : DomainT Σ N;
  Managed : ManagedT Σ N;
  Shield : ShieldT Σ N;

  IsHazardDomain_Persistent : ∀ γd d, Persistent (IsHazardDomain γd d);

  hazard_domain_new_spec : hazard_domain_new_spec' N hazard_pointer_spec_code.(hazard_domain_new) IsHazardDomain;
  hazard_domain_register : hazard_domain_register' N IsHazardDomain Managed;
  shield_new_spec : shield_new_spec' N hazard_pointer_spec_code.(shield_new) IsHazardDomain Shield;
  shield_set_spec : shield_set_spec' N hazard_pointer_spec_code.(shield_set) IsHazardDomain Shield;
  shield_validate : shield_validate' N IsHazardDomain Managed Shield;
  shield_protect_spec : shield_protect_spec' N hazard_pointer_spec_code.(shield_protect) IsHazardDomain Managed Shield;
  shield_unset_spec : shield_unset_spec' N hazard_pointer_spec_code.(shield_unset) IsHazardDomain Shield;
  shield_drop_spec : shield_drop_spec' N hazard_pointer_spec_code.(shield_drop) IsHazardDomain Shield;
  shield_acc : shield_acc' N Shield;
  managed_acc : managed_acc' N Managed;
  managed_exclusive : managed_exclusive' N Managed;
  shield_managed_agree : shield_managed_agree' N Managed Shield;
  hazard_domain_retire_spec : hazard_domain_retire_spec' N hazard_pointer_spec_code.(hazard_domain_retire) IsHazardDomain Managed;
  hazard_domain_do_reclamation_spec : hazard_domain_do_reclamation_spec' N hazard_pointer_spec_code.(hazard_domain_do_reclamation) IsHazardDomain;
}.

Global Arguments hazard_pointer_spec _ {_} _ : assert.

Global Existing Instances IsHazardDomain_Persistent.

Section helpers.
Context {Σ} `{!heapGS Σ} (N : namespace) {hp : hazard_pointer_spec Σ N}.

Global Instance into_inv_shield γd s p γ_p R size_i : IntoInv (hp.(Shield) γd s (Validated p γ_p R size_i)) (ptrN N p) := {}.

Global Instance into_acc_shield E γd s p γ_p R size_i :
  IntoAcc (hp.(Shield) γd s (Validated p γ_p R size_i)) (↑(ptrN N p) ⊆ E) (True%I)
          (fupd E (E∖↑(ptrN N p))) (fupd (E∖↑(ptrN N p)) E)
          (λ lv, ⌜length lv = size_i⌝ ∗ p ↦∗ lv ∗ ▷ R p lv γ_p ∗ hp.(Shield) γd s (Validated p γ_p R size_i))%I
          (λ lv, ∃ lv', ⌜length lv = length lv'⌝ ∗ p ↦∗ lv' ∗ ▷ R p lv' γ_p)%I (λ _, None)%I.
Proof.
  rewrite /IntoAcc /accessor. iIntros (?) "Sh _".
  iMod (hp.(shield_acc) with "Sh") as (lv) "(% & p↦ & R & Sh & CloseSh)"; [solve_ndisj|].
  iExists lv. iSplitL "p↦ R Sh"; [by iFrame|].
  iIntros "!> (% & % & p↦ & R)".
  by iMod ("CloseSh" with "[$p↦ $R]").
Qed.

Global Instance into_inv_managed γd p γ_p size_i R : IntoInv (hp.(Managed) γd p γ_p size_i R) (ptrN N p) := {}.

Global Instance into_acc_managed E γd p γ_p size_i R :
  IntoAcc (hp.(Managed) γd p γ_p size_i R) (↑(ptrN N p) ⊆ E) (True%I)
          (fupd E (E∖↑(ptrN N p))) (fupd (E∖↑(ptrN N p)) E)
          (λ lv, ⌜length lv = size_i⌝ ∗ p ↦∗ lv ∗ ▷ R p lv γ_p ∗ hp.(Managed) γd p γ_p size_i R)%I
          (λ lv, ∃ lv', ⌜length lv = length lv'⌝ ∗ p ↦∗ lv' ∗ ▷ R p lv' γ_p)%I (λ _, None)%I.
Proof.
  rewrite /IntoAcc /accessor. iIntros (?) "M _".
  iMod (managed_acc with "M") as (lv) "(% & p↦ & R & M & CloseM)"; [solve_ndisj|].
  iExists lv. iSplitL "p↦ R M"; [by iFrame|].
  iIntros "!> (% & % & p↦ & R)".
  by iMod ("CloseM" with "[$p↦ $R]").
Qed.

Lemma shield_read R o E γd s p γ_p size_i :
  ↑(ptrN N p) ⊆ E →
  o < size_i →
  (∀ p lv γ_p, Persistent (R p lv γ_p)) →
  {{{ hp.(Shield) γd s (Validated p γ_p R size_i) }}}
    !#(p +ₗ o) @ E
  {{{ lv v, RET v; hp.(Shield) γd s (Validated p γ_p R size_i) ∗ R p lv γ_p ∗ ⌜lv !! o = Some v⌝ }}}.
Proof.
  intros ???.
  iIntros (Φ) "Sh HΦ".
  iInv "Sh" as (lv <-) "(p↦ & #R & Sh)".
  have [v ?] : is_Some (lv !! o) by apply lookup_lt_is_Some.
  wp_apply (wp_load_offset with "p↦") as "p↦"; [done|].
  iModIntro. iSplitL "p↦".
  { iExists _. by iFrame "∗#%". }
  iApply "HΦ". iFrame "∗#%".
Qed.

Lemma managed_read R o E γd p γ_p size_i :
  ↑(ptrN N p) ⊆ E →
  o < size_i →
  (∀ p lv γ_p, Persistent (R p lv γ_p)) →
  {{{ hp.(Managed) γd p γ_p size_i R }}}
    !#(p +ₗ o) @ E
  {{{ lv v, RET v; hp.(Managed) γd p γ_p size_i R ∗ R p lv γ_p ∗ ⌜lv !! o = Some v⌝ }}}.
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
