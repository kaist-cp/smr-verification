From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.
From smr Require Import helpers.

From smr.diaframe.lang Require Import proof_automation atomic_specs atom_spec_notation.
From smr Require Import hazptr.spec_hazptr.

Section spec.

Context `{!heapGS Σ, !hazptrG Σ} (hazptrN: namespace).
Variable (hazptr : hazard_pointer_spec Σ hazptrN).
Definition hazptr_code := hazptr.(hazard_pointer_spec_code).
Notation iProp := (iProp Σ).

Global Instance hazard_domain_new_dspec :
  SPEC {{ True }}
    hazptr_code.(spec_hazptr.hazard_domain_new) #()
  {{ γd d, RET #d; hazptr.(spec_hazptr.IsHazardDomain) γd d }}.
Proof. iStep. wp_apply (hazptr.(hazard_domain_new_spec) with "[//]"). iSteps. Qed.

Global Instance biabd_hazard_domain_register (p: blk) γd γ_p R n E:
  HINT †p…n ✱ [d lv;  hazptr.(IsHazardDomain) γd d ∗ p ↦∗ lv ∗ ⌜ n = (length lv) ⌝ ∗ R p lv γ_p ∗ ⌜ ↑(mgmtN hazptrN) ⊆ E ⌝ ]
      ⊫ [fupd E E]
    ; (hazptr.(Managed) γd p γ_p n R) ✱ [ emp ].
Proof.
  iIntros (?). iSteps. unseal_diaframe. simpl. iSplitL; try done.
  iApply (hazptr.(hazard_domain_register)); try done. iSteps.
Qed.

Global Instance shield_new_dspec d E:
  SolveSepSideCondition (↑(mgmtN hazptrN) ⊆ E) →
  SPEC ⟨E⟩ γd, {{ hazptr.(IsHazardDomain) γd d }}
    hazptr_code.(spec_hazptr.shield_new) #d
  {{ s, RET #s; hazptr.(Shield) γd s Deactivated }}.
Proof.
  intros. iSteps. wp_apply (hazptr.(shield_new_spec)); try done. iSteps.
Qed.

Global Instance shield_set_dspec s p E :
  SolveSepSideCondition (↑(mgmtN hazptrN) ⊆ E) →
  SPEC ⟨E⟩ γd s_st d, {{ hazptr.(IsHazardDomain) γd d ∗ hazptr.(Shield) γd s s_st }}
    hazptr_code.(shield_set) #s #(oblk_to_lit p)
  {{ RET #(); hazptr.(Shield) γd s (if p is Some p then NotValidated p else Deactivated) }}.
Proof.
  intros. iSteps. wp_apply (hazptr.(shield_set_spec) with "H1 H2"); try done. iSteps.
Qed.

Global Instance biabd_shield_acc (p: blk) s size_i E R γ_p γd:
  HINT hazptr.(Shield) γd s (Validated p γ_p R size_i) ✱ [-; ⌜ ↑(ptrN hazptrN p) ⊆ E ⌝ ] ⊫
    [fupd E (E ∖ ↑(ptrN hazptrN p))]
    lv;
      p ↦∗ lv ✱
    [ ▷ R p lv γ_p ∗ ⌜ length lv = size_i ⌝  ∗ hazptr.(Shield) γd s (Validated p γ_p R size_i) ∗
    (∀ lv', ▷ R p lv' γ_p ∗ p ↦∗ lv' ∗ ⌜length lv = length lv'⌝  ={E∖↑(ptrN hazptrN p),E}=∗ True) ].
Proof.
  intros. iStep. iMod (hazptr.(shield_acc) with "H1") as (lv) "(% & p↦ & R & Sh & CloseSh)"; [done|].
  iExists lv. iFrame. do 3 iStep.
  iSpecialize ("CloseSh" with "[$H5 $H4 //]"). done.
Qed.

Global Instance hp_shield_managed_agree γd s p γ_p1 γ_p2 R1 R2 size_i1 size_i2:
  MergablePersist (▷ hazptr.(Managed) γd p γ_p2 size_i2 R2) (λ p' Pin Pout,
  TCAnd (TCEq Pin (hazptr.(Shield) γd s (Validated p γ_p1 R1 size_i1))) $
      TCEq Pout (▷ ⌜ γ_p1 = γ_p2 ⌝))%I.
Proof.
  rewrite /MergablePersist => p' Pin Pout [-> ->].
  rewrite bi.intuitionistically_if_elim.
  iStep.
  iDestruct (hazptr.(shield_managed_agree) with "H2 H1") as "#$AA".
Qed.

Global Instance biabd_shield_validate (p: blk) E s γd size_i R γ_p:
  HINT hazptr.(Shield) γd s (NotValidated p) ✱
     [d; hazptr.(IsHazardDomain) γd d ∗ hazptr.(Managed) γd p γ_p size_i R ∗ ⌜ ↑(mgmtN hazptrN) ⊆ E ⌝ ]
      ⊫ [fupd E E]
    ; hazptr.(Shield) γd s (Validated p γ_p R size_i) ✱ [ hazptr.(Managed) γd p γ_p size_i R ].
Proof.
  iIntros (?). iSteps. unseal_diaframe. simpl. iMod (hazptr.(shield_validate) with "H2 H3 H1") as "[$ $]"; done.
Qed.

Global Instance shield_drop_dspec s E:
  SolveSepSideCondition (↑(mgmtN hazptrN) ⊆ E) →
  SPEC ⟨E⟩ γd s_st d, {{ hazptr.(IsHazardDomain) γd d ∗ hazptr.(Shield) γd s s_st }}
   hazptr_code.(shield_drop) #s
  {{ RET #(); True }}.
Proof.
  intros. iSteps. wp_apply (hazptr.(shield_drop_spec) with "H1 H2"); done.
Qed.

Global Instance hazard_domain_retire_dspec E d p s:
  SolveSepSideCondition (↑hazptrN ⊆ E) →
  SPEC ⟨E⟩ R γd γ_p, {{ hazptr.(IsHazardDomain) γd d ∗ hazptr.(Managed) γd p γ_p s R }}
    hazptr_code.(hazard_domain_retire) #d #p #s
  {{ RET #(); True }}.
Proof.
  intros. iSteps. wp_apply (hazptr.(hazard_domain_retire_spec) with "H1 H2"); done.
Qed.

Global Instance shield_protect_dspec E s d γd s_st a dq :
  SolveSepSideCondition (↑(mgmtN hazptrN) ⊆ E) →
  SPEC ⟨E,∅,↑(mgmtN hazptrN)⟩ pa γ_p size_i R,
  << hazptr.(IsHazardDomain) γd d ∗ hazptr.(Shield) γd s s_st
     ¦  (a ↦{dq} #(oblk_to_lit pa) ∗
        if pa is Some p then
          ▷ hazptr.(Managed) γd p γ_p size_i R
        else True) > >
    hazptr_code.(shield_protect) #s #a
  << RET #(oblk_to_lit pa);
     (a ↦{dq} #(oblk_to_lit pa) ∗
     if pa is Some p then
        hazptr.(Managed) γd p γ_p size_i R ∗ hazptr.(Shield) γd s (Validated p γ_p R size_i)
      else
        hazptr.(Shield) γd s Deactivated) > >.
Proof.
  intros.
  iSteps as (Φ) "IHD Sh AU".
  awp_apply (hazptr.(shield_protect_spec) with "IHD Sh [AU]"); [done|].
  iApply (aacc_aupd with "AU"); [done|].
  iIntros (p_a γ_p size_i R) "[a↦ Ma]".
  iAaccIntro with "[a↦ Ma]".
  1: instantiate (1 := [tele_arg p_a; γ_p; size_i; (R : resource Σ)]); iSteps.
  { iSteps. }
  iStep as "a↦ RES". iRight. iSteps.
Qed.

End spec.

