From smr.algebra Require Export coPset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export invariants.
From iris.prelude Require Import options.

Class coP_cinvG Σ := { #[local] coP_cinv_inG :: inG Σ coPneset_disjR }.

Definition coP_cinvΣ : gFunctors := #[GFunctor coPneset_disjR].

Global Instance subG_coP_cinvΣ {Σ} : subG coP_cinvΣ Σ → coP_cinvG Σ.
Proof. solve_inG. Qed.

Section defs.
  Context `{!invGS_gen hlc Σ, !coP_cinvG Σ}.

  Definition coP_cinv_own (γ : gname) (t : coPneset) : iProp Σ :=
    own γ (CoPNESetDisj t).

  Definition coP_cinv (N : namespace) (γ : gname) (P : iProp Σ) : iProp Σ :=
    inv N (P ∨ coP_cinv_own γ ⊤).
End defs.

Global Instance: Params (@coP_cinv) 5 := {}.

Section proofs.
  Context `{!invGS_gen hlc Σ, !coP_cinvG Σ}.

  Global Instance coP_cinv_own_timeless γ p : Timeless (coP_cinv_own γ p).
  Proof. rewrite /coP_cinv_own; apply _. Qed.

  Global Instance coP_cinv_contractive N γ : Contractive (coP_cinv N γ).
  Proof. solve_contractive. Qed.
  Global Instance coP_cinv_ne N γ : NonExpansive (coP_cinv N γ).
  Proof. exact: contractive_ne. Qed.
  Global Instance coP_cinv_proper N γ : Proper ((≡) ==> (≡)) (coP_cinv N γ).
  Proof. exact: ne_proper. Qed.

  Global Instance coP_cinv_persistent N γ P : Persistent (coP_cinv N γ P).
  Proof. rewrite /coP_cinv; apply _. Qed.

  Lemma coP_cinv_own_fractional γ t1 t2:
    t1 ## t2 →
    coP_cinv_own γ (t1 ∪ t2) ⊣⊢ coP_cinv_own γ t1 ∗ coP_cinv_own γ t2.
  Proof. iIntros. rewrite /coP_cinv_own -own_op coPneset_disj_union; auto. Qed.

  Lemma coP_cinv_own_valid γ t1 t2 :
    coP_cinv_own γ t1 -∗ coP_cinv_own γ t2 -∗ ⌜t1 ## t2⌝.
  Proof.
    iIntros "H1 H2".
    by iCombine "H1 H2" gives %?%coPneset_disj_valid_op.
  Qed.

  Global Instance coP_cinv_own_combine_gives γ t1 t2 :
    CombineSepGives (coP_cinv_own γ t1) (coP_cinv_own γ t2) ⌜t1 ## t2⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (coP_cinv_own_valid with "H1 H2") as %?.
    eauto.
  Qed.

  Global Instance coP_cinv_own_combine_as γ t1 t2 :
    CombineSepAs (coP_cinv_own γ t1) (coP_cinv_own γ t2) (coP_cinv_own γ (t1 ∪ t2)).
  Proof.
    rewrite /CombineSepAs. iIntros "[H1 H2]".
    iCombine "H1 H2" as "H" gives %?.
    rewrite coPneset_disj_union //.
  Qed.

  Lemma coP_cinv_own_1_l γ t : coP_cinv_own γ ⊤ -∗ coP_cinv_own γ t -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (coP_cinv_own_valid with "H1 H2") as %[]%coPneset_top_disjoint.
  Qed.

  Lemma coP_cinv_iff N γ P t : coP_cinv N γ P -∗ ▷ □ (P ↔ t) -∗ coP_cinv N γ t.
  Proof.
    iIntros "HI #HPQ". iApply (inv_iff with "HI"). iIntros "!> !>".
    iSplit; iIntros "[?|$]"; iLeft; by iApply "HPQ".
  Qed.

  (*** Allocation rules. *)
  (** The "strong" variants permit any infinite [I], and choosing [P] is delayed
  until after [γ] was chosen.*)
  Lemma coP_cinv_alloc_strong (I : gname → Prop) E N :
    pred_infinite I →
    ⊢ |={E}=> ∃ γ, ⌜ I γ ⌝ ∗ coP_cinv_own γ ⊤ ∗ ∀ P, ▷ P ={E}=∗ coP_cinv N γ P.
  Proof.
    iIntros (?). iMod (own_alloc_strong (CoPNESetDisj ⊤) I) as
      (γ) "[Hfresh Hγ]"; [done|done|].
    iExists γ. iIntros "!> {$Hγ $Hfresh}" (P) "HP".
    iMod (inv_alloc N _ (P ∨ coP_cinv_own γ ⊤) with "[HP]"); eauto.
  Qed.

  (** The "open" variants create the invariant in the open state, and delay
  having to prove [P].
  These do not imply the other variants because of the extra assumption [↑N ⊆ E]. *)
  Lemma coP_cinv_alloc_strong_open (I : gname → Prop) E N :
    pred_infinite I →
    ↑N ⊆ E →
    ⊢ |={E}=> ∃ γ, ⌜ I γ ⌝ ∗ coP_cinv_own γ ⊤ ∗ ∀ P,
      |={E,E∖↑N}=> coP_cinv N γ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (??). iMod (own_alloc_strong (CoPNESetDisj ⊤) I) as
      (γ) "[Hfresh Hγ]"; [done|done|].
    iExists γ. iIntros "!> {$Hγ $Hfresh}" (P).
    iMod (inv_alloc_open N _ (P ∨ coP_cinv_own γ ⊤)) as "[Hinv Hclose]"; first by eauto.
    iIntros "!>". iFrame. iIntros "HP". iApply "Hclose". iLeft. done.
  Qed.

  Lemma coP_cinv_alloc_cofinite (G : gset gname) E N :
    ⊢ |={E}=> ∃ γ, ⌜ γ ∉ G ⌝ ∗ coP_cinv_own γ ⊤ ∗ ∀ P, ▷ P ={E}=∗ coP_cinv N γ P.
  Proof.
    apply coP_cinv_alloc_strong. apply (pred_infinite_set (C:=gset gname))=> E'.
    exists (fresh (G ∪ E')). apply not_elem_of_union, is_fresh.
  Qed.

  Lemma coP_cinv_alloc E N P : ▷ P ={E}=∗ ∃ γ, coP_cinv N γ P ∗ coP_cinv_own γ ⊤.
  Proof.
    iIntros "HP". iMod (coP_cinv_alloc_cofinite ∅ E N) as (γ _) "[Hγ Halloc]".
    iExists γ. iFrame "Hγ". by iApply "Halloc".
  Qed.

  Lemma coP_cinv_alloc_open E N P :
    ↑N ⊆ E → ⊢ |={E,E∖↑N}=> ∃ γ, coP_cinv N γ P ∗ coP_cinv_own γ ⊤ ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (?). iMod (coP_cinv_alloc_strong_open (λ _, True)) as (γ) "(_ & Htok & Hmake)"; [|done|].
    { apply pred_infinite_True. }
    iMod ("Hmake" $! P) as "[Hinv Hclose]". iIntros "!>". iExists γ. iFrame.
  Qed.

  (*** Accessors *)
  Lemma coP_cinv_acc_strong E N γ p P :
    ↑N ⊆ E →
    coP_cinv N γ P -∗ (coP_cinv_own γ p ={E,E∖↑N}=∗
    ▷ P ∗ coP_cinv_own γ p ∗ (∀ E' : coPset, ▷ P ∨ coP_cinv_own γ ⊤ ={E',↑N ∪ E'}=∗ True)).
  Proof.
    iIntros (?) "Hinv Hown".
    iMod (inv_acc_strong with "Hinv") as "[[$ | >Hown'] H]"; first done.
    - iIntros "{$Hown} !>" (E') "HP". iApply "H". by iNext.
    - iDestruct (coP_cinv_own_1_l with "Hown' Hown") as %[].
  Qed.

  Lemma coP_cinv_acc E N γ p P :
    ↑N ⊆ E →
    coP_cinv N γ P -∗ coP_cinv_own γ p ={E,E∖↑N}=∗ ▷ P ∗ coP_cinv_own γ p ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (?) "#Hinv Hγ".
    iMod (coP_cinv_acc_strong with "Hinv Hγ") as "($ & $ & H)"; first done.
    iIntros "!> HP". iMod ("H" with "[$HP]") as "_".
    rewrite -union_difference_L //.
  Qed.

  (*** Other *)
  Lemma coP_cinv_cancel E N γ P : ↑N ⊆ E → coP_cinv N γ P -∗ coP_cinv_own γ ⊤ ={E}=∗ ▷ P.
  Proof.
    iIntros (?) "#Hinv Hγ".
    iMod (coP_cinv_acc_strong with "Hinv Hγ") as "($ & Hγ & H)"; first done.
    iMod ("H" with "[$Hγ]") as "_".
    rewrite -union_difference_L //.
  Qed.

  Global Instance into_inv_coP_cinv N γ P : IntoInv (coP_cinv N γ P) N := {}.

  Global Instance into_acc_coP_cinv E N γ P p :
    IntoAcc (X:=unit) (coP_cinv N γ P)
            (↑N ⊆ E) (coP_cinv_own γ p) (fupd E (E∖↑N)) (fupd (E∖↑N) E)
            (λ _, ▷ P ∗ coP_cinv_own γ p)%I (λ _, ▷ P)%I (λ _, None)%I.
  Proof.
    rewrite /IntoAcc /accessor bi.exist_unit -assoc.
    iIntros (?) "#Hinv Hown". by iApply coP_cinv_acc.
  Qed.
End proofs.

#[export] Typeclasses Opaque coP_cinv_own coP_cinv.
