From stdpp Require Import coPset.
From iris.algebra Require Import excl functions.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.
From smr Require Import helpers.

Definition token2R : ucmra :=
  (positive * positive) -d> optionUR $ exclR $ unitO.

Definition to_token2 (E1 E2 : coPset) : token2R :=
  λ k, if decide (k.1 ∈ E1 ∧ k.2 ∈ E2)
       then Excl' ()
       else None.

Section token2R_lemmas.
  Implicit Types (k : positive) (E : coPset).

  (* general token2 *)
  Lemma to_token2_valid E1 E2 :
    ✓ to_token2 E1 E2.
  Proof.
    intros x. unfold to_token2.
    by case_decide.
  Qed.

  Lemma to_token2_lookup k1 k2 E1 E2 :
    k1 ∈ E1 → k2 ∈ E2 →
    to_token2 E1 E2 (k1, k2) = Excl' ().
  Proof. intros. unfold to_token2. by rewrite decide_True. Qed.

  Lemma to_token2_lookup_None k1 k2 E1 E2 :
    k1 ∉ E1 ∨ k2 ∉ E2 →
    to_token2 E1 E2 (k1, k2) = None.
  Proof.
    intros. unfold to_token2.
    rewrite decide_False; auto. set_solver.
  Qed.

  Local Ltac yes := (rewrite to_token2_lookup; auto).
  Local Ltac no := (rewrite to_token2_lookup_None; auto).

  Lemma to_token2_op E1A E1B E2A E2B :
    to_token2 E1A E2A ⋅ to_token2 E1B E2B
    = λ x, (to_token2 E1A E2A x) ⋅ (to_token2 E1B E2B x).
  Proof. auto. Qed.

  Lemma to_token2_union_1 E1A E1B E2 :
    E1A ## E1B →
    to_token2 E1A E2 ⋅ to_token2 E1B E2
    ≡ to_token2 (E1A ∪ E1B) E2.
  Proof.
    intros DISJ (k1, k2). rewrite discrete_fun_lookup_op.
    destruct (decide (k1 ∈ E1A)), (decide (k1 ∈ E1B)), (decide (k2 ∈ E2)).
    - set_solver.
    - set_solver.
    - yes. no. yes. set_solver.
    - no. no. no.
    - no. yes. yes. set_solver.
    - no. no. no.
    - no. no. no. set_solver.
    - no. no. no.
  Qed.

  Lemma to_token2_union_1_valid E1A E1B E2 :
    E2 ≠ ∅ → ✓ (to_token2 E1A E2 ⋅ to_token2 E1B E2) → E1A ## E1B.
  Proof.
    intros HE2 HE1.
    rewrite to_token2_op in HE1.
    destruct (coPset_choose E2) as [y Hy]; auto.
    set_unfold.
    intros x. intros.
    specialize (HE1 (x, y)); simpl in HE1.
    unfold to_token2 in HE1; simpl in HE1.
    repeat case_decide; try set_solver.
  Qed.

  Lemma to_token2_union_2 E1 E2A E2B :
    E2A ## E2B →
    to_token2 E1 E2A ⋅ to_token2 E1 E2B
    ≡ to_token2 E1 (E2A ∪ E2B).
  Proof.
    intros DISJ (k1, k2). rewrite discrete_fun_lookup_op.
    destruct (decide (k1 ∈ E1)), (decide (k2 ∈ E2A)), (decide (k2 ∈ E2B)).
    - set_solver.
    - yes. no. yes. set_solver.
    - no. yes. yes. set_solver.
    - no. no. no. set_solver.
    - no. no. no.
    - no. no. no.
    - no. no. no.
    - no. no. no.
  Qed.

  Lemma to_token2_union_2_valid E1 E2A E2B :
    E1 ≠ ∅ → ✓ (to_token2 E1 E2A ⋅ to_token2 E1 E2B) → E2A ## E2B.
  Proof.
    intros HE1 HE2.
    rewrite to_token2_op in HE2.
    destruct (coPset_choose E1) as [x Hx]; auto.
    set_unfold.
    intros y. intros.
    specialize (HE2 (x, y)); simpl in HE2.
    unfold to_token2 in HE2; simpl in HE2.
    repeat case_decide; try set_solver.
  Qed.

  Lemma to_token2_insert_1 E1 E2 k :
    k ∉ E1 →
    to_token2 (E1 ∪ {[k]}) E2
    ≡ to_token2 E1 E2 ⋅ to_token2 {[k]} E2.
  Proof. intros. rewrite to_token2_union_1; set_solver. Qed.

  Lemma to_token2_insert_2 E1 E2 k :
    k ∉ E2 →
    to_token2 E1 (E2 ∪ {[k]})
    ≡ to_token2 E1 E2 ⋅ to_token2 E1 {[k]}.
  Proof. intros. rewrite to_token2_union_2; set_solver. Qed.
End token2R_lemmas.

Class token2G Σ := GhostVars2G {
  token2_inG : inG Σ (token2R);
}.
Local Existing Instance token2_inG.

Definition token2Σ : gFunctors := #[GFunctor token2R].

Global Instance subG_token2Σ {Σ} :
  subG token2Σ Σ → token2G Σ.
Proof. solve_inG. Qed.

Section def.
  Context `{!token2G Σ}.

  Definition token2_def (γ : gname) (E1 E2 : coPset) : iProp Σ :=
    own γ (to_token2 E1 E2).
  Definition token2_aux : seal (@token2_def). Proof. by eexists. Qed.
  Definition token2 := token2_aux.(unseal).
  Definition token2_unseal : @token2 = @token2_def := token2_aux.(seal_eq).
End def.

Section lemmas.
  Context `{!token2G Σ}.
  Implicit Types (k : positive) (E : coPset) (q : Qp).

  Local Ltac unseal := rewrite ?token2_unseal /token2_def.

  Lemma token2_valid_1 γ E1A E1B E2 :
    E2 ≠ ∅ →
    token2 γ E1A E2 -∗ token2 γ E1B E2
    -∗ ⌜E1A ## E1B⌝.
  Proof.
    unseal. iIntros (HE) "T1 T2".
    iCombine "T1 T2" gives %H. iPureIntro.
    eapply to_token2_union_1_valid; done.
  Qed.

  Lemma token2_valid_2 γ E1 E2A E2B :
    E1 ≠ ∅ →
    token2 γ E1 E2A -∗ token2 γ E1 E2B
    -∗ ⌜E2A ## E2B⌝.
  Proof.
    unseal. iIntros (HE) "T1 T2".
    iCombine "T1 T2" gives %?. iPureIntro.
    eapply to_token2_union_2_valid; done.
  Qed.

  Lemma token2_union_1 γ E1A E1B E2 :
    E1A ## E1B →
      token2 γ E1A E2 ∗ token2 γ E1B E2
    ⊣⊢ token2 γ (E1A ∪ E1B) E2.
  Proof. unseal. intros. by rewrite -own_op to_token2_union_1. Qed.

  Lemma token2_union_2 γ E1 E2A E2B :
    E2A ## E2B →
      token2 γ E1 E2A ∗ token2 γ E1 E2B
    ⊣⊢ token2 γ E1 (E2A ∪ E2B).
  Proof. unseal. intros. by rewrite -own_op to_token2_union_2. Qed.

  Lemma token2_get_subset_1 γ E1A E1B E2 :
    E1B ⊆ E1A →
      token2 γ E1A E2 ⊣⊢ token2 γ E1B E2 ∗ token2 γ (E1A ∖ E1B) E2.
  Proof.
    intro SUBSET. assert (E1A = E1B ∪ E1A ∖ E1B) as EQ.
    { rewrite union_comm_L -union_difference_L'; done. }
    rewrite {1}EQ -token2_union_1; [done|].
    apply disjoint_difference_r1. done.
  Qed.

  Lemma token2_get_subset_2 γ E1 E2A E2B :
    E2B ⊆ E2A →
      token2 γ E1 E2A ⊣⊢ token2 γ E1 E2B ∗ token2 γ E1 (E2A ∖ E2B).
  Proof.
    intro SUBSET. assert (E2A = E2B ∪ E2A ∖ E2B) as EQ.
    { rewrite union_comm_L -union_difference_L'; done. }
    rewrite {1}EQ -token2_union_2; [done|].
    apply disjoint_difference_r1. done.
  Qed.

  Lemma token2_get_empty γ E1 E2 :
    E1 = ∅ ∨ E2 = ∅ → ⊢ |==> token2 γ E1 E2.
  Proof.
    unseal. intros. iMod own_unit as "H". iApply (own_update with "H").
    apply discrete_fun_update.
    intros []???; rewrite to_token2_lookup_None; set_solver.
  Qed.
  Lemma token2_get_empty_1 γ E :
    ⊢ |==> token2 γ ∅ E.
  Proof. apply token2_get_empty. by left. Qed.
  Lemma token2_get_empty_2 γ E :
    ⊢ |==> token2 γ E ∅.
  Proof. apply token2_get_empty. by right. Qed.

  Global Instance token2_timeless γ E1 E2 :
    Timeless (token2 γ E1 E2).
  Proof. unseal. apply _. Qed.

  Lemma token2_alloc_strong E1 E2 (P : gname → Prop) :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ token2 γ E1 E2.
  Proof.
    unseal. intros. apply own_alloc_strong; auto using to_token2_valid.
  Qed.
  Lemma token2_alloc E1 E2 :
    ⊢ |==> ∃ γ, token2 γ E1 E2.
  Proof. unseal. apply own_alloc, to_token2_valid. Qed.

  Lemma token2_insert_1 γ E1 E2 k :
    k ∉ E1 →
      token2 γ (E1 ∪ {[k]}) E2
    ⊣⊢ token2 γ E1 E2 ∗ token2 γ {[k]} E2.
  Proof. unseal. intros. by rewrite -own_op -to_token2_insert_1. Qed.

  Lemma token2_insert_2 γ E1 E2 k :
    k ∉ E2 →
      token2 γ E1 (E2 ∪ {[k]})
    ⊣⊢ token2 γ E1 E2 ∗ token2 γ E1 {[k]}.
  Proof. unseal. intros. by rewrite -own_op -to_token2_insert_2. Qed.
End lemmas.
