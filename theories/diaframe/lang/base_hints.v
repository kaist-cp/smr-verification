From iris.proofmode Require Import proofmode.
From diaframe Require Import proofmode_base steps.pure_solver.
From diaframe.lib Require Import persistently intuitionistically.
  (* We import pure_solver to add some pure automation *)
From iris.bi Require Import bi telescopes.

From iris.prelude Require Import options.

Import bi.

(* This file registers the basic hints required to deal with heap_lang's ↦ connective.
   Before we specify the BiAbduction hints, we give some MergableConsume and MergablePersist instances.
   These make Diaframe notice agreement properties, like if we have l ↦{#1/2} v1 and obtain l ↦{#1/2} v2, then
   we must have ⌜v1 = v2⌝ and can combine them to get l ↦ v1. *)


From iris.algebra Require Import lib.frac_auth numbers auth.
From smr.lang Require Import derived_laws notation.

Section instances.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).

  Global Instance simplify_option_fmap_eq_Some {A} {B} f (a: option A) (b: B):
  SimplifyPureHypSafe ((f <$> a) = (Some b)) (∃ a', a = Some a' ∧ f a' = b).
  Proof.
    split.
    - destruct a; try done. simpl. intros [= <-]. eauto.
    - by intros [a' [-> <-]].
  Qed.

  Global Instance simplify_option_fmap_eq_None {A} {B} (f: A -> B) (a: option A):
    SimplifyPureHypSafe ((f <$> a) = None) (a = None).
  Proof.
    split.
    - destruct a; done.
    - naive_solver.
  Qed.

  Global Instance biabd_mapstp_oblk_to_lit_None l:
  HINT l ↦ #(oloc_to_lit None) ✱ [-; True ]
    ⊫ [id] ob;
    l ↦ #(oblk_to_lit ob)  ✱ [ ⌜ ob = None ⌝ ].
  Proof. iSteps. iExists None. iSteps. Qed.

  Global Instance biabd_mapstp_oblk_to_lit_Some l l' ob:
    HINT l ↦ #(oloc_to_lit (Some l')) ✱ [b'; ⌜ l' = blk_to_loc b' ⌝ ∗ ⌜ ob = Some b' ⌝  ]
    ⊫ [id] ob;
    l ↦ #(oblk_to_lit ob)  ✱ [ ⌜ l' = blk_to_loc b' ⌝ ∗ ⌜ ob = Some b' ⌝ ] .
  Proof. iSteps. iExists (Some x). iSteps. Qed.

  Fixpoint array_construction (l: blk) (i: Z) vs: iProp :=
  match vs with
  | [] => True
  | x :: vs' => (l +ₗ i) ↦ x ∗ array_construction l (i + 1) vs'
  end.

  Global Instance start_array_construct (l: blk) v:
    HINT (l +ₗ 0) ↦ v ✱ [vs'; array_construction l 1 vs'] ⊫ [id] vs; l ↦∗ vs ✱ [ ⌜ vs = v :: vs' ⌝ ] | 0.
  Proof.
    do 2 iStep. iExists _; iSplit; last done. rename x into vs.
    iAssert (∀ i, array_construction l i vs -∗ (l +ₗ i) ↦∗ vs)%I as "G". {
      iInduction vs as [| x vs'] "IH"; unfold array; [auto| ].
      iIntros (?) "AC". simpl. rewrite loc_add_assoc. replace (i + 0%nat)%Z with i; last lia. iDestruct "AC" as "[$ AC']".
      iDestruct ("IH" with "AC'") as "big_l↦". iApply (big_sepL_mono with "big_l↦"). iIntros. repeat rewrite loc_add_assoc.
      replace (i + S k)%Z with (i + 1 + k)%Z; last lia. done.
    }
    iSpecialize ("G" with "H2"). unfold array. iFrame. iApply (big_sepL_mono with "G").
    iSteps. rewrite loc_add_assoc.
    have <-: (1 + x = S x)%Z; first lia. done.
  Qed.

  Global Instance construct_array_step (l: blk) (vs: list val) v (n: Z):
    HINT (l +ₗ n) ↦ v ✱ [vs'; array_construction l (n + 1) vs' ∗ ⌜ vs = v :: vs' ⌝ ]
      ⊫ [id];
      array_construction l n vs ✱ [ ⌜ vs = v :: vs' ⌝ ].
  Proof. iSteps. Qed.

  Global Instance construct_array_end (l: blk) (vs: list val) (n: Z) :
    TCIf (SolveSepSideCondition (vs ≠ [])) False TCTrue →
    HINT ε₁ ✱ [-; ⌜ vs = [] ⌝ ]
      ⊫ [id];
    array_construction l n vs ✱ [ ⌜ vs = [] ⌝  ].
  Proof. intros. iSteps. Qed.

  Global Instance biabd_unfold_array l (vs: list val):
    HINT ε₁ ✱ [-; [∗ list] i↦v ∈ vs, (l +ₗ i) ↦ v] ⊫ [id]; l ↦∗ vs ✱ [ True ].
  Proof. unfold array. iSteps. Qed.

  Section mergable.
    Global Instance mergable_consume_mapsto_persist l v1 v2 :
      MergableConsume (l ↦□ v1)%I true (λ p Pin Pout, TCAnd (TCEq Pin (l ↦□ v2)) (TCEq Pout (l ↦□ v1 ∗ ⌜v1 = v2⌝)))%I | 40.
    Proof.
      rewrite /MergableConsume => p Pin Pout [-> ->].
      rewrite bi.intuitionistically_if_elim.
      iStepS.
      iDestruct (mapsto_combine with "H1 H2") as "[H ->]".
      iStepsS.
    Qed.

    Global Instance mergable_consume_mapsto_own q1 q2 q l v1 v2 :
      MergableConsume (l ↦{#q1} v1)%I true (λ p Pin Pout,
          TCAnd (TCEq Pin (l ↦{#q2} v2)) $
          TCAnd (proofmode_classes.IsOp (A := fracR) q q1 q2) $
                (TCEq Pout (l ↦{#q} v1 ∗ ⌜v1 = v2⌝)))%I | 30. (* this does not include q ≤ 1! *)
    Proof.
      rewrite /MergableConsume => p Pin Pout [-> [+ ->]].
      rewrite bi.intuitionistically_if_elim => Hq.
      iStepS.
      iDestruct (mapsto_combine with "H1 H2") as "[H ->]".
      rewrite dfrac_op_own Hq.
      iStepsS.
    Qed.

    Global Instance mergable_persist_mapsto_dfrac_own q1 dq2 l v1 v2 :
      MergablePersist (l ↦{#q1} v1)%I (λ p Pin Pout, TCAnd (TCEq Pin (l ↦{dq2} v2)) (TCEq Pout ⌜v1 = v2 ∧ q1 < 1⌝%Qp))%I | 50.
    Proof.
      rewrite /MergableConsume => p Pin Pout [-> ->].
      rewrite bi.intuitionistically_if_elim.
      iStepS.
      iDestruct (mapsto_combine with "H1 H2") as "[H ->]".
      iDestruct (mapsto_valid with "H") as %?%dfrac_valid_own_l.
      iStepsS.
    Qed.

    Global Instance mergable_persist_mapsto_dfrac_own2 q1 dq2 l v1 v2 :
      MergablePersist (l ↦{dq2} v1)%I (λ p Pin Pout, TCAnd (TCEq Pin (l ↦{#q1} v2)) (TCEq Pout ⌜v1 = v2 ∧ q1 < 1⌝%Qp))%I | 50.
    Proof.
      rewrite /MergableConsume => p Pin Pout [-> ->].
      rewrite bi.intuitionistically_if_elim.
      iStepsS.
    Qed.

    (* this last instance is necessary for opaque dq1 and dq2 *)
    Global Instance mergable_persist_mapsto_last_resort dq1 dq2 l v1 v2 :
      MergablePersist (l ↦{dq1} v1)%I (λ p Pin Pout, TCAnd (TCEq Pin (l ↦{dq2} v2)) (TCEq Pout ⌜v1 = v2⌝))%I | 99.
    Proof.
      rewrite /MergableConsume => p Pin Pout [-> ->].
      rewrite bi.intuitionistically_if_elim.
      iStepS.
      iDestruct (mapsto_combine with "H1 H2") as "[H ->]".
      iStepsS.
    Qed.


    (* prophecies are also exclusive! *)
    Global Instance proph_exclusive p vs vs' : MergableConsume (proph p vs) true (λ b Pin Pout,
        TCAnd (TCEq Pin (proph p vs')) $
              (TCEq Pout (False%I))).
    Proof.
      move => b Pin Pout [-> ->].
      rewrite bi.intuitionistically_if_elim.
      iIntros "[P1 P2]".
      iApply (proph_exclusive with "P1 P2").
    Qed.

    (* as a consequence, this holds. Useful as long as prophecies dont have fractions *)
    Global Instance prophs_are_ne p vs p' vs' : MergablePersist (proph p vs) (λ b Pin Pout,
      TCAnd (TCEq Pin (proph p' vs')) $
             TCEq Pout ⌜p ≠ p'⌝%I).
    Proof.
      move => b Pin Pout [-> ->].
      rewrite bi.intuitionistically_if_elim.
      destruct (decide (p = p')) as [->|Hneq]; iStepsS.
    Qed.
  End mergable.

  Section biabds.
    Global Instance mapsto_val_may_need_more (l : loc) (v1 v2 : val) (q1 q2 : Qp) mq q :
      FracSub q2 q1 mq →
      TCEq mq (Some q) →
      HINT l ↦{#q1} v1 ✱ [v'; ⌜v1 = v2⌝ ∗ l ↦{#q} v'] ⊫ [id]; l ↦{#q2} v2 ✱ [⌜v1 = v2⌝ ∗ ⌜v' = v1⌝] | 55.
    Proof.
      rewrite /FracSub => <- -> v' /=.
      iStepsS.
    Qed.

    Global Instance mapsto_val_have_enough (l : loc) (v1 v2 : val) (q1 q2 : Qp) mq :
      FracSub q1 q2 mq →
      HINT l ↦{#q1} v1 ✱ [- ; ⌜v1 = v2⌝] ⊫ [id]; l ↦{#q2}v2 ✱ [⌜v1 = v2⌝ ∗ match mq with | Some q => l ↦{#q} v1 | _ => True end] | 54.
    Proof.
      rewrite /= /FracSub => <-.
      destruct mq; iStepsS.
      iDestruct "H1" as "[H1 H1']".
      iStepsS.
    Qed.

    Class OffsetLoc l i li :=
      offset_loc_eq : li = l +ₗ i.

    Global Instance offset_loc_default l i : OffsetLoc l i (l +ₗ i) | 50.
    Proof. done. Qed.

    Global Instance offset_loc_collect l i1 li1 i2 :
      OffsetLoc l i1 li1 →
      OffsetLoc li1 i2 (l +ₗ (i1 + i2)).
    Proof.
      rewrite /OffsetLoc => ->.
      rewrite loc_add_assoc //.
    Qed.

    Global Instance as_persistent_mapsto p l q v :
      HINT □⟨p⟩ l ↦{q} v ✱ [- ; emp] ⊫ [bupd]; l ↦□ v ✱ [l ↦□ v] | 100.
    Proof.
      iIntros "Hl" => /=.
      rewrite /= right_id bi.intuitionistically_if_elim.
      iMod (mapsto_persist with "Hl") as "#Hl".
      iStepsS.
    Qed.

    Global Arguments array : simpl never. (* we don't want cbn to expand array *)

    Global Instance array_mapsto_head l v vs q l' :
      OffsetLoc l 1 l' → (* this makes us get (l +ₗ (1 + 1)) instead of ((l +ₗ 1) +ₗ 1) *)
      HINT l ↦∗{q} vs ✱ [- ; ⌜hd_error vs = Some v⌝] ⊫ [id]; l ↦{q} v ✱ [l' ↦∗{q} tail vs ∗ ⌜hd_error vs = Some v⌝] | 20.
    Proof.
      rewrite /= /OffsetLoc => ->.
      iIntros "[H %] /=".
      destruct vs => //.
      iDestruct (array_cons with "H") as "[Hv Hl]"; iFrame.
      case: H => ->. iStepsS.
    Qed.

    Global Instance head_mapsto_array l v vs q l' :
      OffsetLoc l 1 l' →
      HINT l ↦{q} v ✱ [- ; ⌜hd_error vs = Some v⌝ ∗ l' ↦∗{q} tail vs] ⊫ [id]; l ↦∗{q} vs ✱ [emp] | 20.
    Proof.
      rewrite /= => ->.
      iIntros "(H & % & Htl) /=".
      destruct vs => //.
      case: H => ->.
      rewrite array_cons.
      iStepsS.
    Qed.

    Global Instance array_mapsto_head_offset l v vs q i l':
      SolveSepSideCondition (0 ≤ i < length vs)%Z →               (* that this is_Some is given, but that it is equal to v is a proof obligation *)
      OffsetLoc l (Z.succ i) l' →
      HINT l ↦∗{q} vs ✱ [ - ; ⌜vs !! Z.to_nat i = Some v⌝] ⊫ [id]; (l +ₗ i) ↦{q} v ✱ [
           (l ↦∗{q} take (Z.to_nat i) vs) ∗ ⌜vs !! Z.to_nat i = Some v⌝ ∗ (l' ↦∗{q} drop (S $ Z.to_nat i) vs)] | 20.
    Proof.
      rewrite /SolveSepSideCondition /= => Hi ->.
      iStepS.
      rewrite -{1}(take_drop_middle _ _ _ H).
      rewrite array_app array_cons; iRevert "H1"; iStepS.
      rewrite take_length_le; last lia.
      rewrite Z2Nat.id; last lia.
      iStepsS.
      rewrite loc_add_assoc.
      iStepsS.
    Qed.

    Global Instance array_from_shorter vs1 vs2 l l' q :
      SolveSepSideCondition (length vs1 ≤ length vs2) →
      OffsetLoc l (length vs1) l' →
      HINT l ↦∗{q} vs1 ✱ [- ; ⌜take (length vs1) vs2 = vs1⌝ ∗ l' ↦∗{q} (list.drop (length vs1) vs2) ] ⊫ [id];
           l ↦∗{q} vs2 ✱ [emp] | 51.
    Proof.
      rewrite /SolveSepSideCondition => Hl -> /=.
      iStepS.
      rewrite -{2}(take_drop (length vs1) vs2) H array_app.
      iStepsS.
    Qed.

    Global Instance empty_array_solve l q :
      HINT ε₁ ✱ [- ; emp] ⊫ [id]; l ↦∗{q} [] ✱ [emp].
    Proof.
      iStepsS. rewrite array_nil. iStepsS.
    Qed.
  End biabds.

  Section abds.
    Global Instance fork_abduct e (Φ : val → iPropI Σ) s E :
      HINT1 ε₁ ✱ [▷ Φ #() ∗ ▷ WP e @ s; ⊤ {{ _, True }}] ⊫ [id]; wp s E (Fork e) Φ.
    Proof. (* eliding the type of Φ will give fork_abduct weird unsimplified (and ununifiable!) TeleO -t> T types *)
      iStepsS. iApply (wp_fork with "H2"). iStepsS.
    Qed.
  End abds.

End instances.

Global Hint Mode OffsetLoc + + - : typeclass_instances.
Global Hint Mode OffsetLoc - - + : typeclass_instances.

Section side_condition_lemmas.
  Lemma val_neq_lit_neq (l1 l2 : base_lit) : l1 ≠ l2 → LitV l1 ≠ LitV l2.
  Proof. move => H [= /H //]. Qed.

  Lemma lit_neq_Z_neq (l1 l2 : Z) : l1 ≠ l2 → LitInt l1 ≠ LitInt l2.
  Proof. move => H [= /H //]. Qed.

  Lemma lit_neq_bool_neq (l1 l2 : bool) : l1 ≠ l2 → LitBool l1 ≠ LitBool l2.
  Proof. move => H [= /H //]. Qed.

  Lemma injr_neq_val_neq (v1 v2 : val) : v1 ≠ v2 → InjRV v1 ≠ InjRV v2.
  Proof. move => H [= /H //]. Qed.

  Lemma injl_neq_val_neq (v1 v2 : val) : v1 ≠ v2 → InjLV v1 ≠ InjLV v2.
  Proof. move => H [= /H //]. Qed.

  Global Instance simplify_lit_val_neq (l1 l2 : base_lit) : SimplifyPureHypSafe (LitV l1 ≠ LitV l2) (l1 ≠ l2).
  Proof. split; first (move => + Hl; by subst). apply val_neq_lit_neq. Qed.

  Global Instance simplify_lit_int_neq (l1 l2 : Z) : SimplifyPureHypSafe (LitInt l1 ≠ LitInt l2) (l1 ≠ l2).
  Proof. split; first (move => + Hl; by subst). apply lit_neq_Z_neq. Qed.

  Global Instance simplify_lit_bool_neq (l1 l2 : bool) : SimplifyPureHypSafe (LitBool l1 ≠ LitBool l2) (l1 ≠ l2).
  Proof. split; first (move => + Hl; by subst). apply lit_neq_bool_neq. Qed.

  Global Instance simplify_injr_neq (l1 l2 : val) : SimplifyPureHypSafe (InjRV l1 ≠ InjRV l2) (l1 ≠ l2).
  Proof. split; first (move => + Hl; by subst). apply injr_neq_val_neq. Qed.

  Global Instance simplify_injl_neq (l1 l2 : val) : SimplifyPureHypSafe (InjLV l1 ≠ InjLV l2) (l1 ≠ l2).
  Proof. split; first (move => + Hl; by subst). apply injl_neq_val_neq. Qed.

  Global Instance simplify_injl_injr_eq (l1 l2 : val) : SimplifyPureHypSafe (InjLV l1 = InjRV l2) False.
  Proof. split => H; last done. inversion H. Qed.

  Global Instance simplify_injl_injl_eq (l1 l2 : val) : SimplifyPureHypSafe (InjRV l1 = InjLV l2) False.
  Proof. split => H; last done. inversion H. Qed.
End side_condition_lemmas.

Ltac solveValEq :=
  (progress f_equal); trySolvePureEq.


Ltac trySolvePureEqAdd1 :=
  lazymatch goal with
  | |- @eq ?T ?l ?r =>
    match constr:((T, l)) with
    | (val, _) => solveValEq
    | (base_lit, _) => solveValEq
    end
  end.

Global Hint Extern 4 (_ = _) => trySolvePureEqAdd1 : solve_pure_eq_add.

Ltac trySolvePureAdd1 :=
  match goal with
  | |- LitV ?v1 ≠ LitV ?v2 =>
    assert_fails (has_evar v1);
    assert_fails (has_evar v2);
    eapply val_neq_lit_neq; solve [pure_solver.trySolvePure]
  | |- LitInt ?v1 ≠ LitInt ?v2 =>
    assert_fails (has_evar v1);
    assert_fails (has_evar v2);
    eapply lit_neq_Z_neq; solve [pure_solver.trySolvePure]
  | |- LitBool ?v1 ≠ LitBool ?v2 =>
    assert_fails (has_evar v1);
    assert_fails (has_evar v2);
    eapply lit_neq_bool_neq; solve [pure_solver.trySolvePure]
  | |- InjRV ?v1 ≠ InjRV ?v2 =>
    assert_fails (has_evar v1);
    assert_fails (has_evar v2);
    eapply injr_neq_val_neq; solve [pure_solver.trySolvePure]
  | |- InjLV ?v1 ≠ InjLV ?v2 =>
    assert_fails (has_evar v1);
    assert_fails (has_evar v2);
    eapply injl_neq_val_neq; solve [pure_solver.trySolvePure]
  | |- vals_compare_safe _ _ => (by left) || (by right)
  end.

Global Hint Extern 4 => trySolvePureAdd1 : solve_pure_add.
