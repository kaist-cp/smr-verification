From stdpp Require Import gmap.
From iris.algebra Require Export cmra coPset.
From iris.algebra Require Import updates local_updates big_op.
From iris.prelude Require Import options.

(** * coPset lemmas based on nat_tokens.v by Hoang-Hai Dang **)
Section nat_tokens.
Definition Pos_upto_set (up: nat) : gset positive :=
  list_to_set (Pos.of_nat <$> (seq 1 up)).

Definition coPset_from_ex (i: nat): coPset
  := ⊤ ∖  gset_to_coPset (Pos_upto_set i).

Lemma coPset_from_ex_gt i p:
  p ∈ coPset_from_ex i ↔ (i < Pos.to_nat p)%nat.
Proof.
  rewrite elem_of_difference elem_of_gset_to_coPset.
  rewrite elem_of_list_to_set elem_of_list_fmap. split.
  - move => [_ /= NIn].
    apply: not_ge => ?. apply: NIn.
    exists (Pos.to_nat p). rewrite Pos2Nat.id elem_of_list_In in_seq. lia.
  - move => Lt. split; [done|].
    move => [n [Eqn /elem_of_list_In /in_seq [Ge1 Lt2]]].
    subst. rewrite Nat2Pos.id_max in Lt. lia.
Qed.

Lemma coPset_from_insert i:
  coPset_from_ex i = {[Pos.of_succ_nat i]} ∪ coPset_from_ex (S i).
Proof.
  apply leibniz_equiv.
  move => p. rewrite elem_of_union elem_of_singleton !coPset_from_ex_gt. lia.
Qed.

Lemma coPset_from_disjoint i:
  {[Pos.of_succ_nat i]} ## coPset_from_ex (S i).
Proof.
  rewrite disjoint_singleton_l coPset_from_ex_gt SuccNat2Pos.id_succ. lia.
Qed.

Lemma gset_to_coPset_union X Y :
  gset_to_coPset (X ∪ Y) = gset_to_coPset X ∪ gset_to_coPset Y.
Proof.
  apply leibniz_equiv.
  move => ?. by rewrite elem_of_union !elem_of_gset_to_coPset elem_of_union.
Qed.

Lemma gset_to_coPset_intersection X Y :
  gset_to_coPset (X ∩ Y) = gset_to_coPset X ∩ gset_to_coPset Y.
Proof.
  apply leibniz_equiv.
  move => ?. by rewrite elem_of_intersection !elem_of_gset_to_coPset elem_of_intersection.
Qed.

Lemma gset_to_coPset_difference X Y:
  gset_to_coPset (X ∖ Y) = gset_to_coPset X ∖ gset_to_coPset Y.
Proof.
  apply leibniz_equiv => ?.
  by rewrite elem_of_difference !elem_of_gset_to_coPset elem_of_difference.
Qed.

Lemma gset_to_coPset_difference_union (X Y Z: gset positive)
  (Disj: Y ## Z) (Sub: Y ⊆ X):
  gset_to_coPset (X ∖ Z) = gset_to_coPset (X ∖ (Y ∪ Z)) ∪ gset_to_coPset Y.
Proof.
  apply leibniz_equiv => x.
  rewrite elem_of_union !elem_of_gset_to_coPset
          !elem_of_difference elem_of_union.
  split.
  - move => [InX NIn]. case (decide (x ∈ Y)) => [?|NInY].
    + by right.
    + left. split; first auto. by move => [|].
  - set_solver.
Qed.

Lemma gset_to_coPset_difference_disjoint (X Y Z: gset positive):
  gset_to_coPset (X ∖ (Y ∪ Z)) ## gset_to_coPset Y.
Proof.
  rewrite elem_of_disjoint => ?.
  rewrite !elem_of_gset_to_coPset elem_of_difference elem_of_union.
  set_solver.
Qed.

Lemma gset_to_coPset_top_difference (X Y: gset positive) (Disj: X ## Y):
  ⊤ ∖  gset_to_coPset X = (⊤ ∖  gset_to_coPset (Y ∪ X)) ∪ gset_to_coPset Y.
Proof.
  apply leibniz_equiv. move => x.
  rewrite elem_of_union !elem_of_difference
          !elem_of_gset_to_coPset elem_of_union.
  split.
  - move => [_ NIn]. case (decide (x ∈ Y)) => [|?]; [by right|left]. set_solver.
  - set_solver.
Qed.

Lemma gset_to_coPset_top_disjoint (X Y: gset positive):
  (⊤ ∖  gset_to_coPset (Y ∪ X)) ## gset_to_coPset Y.
Proof.
  rewrite elem_of_disjoint.
  move => x. rewrite elem_of_difference gset_to_coPset_union. set_solver.
Qed.

Lemma gset_to_coPset_eq (X Y: gset positive) :
  gset_to_coPset X = gset_to_coPset Y ↔ X = Y.
Proof.
  split; [intro EQ|intros ->;done].
  set_unfold. intro i. specialize (EQ i).
  rewrite !elem_of_gset_to_coPset in EQ. done.
Qed.

Lemma gset_to_coPset_empty :
  gset_to_coPset ∅ = ∅.
Proof. by apply leibniz_equiv. Qed.

Lemma gset_to_coPset_empty_inv X :
  gset_to_coPset X = ∅ → X = ∅.
Proof.
  do 2 rewrite set_eq.
  intro. intros. specialize (H x).
  rewrite elem_of_gset_to_coPset in H. set_solver.
Qed.

Lemma coPset_difference_top_empty:
  ⊤ ∖ ∅ = (⊤ : coPset).
Proof. by apply leibniz_equiv. Qed.

Lemma gset_to_coPset_singleton x :
  gset_to_coPset {[x]} = {[x]}.
Proof. apply leibniz_equiv => ?. rewrite elem_of_gset_to_coPset. set_solver. Qed.

Lemma gset_to_coPset_insert X x :
  gset_to_coPset X ∪ {[x]} =
  gset_to_coPset (X ∪ {[x]}).
Proof. by rewrite gset_to_coPset_union gset_to_coPset_singleton. Qed.

Lemma gset_to_coPset_disjoint X Y :
  X ## Y ↔ gset_to_coPset X ## gset_to_coPset Y.
Proof.
  do 2 rewrite elem_of_disjoint.
  split; intros.
  - rewrite elem_of_gset_to_coPset in H0.
    rewrite elem_of_gset_to_coPset in H1. by eapply H.
  - eapply H; by rewrite elem_of_gset_to_coPset.
Qed.

Lemma gset_to_coPset_subset X Y :
  X ⊆ Y ↔ gset_to_coPset X ⊆ gset_to_coPset Y.
Proof.
  do 2 rewrite elem_of_subseteq.
  split; intros.
  - rewrite elem_of_gset_to_coPset in H0.
    rewrite elem_of_gset_to_coPset. by apply H.
  - rewrite -elem_of_gset_to_coPset.
    apply H; by rewrite elem_of_gset_to_coPset.
Qed.

Lemma not_elem_of_gset_to_coPset i X :
  i ∉ gset_to_coPset X ↔ i ∉ X.
Proof. split; intros ? ?%elem_of_gset_to_coPset; set_solver. Qed.

Lemma coPset_complement_infinite X :
  set_infinite (⊤ ∖ gset_to_coPset X).
Proof. apply difference_infinite; [apply top_infinite|apply gset_to_coPset_finite]. Qed.

End nat_tokens.


(** * Non-empty [coPset] *)
Record coPneset := CoPNESet {
  coPneset_coPset : coPset;
  coPneset_ne : bool_decide (coPneset_coPset ≠ ∅);
}.

Section coPneset.
  Implicit Types (X Y : coPneset).

  Lemma coPneset_eq (X1 X2 : coPneset) :
    X1 = X2 ↔ coPneset_coPset X1 = coPneset_coPset X2.
  Proof.
    split; [by intros ->|intros]. destruct X1, X2; simplify_eq/=.
    f_equal; apply proof_irrel.
  Qed.

  Global Program Instance coPneset_singleton : Singleton positive coPneset :=
    λ x, CoPNESet (singleton x) _.
  Next Obligation. intro. apply bool_decide_pack. set_solver. Qed.

  Program Definition coPneset_complement (s : gset positive) :=
    CoPNESet (⊤ ∖ gset_to_coPset s) _.
  Next Obligation.
    intros. apply bool_decide_pack.
    have F := coPset_complement_infinite s.
    intros Hs. rewrite Hs in F.
    apply (set_not_infinite_finite _ F), empty_finite.
  Qed.

  Global Program Instance coPneset_top : Top coPneset := CoPNESet ⊤ _.
  Next Obligation. intros. apply bool_decide_pack. done. Qed.

  Global Instance coPneset_elem_of: ElemOf positive coPneset :=
    λ p X, p ∈ coPneset_coPset X.

  Global Program Instance coPneset_union : Union coPneset :=
    λ X1 X2, CoPNESet (coPneset_coPset X1 ∪ coPneset_coPset X2) _.
  Next Obligation.
    intros [X1 HX1] [X2 HX2]. apply bool_decide_pack. simpl.
    apply bool_decide_unpack in HX1, HX2. set_solver.
  Qed.

  Global Instance coPneset_disjoint : Disjoint coPneset :=
    λ X1 X2, coPneset_coPset X1 ## coPneset_coPset X2.

  Lemma coPneset_elem_of_iff x (E : coPneset) :
    x ∈ E ↔ x ∈ coPneset_coPset E.
  Proof.
    unfold coPneset_elem_of. done.
  Qed.

  Lemma coPneset_disj_iff (X1 X2 : coPneset) :
    X1 ## X2 ↔ coPneset_coPset X1 ## coPneset_coPset X2.
  Proof.
    unfold coPneset_disjoint. done.
  Qed.

  Lemma coPneset_union_eq (X1 X2 : coPneset) :
    coPneset_coPset (X1 ∪ X2) = coPneset_coPset X1 ∪ coPneset_coPset X2.
  Proof.
    unfold coPneset_union. done.
  Qed.

  Lemma coPneset_union_singleton (X : coPneset) x :
    coPneset_coPset (X ∪ {[x]}) = coPneset_coPset X ∪ {[x]}.
  Proof.
    rewrite coPneset_union_eq. done.
  Qed.

  Lemma coPneset_disjoint_singleton_r (X : coPneset) x :
    X ## {[x]} ↔ x ∉ X.
  Proof.
    rewrite coPneset_disj_iff disjoint_singleton_r. done.
  Qed.

  Lemma coPneset_is_singleton x (E : coPneset) :
    coPneset_coPset E = {[x]} → E = ({[x]} : coPneset).
  Proof. simpl. rewrite coPneset_eq. auto. Qed.

  Lemma coPneset_nonempty (E : coPneset) :
    coPneset_coPset E ≠ ∅.
  Proof.
    destruct E; simpl.
    by apply bool_decide_unpack in coPneset_ne0.
  Qed.

  Lemma coPneset_construct (X : coPset) :
    X ≠ ∅ → ∃ (E : coPneset), coPneset_coPset E = X.
  Proof.
    intros.
    eapply bool_decide_pack in H. Unshelve. 2: apply _.
    exists (CoPNESet X H). auto.
  Qed.

  Lemma coPneset_top_disjoint X : ¬ ⊤ ## X.
  Proof.
    destruct X as [X NE]. intro.
    assert (X = ∅) by set_solver. set_solver.
  Qed.

  Lemma complement_insert ss x :
    x ∉ ss →
    coPneset_complement ss =
    {[x]} ∪ (coPneset_complement (ss ∪ {[x]})).
  Proof.
    intros. apply coPneset_eq. simpl.
    rewrite (gset_to_coPset_top_difference _ {[x]}); last set_solver.
    rewrite gset_to_coPset_singleton.
    replace ({[x]} ∪ ss) with (ss ∪ {[x]}) by set_solver. set_solver.
  Qed.

  Lemma complement_delete ss x :
    x ∈ ss →
    coPneset_complement (ss ∖ {[x]}) =
    {[x]} ∪ coPneset_complement ss.
  Proof.
    rewrite (complement_insert (ss ∖ {[x]}) x); last set_solver.
    intros. replace (ss ∖ {[x]} ∪ {[x]}) with ss; auto.
    rewrite (union_difference_L {[x]} ss); set_solver.
  Qed.

  Lemma top_complement_singleton x :
    ⊤ = {[x]} ∪ (coPneset_complement {[x]}) .
  Proof.
    rewrite -(complement_delete {[x]} x); last set_solver.
    rewrite difference_diag_L.
    rewrite coPneset_eq. set_solver.
  Qed.
End coPneset.

Section coPnesetO.
  Implicit Types (X Y : coPneset).

  Local Instance coPneset_dist : Dist coPneset :=
    λ n '(CoPNESet X1 _) '(CoPNESet X2 _), X1 ≡{n}≡ X2.
  Local Instance coPneset_equiv : Equiv coPneset :=
    λ '(CoPNESet X1 _) '(CoPNESet X2 _), X1 ≡ X2.

  Definition coPneset_ofe_mixin : OfeMixin coPneset.
  Proof.
    split.
    - intros [X1] [X2]; apply equiv_dist.
    - intros n; split.
      + by intros [x].
      + by intros [X1] [X2] ? ?.
      + intros [X1] [X2] [X3] ?? k. by trans (k ∈ X2).
    - done.
  Qed.
  Canonical Structure coPnesetO : ofe := Ofe coPneset coPneset_ofe_mixin.
End coPnesetO.


(** * Non-empty [coPset] camera with disjoint union. *)
Inductive coPneset_disj :=
  | CoPNESetDisj : coPneset → coPneset_disj
  | CoPNESetDisjBot : coPneset_disj.

Section coPneset_disjR.
  Canonical Structure coPneset_disjO := leibnizO coPneset_disj.
  Local Instance coPneset_disj_valid_instance : Valid coPneset_disj :=
    λ X, match X with
    | CoPNESetDisj _ => True
    | CoPNESetDisjBot => False
    end.
  Local Instance coPneset_disj_op_instance : Op coPneset_disj :=
    λ X Y, match X, Y with
    | CoPNESetDisj X, CoPNESetDisj Y =>
       if decide (coPneset_coPset X ## coPneset_coPset Y)
       then CoPNESetDisj (X ∪ Y)
       else CoPNESetDisjBot
    | _, _ => CoPNESetDisjBot
    end.
  Local Instance coPneset_disj_pcore_instance : PCore coPneset_disj :=
    λ _, None.

  Ltac coPneset_disj_solve :=
    repeat (simpl || case_decide || unfold op || unfold cmra_op);
    first [apply (f_equal CoPNESetDisj)|done|exfalso];
    try apply coPneset_eq;
    set_solver.

  Lemma coPneset_disj_ra_mixin : RAMixin coPneset_disj.
  Proof.
    split; try apply _; try done.
    - intros [[X1 ?]|] [[X2 ?]|] [[X3 ?]|]; coPneset_disj_solve.
    - intros [[X1 ?]|] [[X2 ?]|]; coPneset_disj_solve.
    - intros [[X1 ?]|] [[X2 ?]|]; coPneset_disj_solve.
  Qed.
  Canonical Structure coPneset_disjR :=
    discreteR coPneset_disj coPneset_disj_ra_mixin.

  Global Instance coPneset_disj_cmra_discrete : CmraDiscrete coPneset_disjR.
  Proof. apply discrete_cmra_discrete. Qed.

  (* lemmas *)
  Lemma coPneset_disj_validN n E : ✓{n} CoPNESetDisj E.
  Proof. done. Qed.
  Lemma coPneset_disj_valid E : ✓ CoPNESetDisj E.
  Proof. done. Qed.

  Lemma coPneset_disj_validN_op n X Y :
    ✓{n} (CoPNESetDisj X ⋅ CoPNESetDisj Y) ↔ X ## Y.
  Proof. coPneset_disj_solve. Qed.
  Lemma coPneset_disj_valid_op X Y :
    ✓ (CoPNESetDisj X ⋅ CoPNESetDisj Y) ↔ X ## Y.
  Proof. coPneset_disj_solve. Qed.

  Lemma coPneset_disj_validN_inv_l n X Y :
    ✓{n} (CoPNESetDisj X ⋅ Y) → ∃ Y', Y = CoPNESetDisj Y' ∧ X ## Y'.
  Proof.
    destruct Y; intros; try done.
    exists c. by apply coPneset_disj_valid_op in H.
  Qed.
  Lemma coPneset_disj_valid_inv_l X Y :
    ✓ (CoPNESetDisj X ⋅ Y) → ∃ Y', Y = CoPNESetDisj Y' ∧ X ## Y'.
  Proof.
    destruct Y; intros; try done.
    exists c. by apply coPneset_disj_valid_op in H.
  Qed.

  Lemma coPneset_disj_union X Y :
    X ## Y →
    CoPNESetDisj X ⋅ CoPNESetDisj Y = CoPNESetDisj (X ∪ Y).
  Proof. coPneset_disj_solve. Qed.

  Lemma coPneset_disj_op_inv E E1 E2 :
    CoPNESetDisj E1 ⋅ CoPNESetDisj E2 = CoPNESetDisj E →
    E1 ## E2.
  Proof. coPneset_disj_solve. Qed.

  Lemma coPneset_disj_subset X Y :
    coPneset_coPset X ⊆ gset_to_coPset Y ↔
    X ## coPneset_complement Y.
  Proof.
    unfold coPneset_complement. unfold disjoint.
    unfold coPneset_disjoint. simpl.
    split; [rewrite elem_of_disjoint; set_solver|set_solver].
  Qed.

  Lemma coPneset_disj_elem_of x X :
    x ∈ X ↔ {[x]} ## coPneset_complement X.
  Proof.
    rewrite <- coPneset_disj_subset. simpl.
    rewrite <- elem_of_subseteq_singleton.
    by rewrite elem_of_gset_to_coPset.
  Qed.

  Global Instance coPneset_disj_top_exclusive :
    Exclusive (CoPNESetDisj ⊤).
  Proof.
    intro. intros.
    apply coPneset_disj_valid_inv_l in H as [Y [HY HDisj]].
    by apply (coPneset_top_disjoint Y).
  Qed.
End coPneset_disjR.
