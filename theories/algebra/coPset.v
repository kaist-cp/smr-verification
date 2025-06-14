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

Local Ltac simplify_gset_to_coPset := set_unfold; setoid_rewrite elem_of_gset_to_coPset; set_unfold.

Lemma gset_to_coPset_union X Y :
  gset_to_coPset (X ∪ Y) = gset_to_coPset X ∪ gset_to_coPset Y.
Proof. by simplify_gset_to_coPset. Qed.

Lemma gset_to_coPset_intersection X Y :
  gset_to_coPset (X ∩ Y) = gset_to_coPset X ∩ gset_to_coPset Y.
Proof. by simplify_gset_to_coPset. Qed.

Lemma gset_to_coPset_difference X Y:
  gset_to_coPset (X ∖ Y) = gset_to_coPset X ∖ gset_to_coPset Y.
Proof. by simplify_gset_to_coPset. Qed.

Lemma gset_to_coPset_difference_union (X Y Z: gset positive)
  (Disj: Y ## Z) (Sub: Y ⊆ X):
  gset_to_coPset (X ∖ Z) = gset_to_coPset (X ∖ (Y ∪ Z)) ∪ gset_to_coPset Y.
Proof.
  simplify_gset_to_coPset => x. split.
  - move => [InX NIn]. case (decide (x ∈ Y)) => [?|NInY].
    + by right.
    + left. split; first auto. by move => [|].
  - set_solver.
Qed.

Lemma gset_to_coPset_difference_disjoint (X Y Z: gset positive):
  gset_to_coPset (X ∖ (Y ∪ Z)) ## gset_to_coPset Y.
Proof. simplify_gset_to_coPset. set_solver. Qed.

Lemma gset_to_coPset_top_difference (X Y: gset positive) (Disj: X ## Y):
  ⊤ ∖  gset_to_coPset X = (⊤ ∖  gset_to_coPset (Y ∪ X)) ∪ gset_to_coPset Y.
Proof.
  simplify_gset_to_coPset => x. split.
  - move => [_ NIn]. case (decide (x ∈ Y)) => [|?]; [by right|left]. set_solver.
  - set_solver.
Qed.

Lemma gset_to_coPset_top_disjoint (X Y: gset positive):
  (⊤ ∖  gset_to_coPset (Y ∪ X)) ## gset_to_coPset Y.
Proof. simplify_gset_to_coPset. set_solver. Qed.

Lemma gset_to_coPset_eq (X Y: gset positive) :
  gset_to_coPset X = gset_to_coPset Y ↔ X = Y.
Proof. by simplify_gset_to_coPset. Qed.

Lemma gset_to_coPset_empty :
  gset_to_coPset ∅ = ∅.
Proof. set_solver. Qed.

Lemma gset_to_coPset_empty_inv X :
  gset_to_coPset X = ∅ → X = ∅.
Proof. by simplify_gset_to_coPset. Qed.

Lemma coPset_difference_top_empty:
  ⊤ ∖ ∅ = (⊤ : coPset).
Proof. set_solver. Qed.

Lemma gset_to_coPset_singleton x :
  gset_to_coPset {[x]} = {[x]}.
Proof.
  (* FIXME: set_unfold unfolds way too much *)
  apply leibniz_equiv => ?. rewrite elem_of_gset_to_coPset. set_solver.
Qed.

Lemma gset_to_coPset_insert X x :
  gset_to_coPset X ∪ {[x]} =
  gset_to_coPset (X ∪ {[x]}).
Proof. by simplify_gset_to_coPset. Qed.

Lemma gset_to_coPset_disjoint X Y :
  X ## Y ↔ gset_to_coPset X ## gset_to_coPset Y.
Proof. by simplify_gset_to_coPset. Qed.

Lemma gset_to_coPset_subset X Y :
  X ⊆ Y ↔ gset_to_coPset X ⊆ gset_to_coPset Y.
Proof. by simplify_gset_to_coPset. Qed.

Lemma not_elem_of_gset_to_coPset i X :
  i ∉ gset_to_coPset X ↔ i ∉ X.
Proof. by simplify_gset_to_coPset. Qed.

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

  Global Instance coPneset_elem_of_decidable p X : Decision (p ∈ X).
  Proof. unfold elem_of, coPneset_elem_of. apply _. Qed.

  Global Program Instance coPneset_union : Union coPneset :=
    λ X1 X2, CoPNESet (coPneset_coPset X1 ∪ coPneset_coPset X2) _.
  Next Obligation.
    intros [X1 HX1] [X2 HX2]. apply bool_decide_pack. simpl.
    apply bool_decide_unpack in HX1, HX2. set_solver.
  Qed.

  Global Instance coPneset_disjoint : Disjoint coPneset :=
    λ X1 X2, coPneset_coPset X1 ## coPneset_coPset X2.

  Global Instance coPneset_disjoint_decidable X Y : Decision (X ## Y).
  Proof. unfold disjoint, coPneset_disjoint. apply _. Qed.

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
    destruct E as [E HE]; simpl.
    by apply bool_decide_unpack in HE.
  Qed.

  Lemma coPneset_construct (X : coPset) :
    X ≠ ∅ → ∃ (E : coPneset), coPneset_coPset E = X.
  Proof.
    intros HX. assert (bool_decide (X ≠ ∅)) as HbX by auto.
    by exists (CoPNESet X HbX).
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
    rewrite !gset_to_coPset_union !gset_to_coPset_singleton.
    set_solver.
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

(* Section coPnesetO.
  Implicit Types (X Y : coPneset).

  Local Instance coPneset_equiv : Equiv coPneset :=
    λ '(CoPNESet X1 _) '(CoPNESet X2 _), X1 ≡ X2.

  Local Instance coPneset_equiv_equivalence : Equivalence coPneset_equiv.
  Proof.
    split.
    - by intros [x].
    - by intros [X1] [X2] ? ?.
    - intros [X1] [X2] [X3] ?? k. by trans (k ∈ X2).
  Qed.

  Canonical Structure coPnesetO := discreteO coPneset.
End coPnesetO. *)


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
       if decide (X ## Y)
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
  Lemma coPneset_disj_valid E : ✓ CoPNESetDisj E.
  Proof. done. Qed.

  Lemma coPneset_disj_valid_op X Y :
    ✓ (CoPNESetDisj X ⋅ CoPNESetDisj Y) ↔ X ## Y.
  Proof. coPneset_disj_solve. Qed.

  Lemma coPneset_disj_valid_inv_l X Y :
    ✓ (CoPNESetDisj X ⋅ Y) → ∃ Y', Y = CoPNESetDisj Y' ∧ X ## Y'.
  Proof.
    destruct Y; intros HX; try done.
    eexists. by apply coPneset_disj_valid_op in HX.
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
  Proof. split; set_solver. Qed.

  Lemma coPneset_disj_elem_of x X :
    x ∈ X ↔ {[x]} ## coPneset_complement X.
  Proof.
    rewrite -coPneset_disj_subset /= -elem_of_subseteq_singleton.
    by rewrite elem_of_gset_to_coPset.
  Qed.

  Global Instance coPneset_disj_top_exclusive :
    Exclusive (CoPNESetDisj ⊤).
  Proof.
    intros E HE%cmra_discrete_valid.
    apply coPneset_disj_valid_inv_l in HE as [Y [HY HDisj]].
    by apply (coPneset_top_disjoint Y).
  Qed.
End coPneset_disjR.
