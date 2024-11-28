(** Cameras for non-empty [gset]. *)
From stdpp Require Export sets gmap mapset.
From iris.algebra Require Export cmra gset.
From iris.algebra Require Import updates local_updates big_op.
From iris.prelude Require Import options.

Record gneset K `{Countable K} := GNESet {
  gneset_gset : gset K;
  gneset_ne : bool_decide (gneset_gset ≠ ∅);
}.
Global Arguments GNESet {_ _ _} _ _ : assert.
Global Arguments gneset_gset {_ _ _} _ : assert.

Program Definition mk_gneset `{Countable K} (x : K) (s : gset K) :=
  GNESet ({[x]} ∪ s) _.
Next Obligation. intros. apply bool_decide_pack. set_solver. Qed.

(* Program Definition gneset_map `{Countable A, Countable B} *)
(*     (f : A → B) (X : gneset A) : gneset B := *)
(*   GNESet (set_map f (gneset_gset X)) _. *)
(* Next Obligation. *)
(*   intros. destruct X as [X' NE]. simpl. *)
(*   apply bool_decide_unpack in NE. *)
(*   apply bool_decide_pack. set_solver. *)
(* Qed. *)


(* general properties *)
Section gneset.
  Context `{Countable K}.
  Implicit Types (x : K) (X Y : gneset K).

  Lemma gneset_eq (X1 X2 : gneset K) :
    X1 = X2 ↔ gneset_gset X1 = gneset_gset X2.
  Proof.
    split; [by intros ->|intros]. destruct X1, X2; simplify_eq/=.
    f_equal; apply proof_irrel.
  Qed.

  Global Instance gneset_eq_dec : EqDecision (gneset K).
  Proof.
   refine (λ X1 X2, cast_if (decide (gneset_gset X1 = gneset_gset X2)));
    abstract (by rewrite gneset_eq).
  Defined.

  Global Instance gneset_elem_of: ElemOf K (gneset K) :=
    λ x X, elem_of x (gneset_gset X).

  (* no [Empty] *)

  Global Program Instance gneset_singleton : Singleton K (gneset K) :=
    λ x, GNESet (singleton x) _.
  Next Obligation. intro. apply bool_decide_pack. set_solver. Qed.

  Global Program Instance gneset_union : Union (gneset K) :=
    λ X1 X2, GNESet (gneset_gset X1 ∪ gneset_gset X2) _.
  Next Obligation.
    intros [X1 HX1] [X2 HX2]. apply bool_decide_pack. simpl.
    apply bool_decide_unpack in HX1, HX2. set_solver.
  Qed.

  (* no [Intersection], [Difference] *)

  Global Instance gneset_elements : Elements K (gneset K) :=
    λ X, elements (gneset_gset X).

  Global Program Instance gneset_countable : Countable (gneset K) :=
    inj_countable
      gneset_gset
      (λ (X : gset _), if decide (X ≠ ∅) then Some (GNESet X _) else None)
      _.
  Next Obligation. intros. by case_decide. Qed.
  Next Obligation.
    intros [X HX]. simpl. apply bool_decide_unpack in HX as ?.
    case_decide; [|done]. f_equal. by apply gneset_eq.
  Qed.

  Global Instance gneset_equiv_dec : RelDecision (≡@{gneset K}) | 1 :=
    λ X1 X2, decide_rel (≡) (gneset_gset X1) (gneset_gset X2).

  Global Instance gneset_elem_of_dec : RelDecision (∈@{gneset K}) | 1 :=
    λ x X, decide_rel (∈) x (gneset_gset X).

  (* Local Instance : Disjoint (gset K) := _. *)
  (* (* FIXME: [Disjoint (gset K)] is not satisfied without the above explicit *)
  (* instance. Why??? [gneset_subseteq_dec] also has the same issue. *) *)
  (* Global Instance gneset_disjoint_dec : RelDecision (##@{gneset K}) := *)
  (*   λ X1 X2, decide_rel (##) (gneset_gset X1) (gneset_gset X2). *)

  Lemma gneset_disjoint (X1 X2 : gneset K) :
    X1 ## X2 ↔ gneset_gset X1 ## gneset_gset X2.
  Proof. reflexivity. (* ??? *) Qed.

  (* Local Instance : SubsetEq (gset K) := _. *)
  (* Global Instance gneset_subseteq_dec : RelDecision (⊆@{gneset K}) := *)
  (*   λ X1 X2, decide_rel (⊆) (gneset_gset X1) (gneset_gset X2). *)

  (* Global Arguments gneset_eq_dec : simpl never. *)
  (* Global Arguments gneset_elem_of : simpl never. *)
  (* Global Arguments gneset_singleton : simpl never. *)
  (* Global Arguments gneset_union : simpl never. *)
  (* Global Arguments gneset_elements : simpl never. *)
  (* Global Arguments gneset_eq_dec : simpl never. *)
  (* Global Arguments gneset_countable : simpl never. *)
  (* Global Arguments gneset_equiv_dec : simpl never. *)
  (* Global Arguments gneset_elem_of_dec : simpl never. *)
  (* Global Arguments gneset_disjoint_dec : simpl never. *)
  (* Global Arguments gneset_subseteq_dec : simpl never. *)

  Local Instance gneset_dist : Dist (gneset K) :=
    λ n '(GNESet X1 _) '(GNESet X2 _), X1 ≡{n}≡ X2.
  Local Instance gneset_equiv : Equiv (gneset K) :=
    λ '(GNESet X1 _) '(GNESet X2 _), X1 ≡ X2.
  Definition gneset_ofe_mixin : OfeMixin (gneset K).
  Proof.
    split.
    - intros [X1] [X2]; apply equiv_dist.
    - intros n; split.
      + by intros [x].
      + by intros [X1] [X2] ? ?.
      + intros [X1] [X2] [X3] ?? k. by trans (k ∈ X2).
    - done.
  Qed.
  Canonical Structure gnesetO : ofe := Ofe (gneset K) gneset_ofe_mixin.

End gneset.

Global Arguments gnesetO _ {_ _}.


Inductive gneset_disj K `{Countable K} :=
  | GNESetDisj : gneset K → gneset_disj K
  | GNESetDisjBot : gneset_disj K.
Global Arguments GNESetDisj {_ _ _} _.
Global Arguments GNESetDisjBot {_ _ _}.


(* Like [ufrac], but non-fungible. *)
Section gneset_disj.
  Context `{Countable K}.
  Local Arguments op _ _ !_ !_ /.
  Local Arguments cmra_op _ !_ !_ /.
  Local Arguments ucmra_op _ !_ !_ /.
  Local Arguments union _ _ !_ !_ /.
  Local Arguments gneset_union _ _ _ !_ !_ /.

  Canonical Structure gneset_disjO := leibnizO (gneset_disj K).

  Local Instance gneset_disj_valid_instance : Valid (gneset_disj K) := λ X,
    match X with GNESetDisj _ => True | GNESetDisjBot => False end.
  Local Instance gneset_disj_op_instance : Op (gneset_disj K) := λ X Y,
    match X, Y with
    | GNESetDisj X, GNESetDisj Y =>
        if decide (gneset_gset X ## gneset_gset Y) then GNESetDisj (X ∪ Y) else GNESetDisjBot
    | _, _ => GNESetDisjBot
    end.
  Local Instance gneset_disj_pcore_instance : PCore (gneset_disj K) := λ _, None.

  Ltac gneset_disj_solve :=
    repeat (simpl || case_decide);
    first [apply (f_equal GNESetDisj)|done|exfalso];
    try apply gneset_eq;
    set_solver.

  (* Lemma gneset_disj_included X Y : GNESetDisj X ≼ GNESetDisj Y ↔ X ⊆ Y. *)
  (* Proof. *)
  (*   split. *)
  (*   - move=> [[Z|]]; simpl; try case_decide; set_solver. *)
  (*   - intros (Z&->&?)%subseteq_disjoint_union_L. *)
  (*     exists (GNESetDisj Z). gneset_disj_solve. *)
  (* Qed. *)
  Lemma gneset_disj_valid_inv_l X Y : ✓ (GNESetDisj X ⋅ Y) → ∃ Y', Y = GNESetDisj Y' ∧ X ## Y'.
  Proof. destruct Y; repeat (simpl || case_decide); by eauto. Qed.
  Lemma gneset_disj_union X Y : X ## Y → GNESetDisj X ⋅ GNESetDisj Y = GNESetDisj (X ∪ Y).
  Proof. intros. by rewrite /= decide_True. Qed.
  Lemma gneset_disj_valid_op X Y : ✓ (GNESetDisj X ⋅ GNESetDisj Y) ↔ X ## Y.
  Proof. simpl. case_decide; split; try done. Qed.

  Lemma gneset_disj_ra_mixin : RAMixin (gneset_disj K).
  Proof.
    split; try apply _; try done.
    - intros [[X1 ?]|] [[X2 ?]|] [[X3 ?]|]; gneset_disj_solve.
    - intros [[X1 ?]|] [[X2 ?]|]; gneset_disj_solve.
    - intros [[X1 ?]|] [[X2 ?]|]; gneset_disj_solve.
  Qed.
  Canonical Structure gneset_disjR := discreteR (gneset_disj K) gneset_disj_ra_mixin.

  Global Instance gneset_disj_cmra_discrete : CmraDiscrete gneset_disjR.
  Proof. apply discrete_cmra_discrete. Qed.


  Local Arguments op _ _ _ _ : simpl never.

  (* Lemma gneset_disj_alloc_updateP_strong P (Q : gneset_disj K → Prop) X : *)
  (*   (∀ Y, X ⊆ Y → ∃ j, j ∉ Y ∧ P j) → *)
  (*   (∀ i, i ∉ X → P i → Q (GNESetDisj ({[i]} ∪ X))) → *)
  (*   GNESetDisj X ~~>: Q. *)
  (* Proof. *)
  (*   intros Hfresh HQ. *)
  (*   apply cmra_discrete_total_updateP=> ? /gneset_disj_valid_inv_l [Y [->?]]. *)
  (*   destruct (Hfresh (X ∪ Y)) as (i&?&?); first set_solver. *)
  (*   exists (GNESetDisj ({[ i ]} ∪ X)); split. *)
  (*   - apply HQ; set_solver by eauto. *)
  (*   - apply gneset_disj_valid_op. set_solver by eauto. *)
  (* Qed. *)
  (* Lemma gneset_disj_alloc_updateP_strong' P X : *)
  (*   (∀ Y, X ⊆ Y → ∃ j, j ∉ Y ∧ P j) → *)
  (*   GNESetDisj X ~~>: λ Y, ∃ i, Y = GNESetDisj ({[ i ]} ∪ X) ∧ i ∉ X ∧ P i. *)
  (* Proof. eauto using gneset_disj_alloc_updateP_strong. Qed. *)

  (* Lemma gneset_disj_alloc_empty_updateP_strong P (Q : gneset_disj K → Prop) : *)
  (*   (∀ Y : gneset K, ∃ j, j ∉ Y ∧ P j) → *)
  (*   (∀ i, P i → Q (GNESetDisj {[i]})) → GNESetDisj ∅ ~~>: Q. *)
  (* Proof. *)
  (*   intros. apply (gneset_disj_alloc_updateP_strong P); eauto. *)
  (*   intros i; rewrite right_id_L; auto. *)
  (* Qed. *)
  (* Lemma gneset_disj_alloc_empty_updateP_strong' P : *)
  (*   (∀ Y : gneset K, ∃ j, j ∉ Y ∧ P j) → *)
  (*   GNESetDisj ∅ ~~>: λ Y, ∃ i, Y = GNESetDisj {[ i ]} ∧ P i. *)
  (* Proof. eauto using gneset_disj_alloc_empty_updateP_strong. Qed. *)

  (* Section fresh_updates. *)
  (*   Local Set Default Proof Using "Type*". *)
  (*   Context `{!Infinite K}. *)

  (*   Lemma gneset_disj_alloc_updateP (Q : gneset_disj K → Prop) X : *)
  (*     (∀ i, i ∉ X → Q (GNESetDisj ({[i]} ∪ X))) → GNESetDisj X ~~>: Q. *)
  (*   Proof. *)
  (*     intro; eapply gneset_disj_alloc_updateP_strong with (λ _, True); eauto. *)
  (*     intros Y ?; exists (fresh Y). split; [|done]. apply is_fresh. *)
  (*   Qed. *)
  (*   Lemma gneset_disj_alloc_updateP' X : *)
  (*     GNESetDisj X ~~>: λ Y, ∃ i, Y = GNESetDisj ({[ i ]} ∪ X) ∧ i ∉ X. *)
  (*   Proof. eauto using gneset_disj_alloc_updateP. Qed. *)

  (*   Lemma gneset_disj_alloc_empty_updateP (Q : gneset_disj K → Prop) : *)
  (*     (∀ i, Q (GNESetDisj {[i]})) → GNESetDisj ∅ ~~>: Q. *)
  (*   Proof. *)
  (*     intro. apply gneset_disj_alloc_updateP. intros i; rewrite right_id_L; auto. *)
  (*   Qed. *)
  (*   Lemma gneset_disj_alloc_empty_updateP' : GNESetDisj ∅ ~~>: λ Y, ∃ i, Y = GNESetDisj {[ i ]}. *)
  (*   Proof. eauto using gneset_disj_alloc_empty_updateP. Qed. *)
  (* End fresh_updates. *)

  (* Lemma gneset_disj_dealloc_local_update X Y : *)
  (*   (GNESetDisj X, GNESetDisj Y) ~l~> (GNESetDisj (X ∖ Y), GNESetDisj ∅). *)
  (* Proof. *)
  (*   apply local_update_total_valid=> _ _ /gneset_disj_included HYX. *)
  (*   rewrite local_update_unital_discrete=> -[Xf|] _ /leibniz_equiv_iff //=. *)
  (*   rewrite {1}/op /=. destruct (decide _) as [HXf|]; [intros[= ->]|done]. *)
  (*   by rewrite difference_union_distr_l_L *)
  (*     difference_diag_L !left_id_L difference_disjoint_L. *)
  (* Qed. *)
  (* Lemma gneset_disj_dealloc_empty_local_update X Z : *)
  (*   (GNESetDisj Z ⋅ GNESetDisj X, GNESetDisj Z) ~l~> (GNESetDisj X, GNESetDisj ∅). *)
  (* Proof. *)
  (*   apply local_update_total_valid=> /gneset_disj_valid_op HZX _ _. *)
  (*   assert (X = (Z ∪ X) ∖ Z) as HX by set_solver. *)
  (*   rewrite gneset_disj_union // {2}HX. apply gneset_disj_dealloc_local_update. *)
  (* Qed. *)
  (* Lemma gneset_disj_dealloc_op_local_update X Y Z : *)
  (*   (GNESetDisj Z ⋅ GNESetDisj X, GNESetDisj Z ⋅ GNESetDisj Y) ~l~> (GNESetDisj X,GNESetDisj Y). *)
  (* Proof. *)
  (*   rewrite -{2}(left_id ε _ (GNESetDisj Y)). *)
  (*   apply op_local_update_frame, gneset_disj_dealloc_empty_local_update. *)
  (* Qed. *)

  Lemma gneset_disj_alloc_op_local_update X Y Z :
    Z ## X → (GNESetDisj X,GNESetDisj Y) ~l~> (GNESetDisj Z ⋅ GNESetDisj X, GNESetDisj Z ⋅ GNESetDisj Y).
  Proof.
    intros. apply op_local_update_discrete. by rewrite gneset_disj_valid_op.
  Qed.
  (* Lemma gneset_disj_alloc_local_update X Y Z : *)
  (*   Z ## X → (GNESetDisj X,GNESetDisj Y) ~l~> (GNESetDisj (Z ∪ X), GNESetDisj (Z ∪ Y)). *)
  (* Proof. *)
  (*   intros. apply local_update_total_valid=> _ _ /gneset_disj_included ?. *)
  (*   rewrite -!gneset_disj_union //; last set_solver. *)
  (*   auto using gneset_disj_alloc_op_local_update. *)
  (* Qed. *)
  (* Lemma gneset_disj_alloc_empty_local_update X Z : *)
  (*   Z ## X → (GNESetDisj X, GNESetDisj ∅) ~l~> (GNESetDisj (Z ∪ X), GNESetDisj Z). *)
  (* Proof. *)
  (*   intros. rewrite -{2}(right_id_L _ union Z). *)
  (*   apply gneset_disj_alloc_local_update; set_solver. *)
  (* Qed. *)
End gneset_disj.

Global Arguments gneset_disjO _ {_ _}.
Global Arguments gneset_disjR _ {_ _}.
