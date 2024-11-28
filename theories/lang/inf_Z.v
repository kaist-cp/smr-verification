From stdpp Require Import countable.
From iris.algebra Require Import ofe.
From iris.prelude Require Import options.

Inductive inf_Z : Set :=
  | NegInf
  | FinInt (n : Z)
  | PosInf.

Canonical Structure inf_ZO := leibnizO inf_Z.

Global Instance inhabited_inf_Z : Inhabited inf_Z := populate (FinInt 0).

Declare Scope inf_Z_scope.
Delimit Scope inf_Z_scope with inf_Z.
Bind Scope inf_Z_scope with inf_Z.

Module inf_Z.
  Definition compare x y : comparison :=
    match x, y with
    | NegInf, NegInf => Eq
    | NegInf, FinInt _ => Lt
    | NegInf, PosInf => Lt
    | FinInt _, NegInf => Gt
    | FinInt x_z, FinInt y_z => (x_z ?= y_z)%Z
    | FinInt _, PosInf => Lt
    | PosInf, NegInf => Gt
    | PosInf, FinInt _ => Gt
    | PosInf, PosInf => Eq
    end.

  Local Infix "?=" := compare (at level 70, no associativity) : inf_Z_scope.

  Definition eq := @Logic.eq inf_Z.
  Definition eq_equiv := @eq_equivalence inf_Z.

  Definition lt x y := (x ?= y)%inf_Z = Lt.
  Definition gt x y := (x ?= y)%inf_Z = Gt.
  Definition le x y := (x ?= y)%inf_Z <> Gt.
  Definition ge x y := (x ?= y)%inf_Z <> Lt.

  Module Import notations.
    Notation "∞ᵢ" := (PosInf).
    Notation "-∞ᵢ" := (NegInf).
    Infix "<=" := le : inf_Z_scope.
    Infix "≤" := le : inf_Z_scope.
    Infix "<" := lt : inf_Z_scope.
    Infix ">=" := ge : inf_Z_scope.
    Infix "≥" := ge : inf_Z_scope.
    Infix ">" := gt : inf_Z_scope.
  End notations.

  Global Instance eq_dec : EqDecision inf_Z.
  Proof. solve_decision. Defined.
  Global Instance le_dec: RelDecision le.
  Proof. solve_decision. Defined.
  Global Instance lt_dec: RelDecision lt.
  Proof.
    intros [|x|] [|y|]; try ((left; done) || (right; done)).
    unfold lt, eq. solve_decision.
  Defined.
  Global Instance ge_dec: RelDecision ge.
  Proof. solve_decision. Defined.
  Global Instance gt_dec: RelDecision gt.
  Proof.
    intros [|x|] [|y|]; try ((left; done) || (right; done)).
    unfold gt, eq. solve_decision.
  Defined.

  Global Instance inf_Z_countable : Countable inf_Z.
  Proof.
    refine (inj_countable' (λ z, match z with
    | NegInf => (inl false)
    | FinInt n => (inr n)
    | PosInf => (inl true)
    end) (λ z, match z with
    | (inl false) => NegInf
    | (inr n) => FinInt n
    | (inl true) => PosInf
    end) _); by intros [].
  Qed.

  Global Instance FinInt_equiv_inj : Inj (=) (=) FinInt.
  Proof. by inversion_clear 1. Qed.

  Lemma Z_lt_lt (x y : Z) :
    (x < y)%Z → (FinInt x < FinInt y)%inf_Z.
  Proof. done. Qed.

  Lemma lt_Z_lt (x y : Z) :
    (FinInt x < FinInt y)%inf_Z → (x < y)%Z.
  Proof. done. Qed.

  Lemma Z_gt_gt (x y : Z) :
    (x > y)%Z → (FinInt x > FinInt y)%inf_Z.
  Proof. done. Qed.

  Lemma gt_Z_gt (x y : Z) :
    (FinInt x > FinInt y)%inf_Z → (x > y)%Z.
  Proof. done. Qed.

  Global Instance lt_transitive : Transitive lt.
  Proof.
    intros [|x|][|y|][|z|] x_lt_y y_lt_z; try naive_solver.
    all: try by (inversion y_lt_z || inversion x_lt_y).
    apply lt_Z_lt in x_lt_y,y_lt_z.
    apply Z_lt_lt. lia.
  Qed.

  Global Instance lt_irreflexive : Irreflexive lt.
  Proof.
    intros [|n|] LT; try by inversion LT.
    apply lt_Z_lt in LT. lia.
  Qed.
End inf_Z.

Export inf_Z.notations.
