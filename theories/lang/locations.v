From stdpp Require Import countable numbers gmap.
From iris.prelude Require Export prelude.
From iris.prelude Require Import options.

Local Open Scope Z_scope.

(* note: We call it [blk] to avoid naming conflict with stdpp's [blk] *)
Record blk : Set := Blk { blk_car : positive; }.

Global Instance blk_dec_eq : EqDecision blk.
Proof. solve_decision. Defined.

Global Instance blk_inhabited : Inhabited blk := populate {| blk_car := 1 |}.

Global Instance blk_countable : Countable blk.
Proof. by apply (inj_countable' blk_car Blk); intros []. Defined.

Definition loc : Set := blk * Z.

Declare Scope loc_scope.
Bind Scope loc_scope with loc.
Delimit Scope loc_scope with L.
Global Open Scope loc_scope.

Module Loc.
  (* [shift_loc] from lambda-rust *)
  Definition add (l : loc) (o : Z) : loc := (l.1, l.2 + o).
  Record tagged_loc := TLoc {
    tloc_oloc : option loc;
    tloc_tag : Z;
  }.

  Definition to_tagged_loc (l : option loc) (t : Z) : tagged_loc := TLoc l t.
  Global Arguments to_tagged_loc : simpl never.

  Module Import notations.
    Notation "l +ₗ z" := (add l%L z%Z)
      (at level 50, left associativity) : loc_scope.
    Notation "l  '&ₜ'  t" := (to_tagged_loc l t%Z) (at level 12).
  End notations.

  Lemma add_assoc l n n' : l +ₗ n +ₗ n' = l +ₗ (n + n').
  Proof. rewrite /add /=. f_equal. lia. Qed.
  Lemma add_0 l : l +ₗ 0 = l.
  Proof. destruct l as [b o]. rewrite /add /= Z.add_0_r //. Qed.

  Lemma add_assoc_nat l (n n' : nat) : l +ₗ n +ₗ n' = l +ₗ (n + n')%nat.
  Proof. destruct l as [b o]. rewrite /add /=. f_equal. lia. Qed.
  Lemma add_0_nat l : l +ₗ 0%nat = l.
  Proof. destruct l as [b o]. rewrite /add /=. f_equal. lia. Qed.

  Global Instance add_inj l : Inj (=) (=) (add l).
  Proof. destruct l as [b o]; intros n n' [= ?]; lia. Qed.

  Lemma loc_add_blk l n : (l +ₗ n).1 = l.1.
  Proof. done. Qed.

  Definition blk_to_loc (b : blk) : loc := (b, 0).

  Global Instance blk_to_loc_inj : Inj (=) (=) blk_to_loc.
  Proof. intros ??. apply pair_inj. Qed.


  Global Instance tagged_loc_dec_eq : EqDecision tagged_loc.
  Proof. solve_decision. Defined.

  Global Instance tagged_loc_countable : Countable tagged_loc.
  Proof.
    refine (inj_countable'
      (λ tloc, (tloc.(tloc_oloc), tloc.(tloc_tag)))
      (λ '(oloc, tag), TLoc oloc tag) _); by intros [].
  Qed.

  Definition loc_to_tagged_loc l : tagged_loc := (Some l) &ₜ 0.

  Global Instance loc_to_tagged_loc_inj : Inj (=) (=) loc_to_tagged_loc.
  Proof. intros [] []. naive_solver. Qed.
End Loc.

Export Loc.notations.
