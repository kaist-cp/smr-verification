From iris.algebra Require Export auth updates local_updates.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
From smr.algebra Require Import coPset.

(** like frac_auth, but using coPneset_disj instead of frac *)

Definition coP_authR (A : cmra) : cmra :=
  authR (optionUR (prodR coPneset_disjR A)).
Definition coP_authUR (A : cmra) : ucmra :=
  authUR (optionUR (prodR coPneset_disjR A)).

Definition coP_auth_auth {A : cmra} (x : A) : coP_authR A :=
  ● (Some ((CoPNESetDisj ⊤),x)).
Definition coP_auth_frag {A : cmra} (E : coPneset) (x : A) : coP_authR A :=
  ◯ (Some ((CoPNESetDisj E),x)).

#[export] Typeclasses Opaque coP_auth_auth coP_auth_frag.

Global Instance: Params (@coP_auth_auth) 1 := {}.
Global Instance: Params (@coP_auth_frag) 2 := {}.

Notation "●C a" := (coP_auth_auth a) (at level 10).
Notation "◯C{ E } a" := (coP_auth_frag E a) (at level 10, format "◯C{ E }  a").
Notation "◯C a" := (coP_auth_frag ⊤ a) (at level 10).

Section coP_auth.
  Context {A : cmra}.
  Implicit Types a b : A.

  Global Instance coP_auth_auth_ne : NonExpansive (@coP_auth_auth A).
  Proof. solve_proper. Qed.
  Global Instance coP_auth_auth_proper : Proper ((≡) ==> (≡)) (@coP_auth_auth A).
  Proof. solve_proper. Qed.
  Global Instance coP_auth_frag_ne E : NonExpansive (@coP_auth_frag A E).
  Proof. solve_proper. Qed.
  Global Instance coP_auth_frag_proper E : Proper ((≡) ==> (≡)) (@coP_auth_frag A E).
  Proof. solve_proper. Qed.

  Global Instance coP_auth_auth_discrete a : Discrete a → Discrete (●C a).
  Proof. intros; apply auth_auth_discrete; [apply Some_discrete|]; apply _. Qed.
  Global Instance coP_auth_frag_discrete E a : Discrete a → Discrete (◯C{E} a).
  Proof. intros; apply auth_frag_discrete, Some_discrete; apply _. Qed.

  Lemma coP_auth_validN n a : ✓{n} a → ✓{n} (●C a ⋅ ◯C a).
  Proof. by rewrite auth_both_validN. Qed.
  Lemma coP_auth_valid a : ✓ a → ✓ (●C a ⋅ ◯C a).
  Proof. intros. by apply auth_both_valid_2. Qed.

  Lemma coP_auth_agreeN n a b : ✓{n} (●C a ⋅ ◯C b) → a ≡{n}≡ b.
  Proof.
    rewrite auth_both_validN /= => -[Hincl Hvalid].
    by move: Hincl=> /Some_includedN_exclusive /(_ Hvalid ) [??].
  Qed.
  Lemma coP_auth_agree a b : ✓ (●C a ⋅ ◯C b) → a ≡ b.
  Proof.
    intros. apply equiv_dist=> n. by apply coP_auth_agreeN, cmra_valid_validN.
  Qed.
  Lemma coP_auth_agree_L `{!LeibnizEquiv A} a b : ✓ (●C a ⋅ ◯C b) → a = b.
  Proof. intros. by apply leibniz_equiv, coP_auth_agree. Qed.

  Lemma coP_auth_includedN n E a b : ✓{n} (●C a ⋅ ◯C{E} b) → Some b ≼{n} Some a.
  Proof. by rewrite auth_both_validN /= => -[/Some_pair_includedN [_ ?] _]. Qed.
  Lemma coP_auth_included `{CmraDiscrete A} E a b :
    ✓ (●C a ⋅ ◯C{E} b) → Some b ≼ Some a.
  Proof. by rewrite auth_both_valid_discrete /= => -[/Some_pair_included [_ ?] _]. Qed.
  Lemma coP_auth_includedN_total `{CmraTotal A} n E a b :
    ✓{n} (●C a ⋅ ◯C{E} b) → b ≼{n} a.
  Proof. intros. by eapply Some_includedN_total, coP_auth_includedN. Qed.
  Lemma coP_auth_included_total `{CmraDiscrete A, CmraTotal A} E a b :
    ✓ (●C a ⋅ ◯C{E} b) → b ≼ a.
  Proof. intros. by eapply Some_included_total, coP_auth_included. Qed.

  Lemma coP_auth_auth_validN n a : ✓{n} (●C a) ↔ ✓{n} a.
  Proof.
    rewrite auth_auth_dfrac_validN Some_validN. split.
    - by intros [?[]].
    - intros. by split.
  Qed.
  Lemma coP_auth_auth_valid a : ✓ (●C a) ↔ ✓ a.
  Proof. rewrite !cmra_valid_validN. by setoid_rewrite coP_auth_auth_validN. Qed.

  Lemma coP_auth_frag_validN n E a : ✓{n} (◯C{E} a) ↔ ✓{n} a.
  Proof.
    rewrite /coP_auth_frag auth_frag_validN.
    rewrite Some_validN pair_validN.
    split; intros.
    - destruct H. auto.
    - split; auto. apply coPneset_disj_validN.
  Qed.
  Lemma coP_auth_frag_valid E a : ✓ (◯C{E} a) ↔ ✓ a.
  Proof.
    rewrite /coP_auth_frag auth_frag_valid.
    rewrite Some_valid pair_valid.
    split; intros.
    - destruct H. auto.
    - split; auto. apply coPneset_disj_valid.
  Qed.

  Lemma coP_auth_frag_op E1 E2 a1 a2 :
    E1 ## E2 → ◯C{E1 ∪ E2} (a1 ⋅ a2) ≡ ◯C{E1} a1 ⋅ ◯C{E2} a2.
  Proof.
    intros. rewrite -auth_frag_op -Some_op -pair_op.
    by rewrite coPneset_disj_union.
  Qed.
  Lemma coP_auth_frag_validN_op n E1 E2 a1 a2 :
    ✓{n} (◯C{E1} a1 ⋅ ◯C{E2} a2) ↔ E1 ## E2 ∧ ✓{n} (a1 ⋅ a2).
  Proof.
    rewrite -auth_frag_op -Some_op -pair_op.
    rewrite auth_frag_validN Some_validN pair_validN.
    by rewrite coPneset_disj_validN_op.
  Qed.
  Lemma coP_auth_frag_valid_op E1 E2 a1 a2 :
    ✓ (◯C{E1} a1 ⋅ ◯C{E2} a2) ↔ E1 ## E2 ∧ ✓ (a1 ⋅ a2).
  Proof.
    rewrite -auth_frag_op -Some_op -pair_op.
    rewrite auth_frag_valid Some_valid pair_valid.
    by rewrite coPneset_disj_valid_op.
  Qed.

  Lemma coP_auth_frag_validN_op_1_l n E a b : ✓{n} (◯C a ⋅ ◯C{E} b) → False.
  Proof. rewrite coP_auth_frag_validN_op. intros [H _]. by eapply coPneset_top_disjoint. Qed.
  Lemma coP_auth_frag_valid_op_1_l E a b : ✓ (◯C a ⋅ ◯C{E} b) → False.
  Proof. rewrite coP_auth_frag_valid_op. intros [H _]. by eapply coPneset_top_disjoint. Qed.

  Global Instance coP_auth_is_op (E E1 E2 : coPneset) (a a1 a2 : A) :
    IsOp (CoPNESetDisj E) (CoPNESetDisj E1) (CoPNESetDisj E2) →
    IsOp a a1 a2 → IsOp' (◯C{E} a) (◯C{E1} a1) (◯C{E2} a2).
  Proof.
    rewrite /IsOp' /IsOp => /leibniz_equiv_iff. intros HE Ha.
    by rewrite -auth_frag_op -Some_op -pair_op -HE -Ha.
  Qed.

  Global Instance coP_auth_is_op_core_id (E E1 E2 : coPneset) (a  : A) :
    CoreId a → IsOp (CoPNESetDisj E) (CoPNESetDisj E1) (CoPNESetDisj E2) →
    IsOp' (◯C{E} a) (◯C{E1} a) (◯C{E2} a).
  Proof. intros. apply coP_auth_is_op; auto. by rewrite /IsOp -core_id_dup. Qed.

  Lemma coP_auth_update E a b a' b' :
    (a,b) ~l~> (a',b') → ●C a ⋅ ◯C{E} b ~~> ●C a' ⋅ ◯C{E} b'.
  Proof.
    intros. by apply auth_update, option_local_update, prod_local_update_2.
  Qed.

  Lemma coP_auth_update_1 a b a' : ✓ a' → ●C a ⋅ ◯C b ~~> ●C a' ⋅ ◯C a'.
  Proof.
    intros. by apply auth_update, option_local_update, exclusive_local_update.
  Qed.
End coP_auth.
