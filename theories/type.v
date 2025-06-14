From iris.base_logic.lib Require Export iprop.
From smr.lang Require Import notation.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.

Definition resource Σ : Type := blk → list val → gname → iProp Σ.
Definition resourceO Σ : ofe := blk -d> list val -d> gname -d> iPropO Σ.

(* Type of memory block, adapted from lambda-rust *)

Record type {Σ} : Type := PType {
  ty_sz : nat;
  ty_res : blk → list val → gname → iProp Σ;
  ty_sz_eq p lv i : ty_res p lv i -∗ ⌜length lv = ty_sz⌝;
}.
Global Arguments type : clear implicits.

Section type.
  Context {Σ : gFunctors}.
  Notation type := (type Σ).

  Inductive type_equiv' (ty1 ty2 : type) : Prop :=
    Type_equiv :
      ty1.(ty_sz) = ty2.(ty_sz) →
      (∀ p vs i, ty1.(ty_res) p vs i ≡ ty2.(ty_res) p vs i) →
      type_equiv' ty1 ty2.
  Local Instance type_equiv : Equiv type := type_equiv'.
  Inductive type_dist' (n : nat) (ty1 ty2 : type) : Prop :=
    Type_dist :
      ty1.(ty_sz) = ty2.(ty_sz) →
      (∀ p vs i, ty1.(ty_res) p vs i ≡{n}≡ ty2.(ty_res) p vs i) →
      type_dist' n ty1 ty2.
  Local Instance type_dist : Dist type := type_dist'.

  Let T := prodO natO (blk -d> list val -d> gname -d> iPropO Σ).
  Let P (x : T) : Prop :=
    (∀ p vl i, x.2 p vl i -∗ ⌜length vl = x.1⌝).

  Definition type_unpack (ty : type) : T :=
    (ty.(ty_sz), λ p vl i, (ty.(ty_res) p vl i)).
  Program Definition type_pack (x : T) (H : P x) : type :=
    {| ty_sz := x.1; ty_res p vl i := x.2 p vl i|}.
  Solve Obligations with by by intros [? ?] ?.

  Definition type_ofe_mixin : OfeMixin type.
  Proof.
    apply (iso_ofe_mixin type_unpack).
    - split; [by destruct 1|by intros [? ?]; constructor].
    - split; [by destruct 1|by intros [? ?]; constructor].
  Qed.
  Canonical Structure typeO : ofe := Ofe type type_ofe_mixin.

  Global Instance ty_sz_ne n : Proper (dist n ==> eq) ty_sz.
  Proof. intros ?? EQ. apply EQ. Qed.
  Global Instance ty_sz_proper : Proper ((≡) ==> eq) ty_sz.
  Proof. intros ?? EQ. apply EQ. Qed.
  Global Instance ty_res_ne n:
    Proper (dist n ==> eq ==> eq ==> eq ==> dist n) ty_res.
  Proof. intros ?? EQ ??-> ??-> ??->. apply EQ. Qed.
  Global Instance ty_res_proper : Proper ((≡) ==> eq ==> eq ==> eq ==> (≡)) ty_res.
  Proof. intros ?? EQ ??-> ??-> ??->. apply EQ. Qed.

  Global Instance type_cofe : Cofe typeO.
  Proof.
    apply (iso_cofe_subtype' P type_pack type_unpack).
    - by intros [].
    - split; [by destruct 1|by intros [? ?]; constructor].
    - by intros [].
    - repeat apply limit_preserving_and; repeat (apply limit_preserving_forall; intros ?).
      apply bi.limit_preserving_entails=> n ty1 ty2 Hty; first done. f_equiv; [apply Hty|by rewrite Hty].
  Qed.

  Global Program Instance type_inhabited : Inhabited type := populate {|
    ty_sz := 0;
    ty_res p lv i := ⌜length lv = 0⌝;
  |}%I.
  Next Obligation. by iIntros. Qed.
End type.

Global Arguments typeO : clear implicits.


Section type_dist2.
  Context {Σ : gFunctors}.

  (* Size and shr are n-equal, but own is only n-1-equal.
     We need this to express what shr has to satisfy on a Type-NE-function:
     It may only depend contractively on own. *)
  (* TODO: Find a better name for this metric. *)
  Inductive type_dist2 (n : nat) (ty1 ty2 : type Σ) : Prop :=
    Type_dist2 :
      ty1.(ty_sz) = ty2.(ty_sz) →
      (∀ p vs i, dist_later n (ty1.(ty_res) p vs i) (ty2.(ty_res) p vs i)) →
      type_dist2 n ty1 ty2.

  Global Instance type_dist2_equivalence n : Equivalence (type_dist2 n).
  Proof.
    constructor.
    - by constructor.
    - intros ?? Heq; constructor; symmetry; eapply Heq.
    - intros ??? Heq1 Heq2; constructor; etrans; (eapply Heq1 || eapply Heq2).
  Qed.

  Definition type_dist2_later (n : nat) ty1 ty2 : Prop :=
    match n with O => True | S n => type_dist2 n ty1 ty2 end.
  Global Arguments type_dist2_later !_ _ _ /.

  Global Instance type_dist2_later_equivalence n :
    Equivalence (type_dist2_later n).
  Proof. destruct n as [|n]; first by split. apply type_dist2_equivalence. Qed.

  (* The hierarchy of metrics:
     dist n → type_dist2 n → dist_later n → type_dist2_later n. *)
  Lemma type_dist_dist2 n ty1 ty2 : dist n ty1 ty2 → type_dist2 n ty1 ty2.
  Proof. intros EQ. split; intros; try apply dist_dist_later; apply EQ. Qed.
  Lemma type_dist2_dist_later n ty1 ty2 : type_dist2 n ty1 ty2 → dist_later n ty1 ty2.
  Proof. intros EQ. dist_later_fin_intro. split; intros; try apply EQ; lia. Qed.
  Lemma type_later_dist2_later n ty1 ty2 : dist_later n ty1 ty2 → type_dist2_later n ty1 ty2.
  Proof. destruct n; first done. rewrite dist_later_fin_iff. exact: type_dist_dist2. Qed.
  Lemma type_dist2_dist n ty1 ty2 : type_dist2 (S n) ty1 ty2 → dist n ty1 ty2.
  Proof. move=>/type_dist2_dist_later. rewrite dist_later_fin_iff. done. Qed.
  Lemma type_dist2_S n ty1 ty2 : type_dist2 (S n) ty1 ty2 → type_dist2 n ty1 ty2.
  Proof. intros. apply type_dist_dist2, type_dist2_dist. done. Qed.

  Lemma ty_size_type_dist n : Proper (type_dist2 n ==> eq) ty_sz.
  Proof. intros ?? EQ. apply EQ. Qed.
  Lemma ty_own_type_dist n:
    Proper (type_dist2 (S n) ==> eq ==> eq ==> eq ==> dist n) ty_res.
  Proof. intros ?? EQ ??-> ??-> ??->. apply EQ. lia. Qed.
End type_dist2.

Notation TypeNonExpansive T := (∀ n, Proper (type_dist2 n ==> type_dist2 n) T).
Notation TypeContractive T := (∀ n, Proper (type_dist2_later n ==> type_dist2 n) T).

Section type_contractive.
  Context {Σ : gFunctors}.
  Implicit Types (T : type Σ → type Σ).

  Lemma type_ne_dist_later T :
    TypeNonExpansive T → ∀ n, Proper (type_dist2_later n ==> type_dist2_later n) T.
  Proof. intros Hf [|n]; last exact: Hf. hnf. by intros. Qed.

  (* From the above, it easily follows that TypeNonExpansive functions compose with
     TypeNonExpansive and with TypeContractive functions. *)
  Lemma type_ne_ne_compose T1 T2 :
    TypeNonExpansive T1 → TypeNonExpansive T2 → TypeNonExpansive (T1 ∘ T2).
  Proof. intros NE1 NE2 ? ???; simpl. apply: NE1. exact: NE2. Qed.

  Lemma type_contractive_compose_right T1 T2 :
    TypeContractive T1 → TypeNonExpansive T2 → TypeContractive (T1 ∘ T2).
  Proof. intros HT1 HT2 ? ???. apply: HT1. exact: type_ne_dist_later. Qed.

  Lemma type_contractive_compose_left T1 T2 :
    TypeNonExpansive T1 → TypeContractive T2 → TypeContractive (T1 ∘ T2).
  Proof. intros HT1 HT2 ? ???; simpl. apply: HT1. exact: HT2. Qed.

  (* Show some more relationships between properties. *)
  Lemma type_contractive_type_ne T :
    TypeContractive T → TypeNonExpansive T.
  Proof.
    intros HT ? ???. apply type_dist_dist2, dist_later_S, type_dist2_dist_later, HT. done.
  Qed.

  Lemma type_contractive_ne T :
    TypeContractive T → NonExpansive T.
  Proof.
    intros HT ? ???. apply dist_later_S, type_dist2_dist_later, HT, type_dist_dist2. done.
  Qed.
End type_contractive.


Section fixpoint_def.
  Context {Σ : gFunctors}.
  Context (T : type Σ → type Σ) {HT: TypeContractive T}.

  Local Instance type_2_contractive : Contractive (Nat.iter 2 T).
  Proof using Type*.
    intros n ? **. simpl.
    by apply dist_later_S, type_dist2_dist_later, HT, HT, type_later_dist2_later.
  Qed.

  Definition type_fixpoint : type Σ := fixpointK 2 T.
End fixpoint_def.

Lemma type_fixpoint_ne `{Σ : gFunctors} (T1 T2 : type Σ → type Σ)
    `{!TypeContractive T1, !TypeContractive T2} n :
  (∀ t, T1 t ≡{n}≡ T2 t) → type_fixpoint T1 ≡{n}≡ type_fixpoint T2.
Proof. eapply fixpointK_ne; apply type_contractive_ne, _. Qed.

Section fixpoint.
  Context {Σ : gFunctors}.
  Context (T : type Σ → type Σ) {HT: TypeContractive T}.

  Lemma type_fixpoint_unfold : type_fixpoint T ≡ T (type_fixpoint T).
  Proof. apply fixpointK_unfold. by apply type_contractive_ne. Qed.
End fixpoint.
