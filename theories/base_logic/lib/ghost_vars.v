From stdpp Require Import coPset.
From iris.algebra Require Export dfrac.
From iris.algebra Require Import dfrac_agree functions.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.
From smr.algebra Require Import coPset.
From smr Require Import helpers.

(** * Ininitely many (pre-allocated) ghost variable for each [positive]. *)

(* TODO: upstream *)
Global Instance discrete_fun_core_id {A} {B : A → ucmra} (f : discrete_fun B) :
  (∀ i, CoreId (f i)) → CoreId f.
Proof. intros ?. constructor => x. by apply core_id_total. Qed.
Global Hint Extern 100 (CoreId (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.

Definition ghost_varsUR (A : Type) : ucmra :=
  positive -d> optionUR $ dfrac_agreeR $ leibnizO A.

Definition to_ghost_vars {A : Type} (E : coPset) (q : dfrac) (a : A) : ghost_varsUR A :=
  λ k, if decide (k ∈ E) then Some (to_dfrac_agree (A:=leibnizO A) q a) else None.

Section RA_lemmas.
  Context {A : Type}.
  Implicit Types (a : A) (k : positive) (E : coPset) (q : dfrac).

  (* general ghost_vars *)

  Lemma to_ghost_vars_lookup k E q a :
    k ∈ E → to_ghost_vars E q a k = Some (to_dfrac_agree (A:=leibnizO A) q a).
  Proof. intros. rewrite /to_ghost_vars decide_True //. Qed.

  Lemma to_ghost_vars_lookup_None k E q a :
    k ∉ E → to_ghost_vars E q a k = None.
  Proof. intros. rewrite /to_ghost_vars decide_False //. Qed.

  Local Ltac yes := (rewrite to_ghost_vars_lookup; [|set_solver..]; auto).
  Local Ltac no := (rewrite to_ghost_vars_lookup_None; [|set_solver..]; auto).

  Lemma to_ghost_vars_union E1 E2 q a :
    E1 ## E2 →
    to_ghost_vars E1 q a ⋅ to_ghost_vars E2 q a
    ≡ to_ghost_vars (E1 ∪ E2) q a.
  Proof.
    intros H x. rewrite discrete_fun_lookup_op.
    destruct (decide (x ∈ E1)), (decide (x ∈ E2)).
    - set_solver.
    - yes. no. yes.
    - no. yes. yes.
    - no. no. no.
  Qed.

  Lemma to_ghost_vars_frac E p q a :
    to_ghost_vars E p a ⋅ to_ghost_vars E q a ≡ to_ghost_vars E (p ⋅ q) a.
  Proof.
    intros x. rewrite discrete_fun_lookup_op.
    destruct (decide (x ∈ E)).
    - repeat yes. by rewrite -Some_op -pair_op agree_idemp.
    - repeat no.
  Qed.

  Lemma to_ghost_vars_top_valid q a :
    (✓ to_ghost_vars ⊤ q a) ↔ ✓ q.
  Proof.
    split; intros Valid.
    - by destruct (Valid 1%positive).
    - intros x. by yes.
  Qed.

  Lemma to_ghost_vars_empty_valid q a :
    (✓ to_ghost_vars ∅ q a).
  Proof. intros x. by no. Qed.

  Lemma to_ghost_vars_op E1 E2 a1 q1 a2 q2 :
    to_ghost_vars E1 q1 a1 ⋅ to_ghost_vars E2 q2 a2
    = λ k', (to_ghost_vars E1 q1 a1 k') ⋅ (to_ghost_vars E2 q2 a2 k').
  Proof. auto. Qed.

  Lemma to_ghost_vars_update E a b :
    to_ghost_vars E (DfracOwn 1) a ~~> to_ghost_vars E (DfracOwn 1) b.
  Proof.
    apply discrete_fun_update => x.
    unfold to_ghost_vars.
    case_decide as Hx; last done.
    apply option_update, cmra_update_exclusive. done.
  Qed.

  Lemma to_ghost_vars_insert E k q a :
    k ∉ E →
    to_ghost_vars (E ∪ {[k]}) q a
    ≡ to_ghost_vars E q a ⋅ to_ghost_vars {[k]} q a.
  Proof. intros. rewrite to_ghost_vars_union; set_solver. Qed.
End RA_lemmas.

Class ghost_varsG Σ (A : Type) := GhostVarsG {
  ghost_vars_inG : inG Σ (ghost_varsUR A);
}.
Local Existing Instance ghost_vars_inG.

Definition ghost_varsΣ (A : Type) : gFunctors :=
  #[GFunctor (ghost_varsUR (leibnizO A))].

Global Instance subG_ghost_varsΣ {A Σ} :
  subG (ghost_varsΣ A) Σ → ghost_varsG Σ A.
Proof. solve_inG. Qed.

Section ghost.
  Context `{!ghost_varsG Σ A}.

  Local Definition ghost_vars_def (γ : gname) (E : coPset) (q : dfrac) (a : A) : iProp Σ :=
    own γ (to_ghost_vars E q a).
  Local Definition ghost_vars_aux : seal (@ghost_vars_def). Proof. by eexists. Qed.
  Definition ghost_vars := ghost_vars_aux.(unseal).
  Local Definition ghost_vars_unseal : @ghost_vars = @ghost_vars_def := ghost_vars_aux.(seal_eq).
End ghost.


Notation "E ↦P[ γ ] dq a" := (ghost_vars γ E dq a)
  (at level 20, dq custom dfrac at level 1, format "E  ↦P[ γ ] dq  a") : bi_scope.

Notation "k ↦p[ γ ] dq a" := ({[k]} ↦P[γ]{ dq } a)%I
  (at level 20, dq custom dfrac at level 1, format "k  ↦p[ γ ] dq  a") : bi_scope.

Section ghost_lemmas.
  Context `{!ghost_varsG Σ A}.
  Implicit Types (a : A) (k : positive) (E : coPset) (dq : dfrac) (q : Qp).

  Local Ltac unseal := rewrite ?ghost_vars_unseal /ghost_vars_def.

  Global Instance ghost_vars_timeless γ E dq a :
    Timeless (E ↦P[γ]{dq} a).
  Proof. unseal. apply _. Qed.

  Lemma ghost_vars_frac_op γ E a q1 q2 :
    E ↦P[γ]{# q1 + q2 } a ⊣⊢ E ↦P[γ]{# q1 } a ∗ E ↦P[γ]{# q2 } a.
  Proof. unseal. by rewrite -own_op to_ghost_vars_frac. Qed.

  Global Instance ghost_vars_fractional γ E a :
    Fractional (λ q, (E ↦P[γ]{#q} a)%I).
  Proof. intros p q. apply ghost_vars_frac_op. Qed.
  Global Instance ghost_vars_as_fractional γ E a q:
    AsFractional (E ↦P[γ]{# q } a) (λ q, (E ↦P[γ]{# q } a)%I) q.
  Proof. split; [done|]. apply _. Qed.

  Lemma ghost_vars_union γ E1 E2 dq a :
    E1 ## E2 →
    E1 ↦P[γ]{ dq } a ∗ E2 ↦P[γ]{ dq } a ⊣⊢ (E1 ∪ E2) ↦P[γ]{ dq } a.
  Proof. unseal. intros. by rewrite -own_op to_ghost_vars_union. Qed.

  Lemma ghost_vars_top_alloc_strong a (P : gname → Prop) :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ ⊤ ↦P[γ] a.
  Proof.
    unseal. intros HP. apply own_alloc_strong; [exact HP|].
    by apply to_ghost_vars_top_valid.
  Qed.
  Lemma ghost_vars_top_alloc a :
    ⊢ |==> ∃ γ, ⊤ ↦P[γ] a.
  Proof. unseal. by apply own_alloc, to_ghost_vars_top_valid. Qed.

  Lemma ghost_vars_get_empty γ a :
    ⊢ |==> ∅ ↦P[γ] a.
  Proof.
    unseal. iMod own_unit as "H". iApply (own_update with "H").
    apply discrete_fun_update.
    setoid_rewrite to_ghost_vars_lookup_None; set_solver.
  Qed.

  Lemma ghost_vars_valid_2 γ E1 E2 a1 dq1 a2 dq2 :
    E1 ∩ E2 ≠ ∅ →
    E1 ↦P[γ]{ dq1 } a1 -∗ E2 ↦P[γ]{ dq2 } a2 -∗
    ⌜ ✓ (dq1 ⋅ dq2) ∧ a1 = a2⌝.
  Proof.
    unseal. iIntros (NotEmpty) "Hvar1 Hvar2".
    iCombine "Hvar1 Hvar2" gives %Q.
    apply coPset_choose in NotEmpty as [k k_In].
    specialize (Q k). rewrite to_ghost_vars_op in Q.
    rewrite ?to_ghost_vars_lookup in Q; [|set_solver..].
    rewrite -Some_op Some_valid dfrac_agree_op_valid_L in Q. done.
  Qed.
  (** Almost all the time, this is all you really need. *)
  Lemma ghost_vars_agree γ E1 E2 a1 dq1 a2 dq2 :
    E1 ∩ E2 ≠ ∅ →
    E1 ↦P[γ]{ dq1 } a1 -∗ E2 ↦P[γ]{ dq2 } a2 -∗ ⌜a1 = a2⌝.
  Proof.
    iIntros (NotEmpty) "Hvar1 Hvar2".
    iDestruct (ghost_vars_valid_2 with "Hvar1 Hvar2") as %[_ ?]; done.
  Qed.

  (** Update the ghost variable to new value [b]. *)
  Lemma ghost_vars_update b γ E a :
    E ↦P[γ] a ==∗ E ↦P[γ] b.
  Proof. unseal. iApply own_update. apply to_ghost_vars_update. Qed.

  (* Simple version where they must have same value. *)
  Lemma ghost_vars_update_2' b γ E a q1 q2 :
    (q1 + q2 = 1)%Qp →
    E ↦P[γ]{# q1 } a -∗ E ↦P[γ]{# q2 } a ==∗ E ↦P[γ]{# q1 } b ∗ E ↦P[γ]{# q2 } b.
  Proof.
    iIntros (Hq) "V1 V2". iCombine "V1 V2" as "V".
    rewrite -ghost_vars_frac_op !Hq.
    iApply (ghost_vars_update with "V").
  Qed.
  Lemma ghost_vars_update_halves' b γ E a :
    E ↦P[γ]{# 1/2 } a -∗ E ↦P[γ]{# 1/2 } a ==∗ E ↦P[γ]{# 1/2 } b ∗ E ↦P[γ]{# 1/2 } b.
  Proof. apply ghost_vars_update_2', Qp.half_half. Qed.

  (* General version. *)
  Lemma ghost_vars_update_2 b γ E a1 q1 a2 q2 :
    E ≠ ∅ →
    (q1 + q2 = 1)%Qp →
    E ↦P[γ]{# q1 } a1 -∗ E ↦P[γ]{# q2 } a2 ==∗ E ↦P[γ]{# q1 } b ∗ E ↦P[γ]{# q2 } b.
  Proof.
    iIntros (? Hq) "V1 V2".
    iDestruct (ghost_vars_agree with "V1 V2") as %->; [set_solver|].
    iApply (ghost_vars_update_2' with "V1 V2"); done.
  Qed.
  Lemma ghost_vars_update_halves b γ E a1 a2 :
    E ≠ ∅ →
    E ↦P[γ]{# 1/2 } a1 -∗ E ↦P[γ]{# 1/2 } a2 ==∗ E ↦P[γ]{# 1/2 } b ∗ E ↦P[γ]{# 1/2 } b.
  Proof. intros. apply ghost_vars_update_2; [done|]. apply Qp.half_half. Qed.

  Lemma ghost_vars_insert γ E k dq a :
    k ∉ E →
    (E ∪ {[k]}) ↦P[γ]{ dq } a ⊣⊢ E ↦P[γ]{ dq } a ∗ k ↦p[γ]{ dq } a.
  Proof. unseal. intros. by rewrite -own_op -to_ghost_vars_insert. Qed.

  (* Persistent ghost vars *)

  Global Instance ghost_vars_persistent γ E a :
    Persistent (E ↦P[γ]□ a).
  Proof. unseal. unfold to_ghost_vars. apply _. Qed.

  Lemma ghost_vars_persist γ E dq a :
    E ↦P[γ]{ dq } a ==∗ E ↦P[γ]□ a.
  Proof.
    unseal. iApply own_update. apply discrete_fun_update => x.
    destruct (decide (x ∈ E)) as [In|NotIn]; last first.
    { rewrite !to_ghost_vars_lookup_None //. }
    rewrite !to_ghost_vars_lookup //.
    apply option_update, dfrac_agree_persist.
  Qed.
End ghost_lemmas.

(** * Ininitely many (pre-allocated) ghost variable for each [positive * positive]. *)

Definition ghost_vars2R (A : Type) : cmra :=
  positive * positive -d> optionUR (dfrac_agreeR $ leibnizO A).

Definition to_ghost_vars2 {A : Type} (E1 E2 : coPset) (f : dfrac) (a : A) : ghost_vars2R A :=
  λ k, if decide (k.1 ∈ E1 ∧ k.2 ∈ E2)
       then Some (to_dfrac_agree (A:=leibnizO A) f a)
       else None.

Section RA2_lemmas.
  Context {A : Type}.
  Implicit Types (a : A) (k : positive) (E : coPset) (dq : dfrac) (q : Qp).

  Lemma to_ghost_vars2_lookup k1 k2 E1 E2 dq a :
    k1 ∈ E1 → k2 ∈ E2 →
    to_ghost_vars2 E1 E2 dq a (k1, k2) = Some (to_dfrac_agree (A:=leibnizO A) dq a).
  Proof. intros. by rewrite /to_ghost_vars2 decide_True. Qed.

  Lemma to_ghost_vars2_lookup_None k1 k2 E1 E2 dq a :
    k1 ∉ E1 ∨ k2 ∉ E2 →
    to_ghost_vars2 E1 E2 dq a (k1, k2) = None.
  Proof.
    intros. rewrite /to_ghost_vars2 decide_False //=.
    set_solver.
  Qed.

  Local Ltac yes := (rewrite to_ghost_vars2_lookup; [|set_solver..]; auto).
  Local Ltac no := (rewrite to_ghost_vars2_lookup_None; [|set_solver..]; auto).

  Lemma to_ghost_vars2_union_1 E1A E1B E2 dq a :
    E1A ## E1B →
    to_ghost_vars2 E1A E2 dq a ⋅ to_ghost_vars2 E1B E2 dq a
    ≡ to_ghost_vars2 (E1A ∪ E1B) E2 dq a.
  Proof.
    intros H (k1, k2). rewrite discrete_fun_lookup_op.
    destruct (decide (k1 ∈ E1A)), (decide (k1 ∈ E1B)), (decide (k2 ∈ E2)).
    - exfalso. set_solver.
    - exfalso. set_solver.
    - yes. no. yes.
    - no. no. no.
    - no. yes. yes.
    - no. no. no.
    - no. no. no.
    - no. no. no.
  Qed.

  Lemma to_ghost_vars2_union_2 E1 E2A E2B dq a :
    E2A ## E2B →
    to_ghost_vars2 E1 E2A dq a ⋅ to_ghost_vars2 E1 E2B dq a
    ≡ to_ghost_vars2 E1 (E2A ∪ E2B) dq a.
  Proof.
    intros H (k1, k2). rewrite discrete_fun_lookup_op.
    destruct (decide (k1 ∈ E1)), (decide (k2 ∈ E2A)), (decide (k2 ∈ E2B)).
    - set_solver.
    - yes. no. yes.
    - no. yes. yes.
    - no. no. no.
    - no. no. no.
    - no. no. no.
    - no. no. no.
    - no. no. no.
  Qed.

  Lemma to_ghost_vars2_frac E1 E2 p q a :
    to_ghost_vars2 E1 E2 (DfracOwn p) a ⋅ to_ghost_vars2 E1 E2 (DfracOwn q) a ≡
      to_ghost_vars2 E1 E2 (DfracOwn (p + q)) a.
  Proof.
    intros (k1, k2). rewrite discrete_fun_lookup_op.
    destruct (decide (k1 ∈ E1)), (decide (k2 ∈ E2)).
    { repeat yes. by rewrite -Some_op -pair_op agree_idemp. }
    all: repeat no.
  Qed.

  Lemma to_ghost_vars2_op E1A E1B E2A E2B a1 dq1 a2 dq2 :
    to_ghost_vars2 E1A E1B dq1 a1 ⋅ to_ghost_vars2 E2A E2B dq2 a2
    = λ x, (to_ghost_vars2 E1A E1B dq1 a1 x) ⋅ (to_ghost_vars2 E2A E2B dq2 a2 x).
  Proof. auto. Qed.

  Lemma to_ghost_vars2_top_valid dq a :
    (✓ to_ghost_vars2 ⊤ ⊤ dq a) ↔ (✓ dq)%Qp.
  Proof.
    split; intros Valid.
    - by destruct (Valid (1, 1)%positive).
    - intros []. by yes.
  Qed.

  Lemma to_ghost_vars2_empty_1_valid E dq a :
    (✓ to_ghost_vars2 ∅ E dq a).
  Proof. intros []. by no. Qed.

  Lemma to_ghost_vars2_empty_2_valid E dq a :
    (✓ to_ghost_vars2 E ∅ dq a).
  Proof. intros []. by no. Qed.

  Lemma to_ghost_vars2_update E1 E2 a b :
    to_ghost_vars2 E1 E2 (DfracOwn 1) a ~~> to_ghost_vars2 E1 E2 (DfracOwn 1) b.
  Proof.
    apply discrete_fun_update => [[x1 x2]].
    unfold to_ghost_vars2.
    case_decide as Hx; last done.
    apply option_update, cmra_update_exclusive. done.
  Qed.

  Lemma to_ghost_vars2_insert_1 E1 E2 k dq a :
    k ∉ E1 →
    to_ghost_vars2 (E1 ∪ {[k]}) E2 dq a
    ≡ to_ghost_vars2 E1 E2 dq a ⋅ to_ghost_vars2 {[k]} E2 dq a.
  Proof. intros. rewrite to_ghost_vars2_union_1; set_solver. Qed.

  Lemma to_ghost_vars2_insert_2 E1 E2 k dq a :
    k ∉ E2 →
    to_ghost_vars2 E1 (E2 ∪ {[k]}) dq a
    ≡ to_ghost_vars2 E1 E2 dq a ⋅ to_ghost_vars2 E1 {[k]} dq a.
  Proof. intros. rewrite to_ghost_vars2_union_2; set_solver. Qed.

  Lemma to_ghost_vars2_delete_1 k E1 E2 dq a :
    k ∈ E1 →
    to_ghost_vars2 E1 E2 dq a
    ≡ to_ghost_vars2 {[k]} E2 dq a ⋅ to_ghost_vars2 (E1 ∖ {[k]}) E2 dq a.
  Proof.
    intros.
    rewrite to_ghost_vars2_union_1; [|set_solver].
    rewrite -union_difference_L; set_solver.
  Qed.

  Lemma to_ghost_vars2_delete_2 k E1 E2 dq a :
    k ∈ E2 →
    to_ghost_vars2 E1 E2 dq a
    ≡ to_ghost_vars2 E1 {[k]} dq a ⋅ to_ghost_vars2 E1 (E2 ∖ {[k]}) dq a.
  Proof.
    intros.
    rewrite to_ghost_vars2_union_2; [|set_solver].
    rewrite -union_difference_L; set_solver.
  Qed.
End RA2_lemmas.

Class ghost_vars2G Σ (A : Type) := GhostVars2G {
  ghost_vars2_inG : inG Σ (ghost_vars2R A);
}.
Local Existing Instance ghost_vars2_inG.

Definition ghost_vars2Σ (A : Type) : gFunctors :=
  #[GFunctor (ghost_vars2R (leibnizO A))].

Global Instance subG_ghost_vars2Σ {A Σ} :
  subG (ghost_vars2Σ A) Σ → ghost_vars2G Σ A.
Proof. solve_inG. Qed.

Section ghost.
  Context `{!ghost_vars2G Σ A}.
  (* Require a pair in the actual definition so that [simpl] does not undo
     below notations. *)
  Local Definition ghost_vars2_def (γ : gname) (E1E2 : coPset * coPset) (dq : dfrac) (a : A) : iProp Σ :=
    own γ (to_ghost_vars2 E1E2.1 E1E2.2 dq a).
  Local Definition ghost_vars2_aux : seal (@ghost_vars2_def). Proof. by eexists. Qed.
  Definition ghost_vars2 := ghost_vars2_aux.(unseal).
  Local Definition ghost_vars2_unseal : @ghost_vars2 = @ghost_vars2_def := ghost_vars2_aux.(seal_eq).
End ghost.

(* E1E2 : coPset * coPset *)
Notation "E1E2 ↦P2[ γ ] dq a" := (ghost_vars2 γ E1E2 dq a)
  (at level 20, dq custom dfrac at level 1, format "E1E2  ↦P2[ γ ] dq  a").

(* k1k2 : positive * positive *)
Notation "k1k2 ↦p2[ γ ] dq a" := (({[k1k2.1]}, {[k1k2.2]}) ↦P2[ γ ]{ dq } a)
  (at level 20, dq custom dfrac at level 1, format "k1k2  ↦p2[ γ ] dq  a").

Section ghost2_lemmas.
  Context `{!ghost_vars2G Σ A}.
  Implicit Types (a : A) (k : positive) (E : coPset) (dq : dfrac) (q : Qp).

  Local Ltac unseal := rewrite ?ghost_vars2_unseal /ghost_vars2_def.

  Lemma ghost_vars2_union_1 γ E1A E1B E2 dq a :
    E1A ## E1B →
      (E1A,E2) ↦P2[γ]{ dq } a ∗ (E1B, E2) ↦P2[γ]{ dq } a
    ⊣⊢ ((E1A ∪ E1B), E2) ↦P2[γ]{ dq } a.
  Proof. unseal. intros. by rewrite -own_op to_ghost_vars2_union_1. Qed.

  Lemma ghost_vars2_union_2 γ E1 E2A E2B dq a :
    E2A ## E2B →
      (E1,E2A) ↦P2[γ]{ dq } a ∗ (E1,E2B) ↦P2[γ]{ dq } a
    ⊣⊢ (E1,(E2A ∪ E2B)) ↦P2[γ]{ dq } a.
  Proof. unseal. intros. by rewrite -own_op to_ghost_vars2_union_2. Qed.

  Global Instance ghost_vars2_timeless γ E1E2 dq a :
    Timeless (E1E2 ↦P2[γ]{ dq } a).
  Proof. unseal. apply _. Qed.

  Lemma ghost_vars2_frac_op γ E1 E2 a q1 q2 :
    (E1,E2) ↦P2[γ]{# q1 + q2 } a ⊣⊢ (E1,E2) ↦P2[γ]{# q1 } a ∗ (E1,E2) ↦P2[γ]{# q2 } a.
  Proof. unseal. by rewrite -own_op to_ghost_vars2_frac. Qed.

  Global Instance ghost_vars2_fractional γ E1 E2 a :
    Fractional (λ q, (E1,E2) ↦P2[γ]{# q } a).
  Proof. intros p q. apply ghost_vars2_frac_op. Qed.
  Global Instance ghost_vars2_as_fractional γ E1 E2 a q :
    AsFractional ((E1,E2) ↦P2[γ]{# q } a) (λ q, ((E1,E2) ↦P2[γ]{# q } a)%I) q.
  Proof. split; [done|]. apply _. Qed.

  Lemma ghost_vars2_top_alloc_strong a (P : gname → Prop) :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ (⊤,⊤) ↦P2[γ] a.
  Proof.
    unseal. intros. by iApply own_alloc_strong; auto using to_ghost_vars2_top_valid.
  Qed.
  Lemma ghost_vars2_top_alloc a :
    ⊢ |==> ∃ γ, (⊤,⊤) ↦P2[γ] a.
  Proof. unseal. by apply own_alloc, to_ghost_vars2_top_valid. Qed.

  Lemma ghost_vars2_get_empty γ E1 E2 dq a :
    E1 = ∅ ∨ E2 = ∅ → ⊢ |==> (E1,E2) ↦P2[γ]{ dq } a.
  Proof.
    unseal. iIntros (H). iMod own_unit as "H".
    iApply (own_update with "H").
    apply discrete_fun_update.
    setoid_rewrite to_ghost_vars2_lookup_None; set_solver.
  Qed.
  Lemma ghost_vars2_get_empty_1 γ E dq a :
    ⊢ |==> (∅,E) ↦P2[γ]{ dq } a.
  Proof. apply ghost_vars2_get_empty. by left. Qed.
  Lemma ghost_vars2_get_empty_2 γ E dq a :
    ⊢ |==> (E,∅) ↦P2[γ]{ dq } a.
  Proof. apply ghost_vars2_get_empty. by right. Qed.

  Lemma ghost_vars2_valid_2 γ E1A E1B E2A E2B a1 dq1 a2 dq2 :
    E1A ∩ E2A ≠ ∅ → E1B ∩ E2B ≠ ∅ →
    (E1A,E1B) ↦P2[γ]{ dq1 } a1 -∗
    (E2A,E2B) ↦P2[γ]{ dq2 } a2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ a1 = a2⌝.
  Proof.
    unseal. iIntros (NotEmptyA NotEmptyB) "Hvar1 Hvar2".
    iCombine "Hvar1 Hvar2" gives %Q.
    apply coPset_choose in NotEmptyA as [k1 k1_In].
    apply coPset_choose in NotEmptyB as [k2 k2_In].
    specialize (Q (k1, k2)). rewrite discrete_fun_lookup_op in Q.
    rewrite !to_ghost_vars2_lookup in Q; [|set_solver..].
    rewrite -Some_op Some_valid dfrac_agree_op_valid_L in Q. done.
  Qed.
  (** Almost all the time, this is all you really need. *)
  Lemma ghost_vars2_agree γ E1A E1B E2A E2B a1 dq1 a2 dq2 :
    E1A ∩ E2A ≠ ∅ → E1B ∩ E2B ≠ ∅ →
    (E1A,E1B) ↦P2[γ]{ dq1 } a1 -∗
    (E2A,E2B) ↦P2[γ]{ dq2 } a2 -∗
    ⌜a1 = a2⌝.
  Proof.
    iIntros (NotEmptyA NotEmptyB) "Hvar1 Hvar2".
    iDestruct (ghost_vars2_valid_2 with "Hvar1 Hvar2") as %[_ ?]; done.
  Qed.

  (** Update the ghost variable to new value [b]. *)
  Lemma ghost_vars2_update b γ E1 E2 a :
    (E1,E2) ↦P2[γ] a ⊢ |==> (E1,E2) ↦P2[γ] b.
  Proof. unseal. apply own_update, to_ghost_vars2_update. Qed.

  (* Simple version where they must have same value. *)
  Lemma ghost_vars2_update_2' b γ E1 E2 a q1 q2 :
    (q1 + q2 = 1)%Qp →
    (E1,E2) ↦P2[γ]{# q1 } a -∗
    (E1,E2) ↦P2[γ]{# q2 } a ==∗
    (E1,E2) ↦P2[γ]{# q1 } b ∗ (E1,E2) ↦P2[γ]{# q2 } b.
  Proof.
    iIntros (Hq) "V1 V2". iCombine "V1 V2" as "V".
    rewrite -ghost_vars2_frac_op !Hq.
    iApply (ghost_vars2_update with "V").
  Qed.
  Lemma ghost_vars2_update_halves' b γ E1 E2 a :
    (E1,E2) ↦P2[γ]{# 1/2 } a -∗
    (E1,E2) ↦P2[γ]{# 1/2 } a ==∗
    (E1,E2) ↦P2[γ]{# 1/2 } b ∗ (E1,E2) ↦P2[γ]{# 1/2 } b.
  Proof. apply ghost_vars2_update_2', Qp.half_half. Qed.

  (* General version. *)
  Lemma ghost_vars2_update_2 b γ E1 E2 a1 q1 a2 q2 :
    E1 ≠ ∅ → E2 ≠ ∅ →
    (q1 + q2 = 1)%Qp →
    (E1,E2) ↦P2[γ]{# q1 } a1 -∗
    (E1,E2) ↦P2[γ]{# q2 } a2 ==∗
    (E1,E2) ↦P2[γ]{# q1 } b ∗ (E1,E2) ↦P2[γ]{# q2 } b.
  Proof.
    iIntros (???) "V1 V2".
    iDestruct (ghost_vars2_agree with "V1 V2") as %->; [set_solver..|].
    iApply (ghost_vars2_update_2' with "V1 V2"); done.
  Qed.
  Lemma ghost_vars2_update_halves b γ E1 E2 a1 a2 :
    E1 ≠ ∅ → E2 ≠ ∅ →
    (E1,E2) ↦P2[γ]{# 1/2 } a1 -∗
    (E1,E2) ↦P2[γ]{# 1/2 } a2 ==∗
    (E1,E2) ↦P2[γ]{# 1/2 } b ∗ (E1,E2) ↦P2[γ]{# 1/2 } b.
  Proof. intros. apply ghost_vars2_update_2; [done..|]. apply Qp.half_half. Qed.

  Lemma ghost_vars2_insert_1 γ E1 E2 k dq a :
    k ∉ E1 →
      ((E1 ∪ {[k]}),E2) ↦P2[γ]{ dq } a
    ⊣⊢ (E1,E2) ↦P2[γ]{ dq } a ∗ ({[k]}, E2) ↦P2[γ]{ dq } a.
  Proof. unseal. intros. by rewrite -own_op -to_ghost_vars2_insert_1. Qed.

  Lemma ghost_vars2_insert_2 γ E1 E2 k dq a :
    k ∉ E2 →
      (E1,(E2 ∪ {[k]})) ↦P2[γ]{ dq } a
    ⊣⊢ (E1,E2) ↦P2[γ]{ dq } a ∗ (E1, {[k]}) ↦P2[γ]{ dq } a.
  Proof. unseal. intros. by rewrite -own_op -to_ghost_vars2_insert_2. Qed.

  Lemma ghost_vars2_delete_1 γ k E1 E2 dq a :
    k ∈ E1 →
      (E1,E2) ↦P2[γ]{ dq } a
    ⊣⊢ ({[k]}, E2) ↦P2[γ]{ dq } a ∗ ((E1 ∖ {[k]}), E2) ↦P2[γ]{ dq } a.
  Proof. unseal. intros. by rewrite -own_op -to_ghost_vars2_delete_1. Qed.

  Lemma ghost_vars2_delete_2 γ k E1 E2 dq a :
    k ∈ E2 →
      (E1,E2) ↦P2[γ]{ dq } a
    ⊣⊢ (E1,{[k]}) ↦P2[γ]{ dq } a ∗ (E1,(E2 ∖ {[k]})) ↦P2[γ]{ dq } a.
  Proof. unseal. intros. by rewrite -own_op -to_ghost_vars2_delete_2. Qed.

  Lemma ghost_vars2_eq_agree γ E1 E2 a1 dq1 a2 dq2 :
    E1 ≠ ∅ → E2 ≠ ∅ →
    (E1,E2) ↦P2[γ]{ dq1 } a1 -∗
    (E1,E2) ↦P2[γ]{ dq2 } a2 -∗
    ⌜a1 = a2⌝.
  Proof. intros. apply ghost_vars2_agree; set_solver. Qed.

  Lemma ghost_vars2_big_sepM_1 {V} γ (m : gmap positive V) E dq a:
    ((gset_to_coPset (dom m)), E) ↦P2[γ]{ dq } a -∗
    [∗ map] i ↦ _ ∈ m, ({[i]}, E) ↦P2[γ]{ dq } a.
  Proof.
    induction m using map_ind; iIntros "H"; simpl.
    { by iApply big_sepM_empty. }
    iApply big_sepM_insert; auto.
    rewrite dom_insert_L.
    rewrite gset_to_coPset_union gset_to_coPset_singleton -ghost_vars2_union_1.
    - iDestruct "H" as "[$ H]". by iApply IHm.
    - by rewrite disjoint_singleton_l not_elem_of_gset_to_coPset not_elem_of_dom.
    Qed.

  Lemma ghost_vars2_big_sepM_1' {V} γ (m : gmap positive V) E dq a :
    m ≠ ∅ →
    ([∗ map] i ↦ _ ∈ m, ({[i]}, E) ↦P2[γ]{ dq } a) -∗
    (gset_to_coPset (dom m), E) ↦P2[γ]{ dq } a.
  Proof.
    assert (
      ([∗ map] i ↦ _ ∈ m, ({[i]}, E) ↦P2[γ]{ dq } a) -∗
      ⌜m = ∅⌝ ∨ (gset_to_coPset (dom m), E) ↦P2[γ]{ dq } a
    ) as H; last first.
    { iIntros (Hm) "M".
      iDestruct (H with "M") as "[%|M]"; done. }

    induction m using map_ind; iIntros "H". { by iLeft. }
    iDestruct (big_sepM_delete with "H") as "[● H]";
      first apply lookup_insert.
    rewrite delete_insert_delete delete_notin; auto.
    iDestruct (IHm with "H") as "[%|H]"; iRight.
    - subst. by rewrite insert_empty dom_singleton_L gset_to_coPset_singleton.
    - rewrite dom_insert_L gset_to_coPset_union gset_to_coPset_singleton
              -ghost_vars2_union_1; first by iFrame.
      by rewrite disjoint_singleton_l not_elem_of_gset_to_coPset not_elem_of_dom.
  Qed.

  Lemma ghost_vars2_big_sepM_2 γ (l : list positive) E dq a :
    NoDup l →
    (E,list_to_set l) ↦P2[γ]{ dq } a -∗
    [∗ list] _ ↦ i ∈ l, (E,{[i]}) ↦P2[γ]{ dq } a.
  Proof.
    intros ND.
    induction l; iIntros "H".
    { by iApply big_sepL_nil. }
    apply NoDup_cons in ND as [Hal ND].
    iApply big_sepL_cons.
    rewrite list_to_set_cons.
    rewrite -ghost_vars2_union_2.
    - iDestruct "H" as "[$ H]". by iApply IHl.
    - apply disjoint_singleton_l. by rewrite not_elem_of_list_to_set.
  Qed.

  Lemma ghost_vars2_big_sepM_2' γ (l : list positive) E dq a :
    NoDup l →
    l ≠ [] →
    ([∗ list] _ ↦ i ∈ l, (E,{[i]}) ↦P2[γ]{ dq } a) -∗
    (E,list_to_set l) ↦P2[γ]{ dq } a.
  Proof.
    intros ND.
    assert (
      ([∗ list] i ∈ l, (E,{[i]}) ↦P2[γ]{ dq } a) -∗
      ⌜l = []⌝ ∨ (E,list_to_set l) ↦P2[γ]{ dq } a
    ) as H; last first.
    { iIntros (Hnil) "L". iDestruct (H with "L") as "[%|M]"; done. }

    induction l; iIntros "H". { by iLeft. }
    iDestruct (big_sepL_cons with "H") as "[● H]".
    apply NoDup_cons in ND as [Hal ND].
    iDestruct (IHl with "H") as "[%|H]"; auto; iRight.
    - subst. replace (list_to_set [a0]) with ({[a0]} : coPset); auto.
      set_solver.
    - rewrite list_to_set_cons -ghost_vars2_union_2; try iFrame.
      by apply disjoint_singleton_l, not_elem_of_list_to_set.
  Qed.

  (* Persistent ghost2_vars *)

  Global Instance ghost_vars2_persistent γ E1E2 a :
    Persistent (E1E2 ↦P2[γ]□ a).
  Proof. unseal. unfold to_ghost_vars2. apply _. Qed.

  Lemma ghost_vars2_persist γ E1E2 dq a :
    E1E2 ↦P2[γ]{ dq } a ==∗ E1E2 ↦P2[γ]□ a.
  Proof.
    unseal. iApply own_update. apply discrete_fun_update => [[x1 x2]].
    destruct E1E2 as [E1 E2]. simpl.
    destruct (decide (x1 ∈ E1 ∧ x2 ∈ E2)) as [[In1 In2]|NotIn%not_and_l]; last first.
    { rewrite !to_ghost_vars2_lookup_None //=. }
    rewrite !to_ghost_vars2_lookup //=.
    apply option_update, dfrac_agree_persist.
  Qed.
End ghost2_lemmas.
