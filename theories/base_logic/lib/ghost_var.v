(* Modified version supporting persistent ghost vars. *)

(** A simple "ghost variable" of arbitrary type with fractional ownership.
Can be mutated when fully owned. *)
From iris.algebra Require Import dfrac dfrac_agree.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

(** The CMRA we need. *)
Class ghost_varG Σ (A : Type) := GhostVarG {
  ghost_var_inG : inG Σ (dfrac_agreeR $ leibnizO A);
}.
Local Existing Instance ghost_var_inG.
Global Hint Mode ghost_varG - ! : typeclass_instances.

Definition ghost_varΣ (A : Type) : gFunctors :=
  #[ GFunctor (dfrac_agreeR $ leibnizO A) ].

Global Instance subG_ghost_varΣ Σ A : subG (ghost_varΣ A) Σ → ghost_varG Σ A.
Proof. solve_inG. Qed.

Local Definition ghost_var_def `{!ghost_varG Σ A}
    (γ : gname) (q : Qp) (a : A) : iProp Σ :=
  own γ (to_frac_agree (A:=leibnizO A) q a).
Local Definition ghost_var_aux : seal (@ghost_var_def). Proof. by eexists. Qed.
Definition ghost_var := ghost_var_aux.(unseal).
Local Definition ghost_var_unseal :
  @ghost_var = @ghost_var_def := ghost_var_aux.(seal_eq).
Global Arguments ghost_var {Σ A _} γ q a.

Local Definition persistent_ghost_var_def `{!ghost_varG Σ A}
    (γ : gname) (a : A) : iProp Σ :=
  own γ (to_dfrac_agree (A:=leibnizO A) (DfracDiscarded) a).
Local Definition persistent_ghost_var_aux : seal (@persistent_ghost_var_def). Proof. by eexists. Qed.
Definition persistent_ghost_var := persistent_ghost_var_aux.(unseal).
Local Definition persistent_ghost_var_unseal :
  @persistent_ghost_var = @persistent_ghost_var_def := persistent_ghost_var_aux.(seal_eq).
Global Arguments persistent_ghost_var {Σ A _} γ a.

Local Ltac unseal := rewrite ?ghost_var_unseal /ghost_var_def ?persistent_ghost_var_unseal /persistent_ghost_var_def.

Section lemmas.
  Context `{!ghost_varG Σ A}.
  Implicit Types (a b : A) (q : Qp).

  Global Instance ghost_var_timeless γ q a : Timeless (ghost_var γ q a).
  Proof. unseal. apply _. Qed.

  Global Instance ghost_var_fractional γ a : Fractional (λ q, ghost_var γ q a).
  Proof. intros q1 q2. unseal. rewrite -own_op -frac_agree_op //. Qed.
  Global Instance ghost_var_as_fractional γ a q :
    AsFractional (ghost_var γ q a) (λ q, ghost_var γ q a) q.
  Proof. split; [done|]. apply _. Qed.

  Global Instance persistent_ghost_var_timeless γ a : Timeless (persistent_ghost_var γ a).
  Proof. unseal. apply _. Qed.
  Global Instance persistent_ghost_var_persistent γ a : Persistent (persistent_ghost_var γ a).
  Proof. unseal. apply _. Qed.

  Lemma ghost_var_alloc_strong a (P : gname → Prop) :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ ghost_var γ 1 a.
  Proof. unseal. intros. iApply own_alloc_strong; done. Qed.
  Lemma ghost_var_alloc a :
    ⊢ |==> ∃ γ, ghost_var γ 1 a.
  Proof. unseal. iApply own_alloc. done. Qed.

  Lemma ghost_var_valid_2 γ a1 q1 a2 q2 :
    ghost_var γ q1 a1 -∗ ghost_var γ q2 a2 -∗ ⌜(q1 + q2 ≤ 1)%Qp ∧ a1 = a2⌝.
  Proof.
    unseal. iIntros "Hvar1 Hvar2".
    by iCombine "Hvar1 Hvar2" gives %?%frac_agree_op_valid.
  Qed.
  (** Almost all the time, this is all you really need. *)
  Lemma ghost_var_agree γ a1 q1 a2 q2 :
    ghost_var γ q1 a1 -∗ ghost_var γ q2 a2 -∗ ⌜a1 = a2⌝.
  Proof.
    iIntros "Hvar1 Hvar2".
    iDestruct (ghost_var_valid_2 with "Hvar1 Hvar2") as %[_ ?]. done.
  Qed.

  (** This is just an instance of fractionality above, but that can be hard to find. *)
  Lemma ghost_var_split γ a q1 q2 :
    ghost_var γ (q1 + q2) a -∗ ghost_var γ q1 a ∗ ghost_var γ q2 a.
  Proof. iIntros "[$$]". Qed.

  (** Update the ghost variable to new value [b]. *)
  Lemma ghost_var_update b γ a :
    ghost_var γ 1 a ==∗ ghost_var γ 1 b.
  Proof.
    unseal. iApply own_update. apply cmra_update_exclusive. done.
  Qed.
  Lemma ghost_var_update_2 b γ a1 q1 a2 q2 :
    (q1 + q2 = 1)%Qp →
    ghost_var γ q1 a1 -∗ ghost_var γ q2 a2 ==∗ ghost_var γ q1 b ∗ ghost_var γ q2 b.
  Proof.
    intros Hq. unseal. rewrite -own_op. iApply own_update_2.
    apply frac_agree_update_2. done.
  Qed.
  Lemma ghost_var_update_halves b γ a1 a2 :
    ghost_var γ (1/2) a1 -∗
    ghost_var γ (1/2) a2 ==∗
    ghost_var γ (1/2) b ∗ ghost_var γ (1/2) b.
  Proof. iApply ghost_var_update_2. apply Qp.half_half. Qed.

  (** Framing support *)
  Global Instance frame_ghost_var p γ a q1 q2 q :
    FrameFractionalQp q1 q2 q →
    Frame p (ghost_var γ q1 a) (ghost_var γ q2 a) (ghost_var γ q a) | 5.
  Proof. apply: frame_fractional. Qed.

  (** Persistent ghost var rules *)
  Lemma ghost_var_persist γ q a :
    ghost_var γ q a ==∗ persistent_ghost_var γ a.
  Proof. unseal. iApply own_update. apply dfrac_agree_persist. Qed.

  Lemma persistent_ghost_var_agree γ a1 a2 q2 :
    persistent_ghost_var γ a1 -∗ ghost_var γ q2 a2 -∗ ⌜a1 = a2⌝.
  Proof.
    unseal. iIntros "Hvar1 Hvar2".
    by iCombine "Hvar1 Hvar2" gives %[? ?]%dfrac_agree_op_valid_L.
  Qed.
End lemmas.

