From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.
From smr Require Import helpers.

From smr.diaframe.lang Require Import proof_automation atomic_specs.

Section spec.

Context `{!heapGS Σ}.
Notation iProp := (iProp Σ).

Global Instance biabd_pointsto_from_arr (p: blk) (o: nat) (v: val):
HINT ε₁ ✱ [lv; p ↦∗ lv ∗ ⌜ length lv > o ⌝ ∗ ⌜ lv !! o = Some v ⌝ ] ⊫
  [id] ;
    (p +ₗ o) ↦ v ✱
  [ p ↦∗ take o lv ∗ (p +ₗ S o) ↦∗ drop (S o) lv].
Proof.
  iSteps; rewrite Nat2Z.id; [done|]. unfold array. rewrite -Nat2Z.inj_succ. iSteps.
Qed.

End spec.
