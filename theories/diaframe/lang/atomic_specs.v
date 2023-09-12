From iris.bi Require Export bi derived_laws lib.fractional lib.atomic updates.
From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
From iris.prelude Require Import options.

From smr.diaframe.lang Require Import proof_automation.
From diaframe Require Import proofmode_base.
From diaframe.lib Require Export atomic.
From diaframe.lib Require Import persistently intuitionistically.

From smr.diaframe Require Import specs.
From diaframe.symb_exec Require Import defs weakestpre spec_notation.
From diaframe.symb_exec Require Export weakestpre_logatom atom_spec_notation.
From smr.lang Require Import proofmode notation.

Import bi notation.

(* Adds logically atomic specifications for operations in Iris's atomic_heap abstraction *)

Section execution_instances.
  Context `{!heapGS Σ}.

  Global Instance load_step_atomic (l : loc) :
         (* this extra later is an equivalent specification, but easier to use for difficult situations *)
    SPEC v q, << ▷ l ↦{q} v >> (! #l)%E << RET v ; l ↦{q} v >>.
  Proof. iSmash. Qed.

  (* Global Instance alloc_step_wp e v :
    IntoVal e v →
    SPEC {{ True }} alloc e {{ (l : loc), RET #l; l ↦ v }} | 20.
  Proof.
    move => <-.
    iStepsS.
    iApply alloc_spec => //. iStepsS.
  Qed. *)

  Global Instance store_step_atomic (l : loc) (v' : val) :
    SPEC v, << ▷ l ↦ v >> (#l <- v')%E << RET #(); l ↦ v' >>.
  Proof. iSmash. Qed.

  (* Global Instance free_step_wp (l : loc) :
    SPEC v, {{ l ↦ v }} free #l {{ (b : base_lit), RET #b; True }}.
  Proof.
    iStepsS.
    iApply (free_spec with "H1").
    iStepsS.
  Qed. *)

  Global Opaque vals_compare_safe.

  Global Instance cmpxchg_step_atomic (l : loc) (v' w : val) :
    SolveSepSideCondition (val_is_unboxed v') →
    SPEC v, << ▷ l ↦ v >> (CmpXchg #l v' w)%E << (b : bool), RET (v, #b)%V; ⌜b = true⌝ ∗ ⌜v = v'⌝ ∗ l ↦ w ∨ ⌜b = false⌝ ∗ ⌜v ≠ v'⌝ ∗ l ↦ v >>.
  Proof.
    rewrite /SolveSepSideCondition => Hv.
    iSmash.
  Qed.

End execution_instances.

Section biabd_instances.
  Context `{!heapGS Σ}.

  Section mergable.
    Global Instance mergable_consume_mapsto_persist l v1 v2 :
      MergableConsume (l ↦□ v1)%I true (λ p Pin Pout, TCAnd (TCEq Pin (l ↦□ v2)) (TCEq Pout (l ↦□ v1 ∗ ⌜v1 = v2⌝)))%I | 40.
    Proof.
      rewrite /MergableConsume => p Pin Pout [-> ->].
      rewrite bi.intuitionistically_if_elim.
      iStepsS.
    Qed.

    Global Instance mergable_consume_mapsto_own q1 q2 q l v1 v2 :
      MergableConsume (l ↦{#q1} v1)%I true (λ p Pin Pout,
          TCAnd (TCEq Pin (l ↦{#q2} v2)) $
          TCAnd (proofmode_classes.IsOp (A := fracR) q q1 q2) $
                (TCEq Pout (l ↦{#q} v1 ∗ ⌜v1 = v2⌝)))%I | 30. (* this does not include q ≤ 1! *)
    Proof.
      rewrite /MergableConsume => p Pin Pout [-> [+ ->]].
      rewrite bi.intuitionistically_if_elim => Hq.
      iStepsS.
      replace (q2 + q1)%Qp with q; last first.
      { replace (q2 + q1)%Qp with (q1 + q2)%Qp; [done | apply Qp.add_comm]. }
      iStepsS.
    Qed.

    Global Instance mergable_persist_mapsto_dfrac_own q1 dq2 l v1 v2 :
      MergablePersist (l ↦{#q1} v1)%I (λ p Pin Pout, TCAnd (TCEq Pin (l ↦{dq2} v2)) (TCEq Pout ⌜v1 = v2⌝%Qp))%I | 50.
    Proof.
      rewrite /MergableConsume => p Pin Pout [-> ->].
      rewrite bi.intuitionistically_if_elim.
      iStepsS.
    Qed.

    Global Instance mergable_persist_mapsto_dfrac_own2 q1 dq2 l v1 v2 :
      MergablePersist (l ↦{dq2} v1)%I (λ p Pin Pout, TCAnd (TCEq Pin (l ↦{#q1} v2)) (TCEq Pout ⌜v1 = v2⌝%Qp))%I | 50.
    Proof.
      rewrite /MergableConsume => p Pin Pout [-> ->].
      rewrite bi.intuitionistically_if_elim.
      iStepsS.
    Qed.

    (* this last instance is necessary for opaque dq1 and dq2 *)
    Global Instance mergable_persist_mapsto_last_resort dq1 dq2 l v1 v2 :
      MergablePersist (l ↦{dq1} v1)%I (λ p Pin Pout, TCAnd (TCEq Pin (l ↦{dq2} v2)) (TCEq Pout ⌜v1 = v2⌝))%I | 99.
    Proof.
      rewrite /MergableConsume => p Pin Pout [-> ->].
      rewrite bi.intuitionistically_if_elim.
      iStepsS.
    Qed.
  End mergable.

  Section biabds.
    Global Instance mapsto_val_may_need_more (l : loc) (v1 v2 : val) (q1 q2 : Qp) mq q :
      FracSub q2 q1 mq →
      TCEq mq (Some q) →
      HINT l ↦{#q1} v1 ✱ [v'; ⌜v1 = v2⌝ ∗ l ↦{#q} v'] ⊫ [id];
           l ↦{#q2} v2 ✱ [⌜v1 = v2⌝ ∗ ⌜v' = v1⌝] | 55.
    Proof. move => <- ->. iStepsS. Qed.

    Global Instance mapsto_val_have_enough (l : loc) (v1 v2 : val) (q1 q2 : Qp) mq :
      FracSub q1 q2 mq →
      HINT l ↦{#q1} v1 ✱ [- ; ⌜v1 = v2⌝] ⊫ [id]; l ↦{#q2} v2 ✱ [⌜v1 = v2⌝ ∗ match mq with Some q => l ↦{#q} v1 | _ => True end] | 54.
    Proof.
      move => <-.
      destruct mq; iSteps.
      iDestruct "H1" as "[? ?]". iSteps.
    Qed.

    Global Instance as_persistent_mapsto p l q v :
      HINT □⟨p⟩ l ↦{q} v ✱ [- ; emp] ⊫ [bupd]; l ↦□v ✱ [l ↦□ v] | 100.
    Proof.
      iStepS. rewrite bi.intuitionistically_if_elim.
      iMod (mapsto_persist with "H1") as "#Hl".
      iStepsS.
    Qed.
  End biabds.

End biabd_instances.
