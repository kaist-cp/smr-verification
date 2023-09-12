From diaframe.lib Require Import own_hints max_prefix_list_hints.
From diaframe Require Import proofmode_base.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_var.
From iris.prelude Require Import options.

Section automation.
Context `{!ghost_varG Σ A}.

  Global Instance gv_alloc_whole (v : A):
  HINT ε₁ ✱ [ - ; emp ] ⊫ [bupd] γ;  ghost_var γ 1 v ✱ [emp] .
  Proof.
  iIntros (tele _).
  iMod (ghost_var_alloc v) as (γs) "γs".
  iExists γs.
  iModIntro. iFrame.
  Qed.

  Global Instance gv_split (v: A) γ  q1 q2 mq:
  FracSub q1 q2 (Some mq) →
  HINT ghost_var γ q1 v ✱ [- ; True] ⊫ [id]; ghost_var γ q2 v ✱ [ghost_var γ mq v] | 100.
  Proof.
    intros. iSteps. rewrite -H.
    iDestruct (ghost_var_split with "H1") as "[A B]". iStepsS.
  Qed.


  Global Instance gv_mergable γ (v1 v2: A) q1 q2 q:
  MergableConsume (ghost_var γ q1 v1) true (λ p Pin Pout,
      TCAnd (TCEq Pin (ghost_var γ q2 v2)) $
      TCAnd (IsOp q q1 q2)
          (TCEq Pout (ghost_var γ q v1 ∗ ⌜ v1 = v2 ⌝ )))%I.
  Proof.
  rewrite /MergableConsume => p Pin Pout [->  [-> ->]].
  rewrite bi.intuitionistically_if_elim.
  iIntros "[H1 H2]".
  iDestruct (ghost_var_agree with "H1 H2") as %->.
  iCombine "H1 H2" as "H". by iFrame.
  Qed.

  Global Instance gv_split2 (v: A) γ  q1 q2 mq:
  FracSub q2 q1 (Some mq) →
  HINT ghost_var γ q1 v ✱ [- ; ghost_var γ mq v  ]
  ⊫ [id]; ghost_var γ q2 v ✱ [ True ] | 100.
  Proof.
    iIntros (?). iStepsS. rewrite -H. iSteps.
  Qed.


  Global Instance gv_alloc_part (v: A) (qp qp': Qp):
    SolveSepSideCondition (qp < 1)%Qp →
    FracSub 1 qp (Some qp') →
    HINT ε₁ ✱ [ - ; emp ] ⊫ [bupd] γ;  ghost_var γ qp v ✱ [ ghost_var γ qp' v] .
  Proof.
    iIntros (qplt1 EQqpqp' tele _).
    iMod (ghost_var_alloc v) as (γs) "γs". iSteps.
  Qed.


  Global Instance gv_update (v1 v2: A) γ q1 q1' q2 q2':
  TCIf (SolveSepSideCondition (v1 = v2)) False TCTrue →
  FracSub 1 q1 q1' →
  FracSub 1 q2 q2' →
  HINT ghost_var γ q1 v1 ✱ [(v1': A); match q1' with | Some q => ghost_var γ q v1' | None => ⌜ v1' = v1 ⌝ end  ]
  ⊫ [bupd]; ghost_var γ q2 v2 ✱ [ match q2' with | Some q => ghost_var γ q v2  | None => True end ∗ ⌜ v1' = v1 ⌝ ] | 200.
  Proof.
  iIntros (_ Hq1 Hq2). do 2 iStepS. unfold FracSub in *. destruct q1'; subst.
  - iDestruct (ghost_var_agree with "H1 H2") as %<-.
      iCombine "H2 H1" as "H". rewrite Hq1. iMod (ghost_var_update v2 with "H") as "H".
      destruct q2'; rewrite -Hq2; iStepsS.
  - iMod (ghost_var_update v2 with "H1") as "H". iDestruct "H2" as "%H2".
      destruct q2'; rewrite -Hq2; iStepsS.
  Qed.

End automation.
