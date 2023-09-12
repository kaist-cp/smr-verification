From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.
From smr Require Import helpers.

From smr.diaframe.lang Require Import proof_automation atomic_specs.
From smr Require Import ebr.spec_rcu_simple.

Section spec.

Context `{!heapGS Σ, !rcuG Σ} (rcuN: namespace).
Variable (rcu : rcu_simple_spec Σ rcuN).
Definition rcu_code := rcu.(rcu_spec_code).
Notation iProp := (iProp Σ).

Global Instance biabd_rcu_domain_register (p: blk) γd γ_p R n E:
  HINT †p…n ✱ [d lv; rcu.(IsRCUDomain) γd d ∗ p ↦∗ lv ∗ ⌜n = (length lv)⌝ ∗ R p lv γ_p ∗ ⌜↑(mgmtN rcuN) ⊆ E⌝ ]
      ⊫ [fupd E E]
    ; (rcu.(Managed) γd p γ_p n R) ✱ [ emp ].
Proof.
  iSteps. unseal_diaframe. simpl. iSplitL; try done.
  iApply (rcu.(rcu_domain_register)); try done. iSteps.
Qed.

Global Instance guard_activate_dspec g E:
  SolveSepSideCondition (↑(mgmtN rcuN) ⊆ E) →
  SPEC ⟨E⟩ γd d,
  {{ rcu.(Guard) γd g Deactivated ∗ rcu.(IsRCUDomain) γd d}}
    rcu_code.(guard_activate) #g
  {{ γg, RET #(); rcu.(Guard) γd g (Activated γg) }}.
Proof.
  intros. iSteps.
  wp_apply (rcu.(guard_activate_spec) with "H2 H1"); [done|].
  iSteps.
Qed.

Global Instance guard_deactivate_dspec g E:
  SolveSepSideCondition (↑(mgmtN rcuN) ⊆ E) →
  SPEC ⟨E⟩ γg γd d,
  {{ rcu.(Guard) γd g (Activated γg) ∗ rcu.(IsRCUDomain) γd d}}
    rcu_code.(guard_deactivate) #g
  {{ RET #(); rcu.(Guard) γd g Deactivated }}.
Proof.
  intros. iSteps.
  wp_apply (rcu.(guard_deactivate_spec) with "H2 H1"); [done|].
  iSteps.
Qed.

Global Instance rcu_aggressive_guard_protect_and_agree p γg γe γ_p size_i R g:
  MergableConsume (rcu.(Managed) γe p γ_p size_i R) true (λ p' Pin Pout,
  TCAnd (TCEq Pin (rcu.(Guard) γe g (Activated γg)) ) $
      TCEq Pout (
        ∀ d E, ⌜ ↑(mgmtN rcuN) ⊆ E ⌝ -∗ rcu.(IsRCUDomain) γe d -∗
        (|={ E }=> rcu.(Guard) γe g (Activated γg)
        ∗ rcu.(Managed) γe p γ_p size_i R ∗ rcu.(NodeInfo) γe γg p γ_p size_i R)
      ) )%I.
Proof.
  intros. rewrite /MergablePersist => p' Pin Pout [-> ->].
  rewrite bi.intuitionistically_if_elim.
  iIntros "[M G] %d %E % #IRD".

  iMod (rcu.(guard_protect) with "IRD M G") as "(M & G & #Info)"; [done|].
  iFrame "∗#". done.
Qed.

Global Instance biabd_guard_acc (p: blk) γd g γg E:
  HINT rcu.(Guard) γd g (Activated γg) ✱ [γ_p R size_i; rcu.(NodeInfo) γd γg p γ_p size_i R ∗ ⌜↑(ptrN rcuN p) ⊆ E⌝ ] ⊫
    [fupd E (E ∖ ↑(ptrN rcuN p))]
    lv;
    p ↦∗ lv ✱
    [ ▷ R p lv γ_p ∗ ⌜length lv = size_i⌝ ∗ rcu.(Guard) γd g (Activated γg) ∗
    (∀ lv', ▷ R p lv' γ_p ∗ p ↦∗ lv' ∗ ⌜length lv = length lv'⌝  ={E∖↑(ptrN rcuN p),E}=∗ True) ].
Proof.
  intros.
  do 4 iStep.
  iMod (rcu.(guard_acc) with "H2 H1") as (lv) "(% & l↦ & N_l & γg & CloseG)"; [done|].
  iExists lv. iFrame. do 3 iStep. iApply "CloseG". by iFrame.
Qed.

(* Global Instance mc_rcu_guard_managed_agree γd s p γ_p1 γ_p2 R1 R2 size_i1 size_i2 γg :
  MergablePersist (▷ rcu.(Managed) γd p γ_p2 size_i2 R2) (λ p' Pin Pout,
  TCAnd (TCEq Pin (rcu.(NodeInfo) γd γg p γ_p1 size_i1 R1 ∗ rcu.(Guard) γd s (Activated γg))) $
      TCEq Pout (▷ ⌜ γ_p1 = γ_p2 ⌝))%I.
Proof.
  rewrite /MergablePersist => p' Pin Pout [-> ->].
  rewrite bi.intuitionistically_if_elim.
  iStep.
  by iDestruct (rcu.(guard_managed_agree) with "H2 H3 H1") as "#$".
Qed. *)

Definition Managed_NodeInfo γd γg p γ_p1 γ_p2 size_i1 size_i2 R1 R2 : iProp := (▷ rcu.(Managed) γd p γ_p2 size_i2 R2) ∗ rcu.(NodeInfo) γd γg p γ_p1 size_i1 R1.
Global Typeclasses Opaque Managed_NodeInfo.

Global Instance ManagedNodeInfo_merge γd γg p γ_p1 γ_p2 size_i1 size_i2 R1 R2 :
  MergableConsume (▷ rcu.(Managed) γd p γ_p2 size_i2 R2) true (λ p' Pin Pout,
  TCAnd (TCEq Pin (rcu.(NodeInfo) γd γg p γ_p1 size_i1 R1)) $
         TCEq Pout (Managed_NodeInfo γd γg p γ_p1 γ_p2 size_i1 size_i2 R1 R2)).
Proof.
  rewrite /MergableConsume => p' Pin Pout [-> ->].
  rewrite bi.intuitionistically_if_elim /Managed_NodeInfo.
  iSteps.
Qed.

Global Instance Managed_NodeInfo_agree_or_decouple γd γg g p γ_p1 γ_p2 size_i1 size_i2 R1 R2 :
  MergableConsume (Managed_NodeInfo γd γg p γ_p1 γ_p2 size_i1 size_i2 R1 R2) true (λ p' Pin Pout,
  TCAnd (TCEq Pin (rcu.(Guard) γd g (Activated γg))) $
         TCEq Pout (▷ ⌜γ_p1 = γ_p2⌝ ∗ ▷ rcu.(Managed) γd p γ_p2 size_i2 R2 ∗ rcu.(NodeInfo) γd γg p γ_p1 size_i1 R1 ∗ rcu.(Guard) γd g (Activated γg))%I).
Proof.
  rewrite /MergableConsume => p' Pin Pout [-> ->];
  rewrite bi.intuitionistically_if_elim /Managed_NodeInfo.
  iStep.
  iDestruct (guard_managed_agree with "H2 H3 H1") as "#$".
  iSteps.
Qed.

(* Local Definition after_agree_def (γ_p: gname) := True.
Local Definition after_agree_aux : seal (@after_agree_def). Proof. by eexists. Qed.
Definition after_agree := after_agree_aux.(unseal).
Local Definition after_agree_unseal :
    @after_agree = @after_agree_def := after_agree_aux.(seal_eq).

Definition guard_agree_intermediate γg γd size_i1 size_i2 γ_p1 γ_p2 p R1 R2: iProp :=
  ∀ g, rcu.(Guard) γd g (Activated γg) -∗
  rcu.(NodeInfo) γd γg p γ_p1 size_i1 R1 ∗
  ▷ rcu.(Managed) γd p γ_p2 size_i2 R2 ∗
  rcu.(Guard) γd g (Activated γg) ∗
  ▷ ⌜ γ_p1 = γ_p2 ⌝.

(* TODO: MergablePersist is not well-made for three resources. For now, temporarily use a
         MergableConsume.
         We force diaframe to find a correct NodeInfo first, as the protect rule finds a guard.
         Ideally, this will have higher priority than the other MergableConsume instance for guard_protect.
   TODO: NodeInfo disappers from the context, even though it is persistent...
*)
Global Instance mc_guard_agree_step1 γd p γ_p1 γ_p2 R1 R2 size_i1 size_i2 γg :
  TCIf (SolveSepSideCondition (after_agree γ_p2)) False TCTrue →
  MergableConsume (▷ rcu.(Managed) γd p γ_p2 size_i2 R2) (λ p' Pin Pout,
  TCAnd (TCEq Pin (rcu.(NodeInfo) γd γg p γ_p1 size_i1 R1)) $
      TCEq Pout (
        (* The `after_agree` should come before `guard_agree_intermediate` to block multiple hint application,
           since MergableConsume rules are applied in a depth-first way. *)
        ⌜ after_agree γ_p1 ⌝ ∗
        guard_agree_intermediate γg γd size_i1 size_i2 γ_p1 γ_p2 p R1 R2
      ) )%I.
Proof.
  intros. rewrite /MergableConsume => p' Pin Pout [-> ->].
  rewrite bi.intuitionistically_if_elim.
  rewrite after_agree_unseal. iIntros "[M #Info]".  iFrame "#". iIntros (g) "G".

  iDestruct (rcu.(guard_managed_agree) with "Info G M") as "#$".
  by iFrame "∗#".
Qed.

Global Instance mc_guard_agree_step_2 γd p γ_p1 γ_p2 R1 R2 size_i1 size_i2 γg g:
  MergableConsume (guard_agree_intermediate γg γd size_i1 size_i2 γ_p1 γ_p2 p R1 R2) (λ p' Pin Pout,
  TCAnd (TCEq Pin (rcu.(Guard) γd g (Activated γg))) $
      TCEq Pout (
        ▷ ⌜ γ_p1 = γ_p2 ⌝ ∗
        rcu.(NodeInfo) γd γg p γ_p1 size_i1 R1 ∗
        ▷ rcu.(Managed) γd p γ_p2 size_i2 R2 ∗
        rcu.(Guard) γd g (Activated γg)
      ) )%I.
Proof.
  rewrite /MergableConsume => p' Pin Pout [-> ->].
  rewrite bi.intuitionistically_if_elim.
  iStep. iDestruct ("H1" with "H2") as "($ & $ & $ & $)".
Qed. *)

Global Instance rcu_domain_retire_dspec E d p s:
  SolveSepSideCondition (↑rcuN ⊆ E) →
  SPEC ⟨E⟩ R γd γ_p, {{ rcu.(IsRCUDomain) γd d ∗ rcu.(Managed) γd p γ_p s R }}
    rcu_code.(rcu_domain_retire) #d #p #s
  {{ RET #(); True }}.
Proof.
  intros. iSteps. wp_apply (rcu.(rcu_domain_retire_spec) with "H1 H2"); done.
Qed.

End spec.
