From iris.base_logic.lib Require Import invariants ghost_var ghost_map.
From smr.program_logic Require Import atomic.
From smr.lang Require Import lang proofmode notation.
From smr Require Import sorted_list.

From smr Require Import helpers no_recl.code_harris_operations no_recl.code_harris_michael_find.
From smr.no_recl Require Export proof_harris_operations.
From iris.prelude Require Import options.

Section harris_michael_find.
Context `{!heapGS Σ, !hlG Σ}.
Context (listN : namespace).
Notation iProp := (iProp Σ).
Notation IsHList := (IsHList listN).
Notation harris_find_au := (harris_find_au listN).
Notation harris_helping_cas_spec := (harris_helping_cas_spec listN).

Lemma hm_find_inner_wrong_proph E (prev curr : loc) cn (k : Z) (pr : proph_id) pr_v Φ :
  prophecy_to_bool pr_v = false →
  proph pr pr_v -∗
  (curr +ₗ next) ↦□ #(cn &ₜ 1) -∗
  WP hm_find_inner #pr #k #prev #curr @ E {{ v, Φ v}}.
Proof.
  iIntros (Hpr) "pr #c.n↦□". wp_lam. wp_pures.
  wp_apply (wp_resolve_load with "[$pr $c.n↦□]") as (?) "(-> & _ & _)". inversion Hpr.
Qed.

Lemma hm_helping_cas_spec :
  harris_helping_cas_spec' listN.
Proof.
  intros ????????????????.
  iIntros (Φ') "(IsHM & #p↪□ & #c↪□ & #an.n↦□ & AU) HΦ'". wp_bind (CmpXchg _ _ _)%E.
  iInv "IsHM" as (p_all L) "(>Linv & >●p_all & >PTRS & Nodes & >(%HL & %HLh & %HLt))".
  iDestruct (ghost_map_lookup with "●p_all p↪□") as %Hptrs_p.
  iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_c.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[p.k↦□ [p.n|%HLp]]"; [exact Hptrs_p| |].
  { (* prev tagged. Fail cas and return None. *)
    iDestruct "p.n" as (pn pn_k) "[p.n↦□ pn↪□]".
    wp_cmpxchg_fail.
    iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    wp_pures. iApply "HΦ'".
    iModIntro. destruct committing; iFrame.
  }
  (* prev not tagged, obtain next and check if it is still c. *)
  apply elem_of_list_lookup in HLp as [idx HLp].
  iDestruct (Nodes_remove with "Nodes") as (on) "[(_ & _ & p.n↦ & >%HLp_next) Nodes]"; [exact HLp|].
  destruct (decide (on = Some anchor)) as [->|NE]; last first.
  { (* curr changed from c, CAS must fail *)
    wp_cmpxchg_fail.
    iDestruct (Nodes_combine with "Nodes [] [] [p.n↦]") as "Nodes"; [done..|].
    iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    wp_pures. iApply "HΦ'".
    iModIntro. destruct committing; iFrame.
  }
  (* curr is still anchor, CAS succeed *)
  wp_cmpxchg_suc; [done|].
  apply list_lookup_fmap_Some in HLp_next as [[[a_k b] ?] [HLa [= <-]]].
  (* Get info about c *)
  iAssert (⌜b = true ∧ L.*2 !! (idx + 1 + 1)%nat = (Some curr)⌝)%I as %([= ->] & HLa_next).
  { iDestruct (Nodes_rm_idx_remove with "Nodes") as (?) "[(_ & _ & an.n↦ & %) _]"; [exact HLa|lia|].
    destruct b; by iDestruct (pointsto_agree with "an.n↦ an.n↦□") as %[= ->].
  }
  (* Update L *)
  set (L' := delete (S idx) L).
  assert (get_abs_state L = get_abs_state L') as ->.
  { rewrite -(take_drop (S idx) L).
    subst L'. rewrite delete_take_drop !get_abs_state_app.
    f_equal. apply drop_S in HLa. rewrite Nat.add_1_r in HLa.
    by rewrite HLa get_abs_state_cons.
  }
  apply list_lookup_fmap_Some in HLa_next as [[[c_k' b] ?] [HLc [= <-]]].
  iDestruct (get_persistent_Nodes_rm_idx with "Nodes") as (?) "#(c.k↦□ & c↪□' & c.n↦□ & _)"; [exact HLc|lia|].
  iDestruct (ghost_map_elem_agree with "c↪□ c↪□'") as %[= <-].
  iAssert (ghost_var γl (1 / 2) (get_abs_state L') -∗ ▷ HListInternalInv h γp_a γl)%I
            with "[●p_all PTRS p.n↦ Nodes]" as "INV".
  { iIntros "Linv". repeat iExists _. iFrame "●p_all Linv #%".
    unfold AllPtrs,Nodes,Nodes_rm_idx. iSplitL "PTRS"; [|iModIntro; iSplit].
    - iApply (big_sepM_mono with "PTRS").
      iIntros (p' k' Hprts_p) "[$ [$|%HLp']]".
      iRight. iPureIntro. subst L'.
      apply elem_of_list_lookup in HLp' as [idx_p HLp'].
      apply elem_of_list_lookup.
      destruct (decide (idx_p < (S idx))) as [LT|GE].
      + exists idx_p. rewrite lookup_delete_lt; done.
      + exists (idx_p - 1). rewrite lookup_delete_ge; last first.
        { assert (idx_p ≠ idx + 1); [|lia]. naive_solver. }
        rewrite -HLp'. f_equal. lia.
    - rewrite -{2}(take_drop (S idx) L).
      subst L'.
      apply drop_S in HLa. rewrite Nat.add_1_r in HLa.
      rewrite {2}delete_take_drop HLa !big_sepL_app /=.
      iDestruct "Nodes" as "(NodesTake & _ & NodesDrop)".
      assert (S idx <= length L).
      { assert (idx < length L); [|lia]. rewrite -lookup_lt_is_Some. eauto. }
      iSplitR "NodesDrop"; last first.
      { iApply (big_sepL_mono with "NodesDrop"). iIntros (idx' [[k' b'] l'] HLl') "l'".
        rewrite length_take_le; [|done]. case_decide; [lia|].
        iDestruct "l'" as (l'_next) "($ & $ & l'.n↦ & %HLl'next)".
        iExists (l'_next). iFrame. iPureIntro.
        rewrite list_fmap_delete lookup_delete_ge; [|lia].
        rewrite -HLl'next. f_equal. lia.
      }
      rewrite (take_S_r L idx (p_k, false, prev) ltac:(done)) !big_sepL_app /=.
      iDestruct "NodesTake" as "[NodesTake p]". iSplitL "NodesTake"; [|iSplit; [|done]].
      { iApply (big_sepL_mono with "NodesTake"). iIntros (idx' [[k' b'] l'] HLl') "l'".
        case_decide as EQN. { subst idx'. rewrite lookup_take_Some in HLl'. lia. }
        iDestruct "l'" as (l'_next) "($ & $ & l'.n↦ & %HLl'next)".
        iExists (l'_next). iFrame. iPureIntro.
        apply lookup_lt_Some in HLl' as LT. rewrite length_take_le in LT; [|lia].
        by rewrite list_fmap_delete lookup_delete_lt; [|lia].
      }
      iExists (Some curr). iFrame "∗#%". iPureIntro.
      rewrite Nat.add_0_r list_fmap_delete lookup_delete_ge length_take_le; [try lia..].
      get_third HLc. rewrite -HLc. f_equal. lia.
    - iPureIntro. subst L'. split_and!.
      + rewrite !list_fmap_delete. by apply delete_inf_Z_sorted.
      + rewrite lookup_delete_lt; [done|lia].
      + destruct HLt as [t HLt]. exists t.
        apply lookup_lt_Some in HLc as LT.
        assert (length L - 1 ≠ idx + 1) as NE.
        { intros EQ. rewrite -EQ in HLa. naive_solver. }
        rewrite Nat.add_1_r in HLa.
        rewrite lookup_delete_ge length_delete; eauto; [|lia].
        rewrite -HLt. f_equal. lia.
  }
  (* Check if we are committing. *)
  destruct committing; last first.
  { iModIntro. iSplitL "Linv INV"; [iApply "INV"; iFrame|].
    wp_pures. iApply "HΦ'". done.
  }
  (* We are committing. *)
  iDestruct "AU" as "[pr AU]".
  (* Check tag value and key of c_k *)
  destruct (decide (prophecy_to_bool pr_v ∨ (c_k < k)%inf_Z)) as [NotCommit|[Hpr_v'%Is_true_false GE]%Decidable.not_or].
  { (* prophecy predicts that curr is tagged. Do not commit. *)
    iModIntro. iSplitL "Linv INV"; [iApply "INV"; iFrame|].
    wp_pures. iApply "HΦ'". by iFrame.
  }
  (* prophecy predicts that curr is not tagged. *)
  (* assert that we are not tagged. *)
  destruct b.
  { iModIntro. iSplitL "Linv INV"; [iApply "INV"; iFrame|].
    wp_pures. iApply "HΦ'". iFrame. iModIntro. iLeft. iExists _. iFrame "c.n↦□".
  }
  (* Commit. *)
  iMod "AU" as (?) "[[Labs %HLabs] [_ Commit]]".
  iDestruct (ghost_var_agree with "Labs Linv") as %[= ->].
  assert (L' = take idx L ++ [(p_k, false, prev)] ++ [(c_k, false, curr)] ++ drop (S (S (S idx))) L) as ->.
  { subst L'. rewrite delete_take_drop (take_S_r _ _ (p_k, false, prev)); [|done].
    simplify_list_eq. repeat f_equal.
    rewrite (drop_S _ (c_k, false, curr) (S (S idx))); [done|].
    rewrite -HLc. f_equal. lia.
  }
  set (idx' := length (get_abs_state (take idx L))).
  iMod ("Commit" $! (bool_decide (c_k = k)) prev curr _ _ idx' with "[$Labs]") as "HΦ".
  { iFrame "∗#%". iPureIntro. split_and!; auto; last first.
    { case_bool_decide as EQN; [done|]. destruct c_k as [|c_k|]; [naive_solver| |naive_solver].
      simpl in *. apply inf_Z.lt_Z_lt,Z.lt_nge => ?.
      apply GE,inf_Z.Z_lt_lt,Z.lt_nge => ?.
      apply EQN. f_equal. lia.
    }
    all: rewrite !get_abs_state_app /=; simplify_list_eq; rewrite lookup_app_r; [|lia].
    - fold idx'. by replace (S idx' - idx') with 1 by lia.
    - by rewrite Nat.sub_diag.
  }
  iModIntro. iSplitL "Linv INV"; [iApply "INV"; iFrame|].
  wp_pures. iApply "HΦ'". by iFrame.
Qed.

Local Lemma hm_find_inner_spec  (* Auxillary, non-unifiable *) Φ (k : Z) E
                                (* harris inv *) γp_a γl h
                                (* prophecy *) (tagged : bool) (pr : proph_id) (pr_v : list (val * val))
                                (* prev, curr *) (prev curr : loc) (p_k c_k : inf_Z) :
  (p_k < k)%inf_Z →
  prophecy_to_bool pr_v = tagged →
  ↑listN ⊆ E →
  {{{ inv listN (HListInternalInv h γp_a γl) ∗
      prev ↪[γp_a]□ p_k ∗ curr ↪[γp_a]□ c_k ∗
      proph_map.proph pr pr_v ∗
      if decide (tagged ∨ (c_k < k)%inf_Z) then
        harris_find_au E γp_a γl k Φ
      else
        True
  }}}
    hm_find_inner #pr #k #prev #curr @ E
  {{{ v, RET v;
      if decide (tagged ∨ (c_k < k)%inf_Z) then
        (* Failed CAS. *)
        ⌜v = NONEV⌝ ∗ harris_find_au E γp_a γl k Φ ∨
        (* Succeed CAS and continue. *)
        (∃ (ret_b : bool) (ret_prev ret_curr : loc),
          ⌜v = SOMEV (#ret_b, #ret_prev, #ret_curr)⌝ ∗
          Φ (#ret_b, #ret_prev, #ret_curr)%V)
      else
        ⌜v = SOMEV (#(bool_decide (c_k = k)), #prev, #curr)⌝
  }}}.
Proof.
  intros p_k_LT_k Hpr ?.
  iIntros (Φ') "(#IsHM & #p↪□ & #c↪□ & pr & AU) HΦ'".
  iLöb as "IH" forall (tagged prev curr p_k c_k pr_v Hpr p_k_LT_k) "p↪□ c↪□".
  wp_lam. wp_pures.
  wp_bind (Resolve _ _ _)%E.
  iInv "IsHM" as (p_all L) "(>Linv & >●p_all & >PTRS & Nodes & >(%HL & %HLh & %HLt))".
  iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_curr.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[c.k↦□ c_next]"; [exact Hptrs_curr|].
  (* Check prophecy value for tag. *)
  destruct tagged; simpl.
  { (* prophecy says that curr is tagged. Hence, we still have AU, and will try to commit at the later CAS. *)
    (* assert that we must be tagged. *)
    iDestruct "c_next" as "[c_next|%HLcurr]"; last first.
    { apply elem_of_list_lookup in HLcurr as [idx HLcurr].
      iDestruct (Nodes_remove with "Nodes") as (c_next) "[(_ & _ & c.n↦ & >%HLc_next) Nodes]"; [exact HLcurr|].
      wp_apply (wp_resolve_load with "[$pr $c.n↦]") as (?) "(-> & _ & _)". inversion Hpr.
    }
    iDestruct "c_next" as (c_next c_n_k) "[c.n↦□ c_next↪□]".
    wp_apply (wp_resolve_load with "[$pr $c.n↦□]") as (pr_v') "(-> & pr & _)".
    iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    wp_pures. clear dependent L p_all.
    wp_apply (hm_helping_cas_spec true with "[$pr $AU]"); simpl in *; [done|exact p_k_LT_k|by iFrame "#"|].
    iIntros ([]) "[pr AU]"; wp_pures; last first.
    { iApply "HΦ'". iModIntro. iLeft. iSplit; [done|iFrame "AU"]. }
    destruct (decide (prophecy_to_bool pr_v' ∨ (c_n_k < k)%inf_Z)) as [NotCommit|[Hpr_v'%Is_true_false GE]%Decidable.not_or].
    { iApply ("IH" with "[%] [%] pr [AU] [HΦ'] p↪□ c_next↪□"); [done..| |].
      all: repeat case_decide; done.
    }
    (* assert that we are not tagged. *)
    iDestruct "AU" as "[[% c_next.n↦□]|HΦ]".
    { by iApply (hm_find_inner_wrong_proph with "pr c_next.n↦□"). }
    (* Committed. *)
    wp_pures.
    iApply ("IH" $! false with "[%] [%] pr [] [HΦ HΦ'] p↪□ c_next↪□"); [done|done|..].
    - case_decide; [naive_solver|done].
    - case_decide as EQN; [done|].
      iIntros "!>" (? ->). iApply "HΦ'". iRight.
      repeat iExists _. iSplit; done.
  }
  (* prophecy says we are not tagged. *)
  (* assert that we must not be tagged. *)
  iDestruct "c_next" as "[c_next|%HLcurr]".
  { iDestruct "c_next" as (c_next ?) "#[c.n↦□ _]".
    wp_apply (wp_resolve_load with "[$pr $c.n↦□]") as (?) "(-> & _ & _)". inversion Hpr.
  }
  apply elem_of_list_lookup in HLcurr as [idx HLcurr].
  iDestruct (Nodes_remove with "Nodes") as (c_next) "[(_ & _ & c.n↦ & >%HLc_next) Nodes]"; [exact HLcurr|].
  wp_apply (wp_resolve_load with "[$pr $c.n↦]") as (pr_v') "(-> & pr & c.n↦)".
  iDestruct (Nodes_combine with "Nodes [] [] [c.n↦]") as "Nodes"; [done..|].
  iAssert (ghost_var γl (1 / 2) (get_abs_state L) ∗ Nodes L γp_a -∗
            ▷ HListInternalInv h γp_a γl)%I with "[●p_all PTRS]" as "INV".
  { iIntros "[Linv Nodes]". repeat iExists _. by iFrame "∗#%". }
  (* Check if we already committed or not. *)
  destruct (decide (c_k < k)%inf_Z) as [LT|GE]; last first.
  { (* Already committed *)
    case_decide; [naive_solver|]. iClear "AU IH".
    iModIntro. iSplitL "INV Nodes Linv"; [iApply "INV"; iFrame|].
    wp_pures. wp_load. wp_pures.
    iEval (case_bool_decide; [naive_solver|]).
    wp_pures. by iApply "HΦ'".
  }
  destruct (next_not_tail_is_Some idx L c_k false curr c_next) as [c_next' [= ->]]; [naive_solver..|].
  rename c_next' into c_next.
  (* Not yet committed. *)
  apply list_lookup_fmap_Some in HLc_next as [[[cn_k b] ?] [HLc_next [= <-]]].
  iDestruct (get_persistent_Nodes with "Nodes") as (on) "#(c_next.k↦□ & c_next↪□ & #c_next.n↦□ & %HLc_next_next)"; [exact HLc_next|].
  (* Check if this is commit point of next iteration. *)
  (* Check tag and key of c_next *)
  destruct (decide (prophecy_to_bool pr_v' ∨ (cn_k < k)%inf_Z)) as [NotCommit|[Hpr_v'%Is_true_false GE]%Decidable.not_or].
  { (* Tagged or key too small. Do not commit. *)
    iModIntro. iSplitL "INV Nodes Linv"; [iApply "INV"; iFrame|].
    wp_pures. wp_load. wp_pures.
    iEval (case_bool_decide; [|naive_solver]).
    wp_pures.
    case_decide; [|naive_solver].
    iApply ("IH" with "[%] [%] pr [AU] [HΦ'] c↪□ c_next↪□"); [done|done|..].
    all: repeat case_decide; try done.
  }
  (* curr must not be tagged *)
  destruct b.
  { iModIntro. iSplitL "Linv Nodes INV"; [iApply "INV"; iFrame|].
    wp_pures. wp_load. wp_pures.
    iEval (case_bool_decide; [|naive_solver]).
    wp_pures.
    by iApply (hm_find_inner_wrong_proph with "pr c_next.n↦□").
  }
  case_decide; [|naive_solver].
  (* Not tagged and key is GE. Commit. *)
  iMod "AU" as (?) "[[Labs %HLabs] [_ Commit]]".
  iDestruct (ghost_var_agree with "Labs Linv") as %[= ->].
  assert (L = take idx L ++ [(c_k, false, curr)] ++ [(cn_k, false, c_next)] ++ drop (S (S idx)) L) as L_EQ.
  { rewrite -{1}(take_drop (S idx) L). rewrite (take_S_r _ _ (c_k, false, curr)); [|done].
    simplify_list_eq. repeat f_equal. rewrite (drop_S _ (cn_k, false, c_next) (S idx)); [done|].
    by rewrite -Nat.add_1_r.
  }
  set (idx' := length (get_abs_state (take idx L))).
  iMod ("Commit" $! (bool_decide (cn_k = k)) curr c_next _ _ idx' with "[$Labs]") as "HΦ".
  { iFrame "∗#%". iPureIntro. split_and!; auto; last first.
    { case_bool_decide as EQN; [done|]. destruct cn_k as [|cn_k|]; [naive_solver| |naive_solver].
      apply inf_Z.Z_lt_lt,Z.lt_nge => ?.
      apply GE,inf_Z.Z_lt_lt,Z.lt_nge => ?.
      apply EQN. f_equal. lia.
    }
    all: rewrite L_EQ !get_abs_state_app /=; simplify_list_eq; rewrite lookup_app_r; [|lia].
    all: fold idx'.
    - by replace (S idx' - idx') with 1 by lia.
    - by rewrite Nat.sub_diag.
  }
  iModIntro. iSplitL "INV Nodes Linv"; [iApply "INV"; iFrame|].
  wp_pures. wp_load. wp_pures.
  iEval (case_bool_decide; [|naive_solver]).
  wp_pures.
  iApply ("IH" $! false with "[%] [%] pr [] [HΦ HΦ'] c↪□ c_next↪□"); [done..| |].
  - case_decide; [naive_solver|done].
  - case_decide as EQN; [done|].
    iIntros "!>" (v ->). iApply "HΦ'". iRight.
    repeat iExists _. iSplit; done.
Qed.

Lemma hm_find_spec :
  harris_find_spec' listN hm_find.
Proof.
  intros E k h γp_a γl l ?.
  iIntros "#l.h↦□ #h↪□ #IsHM" (Φ) "AU".
  iLöb as "IH".
  wp_lam. wp_pures.
  wp_apply (wp_new_proph with "[//]") as (pr_v pr) "pr".
  wp_pures. wp_load. wp_pures.
  wp_bind (! _)%E.
  iInv "IsHM" as (p_all L) "(>Linv & >●p_all & PTRS & Nodes & >(%HL & %HLh & %HLt))".
  iDestruct (Nodes_remove with "Nodes") as (on) "[(#h.k↦□ & _ & h.n↦ & >%HLh_next) Nodes]"; [exact HLh|].
  wp_load.
  iDestruct (Nodes_combine with "Nodes [] [] [h.n↦]") as "Nodes"; [done..|].
  assert (1 < length L) as [[[c_k c_b] curr] HLnext]%lookup_lt_is_Some.
  { assert (0 < length L); [by apply lookup_lt_Some in HLh|].
    assert (1 ≠ length L); [|lia].
    intros L_EQ. destruct HLt as [t HLt]. rewrite L_EQ Nat.sub_diag in HLt. naive_solver.
  }
  assert (on = Some curr) as ->. { get_third HLnext. naive_solver. }
  iDestruct (get_persistent_Nodes with "Nodes") as (c_next) "(#c.k↦□ & #c↪□ & #c.n↦□ & %HLc_next)"; [exact HLnext|].
  assert (-∞ᵢ < k)%inf_Z as LT_k; [done|].
  (* Check prophecy and key value. *)
  destruct (decide (prophecy_to_bool pr_v ∨ (c_k < k)%inf_Z)) as [NotCommit|[Hpr_v%Is_true_false GE]%Decidable.not_or].
  { (* Curr will be tagged or key too small. Do not commit. *)
    iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    wp_pures.
    wp_apply (hm_find_inner_spec with "[AU $pr]"); [exact LT_k|done|done|iFrame "∗#%"|].
    all: case_decide; try done.
    iIntros (v) "[[%EQ AU]|HΦ]".
    { rewrite EQ. wp_pures. iApply ("IH" with "AU"). }
    iDestruct "HΦ" as (??? ->) "HΦ".
    wp_pures. by iApply "HΦ".
  }
  (* prophecy predicts that curr is not tagged. *)
  destruct c_b.
  { (* cannot be tagged *)
    iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    wp_pures. by wp_apply (hm_find_inner_wrong_proph with "pr c.n↦□").
  }
  (* Not tagged and key value is good. commit. *)
  iMod "AU" as (?) "[[Labs %HLabs] [_ Commit]]".
  iDestruct (ghost_var_agree with "Labs Linv") as %->.
  iMod ("Commit" $! (bool_decide (c_k = k)) h curr _ _ 0 with "[$Labs]") as "HΦ".
  { iFrame "#%". iPureIntro.
    assert (L = [(-∞ᵢ,false,h);(c_k,false,curr)] ++ (drop 2 L)) as ->.
    { rewrite -{1}(take_drop 1 L). rewrite (take_S_r _ _ (-∞ᵢ, false, h)); [|done].
      simplify_list_eq. repeat f_equal.
      rewrite (drop_S _ (c_k, false, curr) 1); done.
    }
    split_and!; [done..|]. case_bool_decide as NE; [done|].
    destruct c_k as [|c_k|]; [naive_solver| |naive_solver].
    apply inf_Z.Z_lt_lt, Z.lt_nge => ?.
    apply GE, inf_Z.Z_lt_lt, Z.lt_nge => ?.
    apply NE. f_equal. lia.
  }
  iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
  { repeat iExists _. by iFrame "∗#%". }
  wp_pures.
  (* Note: the Φ is a placeholder. Normally it will be filled with AU, but we already used it here. *)
  wp_apply (hm_find_inner_spec Φ with "[$pr]"); [exact LT_k|done|done|iFrame "∗#%"|].
  all: case_decide; try naive_solver.
  iIntros (v ->). wp_pures. by iApply "HΦ".
Qed.

End harris_michael_find.

Definition hm_code_impl : code_harris_operations.harris_find_code := {|
  code_harris_operations.harris_find := hm_find;
|}.

Program Definition hm_impl Σ listN `{!heapGS Σ, !hlG Σ} : hfind_spec Σ listN  := {|
  proof_harris_operations.harris_find_spec_code := hm_code_impl;
|}.
Next Obligation. intros. apply hm_find_spec. Qed.
Next Obligation. intros. apply hm_helping_cas_spec. Qed.
