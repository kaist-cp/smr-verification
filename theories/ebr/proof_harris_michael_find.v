From iris.base_logic.lib Require Import invariants ghost_var ghost_map.
From smr.program_logic Require Import atomic.
From smr.lang Require Import lang proofmode notation.
From smr Require Import sorted_list.

From smr Require Import helpers ebr.spec_rcu_traversal ebr.code_harris_michael_find.
From smr.ebr Require Export proof_harris_operations.
From iris.prelude Require Import options.

(* TODO:
  1. Combine proof of initial stage of find_inner.
  2. Combine proof of initial stage of find.
  3. More helper lemmas for pure parts, e.g, when closing invariants.
*)

Section harris_michael_find.
Context `{!heapGS Σ, !hlG Σ}.
Context (listN rcuN : namespace) (DISJN : listN ## rcuN).

Variable (rcu : rcu_traversal_spec Σ rcuN).

Notation iProp := (iProp Σ).
Notation harris_type := (harris_type rcuN rcu).
Notation IsHList := (IsHList listN rcuN rcu).
Notation HListInternalInv := (HListInternalInv rcuN rcu).
Notation harris_find_au := (harris_find_au listN rcuN rcu).
Notation Nodes := (Nodes rcuN rcu).
Notation Nodes_rm_idx := (Nodes_rm_idx rcuN rcu).
Notation Nodes_rm_idx_idx := (Nodes_rm_idx_idx rcuN rcu).

Lemma hm_find_inner_wrong_proph E (d g : loc) (prev curr : blk) (i_c : positive) cn (k : Z) (pr : proph_id) pr_v Φ γg γr γp_a γp_t :
  ↑listN ∪ ↑rcuN ⊆ E →
  prophecy_to_bool pr_v = false →
  proph pr pr_v -∗
  rcu.(RCUNodeInfo) γr γg curr i_c (harris_type γp_a γp_t γr) -∗
  i_c ↪[γp_t]□ (cn, true) -∗
  rcu.(Guard) γr γg g -∗
  WP (hm_find_inner rcu) #pr #d #k #prev #curr @ E {{ v, Φ v }}.
Proof.
  iIntros (? Hpr) "pr #cInfo #c.n↪□ G".
  wp_lam. wp_pures.
  wp_apply (wp_new_proph with "[//]") as (??) "_"; wp_pures.
  wp_bind (!_)%E.
  iInv "cInfo" as (lv) "(c↦ & node & G)".
  iDestruct (harris_node_destruct with "node") as (?? c_t) "(>% & #c↪□ & c.n↪rcu & >[[% c.n↪]|[% c.n↪]])"; subst c_t lv.
  all: wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
  all: iDestruct (ghost_map_elem_agree with "c.n↪□ c.n↪") as %[= ->]; iClear "c.n↪".
  iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu [$c.n↪□]") as "$"; [by iRight|].
  wp_pures.
  wp_apply (wp_resolve_proph with "pr") as  (pvs') "[%Heq _]".
  subst pr_v. inversion Hpr.
Qed.

Lemma hm_helping_cas_spec :
  harris_helping_cas_spec' listN rcuN rcu.
Proof using DISJN.
  intros ?????????????????????????.
  iIntros (Φ') "(#IsHM & #IRD & #pInfo & #aInfo & #p↪□ & #c↪□ & #a.n↪□ & AU & G & Lc) HΦ'".
  wp_bind (CmpXchg _ _ _)%E.
  iInv "pInfo" as (lv) "(p↦ & node & G)".
  iDestruct (harris_node_destruct_agree with "p↪□ node") as (p_on p_t) "(>% & p.n↪rcu & >[[% p.n↪]|[% #p.n↪□]])"; subst lv p_t; last first.
  { (* prev tagged. Fail cas and return None. *)
    wp_apply (wp_cmpxchg_fail_offset with "p↦") as "p↦"; [by simplify_map_eq|simpl in *;auto..|].
    iModIntro. iDestruct (harris_node_combine_on with "p↦ p↪□ p.n↪rcu [$p.n↪□]") as "$"; [by iRight|].
    wp_pures. iApply "HΦ'". iModIntro. iFrame. destruct committing; iFrame.
  }
  iInv "IsHM" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
  iMod (lc_fupd_elim_later with "Lc Nodes") as "Nodes".
  iDestruct (ghost_map_lookup with "●p_all p↪□") as %Hptrs_p.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[p.n|%HLp]"; [exact Hptrs_p| |].
  { iDestruct "p.n" as (???) "[p.n↪□ _]".
    iDestruct (ghost_map_elem_agree with "p.n↪□ p.n↪") as %[= ? ?].
  }
  (* prev not tagged, obtain next and check if it is still c. *)
  apply elem_of_list_lookup in HLp as [idx_p HLp].
  iDestruct (Nodes_remove with "Nodes") as (? p_op) "[(pM & _ & p.n↪' & %HLp_n & %HLp_p) Nodes]"; [exact HLp|].
  iDestruct (ghost_map_elem_agree with "p.n↪' p.n↪") as %[= ->].
  destruct (next_not_tail_is_Some idx_p L p_k false (prev,i_p) p_on) as [(p_n, i_p_n) [= ->]]; [naive_solver..|].
  destruct (decide (p_n = anchor)) as [->|NE]; last first.
  { (* curr changed from c, CAS must fail *)
    wp_apply (wp_cmpxchg_fail_offset with "p↦") as "p↦"; [by simplify_map_eq|simpl in *;naive_solver..|].
    iDestruct (Nodes_combine with "Nodes pM [] [p.n↪]") as "Nodes"; [done..|].
    iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    iModIntro. iDestruct (harris_node_combine_some with "p↦ p↪□ p.n↪rcu [p.n↪']") as "$"; [iLeft; by iFrame|].
    wp_pures. iApply "HΦ'". iModIntro. iFrame. destruct committing; iFrame.
  }
  (* CAS succeed. *)
  wp_apply (wp_cmpxchg_suc_offset with "p↦") as "p↦"; [by simplify_map_eq|simpl in *;auto..].

  (* Agree info of prev and curr. *)
  apply list_lookup_fmap_Some in HLp_n as [[[a_k b] ?] [HLa [= <-]]].
  iDestruct (Nodes_rm_idx_remove with "Nodes") as (a_on' a_op) "[(aM & #a↪□ & a.n↪ & %HLa_n & %HLa_p) Nodes]"; [exact HLa|lia|simpl in *].
  iDestruct (rcu.(guard_managed_agree) with "aInfo G aM") as %<-.
  iAssert (⌜b = true ∧ a_on' = Some (curr, i_c) ∧ a_op = Some (prev, i_p)⌝)%I as %(-> & -> & ->).
  { destruct b; iDestruct (ghost_map_elem_agree with "a.n↪□ a.n↪") as %[= <-].
    iPureIntro. split_and!; auto. destruct a_op as [[??]|]; [|lia]. destruct HLa_p as [_ HLa_p].
    rewrite Nat.add_1_r Nat.sub_1_r /= in HLa_p. get_third HLp. naive_solver.
  }

  (* Destruct Nodes and update managed. *)
  iClear "a.n↪".
  apply list_lookup_fmap_Some in HLa_n as [[[c_k' b] ?] [HLa_n [= <-]]].
  unfold Nodes_rm_idx_idx. rewrite (big_sepL_take_drop _ _ (S idx_p)).
  rewrite (take_S_r _ _ (p_k,false,(prev, i_p))); [|exact HLp].
  rewrite (drop_S _ (a_k,true,(anchor,i_a))); [|rewrite -Nat.add_1_r; exact HLa].
  rewrite (drop_S _ (c_k',b,(curr,i_c))); [|rewrite -2!Nat.add_1_r; exact HLa_n].
  rewrite big_sepL_snoc !big_sepL_cons.
  iDestruct "Nodes" as "([NodesTake _] & _ & [a_n NodesDrop])".
  iEval (repeat (case_decide; [lia|])) in "a_n".
  iDestruct "a_n" as (c_on [[c_p i_c_p]|]) "(cM & #c↪□' & c.n↪ & %HLc_n & %HLc_p)"; [|lia].
  iDestruct (ghost_map_elem_agree with "c↪□ c↪□'") as %[= <-]; iClear "c↪□'".
  iAssert (if b then i_c ↪[ γp_t ]□ (c_on, true) else True)%I as "#c.n↪□". { destruct b; by iFrame. }
  iMod (rcu.(guard_protect_managed) with "IRD cM G") as "(cM & G & #cInfo)"; [solve_ndisj|].
  destruct HLc_p as [_ HLc_p]. assert (c_p = anchor ∧ i_c_p = i_a) as [-> ->]; simpl in *.
  { get_third HLa. rewrite Nat.sub_0_r -Nat.add_1_r HLa in HLc_p. by injection HLc_p as [= -> ->]. }
  iMod (rcu.(rcu_points_to_unlink) with "IRD p.n↪rcu aM") as "[p.n↪rcu aM]"; [solve_ndisj|]. rewrite gmultiset_difference_diag.
  iMod (rcu.(managed_delete) with "IRD aM") as "aD"; [solve_ndisj|].
  iMod (rcu.(deleted_clean) with "IRD aD cM") as "[aD cM]"; [solve_ndisj|].
  iMod (rcu.(rcu_points_to_link) with "IRD p.n↪rcu cM") as "[p.n↪rcu cM]"; [solve_ndisj|].
  rewrite gmultiset_difference_diag (left_id ∅).

  (* Update L *)
  set (L' := delete (S idx_p) L).
  assert (get_abs_state L = get_abs_state L') as ->.
  { rewrite -(take_drop (S idx_p) L).
    subst L'. rewrite delete_take_drop !get_abs_state_app.
    f_equal. apply drop_S in HLa. rewrite Nat.add_1_r in HLa.
    by rewrite HLa get_abs_state_cons.
  }
  iCombine "p.n↪' p.n↪" as "p.n↪".
  iMod (ghost_map_update (Some (curr, i_c), false) with "●p_tag p.n↪") as "[●p_tag [p.n↪ p.n↪']]".

  iAssert (ghost_var γl (1 / 2) (get_abs_state L') -∗ ▷ HListInternalInv h γp_a γp_t γl i_h γr)%I
            with "[●p_all ●p_tag PTRS NodesTake NodesDrop pM p.n↪ cM c.n↪]" as "INV".
  { iIntros "Linv". repeat iExists _. iFrame "●p_all ●p_tag Linv #%".
    unfold AllPtrs,Nodes. iSplitL "PTRS"; [|iModIntro; iSplit].
    - iApply (big_sepM_mono with "PTRS"); iIntros (i_p' [k' p'] Hprts_p') "p'".
      iDestruct "p'" as "[$|%HLp']". iRight. iPureIntro. subst L'.
      apply elem_of_list_lookup in HLp' as [idx_p' HLp'].
      apply elem_of_list_lookup.
      destruct (decide (idx_p' < (S idx_p))) as [LT|GE].
      + exists idx_p'. rewrite lookup_delete_lt; done.
      + exists (idx_p' - 1). rewrite lookup_delete_ge; last first.
        { assert (idx_p' ≠ idx_p + 1); [|lia]. naive_solver. }
        rewrite -HLp'. f_equal. lia.
    - subst L'. iEval (rewrite {2}delete_take_drop).
      iEval (rewrite (take_S_r _ _ (p_k,false,(prev, i_p))); [|exact HLp]).
      iEval (rewrite (drop_S _ (c_k,b,(curr,i_c))); [|rewrite -2!Nat.add_1_r; exact HLa_n]).
      assert (idx_p + 1 < length L). { by apply lookup_lt_Some in HLa. }
      rewrite big_sepL_app big_sepL_snoc big_sepL_cons !app_length /= !take_length_le; [|lia].
      rewrite !Nat.add_0_r !Nat.add_1_r.
      iSplitR "cM c.n↪ NodesDrop"; [iSplitL "NodesTake"|iSplitR "NodesDrop"].
      + iApply (big_sepL_mono with "NodesTake"); iIntros (idx_p' [[k' b'] [l' i_l']] HLl') "l'".
        assert (idx_p' < idx_p). { apply lookup_lt_Some in HLl'. rewrite take_length_le in HLl'; lia. }
        repeat (case_decide; [lia|]).
        iDestruct "l'" as (l'_on l'_op) "(l'M & $ & l'.n↪ & %HLl'_n & %HLl'_p)".
        iExists l'_on,l'_op. iFrame. iPureIntro.
        rewrite !list_fmap_delete !lookup_delete_lt; [done|lia..].
      + iExists (Some (curr,i_c)),p_op. iFrame "∗#". iPureIntro. rewrite !list_fmap_delete. split.
        * rewrite lookup_delete_ge; [|lia]. get_third HLa_n. rewrite -HLa_n. f_equal. lia.
        * rewrite lookup_delete_lt; [done|lia].
      + iExists c_on,(Some (prev,i_p)). iFrame "∗#". iPureIntro. rewrite !list_fmap_delete. split.
        * rewrite lookup_delete_ge; [|lia]. rewrite -HLc_n. f_equal. lia.
        * split; [lia|]. rewrite lookup_delete_lt /=; [|lia]. get_third HLp. by rewrite Nat.sub_0_r.
      + iApply (big_sepL_mono with "NodesDrop"); iIntros (idx_p' [[k' b'] [l' i_l']] HLl') "l'".
        repeat (case_decide; [lia|]).
        iDestruct "l'" as (l'_on l'_op) "(l'M & $ & l'.n↪ & %HLl'_n & %HLl'_p)".
        iExists l'_on,l'_op. iFrame. iPureIntro.
        rewrite !list_fmap_delete !lookup_delete_ge /=; [split|lia..]; simpl in *.
        * rewrite -HLl'_n. f_equal. lia.
        * destruct l'_op as [[??]|]; [|lia]. destruct HLl'_p as [_ HLl'_p]. split; [lia|].
          rewrite -HLl'_p. f_equal. lia.
    - iPureIntro. subst L'. split_and!.
      + rewrite !list_fmap_delete. by apply delete_inf_Z_sorted.
      + rewrite lookup_delete_lt; [done|lia].
      + destruct HLt as [t HLt]. exists t.
        apply lookup_lt_Some in HLa as LT.
        assert (length L - 1 ≠ idx_p + 1) as NE.
        { intros EQ. rewrite -EQ in HLa. naive_solver. }
        rewrite Nat.add_1_r in HLa.
        rewrite lookup_delete_ge length_delete; eauto; [|lia].
        rewrite -HLt. f_equal. lia.
      + rewrite dom_insert_lookup_L; [done|]. rewrite -elem_of_dom -Hdom elem_of_dom. eauto.
  }
  iDestruct (harris_node_combine_some with "p↦ p↪□ p.n↪rcu [p.n↪']") as "$"; [iLeft; by iFrame|].
  destruct committing; last first.
  { iModIntro. iSplitL "Linv INV"; [iApply "INV"; iFrame|]. iModIntro.
    wp_pures. iApply "HΦ'". iModIntro. iFrame.
  }
  (* Committing. *)
  iDestruct "AU" as "[pr AU]".

  (* Check if this is commit point of next iteration. *)
  (* Check tag value and key of cn_k *)
  destruct (decide (prophecy_to_bool pr_v ∨ (c_k < k)%inf_Z)) as [NotCommit|[Hpr_v'%Is_true_false GE]%Decidable.not_or].
  { (* prophecy predicts that curr is tagged. Do not commit. *)
    iModIntro. iSplitL "Linv INV"; [iApply "INV"; iFrame|]. iModIntro.
    wp_pures. iApply "HΦ'". iModIntro. iFrame "∗#%".
  }
  (* prophecy predicts that curr is not tagged. *)
  (* assert that we are not tagged. *)
  destruct b.
  { iModIntro. iSplitL "Linv INV"; [iApply "INV"; iFrame|]. iModIntro.
    wp_pures.
    iApply "HΦ'". iModIntro. iFrame "∗#%".
    iLeft. iExists _. iFrame "#".
  }
  (* Commit. *)
  iMod "AU" as (?) "[[Labs %HLabs] [_ Commit]]".
  iDestruct (ghost_var_agree with "Labs Linv") as %[= ->].
  assert (L' = take idx_p L ++ [(p_k, false, (prev,i_p))] ++ [(c_k, false, (curr,i_c))] ++ drop (S (S (S idx_p))) L) as ->.
  { subst L'. rewrite delete_take_drop (take_S_r _ _ (p_k, false, (prev,i_p))); [|done].
    simplify_list_eq. repeat f_equal.
    rewrite (drop_S _ (c_k, false, (curr,i_c)) (S (S idx_p))); [done|].
    rewrite -HLa_n. f_equal. lia.
  }
  set (idx' := length (get_abs_state (take idx_p L))).
  iMod ("Commit" $! (bool_decide (c_k = k)) i_p i_c idx' with "[$Labs]") as "HΦ".
  { iFrame "∗#%". iPureIntro. split_and!; auto; last first.
    { case_bool_decide as EQN; [done|]. destruct c_k as [|c_k|]; [naive_solver| |naive_solver].
      simpl in *. apply inf_Z.Z_lt_lt,Z.lt_nge => ?.
      apply GE,inf_Z.Z_lt_lt,Z.lt_nge => ?.
      apply EQN. f_equal. lia.
    }
    all: rewrite !get_abs_state_app /=; simplify_list_eq; rewrite lookup_app_r; [|lia].
    - fold idx'. by replace (S idx' - idx') with 1 by lia.
    - by rewrite Nat.sub_diag.
  }
  iModIntro. iSplitL "Linv INV"; [iApply "INV"; iFrame|].
  iModIntro. wp_pures. iApply "HΦ'". iModIntro. iFrame "∗#%".
  iRight. iIntros "G". iApply "HΦ". iFrame "∗#%".
Qed.

Local Lemma hm_find_inner_spec  (* Auxillary *) Φ (k : Z) E
                                (* harris inv *) (h : blk) γp_a γp_t γl i_h
                                (* reclamation *) γr d g γg
                                (* prophecy *) (tagged : bool) (pr : proph_id) (pr_v : list (val * val))
                                (* prev, curr*) (prev curr : blk) (i_p i_c : positive) (p_k c_k : inf_Z) :
  ↑listN ∪ ↑rcuN ⊆ E →
  (p_k < k)%inf_Z →
  prophecy_to_bool pr_v = tagged →
  {{{ inv listN (HListInternalInv h γp_a γp_t γl i_h γr) ∗
      rcu.(IsRCUDomain) γr d ∗
      rcu.(Guard) γr γg g ∗
      rcu.(RCUNodeInfo) γr γg prev i_p (harris_type γp_a γp_t γr) ∗
      rcu.(RCUNodeInfo) γr γg curr i_c (harris_type γp_a γp_t γr) ∗
      i_p ↪[γp_a]□ (p_k,prev) ∗ i_c ↪[γp_a]□ (c_k,curr) ∗
      proph_map.proph pr pr_v ∗
      if decide (tagged ∨ (c_k < k)%inf_Z) then
        harris_find_au E γp_a γp_t γl γr k g γg Φ
      else
        True
  }}}
    (hm_find_inner rcu) #pr #d #k #prev #curr @ E
  {{{ v, RET v;
      if decide (tagged ∨ (c_k < k)%inf_Z) then
        (⌜v = NONEV⌝ ∗ rcu.(Guard) γr γg g ∗ harris_find_au E γp_a γp_t γl γr k g γg Φ) ∨
        (∃ (ret_b : bool) (ret_prev ret_curr : loc),
          ⌜v = SOMEV (#ret_b, #ret_prev, #ret_curr)⌝ ∗
          Φ (#ret_b, #ret_prev, #ret_curr)%V)
      else
        ⌜v = SOMEV (#(bool_decide (c_k = k)), #prev, #curr)⌝ ∗
        rcu.(Guard) γr γg g
  }}}.
Proof using All.
  intros ? p_k_LT_k Hpr.
  iIntros (Φ') "(#IsH & #IRD & G & #pInfo & #cInfo & #p↪□ & #c↪□ & pr & AU) HΦ'".
  iLöb as "IH" forall (tagged prev curr p_k c_k i_p i_c pr pr_v Hpr p_k_LT_k) "p↪□ c↪□ pInfo cInfo".
  wp_lam. wp_pure credit: "Lc". wp_pures.
  wp_apply (wp_new_proph with "[//]") as (pr_v' pr') "pr'".
  wp_pures. wp_bind (! _)%E.
  iInv "cInfo" as (lv) "(c↦ & node & G)".
  iDestruct (harris_node_destruct_agree with "c↪□ node") as (c_on c_t) "(>% & c.n↪rcu & >c.n↪)"; subst lv.
  wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_map_eq|].
  (* Check prophecy value for tag. *)
  destruct tagged; simpl.
  { (* prophecy says that curr is tagged. Hence, we still have AU, and will try to commit at the later CAS. *)
    (* assert that we must be tagged. *)
    iDestruct "c.n↪" as "[[% c.n↪]|[% #c.n↪□]]"; subst c_t.
    { iModIntro; iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu [c.n↪]") as "$"; [iLeft; by iFrame|].
      wp_pures; wp_apply (wp_resolve_proph with "pr") as  (pvs') "[%Heq _]".
      subst pr_v. by inversion Hpr.
    }
    iInv "IsH" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
    iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_c.
    iDestruct (get_persistent_AllPtrs with "PTRS") as "#[c.n|%HLc]"; [exact Hptrs_c| |]; last first.
    { apply elem_of_list_lookup in HLc as [idx HLc].
      iDestruct (Nodes_remove with "Nodes") as (??) "[(_ & _ & c.n↪ & _) _]"; [exact HLc|simpl].
      iMod "c.n↪" as "c.n↪".
      iDestruct (ghost_map_elem_agree with "c.n↪ c.n↪□") as %[= ?].
    }
    iDestruct "c.n" as (i_c_n c_n c_n_k) "[c.n↪□' c_n↪□]".
    iDestruct (ghost_map_elem_agree with "c.n↪□ c.n↪□'") as %[= ->]. simpl in *. iClear "c.n↪□'".
    iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    iModIntro. iDestruct (harris_node_combine_some with "c↦ c↪□ c.n↪rcu [$c.n↪□]") as "$"; [by iRight|].
    wp_pures. wp_apply (wp_resolve_proph with "pr") as  (pvs') "[%Heq _]".
    clear dependent pr pr_v pvs'.
    wp_pures.

    wp_apply (hm_helping_cas_spec true with "[$pr' $G $AU $Lc]"); [done|exact p_k_LT_k|by iFrame "#"|].

    iIntros ([]) "(G & [pr' AU])"; simpl in *; wp_pures; last first.
    { iApply "HΦ'". iModIntro. iLeft. by iFrame. }
    iDestruct "AU" as "(cD & #c_nInfo & AU)".
    wp_apply (rcu.(rcu_domain_retire_spec) with "IRD cD") as "_"; [solve_ndisj|by rewrite harris_type_unfold|]; wp_pures.
    (* Check tag value and key of c_n *)
    destruct (decide (prophecy_to_bool pr_v' ∨ (c_n_k < k)%inf_Z)) as [NotCommit|[Hpr_v'%Is_true_false GE]%Decidable.not_or].
    { iApply ("IH" with "[%] [%] G pr' [AU] [HΦ'] p↪□ c_n↪□ pInfo c_nInfo"); [done|done|case_decide; done..]. }
    (* prophecy predicts that curr is not tagged. *)
    (* assert that we were not tagged. *)
    iDestruct "AU" as "[[% c_n.n↪□]|HΦ]".
    { iApply (hm_find_inner_wrong_proph with "pr' c_nInfo c_n.n↪□ G"); [solve_ndisj|done..]. }
    (* Commited. *)
    iApply ("IH" $! false with "[%] [%] G pr' [] [HΦ HΦ'] p↪□ c_n↪□ pInfo c_nInfo"); [done..| |].
    - case_decide; [naive_solver|done].
    - case_decide as EQN; [done|].
      iIntros "!>" (v ) "[-> G]". iApply "HΦ'". iRight.
      repeat iExists _. iSplit; [done|]. by iApply "HΦ".
  }
  (* prophecy says we are not tagged. *)
  (* assert that we must not be tagged. *)
  iDestruct "c.n↪" as "[[% c.n↪]|[% #c.n↪□]]"; subst c_t; last first.
  { iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu [$c.n↪□]") as "$"; [by iRight|].
    wp_pures. wp_apply (wp_resolve_proph with "pr") as (pvs') "[%Heq _]".
    rewrite Heq in Hpr. inversion Hpr.
  }
  (* Check if we already committed or not. *)
  destruct (decide (c_k < k)%inf_Z) as [LT|GE]; last first.
  { (* Already committed *)
    case_decide; [naive_solver|]. iClear "AU pr'".
    iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu [c.n↪]") as "$"; [iLeft; by iFrame|].
    wp_pures. wp_apply (wp_resolve_proph with "pr") as (pvs') "[_ _]".
    wp_pures. wp_bind (!_)%E.
    iInv "cInfo" as (lv) "(c↦ & node & G)".
    iDestruct (harris_node_destruct_agree with "c↪□ node") as (c_on' c_t) "(>% & c.n↪rcu & >c.n↪)"; subst lv.
    wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
    iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu c.n↪") as "$".
    wp_pures. iEval (case_bool_decide; [naive_solver|]).
    wp_pures. iApply "HΦ'". iModIntro. iFrame. iPureIntro. done.
  }
  iInv "IsH" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
  iMod (lc_fupd_elim_later with "Lc Nodes") as "Nodes".
  iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_c.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[c.n|%HLc]"; [exact Hptrs_c| |].
  { iDestruct "c.n" as (???) "[c.n↪□ _]".
    iDestruct (ghost_map_elem_agree with "c.n↪ c.n↪□") as %[= ? ?].
  }
  apply elem_of_list_lookup in HLc as [idx HLc].
  iDestruct (Nodes_remove with "Nodes") as (? c_op) "[(cM & _ & c.n↪' & %HLc_n & %HLc_p) Nodes]"; [exact HLc|].
  iDestruct (ghost_map_elem_agree with "c.n↪ c.n↪'") as %[= <-].
  iDestruct (Nodes_combine with "Nodes cM [] [c.n↪']") as "Nodes"; [done..|].
  destruct (next_not_tail_is_Some idx L c_k false (curr,i_c) c_on) as [[c_n i_c_n] [= ->]]; [naive_solver..|simpl in *].
  (* Not yet committed. *)
  apply list_lookup_fmap_Some in HLc_n as [[[c_n_k b] ?] [HLc_n [= <-]]].
  iDestruct (Nodes_remove with "Nodes") as (c_n_on c_n_op) "[(c_nM & #c_n↪□ & c_n.n↪ & %HLc_n_n & %HLc_n_p) Nodes]"; [exact HLc_n|].
  iMod (rcu.(guard_protect_managed) with "IRD c_nM G") as "(c_nM & G & #c_nInfo)"; [solve_ndisj|].
  iAssert (if b then i_c_n ↪[ γp_t ]□ (c_n_on, true) else True)%I as "#c_n.n↪□". { destruct b; by iFrame. }
  iDestruct (Nodes_combine with "Nodes c_nM [] [c_n.n↪]") as "Nodes"; [done..|].
  (* Check if this is commit point of next iteration. *)
  destruct (decide (prophecy_to_bool pr_v' ∨ (c_n_k < k)%inf_Z)) as [NotCommit|[Hpr_v'%Is_true_false GE]%Decidable.not_or].
  { (* Tagged or key too small. Do not commit. *)
    iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    iModIntro. iDestruct (harris_node_combine_some with "c↦ c↪□ c.n↪rcu [c.n↪]") as "$"; [iLeft; by iFrame|].
    wp_pures. wp_apply (wp_resolve_proph with "pr") as (pvs') "[_ _]". clear dependent pr pr_v pvs'.
    wp_pures. wp_bind (!_)%E.
    iInv "cInfo" as (lv) "(c↦ & node & G)".
    iDestruct (harris_node_destruct_agree with "c↪□ node") as (c_on' c_t) "(>% & c.n↪rcu & >c.n↪)"; subst lv.
    wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
    iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu c.n↪") as "$".
    wp_pures. iEval (case_bool_decide; [|naive_solver]).
    wp_pures.
    case_decide; [|naive_solver].
    iApply ("IH" with "[%] [%] G pr' [AU] [HΦ'] c↪□ c_n↪□ cInfo c_nInfo"); [done..| |].
    all: case_decide; done.
  }
  (* curr must not be tagged *)
  destruct b.
  { iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    iModIntro. iDestruct (harris_node_combine_some with "c↦ c↪□ c.n↪rcu [c.n↪]") as "$"; [iLeft; by iFrame|].
    wp_pures. wp_apply (wp_resolve_proph with "pr") as  (?) "_".
    wp_pures. wp_bind (!_)%E.
    iInv "cInfo" as (lv) "(c↦ & node & G)".
    iDestruct (harris_node_destruct_agree with "c↪□ node") as (c_on' c_t) "(>% & c.n↪rcu & >c.n↪)"; subst lv.
    wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
    iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu c.n↪") as "$".
    wp_pures. iEval (case_bool_decide; [|naive_solver]).
    wp_pures.
    by iApply (hm_find_inner_wrong_proph with "pr' c_nInfo c_n.n↪□ G").
  }
  case_decide as EQN; last first; [|clear EQN].
  { rewrite False_or in EQN. naive_solver. }

  (* Not tagged and key is GE. Commit. *)
  iMod "AU" as (?) "[[Labs %HLabs] [_ Commit]]".
  iDestruct (ghost_var_agree with "Labs Linv") as %[= ->].
  assert (L = take idx L ++ [(c_k, false, (curr,i_c))] ++ [(c_n_k, false, (c_n,i_c_n))] ++ drop (S (S idx)) L) as L_EQ.
  { rewrite -{1}(take_drop (S idx) L). rewrite (take_S_r _ _ (c_k, false, (curr, i_c))); [|done].
    simplify_list_eq. repeat f_equal. rewrite (drop_S _ (c_n_k, false, (c_n,i_c_n)) (S idx)); [done|].
    by rewrite -Nat.add_1_r.
  }
  set (idx' := length (get_abs_state (take idx L))).
  iMod ("Commit" $! (bool_decide (c_n_k = k)) i_c i_c_n idx' with "[$Labs]") as "HΦ".
  { iFrame "∗#%". iPureIntro. split_and!; auto; last first.
    { case_bool_decide as EQN; [done|]. destruct c_n_k as [|c_n_k|]; [naive_solver| |naive_solver].
      apply inf_Z.Z_lt_lt,Z.lt_nge => ?.
      apply GE,inf_Z.Z_lt_lt,Z.lt_nge => ?.
      apply EQN. f_equal. lia.
    }
    all: rewrite L_EQ !get_abs_state_app /=; simplify_list_eq; rewrite lookup_app_r; [|lia].
    all: fold idx'.
    - by replace (S idx' - idx') with 1 by lia.
    - by rewrite Nat.sub_diag.
  }
  iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
  { repeat iExists _. by iFrame "∗#%". }
  iModIntro. iDestruct (harris_node_combine_some with "c↦ c↪□ c.n↪rcu [c.n↪]") as "$"; [iLeft; by iFrame|].
  wp_pures. wp_apply (wp_resolve_proph with "pr") as  (?) "_". clear dependent pr pr_v.
  wp_pures. wp_bind (!_)%E.
  iInv "cInfo" as (lv) "(c↦ & node & G)".
  iDestruct (harris_node_destruct_agree with "c↪□ node") as (c_on' c_t) "(>% & c.n↪rcu & >c.n↪)"; subst lv.
  wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
  iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu c.n↪") as "$".
  wp_pures. iEval (case_bool_decide; [|naive_solver]).
  wp_pures.
  iApply ("IH" $! false with "[%] [%] G pr' [] [HΦ HΦ'] c↪□ c_n↪□ cInfo c_nInfo"); [done..| |].
  - case_decide; [naive_solver|done].
  - case_decide as EQN; [done|].
    iIntros "!>" (v) "[-> G]". iApply "HΦ'". iRight.
    repeat iExists _. iSplit; [done|]. iApply "HΦ". iFrame "∗#%".
Qed.

(* Note: Almost the same as the proof of harris_find_spec *)
Lemma hm_find_spec :
  harris_find_spec' listN rcuN rcu (hm_find rcu).
Proof using All.
  intros E k h γp_a γp_t γl i_h γr l d g γg ?.
  iIntros "#IRD G #l.d↦□ #h↪□ #IsH" (Φ) "AU".
  iLöb as "IH".
  wp_lam. wp_pure credit: "Lc". wp_pures.
  wp_apply (wp_new_proph with "[//]") as (pr_v_tag pr_tag) "pr_tag".
  wp_pures. wp_load. wp_pures. wp_bind (! _)%E.
  iInv "IsH" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
  iMod (lc_fupd_elim_later with "Lc Nodes") as "Nodes".
  iDestruct (Nodes_remove with "Nodes") as (h_on h_op) "[(hM & _ & h.n↪ & %HLh_n & %HLh_p) Nodes]"; [exact HLh|]; simpl in *.
  iMod (rcu.(guard_protect_managed) with "IRD hM G") as "(hM & G & #hInfo)"; [solve_ndisj|].
  iInv "hM" as (lv) "(h↦ & node & hM)".
  iDestruct (harris_node_destruct_agree with "h↪□ node") as (? h_t) "(>% & h.n↪rcu & >[[%n h.n↪']|[%n h.n↪']])"; subst lv.
  all: subst h_t; iDestruct (ghost_map_elem_agree with "h.n↪ h.n↪'") as %[= <-].
  wp_apply (wp_load_offset with "h↦") as "h↦"; [by simplify_list_eq|].
  assert (1 < length L) as [[[c_k c_b] [c i_c]] HLh_n']%lookup_lt_is_Some.
  { assert (0 < length L); [by apply lookup_lt_Some in HLh|].
    assert (1 ≠ length L); [|lia]. intros L_EQ. destruct HLt as [t HLt].
    rewrite L_EQ Nat.sub_diag in HLt. naive_solver.
  }
  assert (h_on = Some (c,i_c)) as ->; simpl. { get_third HLh_n'. naive_solver. }
  rewrite HLh_n.
  iDestruct (Nodes_rm_idx_remove with "Nodes") as (c_on c_op) "[(cM & #c↪□ & c.n↪ & %HLc_n & %HLc_p) Nodes]"; [exact HLh_n'|lia|simpl in *].
  iMod (rcu.(guard_protect_managed) with "IRD cM G") as "(cM & G & #cInfo)"; [solve_ndisj|].
  iDestruct (Nodes_rm_idx_combine with "Nodes cM [] [c.n↪]") as "Nodes"; [done..|].
  iDestruct (Nodes_combine with "Nodes [hM] [] [h.n↪']") as "Nodes"; [done..|].
  iModIntro. iDestruct (harris_node_combine_some with "h↦ h↪□ h.n↪rcu [h.n↪]") as "$"; [iLeft; by iFrame|].
  assert (-∞ᵢ < k)%inf_Z as LT_k; [done|].
  (* Check tag and key value. *)
  destruct (decide (prophecy_to_bool pr_v_tag ∨ (c_k < k)%inf_Z)) as [NotCommit|[Hpr_v'%Is_true_false GE]%Decidable.not_or].
  { (* Tagged or key value too small. Do not commit. *)
    iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    wp_pures.
    wp_apply (hm_find_inner_spec with "[$IsH $IRD AU $G $pr_tag]"); [solve_ndisj|exact LT_k|done|iFrame "#"|].
    { case_decide; done. }
    case_decide; [|done].
    iIntros (v) "[AU|HΦ]".
    { iDestruct "AU" as (->) "[G AU]". wp_pures. iApply ("IH" with "G AU"). }
    iDestruct "HΦ" as (??? ->) "HΦ".
    wp_pures. iApply "HΦ".
  }
  (* prophecy predicts that curr is not tagged. *)
  destruct c_b.
  { (* cannot be tagged *)
    iDestruct (get_persistent_Nodes with "Nodes") as (??) "#(_&c.n↪□&_)"; [exact HLh_n'|simpl in *].
    iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    wp_pures.
    wp_apply (hm_find_inner_wrong_proph with "pr_tag cInfo c.n↪□ G"); [done..|by simplify_map_eq].
  }

  (* Not tagged and key value is good. commit. *)
  iMod "AU" as (?) "[[Labs %HLabs] [_ Commit]]".
  iDestruct (ghost_var_agree with "Labs Linv") as %->.
  iMod ("Commit" $! (bool_decide (c_k = k)) i_h i_c 0 with "[$Labs]") as "HΦ".
  { iFrame "#%". iPureIntro.
    assert (L = [(-∞ᵢ,false,(h,i_h));(c_k,false,(c,i_c))] ++ (drop 2 L)) as ->.
    { rewrite -{1}(take_drop 1 L). rewrite (take_S_r _ _ (-∞ᵢ, false, (h,i_h))); [|done].
      simplify_list_eq. repeat f_equal.
      rewrite (drop_S _ (c_k, false, (c,i_c)) 1); done.
    }
    split_and!; [done..|]. case_bool_decide as NE'; [done|].
    destruct c_k as [|c_k|]; [naive_solver| |naive_solver].
    apply inf_Z.Z_lt_lt, Z.lt_nge => ?.
    apply GE, inf_Z.Z_lt_lt, Z.lt_nge => ?.
    apply NE'. f_equal. lia.
  }
  iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
  { repeat iExists _. by iFrame "∗#%". }
  wp_pures.
  wp_apply (hm_find_inner_spec Φ with "[$IRD $IsH $G $pr_tag]"); [solve_ndisj|exact LT_k|done|iFrame "#"|].
  { case_decide; naive_solver. }
  case_decide; [naive_solver|].
  iIntros (v) "[-> G]". wp_pures. iApply "HΦ".
  iModIntro. by iFrame "∗#%".
Qed.

End harris_michael_find.

Definition hm_code_impl (rcu : rcu_code) : code_harris_operations.harris_find_code := {|
  code_harris_operations.harris_find := hm_find rcu;
|}.

Program Definition hm_impl Σ listN rcuN (DISJN : listN ## rcuN) `{!heapGS Σ, !hlG Σ} (rcu : rcu_traversal_spec Σ rcuN) : hfind_spec Σ listN rcuN DISJN rcu := {|
  proof_harris_operations.harris_find_spec_code := hm_code_impl rcu.(rcu_spec_code);
|}.
Next Obligation. intros. apply hm_find_spec. done. Qed.
Next Obligation. intros. apply hm_helping_cas_spec. done. Qed.