From iris.base_logic.lib Require Import invariants ghost_var ghost_map.
From smr.program_logic Require Import atomic.
From smr.lang Require Import lang proofmode notation.
From smr Require Import sorted_list.

From smr Require Import helpers no_recl.code_harris_operations no_recl.code_harris_find.
From smr.no_recl Require Export proof_harris_operations.
From iris.prelude Require Import options.

Section harris_find.
Context `{!heapGS Σ, !hlG Σ}.
Context (listN : namespace).
Notation iProp := (iProp Σ).
Notation IsHList := (IsHList listN).
Notation harris_find_au := (harris_find_au listN).

Lemma harris_find_inner_wrong_proph E (prev curr : loc) cn (k : Z) (pr_tag : proph_id) pr_v_tag Φ (anchor : tagged_loc) :
  prophecy_to_bool pr_v_tag = false →
  proph pr_tag pr_v_tag -∗
  (curr +ₗ next) ↦□ #(cn &ₜ 1) -∗
  WP harris_find_inner #pr_tag #k #prev #curr #anchor @ E {{ v, Φ v}}.
Proof.
  iIntros (Hpr) "pr #c.n↦□".
  wp_lam. wp_pures.
  wp_apply (wp_new_proph with "[//]") as (??) "_"; wp_pures.
  wp_load. wp_pures.
  wp_apply (wp_resolve_proph with "pr") as  (pvs') "[%Heq _]".
  subst pr_v_tag. inversion Hpr.
Qed.

Fixpoint RetireChain anchor ret_curr (rL : list loc) : iProp :=
  match rL with
  | [] => False
  | [p] => ⌜p = anchor⌝ ∗ (p +ₗ next) ↦□ #(Some ret_curr &ₜ 1)
  | p::rL' => ∃ (anchor' : loc),
            ⌜p = anchor⌝ ∗ (p +ₗ next) ↦□ #(Some anchor' &ₜ 1) ∗
            RetireChain anchor' ret_curr rL'
  end.

Local Lemma RetireChain_in_list anchor curr (L : list (inf_Z * bool * loc)) rL idx_a idx γp_a :
  L.*2 !! idx_a = Some anchor →
  idx < idx_a →
  RetireChain anchor curr rL -∗
  Nodes_rm_idx idx L γp_a -∗
  ⌜∀r (idx : nat), rL !! idx = Some r → ∃ (r_k : inf_Z), L !! (idx_a + idx)%nat = Some (r_k, true, r)⌝.
Proof.
  iIntros (HLa LT) "RChain Nodes". iIntros (r idx_r Hr).
  destruct rL as [|rn rL]; try done.
  iInduction rL as [|rn' rL] "IH" forall (anchor rn idx_r Hr idx_a LT HLa).
  - iDestruct "RChain" as (->) "#an.n↦□".
    specialize HLa as HLa'.
    apply list_lookup_fmap_Some in HLa as [[[a_k []] ?] [HLa [= <-]]]; last first.
    { iDestruct (Nodes_rm_idx_remove with "Nodes") as (?) "[(_&_&an.n↦&_) _]"; [exact HLa|lia|].
      by iDestruct (mapsto_ne with "an.n↦ an.n↦□") as %?.
    }
    iDestruct (get_persistent_Nodes_rm_idx with "Nodes") as (an_n) "#(_&_& an.n↦ & %Han_n)"; [exact HLa|lia|].
    simpl. iDestruct (mapsto_agree with "an.n↦□ an.n↦") as %[= <-]; iClear "an.n↦".
    destruct idx_r; last first.
    { apply lookup_lt_Some in Hr. simpl in *. lia. }
    injection Hr as [= <-]. iPureIntro. rewrite Nat.add_0_r. eauto.
  - iDestruct "RChain" as (an') "(%EQ & #an.n↦□ & RChain)". subst rn. fold (RetireChain an' curr (rn' :: rL)).
    apply list_lookup_fmap_Some in HLa as [[[a_k []] ?] [HLa [= <-]]]; last first.
    { iDestruct (Nodes_rm_idx_remove with "Nodes") as (?) "[(_&_&an.n↦&_) _]"; [exact HLa|lia|].
      by iDestruct (mapsto_ne with "an.n↦ an.n↦□") as %?.
    }
    iDestruct (get_persistent_Nodes_rm_idx with "Nodes") as (?) "#(_&_& an.n↦ & %Han')"; [exact HLa|lia|].
    iDestruct (mapsto_agree with "an.n↦□ an.n↦") as %[= <-]; iClear "an.n↦".
    destruct idx_r as [|[|]]; last first.
    { replace (idx_a + S (S n)) with (idx_a + 1 + S n) by lia.
      iApply ("IH" with "[%] [%] [%] RChain Nodes"); [|lia|exact Han'].
      rewrite lookup_cons_ne_0 in Hr; [|lia]. rewrite -Hr. f_equal.
    }
    all: iClear "IH"; injection Hr as [= ->].
    + iAssert (∃ (an'_n : loc), ⌜an' = r⌝ ∗ (an' +ₗ next) ↦□ #(Some an'_n &ₜ 1))%I with "[RChain]" as (an'_n <-) "an'.n↦".
      { destruct rL; simpl.
        + iDestruct "RChain" as (->) "an'.n↦". iExists curr. by iFrame.
        + iDestruct "RChain" as (an'_n ->) "(an'.n↦ & RChain)". iExists an'_n. by iFrame.
      }
      apply list_lookup_fmap_Some in Han' as [[[an'_k []] ?] [Han' [= <-]]]; last first.
      { iDestruct (Nodes_rm_idx_remove with "Nodes") as (?) "[(_&_&an'.n↦'&_) _]"; [exact Han'|lia|].
        by iDestruct (mapsto_ne with "an'.n↦' an'.n↦") as %?.
      }
      iPureIntro. eauto.
    + iPureIntro. rewrite !Nat.add_0_r. eauto.
Qed.

Lemma RetireChain_curr anchor curr (L : list (inf_Z * bool * loc)) rL idx_a idx γp_a :
  L.*2 !! idx_a = Some anchor →
  idx < idx_a →
  RetireChain anchor curr rL -∗
  Nodes_rm_idx idx L γp_a -∗
  ⌜L.*2 !! (idx_a + length rL)%nat = Some curr⌝.
Proof.
  iIntros (HLa LT) "RChain Nodes".
  destruct rL as [|rn rL]; [done|].
  iInduction rL as [|rn' rL] "IH" forall (rn anchor idx_a LT HLa).
  { iDestruct (RetireChain_in_list with "RChain Nodes") as %ElemOfL; [exact HLa|lia|].
    simpl in *. iDestruct "RChain" as (<-) "rn.n↦".
    specialize (ElemOfL _ 0 ltac:(done)) as [a_k HLan].
    iDestruct (get_persistent_Nodes_rm_idx with "Nodes") as (?) "#(_&_& rn.n↦' & %Hrn_n)"; [exact HLan|lia|].
    iDestruct (mapsto_agree with "rn.n↦ rn.n↦'") as %[= <-]; iClear "rn.n↦'".
    iPureIntro. by rewrite -Hrn_n Nat.add_0_r.
  }
  iDestruct (RetireChain_in_list with "RChain Nodes") as %ElemOfL; [exact HLa|lia|].
  iDestruct "RChain" as (rn_n <-) "(rn.n↦ & RChain)". fold RetireChain.
  replace (idx_a + length (rn :: rn' :: rL)) with (idx_a + 1 + length (rn' :: rL)); last first.
  { simpl. lia. }
  iAssert (⌜rn' = rn_n⌝)%I as %<-.
  { destruct rL.
    - by iDestruct "RChain" as (->) "_".
    - by iDestruct "RChain" as (? ->) "_".
  }
  specialize (ElemOfL _ 1 ltac:(done)) as [rn'_k HLrn'].
  get_third HLrn'.
  iApply ("IH" with "[%] [%] RChain Nodes"); [lia|exact HLrn'].
Qed.

Local Lemma get_anchor_spec (o_anchor : option loc) (curr c_n : loc) E rL :
  {{{ match o_anchor with
      | None => ⌜rL = []⌝
      | Some anchor => RetireChain anchor curr rL
      end ∗ (curr +ₗ next) ↦□ #(Some c_n &ₜ 1)
  }}}
    get_anchor #(o_anchor &ₜ 0) #curr @ E
  {{{ (new_anchor : loc), RET #new_anchor; RetireChain new_anchor c_n (rL ++ [curr]) }}}.
Proof.
  iIntros (Φ) "[RChain #c.n↦□] HΦ".
  wp_lam. wp_pures. destruct o_anchor as [anchor|]; wp_pures; iApply "HΦ"; last first.
  { iDestruct "RChain" as %->. by iFrame "∗#". }
  iModIntro.
  destruct rL as [|rn rL]; [done|].
  iInduction rL as [|rn' rL] "IH" forall (rn anchor) "RChain".
  + iDestruct "RChain" as (->) "#an'.n↦".
    iExists curr. by iFrame "#".
  + iDestruct "RChain" as (an' ->) "(#an.n↦□ & RChain)". fold RetireChain.
    iExists an'. iFrame "#". iSplit; [done|]. iApply "IH". done.
Qed.

Lemma harris_helping_cas_spec (committing : bool) rL Φ pr pr_v h γp_a γl (prev anchor curr : loc) p_k c_k (k : Z) E  :
  ↑listN ⊆ E →
  (p_k < k)%inf_Z →
  {{{ inv listN (HListInternalInv h γp_a γl) ∗
      prev ↪[ γp_a ]□ p_k ∗
      curr ↪[ γp_a ]□ c_k ∗
      RetireChain anchor curr rL ∗
      if committing then proph pr pr_v ∗ harris_find_au E γp_a γl k Φ else True
  }}}
    CAS #(prev +ₗ 0%nat) #anchor #curr @ E
  {{{ (b : bool), RET #b;
      if (negb committing) then
        True
      else
        proph pr pr_v ∗
        if b then
          (if decide (prophecy_to_bool pr_v ∨ (c_k < k)%inf_Z) then
            (* CAS success but curr is bad. *)
            harris_find_au E γp_a γl k Φ
          else
            (* CAS success and commit. *)
            (* Impossible case, cause contradiction. *)
            (∃ (c_n : option loc), (curr +ₗ 0%nat) ↦□ #(c_n &ₜ 1)) ∨
            (True -∗ Φ (#(bool_decide (c_k = k)), #prev, #curr)%V))
        else
          harris_find_au E γp_a γl k Φ
  }}}.
Proof.
  iIntros (? p_k_LT_k Φ') "(#IsHarris & #p↪□ & #c↪□ & RChain & prAU) HΦ'".
  wp_bind (CmpXchg _ _ _)%E.
  iInv "IsHarris" as (p_all L) "(>Linv & >●p_all & >PTRS & Nodes & >(%HL & %HLh & %HLt))".
  iDestruct (ghost_map_lookup with "●p_all p↪□") as %Hptrs_prev.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[_ [p.n|%HLp]]"; [exact Hptrs_prev| |].
  { (* prev tagged, cas must fail. *)
    iDestruct "p.n" as (p_n p_n_k) "[p.n↦□ _]".
    wp_cmpxchg_fail.
    iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
    { iNext. repeat iExists _. by iFrame "∗#%". }
    wp_pures. iApply "HΦ'". iFrame. destruct committing; by iFrame.
  }
  apply elem_of_list_lookup in HLp as [idx_L_p HLp].
  iDestruct (Nodes_remove with "Nodes") as (p_n) "[(#p.k↦□ & _ & p.n↦ & >%HLp_next) Nodes]"; [exact HLp|].
  destruct (decide (p_n = Some anchor)) as [->|NE]; last first.
  { (* prev's next changed from anchor, cas must fail. *)
    wp_cmpxchg_fail.
    iDestruct (Nodes_combine with "Nodes [] [] [p.n↦]") as "Nodes"; [done..|].
    iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
    { iNext. repeat iExists _. by iFrame "∗#%". }
    wp_pures. iApply "HΦ'". destruct committing; by iFrame.
  }
  wp_cmpxchg_suc; [done|].
  (* Get info about curr *)
  iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_curr.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[c.k↦□ c]"; [exact Hptrs_curr|].
  iDestruct (RetireChain_in_list with "RChain Nodes") as %ElemOfL; [exact HLp_next|lia|].
  iDestruct (RetireChain_curr with "RChain Nodes") as %HL_curr; [exact HLp_next|lia|].
  set (L' := take (idx_L_p + 1) L ++ drop (idx_L_p + 1 + length rL) L).
  assert (idx_L_p + 1 ≤ length L).
  { apply lookup_lt_Some in HLp_next. rewrite fmap_length in HLp_next. lia. }
  assert (length (take (idx_L_p + 1) L) = idx_L_p + 1).
  { rewrite take_length_le; done. }
  assert (get_abs_state L = get_abs_state L') as ->.
  { rewrite -(take_drop (idx_L_p + 1 + length rL) L). subst L'. rewrite !get_abs_state_app. f_equal.
    rewrite -{1}(take_drop (idx_L_p + 1) L) take_add_app; [|done].
    rewrite get_abs_state_app -{2}(app_nil_r (get_abs_state (take (idx_L_p + 1) L))). f_equal.
    apply length_zero_iff_nil, dec_stable.
    intros [n_k ElemOf%elem_of_list_lookup_2]%Nat.neq_0_lt_0%lookup_lt_is_Some.
    unfold get_abs_state in ElemOf.
    do 2 apply elem_of_list_fmap_2 in ElemOf as [[? ?] [[= <-] ElemOf]].
    apply elem_of_list_filter in ElemOf as [Hn [i_n_L [HL_n Hi_n_L]]%elem_of_take].
    rewrite lookup_drop in HL_n.
    have [n HrLn] : is_Some (rL !! i_n_L).
    { by apply lookup_lt_is_Some. }
    specialize (ElemOfL n i_n_L HrLn) as [n_k' HL_n'].
    rewrite HL_n in HL_n'. injection HL_n' as [= -> -> ->]. naive_solver.
  }
  (* Close invariant early *)
  iAssert (ghost_var γl (1 / 2) (get_abs_state L') ∗ Nodes_rm_idx idx_L_p L γp_a
           -∗ ▷ HListInternalInv h γp_a γl)%I with "[●p_all PTRS p.n↦]" as "INV".
  { iIntros "[Linv Nodes] !>". repeat iExists _. iFrame "Linv ∗#%".
    unfold AllPtrs, Nodes, Nodes_rm_idx. iSplitL "PTRS"; [|iSplit].
    - iApply (big_sepM_mono with "PTRS"). iIntros (n n_k Hptrs_n) "[$ [$|%HLn]]".
      iRight. iPureIntro. apply elem_of_app.
      rewrite -(take_drop (idx_L_p + 1 + length rL) L) in HLn.
      apply elem_of_app in HLn as [HLn|HLn]; [left|by right].
      rewrite -(take_drop (idx_L_p + 1) L) take_add_app in HLn; [|done].
      apply elem_of_app in HLn as [HLn|[i_n_L [HL_n Hi_n_L]]%elem_of_take]; [done|exfalso].
      rewrite lookup_drop in HL_n.
      apply lookup_lt_is_Some in Hi_n_L as [n' HrLn].
      specialize (ElemOfL n' i_n_L HrLn) as [n_k' HL_n'].
      naive_solver.
    - rewrite (big_sepL_take_drop _ L (idx_L_p + 1 + length rL)).
      iDestruct "Nodes" as "[NodesTake NodesDrop]".
      iEval (rewrite -{2}(take_drop (idx_L_p + 1) L) take_add_app; [|done]) in "NodesTake".
      iDestruct "NodesTake" as "[NodesTake _]". subst L'.
      rewrite Nat.add_1_r (take_S_r _ _ (p_k,false,prev)); [|exact HLp].
      iDestruct "NodesTake" as "[NodesTake _]".
      rewrite !big_sepL_app big_sepL_singleton /=.
      iSplitR "NodesDrop"; [iSplitR "p.n↦"|].
      + iApply (big_sepL_mono with "NodesTake"). iIntros (idx_n [[n_k b_n] l_n] HLn) "LN".
        assert (idx_n < idx_L_p) as LT.
        { apply lookup_lt_Some in HLn as LT_take. rewrite take_length_le in LT_take; [lia|].
          apply lookup_lt_Some in HLp_next. rewrite fmap_length in HLp_next. lia.
        }
        case_decide; [lia|].
        unfold ListNode.
        iDestruct "LN" as (on) "($ & $ & l_n.n↦ & %HLl_n)".
        iExists on. iFrame. iPureIntro. rewrite !fmap_app lookup_app_l; last first.
        { rewrite /= app_length fmap_length take_length_le /=; lia. }
        rewrite -fmap_app -take_S_r; [|done]. rewrite fmap_take lookup_take; [done|lia].
      + unfold ListNode. iExists (Some curr). iFrame "∗#". iPureIntro.
        rewrite fmap_app lookup_app_r fmap_app app_length /= fmap_length; [|lia].
        rewrite Nat.add_0_r Nat.sub_diag fmap_drop lookup_drop Nat.add_0_r -HL_curr.
        f_equal. lia.
      + iApply (big_sepL_mono with "NodesDrop"). iIntros (idx_n [[n_k b_n] l_n] HLn) "LN".
        case_decide; [lia|].
        iDestruct "LN" as (on) "($ & $ & l_n.n↦ & %HLl_n)".
        iExists on. iFrame. iPureIntro. rewrite !fmap_app lookup_app_r; last first.
        all: rewrite /= app_length app_length /= fmap_length take_length_le /=; try lia.
        rewrite fmap_drop lookup_drop -HLl_n. f_equal. lia.
    - iPureIntro. subst L'. split_and!.
      + rewrite !fmap_app !fmap_take !fmap_drop. apply take_drop_inf_Z_sorted; [lia|done].
      + rewrite lookup_app_l; [|lia]. rewrite lookup_take; [done|lia].
      + destruct HLt as [t HLt]. exists t.
        rewrite lookup_app_r; last first.
        all: rewrite /= !app_length /= !take_length_le /=; try lia.
        { rewrite drop_length. apply lookup_lt_Some in HL_curr. rewrite fmap_length in HL_curr. lia. }
        rewrite lookup_drop -HLt. f_equal. rewrite drop_length.
        apply lookup_lt_Some in HL_curr. rewrite fmap_length in HL_curr. lia.
  }
  (* Check if we need to commit. *)
  destruct committing; simpl in *; last first.
  { iModIntro. iSplitL "Linv Nodes INV"; [iApply "INV"; iFrame|].
    wp_pures. iApply "HΦ'". by iFrame.
  }
  iDestruct "prAU" as "[pr AU]".
  (* Check if this is commit point. *)
  destruct (decide (prophecy_to_bool pr_v ∨ (c_k < k)%inf_Z)) as [NotCommit|[Hpr_v%Is_true_false GE]%Decidable.not_or].
  { (* Tagged or key too small *)
    iClear "c". iModIntro. iSplitL "Linv Nodes INV"; [iApply "INV"; iFrame|].
    clear dependent p_all L.
    wp_pures. iApply "HΦ'". by iFrame.
  }
  (* Not tagged and key large. Commit. *)
  (* Assert that we are not tagged *)
  iDestruct "c" as "[c.n|%HLc]".
  { (* Tagged, impossible. *)
    iDestruct "c.n" as (c_n c_n_k) "#[c.n↦□ _]".
    iModIntro. iSplitL "Linv Nodes INV"; [iApply "INV"; iFrame|].
    wp_pures. iApply "HΦ'". iModIntro. iFrame. iLeft. iExists _. iFrame "#".
  }
  apply elem_of_list_lookup in HLc as [idx_c HLc].
  apply list_lookup_fmap_Some in HL_curr as [[[c_k' b] ?] [HL_curr [= <-]]].
  iDestruct (get_persistent_Nodes_rm_idx with "Nodes") as (?) "#(c.k↦□' & _ & _ & _)"; [exact HL_curr|lia|].
  iDestruct (mapsto_agree with "c.k↦□' c.k↦□") as %[= ->]; iClear "c.k↦□".
  assert (idx_c = idx_L_p + 1 + length rL) as ->.
  { get_first HLc. get_first HL_curr. assert (NoDup L.*1.*1) as NoDup; [by apply sorted_inf_Z_nodup|].
    rewrite NoDup_alt in NoDup. apply (NoDup _ _ c_k); auto.
  }
  iMod "AU" as (?) "[[Labs %HLabs] [_ Commit]]".
  iDestruct (ghost_var_agree with "Labs Linv") as %->.
  set (idx' := length (get_abs_state (take idx_L_p L))).
  iMod ("Commit" $! (bool_decide (c_k = k)) prev curr _ _ idx' with "[$Labs]") as "HΦ".
  { iFrame "∗#%". iPureIntro. split_and!; auto; last first.
    { case_bool_decide as EQN; [done|]. destruct c_k as [|c_k|]; [naive_solver| |naive_solver].
      simpl in *. apply inf_Z.Z_lt_lt,Z.lt_nge => ?.
      apply GE,inf_Z.Z_lt_lt,Z.lt_nge => ?.
      apply EQN. f_equal. lia.
    }
    all: rewrite !get_abs_state_app /= Nat.add_1_r (take_S_r _ _ (p_k,false,prev)); simplify_list_eq; auto.
    - rewrite lookup_app_r get_abs_state_snoc app_length /=; [|lia]. fold idx'.
      replace (S idx' - (idx' + 1)) with 0 by lia.
      rewrite (drop_S L (c_k, false, curr)); last first.
      { rewrite -HL_curr. f_equal. lia. }
      by rewrite get_abs_state_cons.
    - rewrite lookup_app_l get_abs_state_snoc; last first.
      { rewrite app_length /=. lia. }
      subst idx'. by rewrite snoc_lookup.
  }
  iModIntro. iSplitL "Linv Nodes INV"; [iApply "INV"; iFrame|].
  wp_pures. iApply "HΦ'". iModIntro. iFrame.
Qed.

Local Lemma harris_find_inner_spec  (* Auxillary, non-unifiable *) Φ (k : Z) E
                                    (* harris inv *) γp_a γl h
                                    (* retire chain stuff*) (o_anchor : option loc) rL
                                    (* prophecy *) (tagged : bool) (pr_tag : proph_id) (pr_v_tag : list (val * val))
                                    (* prev, curr *) (prev curr : loc) (p_k c_k : inf_Z) :
  (p_k < k)%inf_Z →
  prophecy_to_bool pr_v_tag = tagged →
  ↑listN ⊆ E →
  {{{ inv listN (HListInternalInv h γp_a γl) ∗
      prev ↪[γp_a]□ p_k ∗ curr ↪[γp_a]□ c_k ∗
      proph pr_tag pr_v_tag ∗
      match o_anchor with
      | None => ⌜rL = []⌝
      | Some anchor => RetireChain anchor curr rL
      end ∗
      (* Check if we will be going into another iteration *)
      if decide (tagged ∨ (c_k < k)%inf_Z) then
        harris_find_au E γp_a γl k Φ
      else
        (* We are going to return. Will we do a CAS? *)
        match o_anchor with
        | None => True
        | Some _ => harris_find_au E γp_a γl k Φ
        end
  }}}
    harris_find_inner #pr_tag #k #prev #curr #(o_anchor &ₜ 0) @ E
  {{{ v, RET v;
    if decide (tagged ∨ (c_k < k)%inf_Z) then
      (* We went into another iteration. *)
      ⌜v = NONEV⌝ ∗ harris_find_au E γp_a γl k Φ ∨
      (∃ (ret_b : bool) (ret_prev ret_curr : loc),
        ⌜v = SOMEV (#ret_b, #ret_prev, #ret_curr)⌝ ∗
        (True -∗ Φ (#ret_b, #ret_prev, #ret_curr)%V))
    else
      (* We didn't go into another iteration. *)
      match o_anchor with
      | None =>
        (* Didn't do cas. *)
        ⌜v = SOMEV (#(bool_decide (c_k = k)), #prev, #curr)⌝
      | Some _ =>
        (* Failed cas *)
        ⌜v = NONEV⌝ ∗ harris_find_au E γp_a γl k Φ ∨
        (* cas success *)
        ⌜v = SOMEV (#(bool_decide (c_k = k)), #prev, #curr)⌝ ∗
        (True -∗ Φ (#(bool_decide (c_k = k)), #prev, #curr)%V)
      end
  }}}.
Proof.
  intros p_k_LT_k Hpr_tag ?.
  iIntros (Φ') "(#IsHarris & #p↪□ & #c↪□ & pr_tag & RChain & AU) HΦ'".
  iLöb as "IH" forall (tagged prev curr p_k c_k p_k_LT_k pr_tag pr_v_tag o_anchor Hpr_tag rL) "p↪□ c↪□".
  wp_lam. wp_pures.
  wp_apply (wp_new_proph with "[//]") as (pr_v_tag' pr_tag') "pr_tag'".
  wp_pures. wp_bind (! _)%E.
  iInv "IsHarris" as (p_all L) "(>Linv & >●p_all & >PTRS & Nodes & >(%HL & %HLh & %HLt))".
  iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_curr.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[c.k↦□ c_next]"; [exact Hptrs_curr|].
  (* Check prophecy value for tag. *)
  destruct tagged; simpl.
  { (* Tagged, so going into next iteration. *)
    (* Assert that we must be tagged. *)
    iDestruct "c_next" as "[c_next|%HLcurr]"; last first.
    { apply elem_of_list_lookup in HLcurr as [idx HLcurr].
      iDestruct (Nodes_remove with "Nodes") as (c_next) "[(_ & _ & c.n↦ & >%HLc_next) Nodes]"; [exact HLcurr|].
      wp_load. iDestruct (Nodes_combine with "Nodes [] [] [c.n↦]") as "Nodes"; [done..|].
      iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
      { repeat iExists _. by iFrame "∗#%". }
      wp_pures.
      wp_apply (wp_resolve_proph with "pr_tag") as (?) "[%Heq _]".
      rewrite Heq in Hpr_tag. inversion Hpr_tag.
    }
    iDestruct "c_next" as (c_n c_n_k) "[c.n↦□ c_n↪□]".
    wp_load.
    (* Get information of next pointer. *)
    iDestruct (ghost_map_lookup with "●p_all c_n↪□") as %Hptrs_c_n.
    iDestruct (get_persistent_AllPtrs with "PTRS") as "#[c_n.k↦□ c_n]"; [exact Hptrs_c_n|].
    iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    wp_pures.
    wp_apply (wp_resolve_proph with "pr_tag") as  (?) "_".
    wp_pures.
    wp_apply (get_anchor_spec with "[$RChain $c.n↦□]") as  (new_a) "RChain".
    wp_pures. iApply ("IH" with "[%] [%] pr_tag' [RChain] [AU] [HΦ'] p↪□ c_n↪□"); [done..| |].
    all: case_decide; try done.
    iIntros "!>" (v) "[[% HΦ]|[% HΦ]]"; iApply "HΦ'"; subst v.
    - iLeft. by iFrame "∗#".
    - iRight. repeat iExists _. by iFrame "∗#".
  }
  (* assert that we must not be tagged. *)
  iDestruct "c_next" as "[c_next|%HLcurr]".
  { iDestruct "c_next" as (c_next ?) "#[c.n↦□ _]".
    wp_load.
    iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    wp_pures.
    wp_apply (wp_resolve_proph with "pr_tag") as (pvs') "[%Heq _]".
    rewrite Heq in Hpr_tag. inversion Hpr_tag.
  }
  apply elem_of_list_lookup in HLcurr as [idx HLcurr].
  iDestruct (Nodes_remove with "Nodes") as (c_next) "[(_ & _ & c.n↦ & >%HLc_next) Nodes]"; [exact HLcurr|].
  wp_load.
  iDestruct (Nodes_combine with "Nodes [] [] [c.n↦]") as "Nodes"; [done..|].
  (* Check to see if we are going into next iteration. *)
  destruct (decide (c_k < k)%inf_Z) as [c_k_LT|c_k_GE].
  { case_decide; [|naive_solver].
    (* Will go into next iteration with adjacent pointers. Check prophecy value & check c_n_k to commit. *)
    (* Get information about c_next *)
    destruct (next_not_tail_is_Some idx L c_k false curr c_next) as [c_next' [= ->]]; [naive_solver..|].
    rename c_next' into c_next.
    apply list_lookup_fmap_Some in HLc_next as [[[cn_k b] ?] [HLc_next [= <-]]].
    iDestruct (get_persistent_Nodes with "Nodes") as (on) "#(c_next.k↦□ & c_next↪□ & #c_next.n↦□ & %HLc_next_next)"; [exact HLc_next|].
    destruct (decide (prophecy_to_bool pr_v_tag' ∨ (cn_k < k)%inf_Z)) as [NotCommit|[Hpr_v'%Is_true_false GE]%Decidable.not_or].
    { (* Tagged or key too small. Do not commit. *)
      iModIntro. iSplitL "●p_all PTRS Nodes Linv".
      { repeat iExists _. by iFrame "∗#%". }
      wp_pures.
      wp_apply (wp_resolve_proph with "pr_tag") as (pvs') "[_ _]".
      wp_pures. wp_load. wp_pures.
      iEval (case_bool_decide; [|naive_solver]).
      wp_pures.
      iApply ("IH" with "[%] [%] pr_tag' [RChain] [AU] [HΦ'] c↪□ c_next↪□"); [done..| |].
      all: repeat case_decide; naive_solver.
    }
    (* Not tagged and key value good. Commit. *)
    (* curr must not be physically not tagged *)
    destruct b.
    { iModIntro. iSplitL "●p_all PTRS Nodes Linv".
    { repeat iExists _. by iFrame "∗#%". }
      wp_pures.
      wp_apply (wp_resolve_proph with "pr_tag") as  (?) "_".
      wp_pures. wp_load. wp_pures.
      iEval (case_bool_decide; [|naive_solver]).
      wp_pures.
      by iApply (harris_find_inner_wrong_proph with "pr_tag' c_next.n↦□").
    }
    iMod "AU" as (?) "[[Labs %HLabs] [_ Commit]]".
    iDestruct (ghost_var_agree with "Labs Linv") as %[= ->].
    assert (L = take idx L ++ [(c_k, false, curr)] ++ [(cn_k, false, c_next)] ++ drop (S (S idx)) L) as EQ.
    { rewrite -{1}(take_drop idx L). f_equal. simplify_list_eq.
      rewrite -drop_S; [|by rewrite -Nat.add_1_r].
      rewrite -drop_S; done.
    }
    set (idx' := length (get_abs_state (take idx L))).
    iMod ("Commit" $! (bool_decide (cn_k = k)) curr c_next _ _ idx' with "[$Labs]") as "HΦ".
    { iFrame "∗#%". iPureIntro. split_and!; auto; last first.
      { case_bool_decide as EQN; [done|]. destruct cn_k as [|cn_k|]; [naive_solver| |naive_solver].
        simpl in *. apply inf_Z.Z_lt_lt,Z.lt_nge => ?.
        apply GE,inf_Z.Z_lt_lt,Z.lt_nge => ?.
        apply EQN. f_equal. lia.
      }
      all: rewrite EQ !get_abs_state_app /=; simplify_list_eq; rewrite lookup_app_r; [|lia].
      all: fold idx'.
      - by replace (S idx' - idx') with 1 by lia.
      - by rewrite Nat.sub_diag.
    }
    iModIntro.
    iSplitL "●p_all PTRS Nodes Linv".
    { repeat iExists _. by iFrame "∗#%". }
    wp_pures.
    wp_apply (wp_resolve_proph with "pr_tag") as  (?) "_".
    wp_pures. wp_load. wp_pures.
    iEval (case_bool_decide; [|naive_solver]).
    wp_pures.
    iApply ("IH" $! false with "[%] [%] pr_tag' [] [] [HΦ HΦ'] c↪□ c_next↪□"); [done|done|done|..].
    - case_decide; [naive_solver|done].
    - case_decide as EQN; [done|].
      iIntros "!>" (? ->). iApply "HΦ'". iRight.
      repeat iExists _. iSplit; done.
  }
  (* Curr is target node. Finish find procedure. *)
  iClear "IH". case_decide; [naive_solver|].
  iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
  { repeat iExists _. by iFrame "∗#%". }
  clear dependent p_all L. wp_pures.
  wp_apply (wp_resolve_proph with "pr_tag") as  (?) "_".
  wp_pures. wp_load. wp_pures.
  iEval (case_bool_decide; [naive_solver|]).
  wp_pures.
  (* Check if we will preform a CAS *)
  destruct o_anchor as [anchor|]; last first.
  { wp_pures. by iApply "HΦ'". }
  (* We will preform a CAS *)
  wp_pures.
  wp_apply (wp_new_proph with "[//]") as (pr_v_cas pr_cas) "pr_cas".
  wp_pures.
  wp_apply (harris_helping_cas_spec true rL with "[$pr_cas $AU $RChain]") as ([]) "[pr_cas AU]"; [done|exact p_k_LT_k|by iFrame "#"|..];

  last first; wp_pures.
  { iApply "HΦ'". iLeft. by iFrame "AU". }

  (* Check if tag check on curr will succeed. *)
  destruct (prophecy_to_bool pr_v_cas) eqn:Hpr_v_cas.
  { (* Tagged, do not commit. *)
    case_decide; [|naive_solver].
    wp_pures. wp_bind (!_)%E.
    iInv "IsHarris" as (p_all L) "(>Linv & >●p_all & >PTRS & Nodes & >(%HL & %HLh & %HLt))".
    (* Get information of next pointer. *)
    iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_c.
    iDestruct (get_persistent_AllPtrs with "PTRS") as "#[_ [#c.n|%HLc]]"; [exact Hptrs_c| |]; last first.
    { (* Not tagged, impossible. *)
      apply elem_of_list_lookup in HLc as [idx_c HLc].
      iDestruct (Nodes_remove with "Nodes") as (c_n) "[(_ & _ & c.n↦ & >%HLc_n) Nodes]"; [exact HLc|].
      wp_load.
      iDestruct (Nodes_combine with "Nodes [] [] [c.n↦]") as "Nodes"; [done..|].
      iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
      { repeat iExists _. by iFrame "∗#%". }
      wp_pures.
      wp_apply (wp_resolve_proph with "pr_cas") as (?) "[%Heq _]".
      subst pr_v_cas. inversion Hpr_v_cas.
    }
    iDestruct "c.n" as (c_n c_n_k) "#[c.n↦ _]".
    wp_load.
    iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    wp_pures.
    wp_apply (wp_resolve_proph with "pr_cas") as (?) "_".
    wp_pures. iApply "HΦ'". iModIntro. iLeft. by iFrame "AU".
  }
  case_decide; [naive_solver|].
  (* Assert that we are not tagged *)
  iDestruct "AU" as "[[% c.n↦□]|HΦ]".
  { (* Tagged, impossible. *)
    wp_load. wp_pures.
    wp_apply (wp_resolve_proph with "pr_cas") as (?) "[%Heq _]".
    subst pr_v_cas. inversion Hpr_v_cas.
  }
  wp_bind (!_)%E.
  iInv "IsHarris" as (p_all L) "(>Linv & >●p_all & >PTRS & Nodes & >(%HL & %HLh & %HLt))".
  (* Get information of next pointer. *)
  iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_c.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[_ [#c.n|%HLc]]"; [exact Hptrs_c| |].
  { (* Tagged, impossible. *)
    iDestruct "c.n" as (c_n c_n_k) "#[c.n↦ _]".
    wp_load.
    iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    wp_pures.
    wp_apply (wp_resolve_proph with "pr_cas") as (?) "[%Heq _]".
    subst pr_v_cas. inversion Hpr_v_cas.
  }
  (* Not tagged. *)
  apply elem_of_list_lookup in HLc as [idx_c HLc].
  iDestruct (Nodes_remove with "Nodes") as (c_n) "[(_ & _ & c.n↦ & >%HLc_n) Nodes]"; [exact HLc|].
  wp_load.
  iDestruct (Nodes_combine with "Nodes [] [] [c.n↦]") as "Nodes"; [done..|].
  iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
  { repeat iExists _. by iFrame "∗#%". }
  wp_pures.
  wp_apply (wp_resolve_proph with "pr_cas") as (?) "_".
  wp_pures. iApply "HΦ'". iModIntro. iRight. iSplit; done.
Qed.

Lemma harris_find_spec :
  harris_find_spec' listN harris_find.
Proof.
  intros E k h γp_a γl l ?.
  iIntros "#l.h↦ #h↪□ #IsHarris" (Φ) "AU".
  iLöb as "IH".
  wp_lam. wp_pures.
  wp_apply (wp_new_proph with "[//]") as (pr_v_tag pr_tag) "pr_tag".
  wp_pures. wp_bind (! _)%E.
  iInv "IsHarris" as (p_all L) "(>Linv & >●p_all & PTRS & Nodes & >(%HL & %HLh & %HLt))".
  wp_load.
  iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
  { repeat iExists _. by iFrame "∗#". }
  clear dependent p_all L. wp_pures. wp_bind (! _)%E.
  iInv "IsHarris" as (ptrs L) "(>Linv & >●p_all & PTRS & Nodes & >(%HL & %HLh & %HLt))".
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
  (* Check tag and key value. *)
  destruct (decide (prophecy_to_bool pr_v_tag ∨ (c_k < k)%inf_Z)) as [NotCommit|[Hpr_v'%Is_true_false GE]%Decidable.not_or].
  { (* Tagged or key value too small. Do not commit. *)
    iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    wp_pures.
    wp_apply (harris_find_inner_spec with "[$IsHarris AU $pr_tag]"); [exact LT_k|done|done|iFrame "∗#%"|].
    { iSplit; [done|]. case_decide; done. }
    case_decide; [|done].
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
    wp_pures.
    by wp_apply (harris_find_inner_wrong_proph with "pr_tag c.n↦□").
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
    destruct c_k as [|c_k|]; try naive_solver.
    apply inf_Z.Z_lt_lt, Z.lt_nge => ?.
    apply GE, inf_Z.Z_lt_lt, Z.lt_nge => ?.
    apply NE. f_equal. lia.
  }
  iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
  { repeat iExists _. by iFrame "∗#%". }
  wp_pures.
  wp_apply (harris_find_inner_spec (λ _, True)%I with "[$pr_tag]"); [exact LT_k|done|done|iFrame "∗#%"|].
  { case_decide; naive_solver. }
  case_decide; [naive_solver|].
  iIntros (v ->). wp_pures. by iApply "HΦ".
Qed.

End harris_find.

Definition harris_code_impl : code_harris_operations.harris_find_code := {|
  code_harris_operations.harris_find := harris_find;
|}.

Program Definition harris_impl Σ listN `{!heapGS Σ, !hlG Σ} : hfind_spec Σ listN  := {|
  proof_harris_operations.harris_find_spec_code := harris_code_impl;
|}.
Next Obligation. intros. apply harris_find_spec. Qed.
Next Obligation.
  intros. intros ????????????????.
  iIntros (Φ') "(#IsHarris & #p↪□ & #c↪□ & #an.n↦□ & AU) HΦ".
  wp_apply (harris_helping_cas_spec _ committing [anchor] Φ pr with "[$AU]"); [| |simpl;iFrame "#"|]; done.
Qed.
