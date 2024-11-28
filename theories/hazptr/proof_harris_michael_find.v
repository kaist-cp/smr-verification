From iris.base_logic.lib Require Import invariants ghost_var ghost_map.
From smr.program_logic Require Import atomic.
From smr.lang Require Import lang proofmode notation.
From smr Require Import sorted_list.

From smr Require Import helpers hazptr.spec_hazptr hazptr.code_harris_operations hazptr.code_harris_michael_find.
From smr.hazptr Require Export proof_harris_operations.
From iris.prelude Require Import options.

Section harris_michael_find.
Context `{!heapGS Σ, !hlG Σ}.
Context (listN hazptrN : namespace) (DISJN : listN ## hazptrN).

Variable (hazptr : hazard_pointer_spec Σ hazptrN).

Notation iProp := (iProp Σ).
Notation IsHList := (IsHList listN hazptrN hazptr).
Notation HListInternalInv := (HListInternalInv hazptrN hazptr).
Notation Nodes := (Nodes hazptrN hazptr).
Notation Nodes_rm_idx := (Nodes_rm_idx hazptrN hazptr).
Notation Nodes_rm_idx_idx := (Nodes_rm_idx_idx hazptrN hazptr).
Notation harris_helping_cas_spec := (harris_helping_cas_spec listN hazptrN DISJN hazptr).

Local Lemma hm_find_inner_spec d (prev curr : blk) E γp_a γp_t γl γh γz
                              (h : blk) (k : Z) (p_k : inf_Z)
                              (prev_sh curr_sh : loc) γ_prev c_st :
  (p_k < k)%inf_Z →
  (↑listN ∪ ↑hazptrN) ⊆ E →
  hazptr.(IsHazardDomain) γz d -∗
  hazptr.(Shield) γz prev_sh (Validated prev γ_prev (node γp_a γp_t) 2) -∗
  hazptr.(Shield) γz curr_sh c_st -∗
  γ_prev ↪[γp_a]□ (p_k,prev) -∗
  inv listN (HListInternalInv h γp_a γp_t γl γh γz) -∗
  <<{ ∀∀ (L : list inf_Z), HList γl L }>>
    (hm_find_inner hazptr) #d #k #prev #curr #prev_sh #curr_sh @ @ E, (↑listN ∪ (↑ptrsN hazptrN)), ↑mgmtN hazptrN
  <<{ ∃∃ (b : bool) (v : val) (ret_b : bool) (ret_p ret_c : blk) (ret_p_k ret_c_k : inf_Z) (idx : nat) (γ_ret_p γ_ret_c : gname) (ret_p_sh ret_c_sh : loc),
      ⌜v = if (b : bool) then SOMEV (#ret_b, #ret_p, #ret_c) else NONEV⌝ ∗
      HList γl L ∗
      (if (b : bool) then
        γ_ret_p ↪[γp_a]□ (ret_p_k, ret_p) ∗ γ_ret_c ↪[γp_a]□ (ret_c_k, ret_c) ∗
        ⌜L !! idx = Some ret_p_k ∧
         L !! S idx = Some ret_c_k ∧
         (ret_p_k < k)%inf_Z ∧
         (if ret_b then ret_c_k = k else (k < ret_c_k)%inf_Z)⌝
      else
        True%I
      ) |
      RET (#ret_p_sh, #ret_c_sh, v);
      ∃ ret_p_st ret_c_st,
      ⌜if (b : bool) then
        ret_p_st = (Validated ret_p γ_ret_p (node γp_a γp_t) nodeSize) ∧
        ret_c_st = (Validated ret_c γ_ret_c (node γp_a γp_t) nodeSize)
       else
        True⌝ ∗
      hazptr.(Shield) γz ret_p_sh ret_p_st ∗ hazptr.(Shield) γz ret_c_sh ret_c_st
  }>>.
Proof using DISJN.
  intros p_k_LT_k ?.
  iIntros "#IHD pS cS #p↪□ #IsHarris" (Φ) "AU".
  iLöb as "IH" forall (prev curr p_k p_k_LT_k prev_sh curr_sh γ_prev c_st) "p↪□".
  wp_lam. wp_pure credit: "Lc". wp_pure credit: "Lc'". wp_pure credit: "Lc''". wp_pures.
  wp_apply (hazptr.(shield_set_spec) (Some _) with "IHD cS") as "cS"; [solve_ndisj|]. wp_seq.
  wp_apply (wp_new_proph with "[//]") as (pr_v pr) "pr". wp_pures.
  wp_bind (!_)%E.
  (* Check status of p to see if we will fail. *)
  iInv "pS" as (?) "(_ & p↦ & >node & pS)".
  iDestruct (harris_node_destruct_agree with "node [//]") as (p_on p_t ->) "[% [[% p.n↪]|[% #p.n↪□]]]"; subst p_t; last first.
  all: wp_apply (wp_load_offset with "p↦") as "p↦"; [by simplify_list_eq|].
  { (* prev tagged, fail and return. *)
    iModIntro. iDestruct (harris_node_combine_on with "p↦ p↪□ [% //] [$p.n↪□]" ) as "$"; [by iRight|].
    wp_pures.
    iMod "AU" as (?) "[Labs [_ Commit]]".
    iMod ("Commit" $! false _ false prev curr p_k p_k 0 γ_prev γ_prev with "[$Labs]") as "HΦ"; [done|].
    iApply "HΦ". iModIntro. repeat iExists _. iFrame.
  }
  iInv "IsHarris" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
  iMod (lc_fupd_elim_later with "Lc Nodes") as "Nodes".
  iDestruct (ghost_map_lookup with "●p_all p↪□") as %Hptrs_p.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[p.n|%HLp]"; [exact Hptrs_p| |].
  { (* prev tagged, impossible *)
    iDestruct "p.n" as (γ_p_n p_n p_n_k) "[p.n↪□ p_n↪□]".
    iDestruct (ghost_map_elem_agree with "p.n↪□ p.n↪") as %[= ?].
  }
  apply elem_of_list_lookup in HLp as [idx HLp].
  iDestruct (Nodes_remove with "Nodes") as (?) "[(pM & _ & p.n↪' & %HLp_next) Nodes]"; [exact HLp|]; simpl.
  iDestruct (ghost_map_elem_agree with "p.n↪ p.n↪'") as %[= <-].
  iDestruct (Nodes_combine with "Nodes pM [] [p.n↪']") as "Nodes"; [done..|].
  destruct (next_not_tail_is_Some idx L p_k false (prev,γ_prev) p_on) as [[curr' γ_curr] [= ->]]; simpl in *; [naive_solver..|].
  apply list_lookup_fmap_Some in HLp_next as [[[c_k b] ?] [HLc [= <-]]].
  destruct (decide (curr' = curr)) as [->|NE]; last first.
  { (* validation failed, loop. *)
    iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { by iFrame "∗#%". }
    iModIntro. iDestruct (harris_node_combine_some with "p↦ [//] [p.n↪]") as "$"; [iLeft; by iFrame|].
    wp_pures. case_bool_decide; [naive_solver|].
    wp_pures.
    by iApply ("IH" with "[%] pS cS AU p↪□").
  }
  (* Equal. Get managed for curr to validate. *)
  iDestruct (Nodes_remove with "Nodes") as (cn) "[(cM & #c↪□ & c.n↪ & %HLc_next) Nodes]"; [exact HLc|]; simpl.
  iMod (hazptr.(shield_validate) with "IHD cM cS") as "[cM cS]"; [solve_ndisj|].
  iAssert (if b then γ_curr ↪[ γp_t ]□ (cn, true) else True)%I as "#c.n↪□b"; [by destruct b|].
  iDestruct (Nodes_combine with "Nodes cM [//] [c.n↪]") as "Nodes"; [done..|].
  (* Check prophecy check for curr *)
  destruct (prophecy_to_bool pr_v) eqn:Hpr_v.
  { (* Tagged, so cannot commit here. *)
    iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { by iFrame "∗#%". } clear dependent L idx p_all p_tag.
    iModIntro. iDestruct (harris_node_combine_some with "p↦ [//] [p.n↪]" ) as "$"; [iLeft; by iFrame|].
    wp_pures. wp_bind (Resolve _ _ _)%E.
    iInv "cS" as (?) "(_ & c↦ & >node & cS)".
    iDestruct (harris_node_destruct_agree with "node [//]") as (c_on c_t ->) "[% [[% c.n↪]|[% #c.n↪□]]]"; subst c_t.
    all: wp_apply (wp_resolve_load_offset with "[$pr $c↦]") as (?) "(% & _ & c↦)"; [by simplify_list_eq|]; subst pr_v; inversion Hpr_v.
    iInv "IsHarris" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
    iMod (lc_fupd_elim_later with "Lc' Nodes") as "Nodes".
    iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_c.
    iDestruct (get_persistent_AllPtrs with "PTRS") as "#[c.n|%HLc]"; [exact Hptrs_c| |]; last first.
    { (* not tagged, impossible *)
      apply elem_of_list_lookup in HLc as [idx HLc].
      iDestruct (Nodes_remove with "Nodes") as (?) "[(_ & _ & c.n↪ & _) _]"; [exact HLc|]; simpl.
      iDestruct (ghost_map_elem_agree with "c.n↪ c.n↪□") as %[= ?].
    }
    iDestruct "c.n" as (γ_c_n c_n c_n_k) "[c.n↪□' c_n↪□]".
    iDestruct (ghost_map_elem_agree with "c.n↪□ c.n↪□'") as %[= ->]; iClear "c.n↪□'"; simpl in *.
    iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { by iFrame "∗#%". }
    iModIntro. iDestruct (harris_node_combine_some with "c↦ [//] [$c.n↪□]") as "$"; [by iRight|].
    clear dependent p_all p_tag L. wp_pures.
    wp_apply (harris_helping_cas_spec with "[$pS $cS $Lc'']") as ([]) "(pS & cS & cM)"; [done..|iFrame "#"| |]; last first.

    all: wp_pures.
    { iMod "AU" as (?) "[Labs [_ Commit]]".
      iMod ("Commit" $! false _ false prev curr p_k p_k 0 γ_prev γ_prev with "[$Labs]") as "HΦ"; [done|].
      iApply "HΦ". iModIntro. iFrame.
    }
    wp_apply (hazptr.(hazard_domain_retire_spec) with "IHD cM") as "_"; [solve_ndisj|]. wp_pures.
    by iApply ("IH" with "[%] pS cS AU p↪□").
  }
  (* prophecy says we are not tagged. *)
  (* assert that we must not be tagged. *)
  destruct b.
  { iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { by iFrame "∗#%". }
    iModIntro. iDestruct (harris_node_combine_some with "p↦ [//] [p.n↪]") as "$"; [iLeft; by iFrame|].
    clear dependent L p_all p_tag idx.
    wp_pures. wp_bind (Resolve _ _ _)%E.
    iInv "cS" as (?) "(_ & c↦ & >node & cS)".
    iDestruct (harris_node_destruct_agree with "node [//]") as (c_on c_t ->) "[% [[% c.n↪]|[% c.n↪]]]"; subst c_t.
    all: wp_apply (wp_resolve_load_offset with "[$pr $c↦]") as (?) "(% & _ & c↦)"; [by simplify_list_eq|]; subst pr_v; inversion Hpr_v.
    iDestruct (ghost_map_elem_agree with "c.n↪□b c.n↪") as %[= <-]; iClear "c.n↪".
  }
  (* Check key range *)
  destruct (decide (c_k < k)%inf_Z) as [LT|GE].
  { (* Go into next iteration. *)
    iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { by iFrame "∗#%". }
    iModIntro. iDestruct (harris_node_combine_some with "p↦ [//] [p.n↪]") as "$"; [iLeft; by iFrame|].
    clear dependent L p_all p_tag idx.
    wp_pures. wp_bind (Resolve _ _ _)%E.
    iInv "cS" as (?) "(_ & c↦ & >node & cS)".
    iDestruct (harris_node_destruct_agree with "node [//]") as (c_on c_t ->) "[% [[% c.n↪]|[% #c.n↪□]]]"; subst c_t; last first.
    all: wp_apply (wp_resolve_load_offset with "[$pr $c↦]") as (?) "(% & _ & c↦)"; [by simplify_list_eq|]; subst pr_v; inversion Hpr_v.
    iInv "IsHarris" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
    iMod (lc_fupd_elim_later with "Lc' Nodes") as "Nodes".
    iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_c.
    iDestruct (get_persistent_AllPtrs with "PTRS") as "#[c.n|%HLc]"; [exact Hptrs_c| |].
    { (* curr tagged, impossible *)
      iDestruct "c.n" as (γ_p_n p_n p_n_k) "[c.n↪□ c_n↪□]".
      iDestruct (ghost_map_elem_agree with "c.n↪□ c.n↪") as %[= ?].
    }
    apply elem_of_list_lookup in HLc as [idx HLc].
    iDestruct (Nodes_remove with "Nodes") as (?) "[(cM & _ & c.n↪' & %HLc_n) Nodes]"; [exact HLc|].
    iDestruct (ghost_map_elem_agree with "c.n↪ c.n↪'") as %[= <-].
    iDestruct (Nodes_combine with "Nodes cM [] [c.n↪']") as "Nodes"; [done..|].
    destruct (next_not_tail_is_Some idx L c_k false (curr,γ_curr) c_on) as [[c_n γ_c_n] [= ->]]; [naive_solver..|]; simpl in *.
    apply list_lookup_fmap_Some in HLc_n as [[[c_n_k ?] [??]] [HLc_n [= <- <-]]].
    iDestruct (get_persistent_Nodes with "Nodes") as (?) "#(c_n↪□ & _)"; [exact HLc_n|].
    iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { by iFrame "∗#%". }
    iModIntro. iDestruct (harris_node_combine_some with "c↦ [//] [c.n↪]") as "$"; [iLeft; by iFrame|].
    clear dependent L p_all p_tag idx.
    wp_pures. wp_bind (!_)%E.
    iInv "cS" as (?) "(_ & c↦ & >node & cS)".
    iDestruct (harris_node_destruct_agree with "node [//]") as (c_on c_t ->) "[% c.n]".
    wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
    iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ [% //] c.n") as "$".
    wp_pures. case_bool_decide; [|naive_solver].
    wp_pures.
    by iApply ("IH" with "[%] cS pS AU c↪□").
  }
  (* Key in range. Commit *)
  iMod "AU" as (?) "[[Labs %HLabs] [_ Commit]]".
  iDestruct (ghost_var_agree with "Labs Linv") as %[= ->].
  assert (L = take idx L ++ [(p_k, false, (prev,γ_prev))] ++ [(c_k, false, (curr,γ_curr))] ++ drop (S (S idx)) L) as L_EQ.
  { rewrite -{1}(take_drop (S idx) L). rewrite (take_S_r _ _ (p_k, false, (prev,γ_prev))); [|done].
    simplify_list_eq. repeat f_equal. rewrite (drop_S _ (c_k, false, (curr,γ_curr)) (S idx)); [done|].
    by rewrite -Nat.add_1_r.
  }
  set (idx' := length (get_abs_state (take idx L))).
  iMod ("Commit" $! true _ (bool_decide (c_k = k)) prev curr _ _ idx' with "[$Labs]") as "HΦ".
  { iFrame "∗#%". iPureIntro. split_and!; auto; last first.
    { case_bool_decide as EQN; [done|]. destruct c_k as [|c_k|]; [naive_solver| |naive_solver].
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
  { by iFrame "∗#%". }
  iModIntro. iDestruct (harris_node_combine_some with "p↦ p↪□ [p.n↪]") as "$"; [iLeft; by iFrame|].
  clear dependent L p_all p_tag.
  wp_pures. wp_bind (Resolve _ _ _)%E.
  iInv "cS" as (?) "(_ & c↦ & >node & cS)".
  iDestruct (harris_node_destruct_agree with "node [//]") as (? c_t ->) "c.n".
  all: wp_apply (wp_resolve_load_offset with "[$pr $c↦]") as (?) "(% & _ & c↦)"; [by simplify_list_eq|]; subst pr_v.
  iDestruct "c.n" as "[% [[% c.n]|[% #c.n□]]]"; subst c_t; inversion Hpr_v.
  iModIntro. iDestruct (harris_node_combine_on with "c↦ [//] [% //] [c.n]") as "$"; [iLeft; by iFrame|].
  wp_pures. wp_bind (!_)%E.
  iInv "cS" as (?) "(_ & c↦ & >node & cS)".
  iDestruct (harris_node_destruct_agree with "node [//]") as (? c_t ->) "[% c.n]".
  wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
  iModIntro. iDestruct (harris_node_combine_on with "c↦ [//] [% //] c.n") as "$".
  wp_pures. clear dependent Hpr_v. iEval (rewrite bool_decide_eq_false_2 //).
  wp_pures. iApply "HΦ". iModIntro. by iFrame.
Qed.

Lemma hm_find_spec :
  harris_find_spec' listN hazptrN hazptr (hm_find hazptr).
Proof using DISJN.
  intros E k h γp_a γp_t γl γh γz l d prev_sh curr_sh p_st c_st ?.
  iIntros "#IHD pS cS #l.h↦□ #h↪□ #IsHarris" (Φ) "AU".
  iLöb as "IH" forall (p_st c_st prev_sh curr_sh).
  wp_lam. wp_pure credit: "Lc". wp_pure credit: "Lc'". wp_pures.
  wp_load.
  wp_pures. wp_bind (!_)%E.
  iInv "IsHarris" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
  iMod (lc_fupd_elim_later with "Lc Nodes") as "Nodes".
  iDestruct (Nodes_remove with "Nodes") as (h_on) "[(hM & _ & h.n↪ & %HLh_n) Nodes]"; [exact HLh|]; simpl in *.
  iInv "hM" as (?) "(_ & h↦ & >node & hM)".
  iDestruct (harris_node_destruct_agree with "node [//]") as (? h_t ->) "[% [[% h.n↪']|[% #h.n↪']]]"; subst h_t.
  all: iDestruct (ghost_map_elem_agree with "h.n↪ h.n↪'") as %[= <-].
  wp_apply (wp_load_offset with "h↦") as "h↦"; [by simplify_list_eq|].
  iDestruct (Nodes_combine with "Nodes hM [] [h.n↪']") as "Nodes"; [done..|].
  assert (1 < length L) as [[[c_k c_b] [c γ_c]] HLh_n']%lookup_lt_is_Some.
  { assert (0 < length L); [by apply lookup_lt_Some in HLh|].
    assert (1 ≠ length L); [|lia]. intros L_EQ. destruct HLt as [t HLt].
    rewrite L_EQ Nat.sub_diag in HLt. naive_solver.
  }
  assert (h_on = Some (c,γ_c)) as ->; simpl. { get_third HLh_n'. naive_solver. }
  iDestruct (get_persistent_Nodes with "Nodes") as (h_on) "#(c↪□ & _)"; [exact HLh_n'|].
  iModIntro. iSplitL "h↦ h.n↪".
  { iExists _. iFrame "h↦". iSplit; [done|]. iNext. iExists _,(Some (_,_)),_. simpl.
    iFrame "#". iSplit; [done|]. iSplit; [done|]. iLeft. by iSplit.
  }
  iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
  { by iFrame "∗#%". } rewrite HLh_n /=. clear dependent p_all p_tag L h_on c_b.
  wp_pures.
  wp_apply (hazptr.(shield_set_spec) (Some _) with "IHD pS") as "pS"; [solve_ndisj|]. wp_seq.
  wp_apply (fupd_wp).
  iInv "IsHarris" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
  iMod (lc_fupd_elim_later with "Lc' Nodes") as "Nodes".
  iDestruct (Nodes_remove with "Nodes") as (h_on) "[(hM & _ & h.n↪ & %HLh_n) Nodes]"; [exact HLh|]; simpl in *.
  iMod (hazptr.(shield_validate) with "IHD hM pS") as "[hM pS]"; [solve_ndisj|].
  iDestruct (Nodes_combine with "Nodes hM [] [h.n↪]") as "Nodes"; [done..|].
  iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
  { by iFrame "∗#%". } clear dependent p_all p_tag L h_on.
  iModIntro.
  awp_apply (hm_find_inner_spec with "IHD pS cS h↪□ IsHarris"); [naive_solver|done|].
  iApply (aacc_aupd with "AU"); [done|].
  iIntros (L) "HList". iAaccIntro with "HList"; first eauto with iFrame.
  iIntros ([] v r_b r_p r_c r_p_k r_c_k idx γ_r_p γ_r_c r_p_s r_c_s) "(-> & HList & Commit)"; last first.
  { iModIntro. iLeft. iFrame. iIntros "AU !> Post".
    iDestruct "Post" as (p_st' c_st' _) "[pS cS]".
    wp_pures. wp_apply ("IH" with "pS cS AU").
  }
  iDestruct "Commit" as "(#ret_p↪□ & #ret_c↪□ & Post)".
  iModIntro. iRight. iFrame "Post ∗#%". iExists _,_.
  iIntros "HΦ !> Post". iDestruct "Post" as (p_st' c_st' [-> ->]) "[pS cS]".
  wp_pures. iApply ("HΦ" with "[$pS $cS]").
Qed.

End harris_michael_find.

Definition hm_code_impl (hazptr : hazard_pointer_code) : code_harris_operations.harris_find_code := {|
  code_harris_operations.harris_find := hm_find hazptr;
|}.

Program Definition hm_impl Σ listN hazptrN (DISJN : listN ## hazptrN) `{!heapGS Σ, !hlG Σ} (hazptr : hazard_pointer_spec Σ hazptrN) : hfind_spec Σ listN hazptrN DISJN hazptr := {|
  proof_harris_operations.harris_find_spec_code := hm_code_impl hazptr.(hazard_pointer_spec_code);
|}.
Next Obligation. intros. apply hm_find_spec. done. Qed.
