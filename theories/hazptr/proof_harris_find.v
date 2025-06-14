From iris.base_logic.lib Require Import invariants ghost_var ghost_map.
From smr.program_logic Require Import atomic.
From smr.lang Require Import lang proofmode notation.
From smr Require Import sorted_list.

From smr Require Import helpers hazptr.spec_hazptr hazptr.code_harris_operations hazptr.code_harris_find.
From smr.hazptr Require Export proof_harris_operations.
From iris.prelude Require Import options.

Section harris_find.
Context `{!heapGS Σ, !hlG Σ}.
Context (listN hazptrN : namespace) (DISJN : listN ## hazptrN).

Variable (hazptr : hazard_pointer_spec Σ hazptrN).

Notation iProp := (iProp Σ).
Notation IsHList := (IsHList listN hazptrN hazptr).
Notation HListInternalInv := (HListInternalInv hazptrN hazptr).
Notation Nodes := (Nodes hazptrN hazptr).
Notation Nodes_rm_idx := (Nodes_rm_idx hazptrN hazptr).
Notation Nodes_rm_idx_idx := (Nodes_rm_idx_idx hazptrN hazptr).

Local Fixpoint RetireChain γp_t anchor i_a ret_curr i_r_c (rL : list (blk * positive)) : iProp :=
  match rL with
  | [] => False
  | [(p,i_p)] => ⌜p = anchor ∧ i_p = i_a⌝ ∗ i_p ↪[γp_t]□ (Some (ret_curr,i_r_c), true)
  | (p,i_p)::rL' => ∃ (anchor' : blk) (i_a' : positive),
            ⌜p = anchor ∧ i_p = i_a⌝ ∗ i_p ↪[γp_t]□ (Some (anchor',i_a'), true) ∗
            RetireChain γp_t anchor' i_a' ret_curr i_r_c rL'
  end.

Local Instance RetireChain_persistent γp_t anchor i_a ret_curr i_r_c rL :
  Persistent (RetireChain γp_t anchor i_a ret_curr i_r_c rL).
Proof. revert anchor i_a. induction rL as [|[] [] ?]; apply _. Qed.

Local Lemma RetireChain_in_list anchor i_a curr i_c rL L idx_a idx γp_a γp_t γr :
  L.*2 !! idx_a = Some (anchor,i_a) →
  idx < idx_a →
  RetireChain γp_t anchor i_a curr i_c rL -∗
  Nodes_rm_idx idx L γp_a γp_t γr -∗
  ⌜∀ r i_r (idx : nat), rL !! idx = Some (r,i_r) → ∃ (r_k : inf_Z), L !! (idx_a + idx)%nat = Some (r_k, true, (r,i_r))⌝.
Proof.
  iIntros (HLa LT) "RChain Nodes". iIntros (r i_r idx_r Hr).
  destruct rL as [|[rn i_rn] rL]; try done.
  iInduction rL as [|[rn' i_rn'] rL IH] forall (anchor i_a rn i_rn idx_r Hr idx_a LT HLa).
  - iDestruct "RChain" as ([[= ->] [= ->]]) "#an.n↪□".
    specialize HLa as HLa'.
    apply list_lookup_fmap_Some in HLa as [[[a_k []] ?] [HLa [= <-]]]; last first.
    { iDestruct (Nodes_rm_idx_remove with "Nodes") as (?) "[(_&_&an.n↪&_) _]"; [exact HLa|lia|]; simpl.
      by iDestruct (ghost_map_elem_agree with "an.n↪□ an.n↪") as %[= ? ?].
    }
    iDestruct (get_persistent_Nodes_rm_idx with "Nodes") as (an_n) "#(_& an.n↪ & %Han_n)"; [exact HLa|lia|].
    simpl. iDestruct (ghost_map_elem_agree with "an.n↪□ an.n↪") as %[= <-]; iClear "an.n↪".
    destruct idx_r; last first.
    { apply lookup_lt_Some in Hr. simpl in *. lia. }
    injection Hr as [= <- <-]. iPureIntro. rewrite Nat.add_0_r. eauto.
  - iDestruct "RChain" as (an' i_an') "(%EQ & #an.n↪□ & RChain)". destruct EQ as [-> ->].
    fold (RetireChain γp_t an' i_an' curr i_c ((rn',i_rn') :: rL)).
    apply list_lookup_fmap_Some in HLa as [[[a_k []] ?] [HLa [= <-]]]; last first.
    { iDestruct (Nodes_rm_idx_remove with "Nodes") as (?) "[(_&_&an.n↪&_) _]"; [exact HLa|lia|]; simpl.
      by iDestruct (ghost_map_elem_agree with "an.n↪□ an.n↪") as %[= ? ?].
    }
    iDestruct (get_persistent_Nodes_rm_idx with "Nodes") as (an_n) "#(_& an.n↪ & %Han')"; [exact HLa|lia|].
    simpl. iDestruct (ghost_map_elem_agree with "an.n↪□ an.n↪") as %[= <-]; iClear "an.n↪".
    destruct idx_r as [|[|]]; last first.
    { replace (idx_a + S (S n)) with (idx_a + 1 + S n) by lia.
      iApply ("IH" with "[%] [%] [%] RChain Nodes"); [|lia|exact Han'].
      rewrite lookup_cons_ne_0 in Hr; [|lia]. rewrite -Hr. f_equal.
    }
    all: iClear "IH"; injection Hr as [= -> ->].
    + iAssert (∃ (an'_n : blk) (i_an'_n : positive), ⌜an' = r ∧ i_an' = i_r⌝ ∗ i_an' ↪[γp_t]□ (Some (an'_n,i_an'_n), true))%I with "[RChain]" as (an'_n i_an'_n [-> ->]) "#an'.n↪□".
      { destruct rL as [|[r' i_r'] rL]; simpl.
        - iDestruct "RChain" as ([-> ->]) "an'.n↦". iExists curr,i_c. by iFrame.
        - iDestruct "RChain" as (an'_n i_an'_n [-> ->]) "(an'.n↦ & RChain)". iExists an'_n,i_an'_n. by iFrame.
      }
      apply list_lookup_fmap_Some in Han' as [[[an'_k []] ?] [Han' [= <-]]]; last first. {
        iDestruct (Nodes_rm_idx_remove with "Nodes") as (?) "[(_&_&an'.n↪&_) _]"; [exact Han'|lia|]; simpl.
        by iDestruct (ghost_map_elem_agree with "an'.n↪□ an'.n↪") as %[= ? ?].
      }
      iPureIntro. eauto.
    + iPureIntro. rewrite !Nat.add_0_r. eauto.
Qed.

Lemma RetireChain_curr anchor i_a curr i_c rL L idx_a idx γp_a γp_t γr :
  L.*2 !! idx_a = Some (anchor,i_a) →
  idx < idx_a →
  RetireChain γp_t anchor i_a curr i_c rL -∗
  Nodes_rm_idx idx L γp_a γp_t γr -∗
  ⌜L.*2 !! (idx_a + length rL)%nat = Some (curr,i_c)⌝.
Proof.
  iIntros (HLa LT) "RChain Nodes".
  destruct rL as [|[rn i_rn] rL]; [done|].
  iInduction rL as [|[rn' i_rn'] rL IH] forall (rn i_rn anchor i_a idx_a LT HLa).
  { iDestruct (RetireChain_in_list with "RChain Nodes") as %ElemOfL; [exact HLa|lia|].
    simpl in *. iDestruct "RChain" as ([<- <-]) "#rn.n↪".
    specialize (ElemOfL _ _ 0 ltac:(done)) as [a_k HLan].
    iDestruct (get_persistent_Nodes_rm_idx with "Nodes") as (?) "(_ & #rn.n↪' & %Hrn_n)"; [exact HLan|lia|simpl].
    iDestruct (ghost_map_elem_agree with "rn.n↪ rn.n↪'") as %[= <-]; iClear "rn.n↪'".
    iPureIntro. by rewrite -Hrn_n Nat.add_0_r.
  }
  iDestruct (RetireChain_in_list with "RChain Nodes") as %ElemOfL; [exact HLa|lia|].
  iSimpl in "RChain".
  iDestruct "RChain" as (rn_n i_rn_n [<- <-]) "(rn.n↪ & RChain)".
  replace (idx_a + length ((rn,i_rn) :: (rn',i_rn') :: rL)) with (idx_a + 1 + length ((rn',i_rn') :: rL)); [|simpl;lia].
  iAssert (⌜rn' = rn_n ∧ i_rn' = i_rn_n⌝)%I as %[<- <-].
  { destruct rL.
    - by iDestruct "RChain" as ([-> ->]) "_".
    - by iDestruct "RChain" as (?? [-> ->]) "_".
  }
  specialize (ElemOfL _ _ 1 ltac:(done)) as [rn'_k HLrn'].
  get_third HLrn'.
  iApply ("IH" with "[%] [%] RChain Nodes"); [lia|exact HLrn'].
Qed.

Fixpoint DeletedChain γp_a γp_t γr anchor i_a ret_curr i_r_c (rL : list (blk * gname)) : iProp :=
  match rL with
  | [] => ⌜anchor = ret_curr ∧ i_a = i_r_c⌝
  | (p,i_p)::rL' => ∃ (anchor' : blk) (i_a' : gname),
      ⌜p = anchor ∧ i_p = i_a⌝ ∗ i_p ↪[γp_t]□ (Some (anchor',i_a'), true) ∗
      hazptr.(Managed) γr p i_p 2 (node γp_a γp_t) ∗
      DeletedChain γp_a γp_t γr anchor' i_a' ret_curr i_r_c rL'
  end.

Lemma create_delete_chain idx_p γp_a γp_t γr a_k anchor i_a curr i_c rL L b (o_an : option (blk * gname)) :
  (∃ tit, L !! (length L - 1) = Some (∞ᵢ, false, tit)) →
  L !! (idx_p + 1) = Some (a_k, b, (anchor, i_a)) →
  L.*2 !! (idx_p + 1 + 1) = o_an →
  (if (b : bool) then i_a ↪[ γp_t ]□ (o_an, true) else i_a ↪[γp_t]{#1 / 2} (o_an, false))%I -∗
  RetireChain γp_t anchor i_a curr i_c rL -∗
  hazptr.(Managed) γr anchor i_a 2 (node γp_a γp_t) -∗
  ([∗ list] k↦y ∈ take (length rL - 1) (drop (S (idx_p + 1)) L),
      ListNode hazptrN hazptr (idx_p + 1 + S k) y L γp_a γp_t γr)
  -∗
  DeletedChain γp_a γp_t γr anchor i_a curr i_c rL.
Proof.
  iIntros (HLt HLa HLan) "a.n↪ RChain aM Ms". destruct rL as [|[r i_r] rL]; [done|].
  iInduction rL as [|[r' i_r'] rL IH] forall (idx_p r i_r a_k anchor i_a o_an b HLa HLan).
  { iDestruct "RChain" as ([-> ->]) "#a.n↪□". iExists curr,i_c. by iFrame "∗#".
  }
  iDestruct "RChain" as (an i_an [-> ->]) "[#a.n↪□ RChain]".
  fold (RetireChain γp_t an i_an curr i_c ((r',i_r')::rL)).
  assert (length ((anchor, i_a) :: (r', i_r') :: rL) - 1 = length ((r', i_r') :: rL)) as ->; [done|].
  destruct b; last first. { by iDestruct (ghost_map_elem_agree with "a.n↪□ a.n↪") as %[= ?]. }
  destruct (next_not_tail_is_Some (idx_p + 1) L a_k true (anchor, i_a) o_an) as [[an' i_an'] [= ->]]; [naive_solver..|].
  iDestruct (ghost_map_elem_agree with "a.n↪□ a.n↪") as %[= <- <-].
  apply list_lookup_fmap_Some in HLan as [[[an_k b] ?] [HLan [= <-]]].
  iEval (rewrite (drop_S _ (an_k,b, (an, i_an))); [|rewrite -Nat.add_1_r; exact HLan]) in "Ms".
  iEval (rewrite (take_cons' (an_k,b, (an, i_an))); [|simpl;lia]) in "Ms".
  iDestruct "Ms" as "[an Ms]".
  iDestruct "an" as (ann) "(anM & _ & an.n↪ & %HLann)".
  iSimpl in "anM".
  iAssert (⌜an = r' ∧ i_an = i_r'⌝)%I as %[<- <-].
  { destruct rL; simpl in *.
    - by iDestruct "RChain" as ([-> ->]) "_".
    - by iDestruct "RChain" as (?? [-> ->]) "_".
  }
  iDestruct ("IH" with "[%] [%] an.n↪ RChain anM [Ms]") as "Chain"; [exact HLan|exact HLann|rewrite !Nat.add_1_r|].
  { iApply (big_sepL_mono with "Ms"). iIntros (???) "?". by rewrite !Nat.add_succ_comm. }
  iExists an, i_an. do 2 (iSplit; [done|]). iFrame.
Qed.

Local Lemma chain_retire_spec d γp_a γp_t γr anchor i_a curr i_c rL E :
  ↑hazptrN ⊆ E →
  {{{ hazptr.(IsHazardDomain) γr d ∗ DeletedChain γp_a γp_t γr anchor i_a curr i_c rL }}}
    chain_retire hazptr #d #anchor #curr @ E
  {{{ RET #(); True }}}.
Proof.
  iIntros (? Φ) "(#IRD & DChain) HΦ".
  iInduction (rL) as [|[r i_r] rL IH] forall (anchor i_a).
  all: wp_lam; wp_pures.
  { case_bool_decide as EQ; wp_pures.
    { by iApply "HΦ". }
    assert (anchor ≠ curr). { naive_solver. }
    iDestruct "DChain" as %?. naive_solver.
  }
  case_bool_decide as EQ; wp_pures.
  { by iApply "HΦ". }
  assert (anchor ≠ curr). { naive_solver. }
  iDestruct "DChain" as (a' i_a' [-> ->]) "(#a.n↪□ & aD & DChain)". fold DeletedChain.
  wp_pures. wp_bind (! _)%E.
  iInv "aD" as (lv _) "(a↦ & >node & aD)".
  iDestruct "node" as (a_k a_n a_t ->) "(#a↪□ & [% [[% a.n↪]|[% a.n↪]]])"; subst a_t; simpl in *.
  all: iDestruct (ghost_map_elem_agree with "a.n↪ a.n↪□") as %[= ->]; iClear "a.n↪"; simpl in *.
  wp_apply (wp_load_offset with "a↦") as "a↦"; [by simplify_list_eq|].
  iModIntro. iDestruct (harris_node_combine_some with "a↦ [# //] [$a.n↪□]") as "$"; [by iRight|].
  wp_pures. wp_apply (hazptr.(hazard_domain_retire_spec) with "IRD aD") as "_"; [done|].
  wp_pures. iApply ("IH" with "DChain HΦ").
Qed.

(* Loop invarinats... *)
(* Case analysis on c_tag:
    If c_tag = 0:
      a_pa: is None.
      a_sh a_p_sh : empty protection.
      prev_sh : protects prev.
      curr_sh : empty protection.
    If c_tag = 1 ∧ a = prev.
      a_pa : is_Some.
      a_p : protects a_p:
      a : no protection.
      prev_sh : protects a and prev.
      γ_a = γ_prev.
    else (c_tag = 1 ∧ a ≠ prev) :
      a_pa: is Some.
      a_p_sh, a_sh : protects a_p and a.
      prev_sh : protects prev.
      curr_sh : empty protection.
*)
Local Lemma harris_find_inner_spec
  (o_a_p o_a : option (blk * gname)) (a_p_k : inf_Z)
  d (prev curr : blk) (c_tag : Z) rL
  E γp_a γp_t γl γh γz
  (h : blk) (k : Z) (p_k c_k : inf_Z)
  (a_p_sh a_sh prev_sh curr_sh : loc) γ_prev γ_curr a_p_st a_st c_st :
  (if decide (c_tag = 0%Z) then
    o_a_p = None ∧ o_a = None ∧ (p_k < k)%inf_Z
  else
    ∃ (a_p a : blk) (γ_a_p γ_a : gname),
    o_a_p = Some (a_p,γ_a_p) ∧
    o_a = Some (a,γ_a) ∧
    (a_p_k < k)%inf_Z ∧
    a_p_st = (Validated a_p γ_a_p (node γp_a γp_t) nodeSize) ∧
    (a_st = if decide (a = prev) then a_st
            else (Validated a γ_a (node γp_a γp_t) nodeSize)) ∧
    γ_a = if decide (a = prev) then γ_prev
          else γ_a
  ) →
  (↑listN ∪ ↑hazptrN) ⊆ E →
  ⊢ hazptr.(IsHazardDomain) γz d -∗
  hazptr.(Shield) γz a_p_sh a_p_st -∗
  hazptr.(Shield) γz a_sh a_st -∗
  hazptr.(Shield) γz prev_sh (Validated prev γ_prev (node γp_a γp_t) nodeSize) -∗
  hazptr.(Shield) γz curr_sh c_st -∗
  γ_prev ↪[γp_a]□ (p_k,prev) -∗ γ_curr ↪[γp_a]□ (c_k,curr) -∗
  inv listN (HListInternalInv h γp_a γp_t γl γh γz) -∗
  match o_a with
  | Some (a, γ_a) =>
    RetireChain γp_t a γ_a curr γ_curr rL
  | None => ⌜rL = []⌝
  end -∗
  match o_a_p with
  | Some (a_p, γ_a_p) =>
    γ_a_p ↪[γp_a]□ (a_p_k,a_p)
  | None => True
  end -∗
  <<{ ∀∀ (L : list inf_Z), HList γl L }>>
    (harris_find_inner hazptr)
      #d #k
      #((Loc.blk_to_loc ∘ fst <$> o_a_p) &ₜ 0) #((Loc.blk_to_loc ∘ fst <$> o_a) &ₜ 0) #prev #(Some (Loc.blk_to_loc curr) &ₜ c_tag)
      #a_p_sh #a_sh #prev_sh #curr_sh
      @ E, (↑listN ∪ (↑ptrsN hazptrN)), ↑mgmtN hazptrN
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
        True
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
  intros Hst HE.
  iIntros "#IHD a_pS aS pS cS #p↪□ #c↪□ #IsH RL #a_p↪□" (Φ).
  set AtU := (AtU in (AtU -∗ _)%I).
  iIntros "AU".
  iLöb as "IH" forall
    (o_a_p o_a a_p_k prev curr c_tag
    rL p_k c_k
    a_p_sh a_sh prev_sh curr_sh
    γ_prev γ_curr
    a_p_st a_st c_st Hst)
  "p↪□ c↪□ a_p↪□".
  set IH := (IH in (▷ IH)%I).

  wp_lam. wp_pure credit: "Lc". wp_pures.
  wp_apply (hazptr.(shield_set_spec) (Some _) with "IHD cS") as "cS"; [solve_ndisj|].
  wp_pures.
  wp_apply (wp_new_proph with "[//]") as (pr_v p) "pr".
  wp_pure. wp_pure.
  set continue := (continue in (let: "continue" := (λ: <>, continue) in _)%E).

  wp_pures.

  destruct (decide (c_tag = 0%Z)) as [->|NE].
  - (* Validate on curr. *)
    destruct Hst as (-> & -> & LE). simpl.
    iClear "a_p↪□ c↪□ RL". clear γ_curr c_k rL.
    wp_pures. wp_bind (!_)%E.
    iInv "pS" as (? _) "(p↦ & >node & pS)".
    iDestruct (harris_node_destruct_agree with "node [//]") as ([p_on|] p_t ->) "[%Hpk p.n↪]"; simpl; last first.
    { exfalso. clear -Hpk LE. eapply is_Some_None, Hpk. left. transitivity k; done. }
    iDestruct "p.n↪" as "[[% p.n↪]|[% #p.n↪□]]"; subst p_t; last first.
    all: wp_apply (wp_load_offset with "p↦") as "p↦"; [by simplify_list_eq|].
    { (* Tagged prev, restart. *)
      iModIntro. destruct p_on. simpl in *.
      iDestruct (harris_node_combine_some with "p↦ p↪□ [$p.n↪□]" ) as "$"; [by iRight|].
      clear Hpk.
      wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "IHD a_pS") as "_"; [solve_ndisj|]; wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "IHD aS") as "_"; [solve_ndisj|]; wp_pures.
      iMod "AU" as (L) "[Labs [_ Commit]]".
      iMod ("Commit" $! false _ false prev curr 0 0 0 γ_prev γ_prev _ with "[$Labs]") as "HΦ"; [done|].
      iApply "HΦ". iModIntro. iFrame.
    }
    iInv "IsH" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
    iMod (lc_fupd_elim_later with "Lc Nodes") as "Nodes".
    iDestruct (ghost_map_lookup with "●p_all p↪□") as %Hptrs_p.
    iDestruct (get_persistent_AllPtrs with "PTRS") as "#[p.n|%HLp]"; [exact Hptrs_p| |].
    { (* prev tagged, impossible *)
      iDestruct "p.n" as (???) "[p.n↪□ p_n↪□]".
      iDestruct (ghost_map_elem_agree with "p.n↪□ p.n↪") as %[= ?].
    }
    apply elem_of_list_lookup in HLp as [idx HLp].
    iDestruct (Nodes_remove with "Nodes") as (?) "[(pM & _ & p.n↪' & %HLp_next) Nodes]"; [exact HLp|]; simpl.
    iDestruct (ghost_map_elem_agree with "p.n↪ p.n↪'") as %[= <-].
    iDestruct (Nodes_combine with "Nodes pM [] [p.n↪']") as "Nodes"; [done..|].
    destruct (next_not_tail_is_Some idx L p_k false (prev,γ_prev) (Some p_on)) as [[curr' γ_curr] [= ->]]; simpl in *; [naive_solver..|].
    apply list_lookup_fmap_Some in HLp_next as [[[c_k c_b] ?] [HLc [= <-]]].
    iDestruct (Nodes_remove with "Nodes") as (cn) "[(cM & #c↪□ & c.n↪ & %HLc_next) Nodes]"; [exact HLc|]; simpl.
    destruct (decide (curr' = curr)) as [->|NE]; last first.
    { (* validation failed, loop. *)
      iDestruct (Nodes_combine with "Nodes cM [# //] c.n↪") as "Nodes"; [done..|].
      iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
      { by iFrame "∗#%". } clear dependent p_all p_tag L idx.
      iModIntro. iDestruct (harris_node_combine_some with "p↦ [//] [p.n↪]" ) as "$"; [iLeft; by iFrame|].
      clear Hpk.

      wp_pures. rewrite bool_decide_eq_false_2 //.
      wp_pures.
      iApply ("IH" $! None None 0 prev curr' 0%Z []
        with "[%] a_pS aS pS cS [# //] AU [# //] [# //] [# //]").
      rewrite ->decide_True; done.
    }
    (* Equal. Get managed for curr to validate. *)
    iMod (hazptr.(shield_validate) with "IHD cM cS") as "[cM cS]"; [solve_ndisj|].
    iAssert (if c_b then γ_curr ↪[ γp_t ]□ (cn, true) else True)%I as "#c.n↪□b"; [by destruct c_b|].
    iDestruct (Nodes_combine with "Nodes cM [//] [c.n↪]") as "Nodes"; [done..|].
    (* Check prophecy check for curr *)
    destruct (prophecy_to_bool pr_v) eqn:Hpr_v.
    { (* Tagged, so cannot commit here. *)
      iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
      { by iFrame "∗#%". } clear dependent L idx p_all p_tag.
      iModIntro. iDestruct (harris_node_combine_some with "p↦ [//] [p.n↪]" ) as "$"; [iLeft; by iFrame|].
      clear Hpk.
      wp_pures. subst continue. wp_pures.
      wp_bind (Resolve _ _ _)%E.
      iInv "cS" as (lv _) "(c↦ & >node & cS)".
      iDestruct (harris_node_destruct_agree with "node [# //]") as (c_on c_t ->) "[%Hck c.n↪]".
      wp_apply (wp_resolve_load_offset with "[$pr $c↦]") as (pvs') "(%EQ & pr & c↦)"; [by simplify_list_eq|].
      rewrite {}EQ /= bool_decide_eq_true in Hpr_v.

      iDestruct "c.n↪" as "[[-> c.n↪]|[-> #c.n↪□]]".
      { exfalso. clear -Hpr_v. lia. }
      have [[c_n γ_c_n] ->] : (is_Some c_on).
      { apply Hck. right. done. }
      iInv "IsH" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
      iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_c.
      iDestruct (get_persistent_AllPtrs with "PTRS") as "#[c.n|%HLc]"; [exact Hptrs_c| |]; last first.
      { apply elem_of_list_lookup in HLc as [idx HLc].
        iDestruct (Nodes_remove with "Nodes") as (?) "[(_ & _ & >c.n↪ & _) _]"; [exact HLc|]; simpl.
        iDestruct (ghost_map_elem_agree with "c.n↪□ c.n↪") as %[= ? ?].
      }
      iDestruct "c.n" as (?? c_n_k) "[c.n↪□' c_n↪□]".
      iDestruct (ghost_map_elem_agree with "c.n↪□ c.n↪□'") as %[= <- <-].
      iClear "c.n↪□'".
      iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
      { by iFrame "∗#%". } clear dependent L p_tag p_all.
      iModIntro.
      iDestruct (harris_node_combine_on with "c↦ [# //] [% //] []") as "$"; [iRight; by iFrame "#"|].
      rewrite /get_anchor.
      wp_pures.
      (* c_tag = 1, a = prev *)
      iApply ("IH" $! (Some (prev,_)) (Some (curr,_)) _ curr c_n 1%Z [(_,_)]
        with "[%] pS aS cS a_pS [#] AU [# //] [# //] [# //]").
      - rewrite ->decide_False; [|lia].
        eexists _,_,_,_. split_and!; try done.
        all: case_decide; [done|naive_solver].
      - iFrame "#". iPureIntro. split; reflexivity.
    }
    (* prophecy says we are not tagged. *)
    (* assert that we must not be tagged. *)
    destruct c_b.
    { iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
      { by iFrame "∗#%". }
      iModIntro. iDestruct (harris_node_combine_some with "p↦ [//] [p.n↪]") as "$"; [iLeft; by iFrame|].
      clear dependent L p_all p_tag idx.
      subst continue.
      wp_pures.
      wp_bind (Resolve _ _ _)%E.
      iInv "cS" as (lv _) "(c↦ & >node & cS)".
      iDestruct (harris_node_destruct_agree with "node [# //]") as (c_on c_t ->) "[%Hck c.n↪]".
      wp_apply (wp_resolve_load_offset with "[$pr $c↦]") as (pvs') "(%EQ & pr & c↦)"; [by simplify_list_eq|].
      rewrite {}EQ /= bool_decide_eq_false in Hpr_v.
      iDestruct "c.n↪" as "[[% c.n↪]|[% #c.n↪□]]"; subst c_t; last first.
      { exfalso. lia. }
      iDestruct (ghost_map_elem_agree with "c.n↪ c.n↪□b") as %[= ?].
    }
    (* Check key range *)
    destruct (decide (c_k < k)%inf_Z) as [LT|GE].
    { (* Go into next iteration. *)
      iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
      { by iFrame "∗#%". }
      iModIntro. iDestruct (harris_node_combine_some with "p↦ [//] [p.n↪]") as "$"; [iLeft; by iFrame|].
      clear dependent L p_all p_tag idx.
      subst continue.
      wp_pure credit: "Lc". wp_pures.
      wp_bind (Resolve _ _ _)%E.
      iInv "cS" as (lv _) "(c↦ & >node & cS)".
      iDestruct (harris_node_destruct_agree with "node [# //]") as (c_on c_t ->) "[%Hck c.n↪]".
      wp_apply (wp_resolve_load_offset with "[$pr $c↦]") as (pvs') "(%EQ & pr & c↦)"; [by simplify_list_eq|].
      rewrite {}EQ /= bool_decide_eq_false in Hpr_v.

      iDestruct "c.n↪" as "[[-> c.n↪]|[-> #c.n↪□]]"; last first.
      { exfalso. clear -Hpr_v. lia. }
      have [[c_n γ_c_n] ->] : (is_Some c_on).
      { apply Hck. left. transitivity k; done. }
      iInv "IsH" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
      iMod (lc_fupd_elim_later with "Lc Nodes") as "Nodes".
      iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_c.
      iDestruct (get_persistent_AllPtrs with "PTRS") as "#[c.n|%HLc]"; [exact Hptrs_c| |].
      { iDestruct "c.n" as (???) "[c.n↪□ _]".
        iDestruct (ghost_map_elem_agree with "c.n↪ c.n↪□") as %[= ?].
      }
      apply elem_of_list_lookup in HLc as [idx HLc].
      iDestruct (Nodes_remove with "Nodes") as (?) "[(cM & _ & c.n↪' & %HLc_n) Nodes]"; [exact HLc|]; simpl.
      iDestruct (ghost_map_elem_agree with "c.n↪ c.n↪'") as %[= <-].
      iDestruct (Nodes_combine with "Nodes cM [# //] [c.n↪']") as "Nodes"; [done..|].
      apply list_lookup_fmap_Some in HLc_n as [[[c_n_k b] ?] [HLc_n [= <-]]].
      iDestruct (Nodes_remove with "Nodes") as (c_n_n) "[(c_nM & #c_n↪□ & c_n.n↪ & %HLc_n_n) Nodes]"; [exact HLc_n|]; simpl.
      iDestruct (Nodes_combine with "Nodes c_nM [# //] c_n.n↪") as "Nodes"; [done..|].
      iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
      { by iFrame "∗#%". } clear dependent p_all p_tag L c_n_n.
      iModIntro.
      iDestruct (harris_node_combine_some with "c↦ [# //] [c.n↪]") as "$"; [iLeft; by iFrame|].
      rewrite /get_anchor.
      wp_pures.
      wp_bind (!_)%E.
      iInv "cS" as (lv _) "(c↦ & >node & cS)".
      iDestruct (harris_node_destruct_agree with "node [# //]") as (c_on' c_t ->) "[%Hck' c.n↪]".
      wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
      iDestruct (harris_node_combine_on with "c↦ [# //] [% //] c.n↪") as "$".
      iModIntro. wp_pures.
      rewrite bool_decide_eq_true_2; [|done].
      wp_pures.
      (* c_tag = 0 *)
      iApply ("IH" $! None None 0 curr c_n 0%Z []
        with "[%] a_pS aS cS pS [# //] AU [# //] [# //] [# //]").
      rewrite ->decide_True; done.
    }
    (* Key in range. Commit *)
    iMod "AU" as (?) "[[Labs %HLabs] [_ Commit]]".
    iDestruct (ghost_var_agree with "Labs Linv") as %[= ->].
    assert (L = take idx L ++ [(p_k, false, (prev,γ_prev))] ++ [(c_k, false, (curr,γ_curr))] ++ drop (S (S idx)) L) as L_EQ.
    { rewrite /= -!drop_S ?take_drop //. rewrite -HLc Nat.add_1_r //. }
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
    { by iFrame "∗#%". } clear dependent p_all p_tag L.
    iModIntro. iDestruct (harris_node_combine_some with "p↦ [//] [p.n↪]" ) as "$"; [iLeft; by iFrame|].

    subst continue.
    wp_pures.

    wp_bind (Resolve _ _ _)%E.
    iInv "cS" as (lv _) "(c↦ & >node & cS)".
    iDestruct (harris_node_destruct_agree with "node [# //]") as (c_on c_t ->) "[%Hck c.n↪]".
    wp_apply (wp_resolve_load_offset with "[$pr $c↦]") as (pvs') "(%EQ & pr & c↦)"; [by simplify_list_eq|].
    rewrite {}EQ /= bool_decide_eq_false in Hpr_v.
    iDestruct "c.n↪" as "[[% c.n↪]|[% #c.n↪]]"; subst c_t; last lia.
    iDestruct (harris_node_combine_on with "c↦ [# //] [% //] [c.n↪]") as "$"; [by iLeft; iFrame|].
    iModIntro. wp_pures.

    wp_bind (!_)%E.
    iInv "cS" as (lv _) "(c↦ & >node & cS)".
    iDestruct (harris_node_destruct_agree with "node [# //]") as (? ? ->) "[% c.n↪]".
    wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
    iDestruct (harris_node_combine_on with "c↦ [# //] [% //] c.n↪") as "$".
    iModIntro. wp_pures.

    iEval (rewrite bool_decide_eq_false_2 //).
    wp_pures.

    wp_apply (hazptr.(shield_drop_spec) with "IHD a_pS") as "_"; [solve_ndisj|];
    wp_pures.
    wp_apply (hazptr.(shield_drop_spec) with "IHD aS") as "_"; [solve_ndisj|];
    wp_pures.

    iApply "HΦ". iModIntro. iFrame. done.
  - (* Validate on anchor. *)
    destruct Hst as (a_p & a & γ_a_p & γ_a & -> & -> & LE & -> & -> & Hγ_a).
    iEval (rewrite bool_decide_eq_false_2; [|intros [= ->]; lia..]).
    iSimpl.
    wp_pures.


    wp_bind (!_)%E.
    iInv "a_pS" as (lv ?) "(a_p↦ & >node & a_pS)".
    iDestruct (harris_node_destruct_agree with "node [//]") as (o_a a_p_t ->) "[%Ho_a [[% a_p.n↪]|[% #a_p.n↪□]]]"; subst a_p_t; last first.
    all: wp_apply (wp_load_offset with "a_p↦") as "a_p↦"; [by simplify_list_eq|].
    all: simpl in *.
    { (* Tagged, restart. *)
      iDestruct (harris_node_combine_on with "a_p↦ [# //] [% //] []") as "$"; [by iRight; iFrame "#"|].
      iModIntro. wp_pures.

      wp_apply (hazptr.(shield_drop_spec) with "IHD a_pS") as "_"; [solve_ndisj|];
      wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "IHD aS") as "_"; [solve_ndisj|];
      wp_pures.

      iMod "AU" as (L) "[Labs [_ Commit]]".
      iMod ("Commit" $! false _ false prev curr 0 0 0 γ_prev γ_prev _ with "[$Labs]") as "HΦ"; [done|].
      iApply "HΦ". iModIntro. iFrame.
    }

    iInv "IsH" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
    iMod (lc_fupd_elim_later with "Lc Nodes") as "Nodes".
    iDestruct (ghost_map_lookup with "●p_all a_p↪□") as %Hptrs_a_p.
    iDestruct (get_persistent_AllPtrs with "PTRS") as "#[a_p.n|%HLa_p]"; [exact Hptrs_a_p| |].
    { (* prev tagged, impossible *)
      iDestruct "a_p.n" as (???) "[a_p.n↪□ a_p_n↪□]".
      iDestruct (ghost_map_elem_agree with "a_p.n↪□ a_p.n↪") as %[= ?].
    }

    apply elem_of_list_lookup in HLa_p as [idx HLa_p].
    iDestruct (Nodes_remove with "Nodes") as (?) "[(a_pM & _ & a_p.n↪' & %HLa) Nodes]"; [exact HLa_p|]; simpl.
    iDestruct (ghost_map_elem_agree with "a_p.n↪ a_p.n↪'") as %[= <-].
    iDestruct (Nodes_combine with "Nodes a_pM [] [a_p.n↪']") as "Nodes"; [done..|].
    destruct (next_not_tail_is_Some idx L a_p_k false (a_p,γ_a_p) o_a) as [[a' γ_a'] [= ->]]; simpl in *; [naive_solver..|].
    apply list_lookup_fmap_Some in HLa as [[[a_k b] ?] [HLa [= <-]]].
    iDestruct (Nodes_remove with "Nodes") as (an) "[(aM & #a↪□ & a.n↪ & %HLa_next) Nodes]"; [exact HLa|]; simpl.
    destruct (decide (a' = a)) as [->|NE_a]; last first.
    { (* validation failed, loop. *)
      iDestruct (Nodes_combine with "Nodes aM [# //] a.n↪") as "Nodes"; [done..|].
      iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
      { by iFrame "∗#%". } clear dependent L p_all p_tag.
      iModIntro. iDestruct (harris_node_combine_some with "a_p↦ [//] [a_p.n↪]" ) as "$"; [iLeft; by iFrame|].
      wp_pures. case_bool_decide; [naive_solver|].
      wp_pures.
      iApply ("IH" $! None None 0 a_p a' 0%Z []
        with "[%] cS pS a_pS aS [# //] AU [# //] [# //] [# //]").
      rewrite ->decide_True; done.
    }
    (* Equal. Get managed for a to validate. *)
    iAssert (⌜(if decide (a = prev) then γ_prev else γ_a) = γ_a'⌝)%I as %<-.
    { destruct (decide (a = prev)) as [<-|Ha_prev].
      - by iDestruct (hazptr.(shield_managed_agree) with "pS aM") as %<-.
      - by iDestruct (hazptr.(shield_managed_agree) with "aS aM") as %<-.
    }
    iDestruct (Nodes_combine with "Nodes aM [//] [a.n↪]") as "Nodes"; [done..|].
    clear dependent an.
    iDestruct (Nodes_remove with "Nodes") as (?) "[(a_pM & _ & a_p.n↪' & %HLa') Nodes]"; [exact HLa_p|]; simpl.
    iDestruct (ghost_map_elem_agree with "a_p.n↪ a_p.n↪'") as %[= <-].

    rewrite -Hγ_a in HLa'.
    iDestruct (RetireChain_curr with "RL Nodes") as %HLc; [exact HLa'|lia|].
    rewrite Hγ_a in HLa'.
    iDestruct (Nodes_combine with "Nodes a_pM [//] [a_p.n↪']") as "Nodes"; [done..|].
    apply list_lookup_fmap_Some in HLc as [[[c_k' c_b] ?] [HLc [= <-]]].
    iDestruct (Nodes_remove with "Nodes") as (c_on) "[(cM & #c↪□' & c.n↪ & %HLc_n) Nodes]"; [exact HLc|].
    iDestruct (ghost_map_elem_agree with "c↪□ c↪□'") as %[= <-].
    iClear "c↪□'".

    iMod (hazptr.(shield_validate) with "IHD cM cS") as "[cM cS]"; [solve_ndisj|].

    (* Some booking regarding pointer equality for later. *)

    iAssert (⌜if decide (a = curr) then γ_a = γ_curr else True⌝)%I as %Ha_curr.
    { destruct (decide (a = curr)) as [->|]; last done.
      destruct (decide (curr = prev)) as [->|Hc_p].
      - by iDestruct (hazptr.(shield_managed_agree) with "pS cM") as %<-.
      - by iDestruct (hazptr.(shield_managed_agree) with "aS cM") as %<-.
    }

    iAssert (⌜if decide (prev = curr) then γ_prev = γ_curr else True⌝)%I as %Hp_c.
    { destruct (decide (prev = curr)) as [->|]; last done.
      by iDestruct (hazptr.(shield_managed_agree) with "pS cM") as %<-.
    }

    iDestruct (Nodes_combine with "Nodes cM [//] [c.n↪]") as "Nodes"; [done..|].
    clear dependent c_on.
    iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { by iFrame "∗#%". } clear dependent p_all p_tag L.
    iModIntro. iDestruct (harris_node_combine_some with "a_p↦ [//] [a_p.n↪]" ) as "$"; [iLeft; by iFrame|].

    subst continue.
    wp_pure credit: "Lc". wp_pures.

    wp_bind (Resolve _ _ _)%E.
    iInv "cS" as (lv _) "(c↦ & >node & cS)".
    iDestruct (harris_node_destruct_agree with "node [# //]") as (c_on c_t ->) "[%Hck c.n↪]".
    wp_apply (wp_resolve_load_offset with "[$pr $c↦]") as (pvs') "(%EQ & pr & c↦)"; [by simplify_list_eq|].
    subst pr_v.

    iDestruct "c.n↪" as "[[-> c.n↪]|[-> #c.n↪□]]"; last first.
    { have [[c_n γ_c_n] ->] : is_Some c_on.
      { apply Hck. right. done. }

      iInv "IsH" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
      iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_c.
      iDestruct (get_persistent_AllPtrs with "PTRS") as "#[c.n|%HLc]"; [exact Hptrs_c| |]; last first.
      { clear idx.
        apply elem_of_list_lookup in HLc as [idx HLc].
        iDestruct (Nodes_remove with "Nodes") as (?) "[(_ & _ & c.n↪ & _) _]"; [exact HLc|]; simpl.
        iMod "c.n↪".
        iDestruct (ghost_map_elem_agree with "c.n↪□ c.n↪") as %[= ? ?].
      }
      iDestruct "c.n" as (?? c_n_k) "[c.n↪□' c_n↪□]".
      iDestruct (ghost_map_elem_agree with "c.n↪□ c.n↪□'") as %[= <- <-].
      iClear "c.n↪□'".
      iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
      { by iFrame "∗#%". }

      iDestruct (harris_node_combine_on with "c↦ [# //] [% //] []") as "$"; [by iRight; iFrame "#"|].
      iModIntro. rewrite /get_anchor.
      wp_pures.

      destruct (decide (a = prev)) as [->|Ha_prev]; last first.
      - iEval (rewrite bool_decide_eq_false_2; [|naive_solver]).
        wp_pures.

        iApply ("IH" $! (Some (a_p,_)) (Some (a,_)) _ curr c_n 1%Z (rL ++ [(curr,γ_curr)])
        with "[%] a_pS aS cS pS [#] AU [# //] [# //] [# //]").
        + clear Hp_c. erewrite decide_False; [|lia].
          eexists _,_,_,_. split_and!; try done.
          * case_decide; [done|naive_solver].
          * case_decide; done.
        + iClear "AU pr Lc a_p↪□ a↪□ IH IHD IsH p↪□ c↪□".
          clear.
          destruct rL as [|[rn γ_rn] rL]; [done|].
          iInduction rL as [|[rn' γ_rn'] rL IH] forall (rn γ_rn a γ_a) "RL".
          * iDestruct "RL" as ([-> ->]) "$". by iFrame "#".
          * iDestruct "RL" as (an' γ_an' [-> ->]) "($ & RL)".
            iSplit; [done|]. iApply "IH". iFrame.
      - iEval (rewrite bool_decide_eq_true_2; [|done]).
        wp_pures.

        iApply ("IH" $! (Some (a_p,_)) (Some (prev,_)) _ curr c_n 1%Z (rL ++ [(curr,γ_curr)])
        with "[%] a_pS pS cS aS [#] AU [# //] [# //] [# //]").
        + clear Ha_curr. erewrite decide_False; [|lia].
          eexists _,_,_,_. split_and!; try done.
          * case_decide; [done|naive_solver].
          * case_decide; done.
        + iClear "AU pr Lc a_p↪□ a↪□ IH IHD IsH p↪□ c↪□".
          subst γ_a. clear.
          destruct rL as [|[rn γ_rn] rL]; [done|].
          iInduction rL as [|[rn' γ_rn'] rL IH] forall (rn γ_rn prev γ_prev) "RL".
          * iDestruct "RL" as ([-> ->]) "$". by iFrame "#".
          * iDestruct "RL" as (an' γ_an' [-> ->]) "($ & RL)".
            iSplit; [done|]. iApply "IH". iFrame.
    }

    iInv "IsH" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
    iMod (lc_fupd_elim_later with "Lc Nodes") as "Nodes".
    iAssert (
      if decide (c_k < k)%inf_Z then ∃ γ_c_n c_n c_n_k, ⌜c_on = Some (c_n,γ_c_n)⌝ ∧ γ_c_n ↪[γp_a]□ (c_n_k, c_n) else True
    )%I as "#c_n↪□".
    { destruct (decide (c_k < k)%inf_Z); [|done].
      iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_c.
      iDestruct (get_persistent_AllPtrs with "PTRS") as "#[c.n|%HLc]"; [exact Hptrs_c| |].
      { iDestruct "c.n" as (???) "[c.n↪□ _]".
        iDestruct (ghost_map_elem_agree with "c.n↪ c.n↪□") as %[= ?].
      }
      apply elem_of_list_lookup in HLc as [idx_c HLc].
      iDestruct (Nodes_remove with "Nodes") as (?) "[(cM & _ & c.n↪' & %HLc_next) Nodes]"; [exact HLc|]; simpl.
      iDestruct (ghost_map_elem_agree with "c.n↪ c.n↪'") as %[= <-].
      destruct (next_not_tail_is_Some idx_c L c_k false (curr, γ_curr) c_on) as [[c_n γ_c_n] [= ->]]; [naive_solver..|simpl in *].
      apply list_lookup_fmap_Some in HLc_next as [([c_n_k c_n_b]&?&?) [HLc_next [= <- <-]]].
      iDestruct (Nodes_rm_idx_remove with "Nodes") as (c_n_n) "[(c_nM & #c_n↪□ & c_n.n↪ & %HLc_n) Nodes]"; [exact HLc_next|lia|].
      by iFrame "c_n↪□".
    }

    iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { by iFrame "∗#%". } clear dependent p_all p_tag L.
    iModIntro.
    iDestruct (harris_node_combine_on with "c↦ [# //] [% //] [c.n↪]") as "$"; [iLeft; by iFrame|].
    clear dependent c_b.

    wp_pures.

    wp_bind (!_)%E.
    iInv "cS" as (lv _) "(c↦ & >node & cS)".
    iDestruct (harris_node_destruct_agree with "node [# //]") as (c_on' c_t' ->) "[% c.n↪]".
    wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
    iDestruct (harris_node_combine_on with "c↦ [# //] [% //] c.n↪") as "$".
    iModIntro. wp_pures.
    clear dependent c_on' c_t'.

    case_bool_decide as GE.
    { wp_pures.
      iEval (erewrite decide_True; [|done]) in "c_n↪□".
      iDestruct "c_n↪□" as (??? ->) "c_n↪□".
      iSimpl.
      iApply ("IH" $! None None 0 curr c_n 0 [] with "[%] a_pS aS cS pS [# //] AU [# //] [# //] [# //]").
      erewrite decide_True; done.
    }
    iClear "c_n↪□".
    wp_pure credit: "Lc". wp_pures.

    wp_bind (CmpXchg _ _ _).

    iInv "a_pS" as (lv _) "(a_p↦ & >node & a_pS)".
    clear Ho_a.
    iDestruct (harris_node_destruct_agree with "node [# //]") as (o_a a_t ->) "[%Ho_a [[% a_p.n↪]|[% #a_p.n↪□]]]"; last first; subst a_t; simpl in *.
    { (* anchor tagged, cas must fail. *)
      wp_apply (wp_cmpxchg_fail_offset with "a_p↦") as "a_p↦"; [by simplify_list_eq|naive_solver..|].
      iModIntro. iDestruct (harris_node_combine_on with "a_p↦ [# //] [% //] []") as "$"; [by iRight; iFrame "#"|].
      wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "IHD a_pS") as "_"; [solve_ndisj|]; wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "IHD aS") as "_"; [solve_ndisj|]; wp_pures.
      iMod "AU" as (?) "[Labs [_ Commit]]".
      iMod ("Commit" $! false _ false prev curr 0 0 0 γ_prev γ_prev _ with "[$Labs]") as "HΦ"; [done|].
      iApply "HΦ". iModIntro. iFrame.
    }
    iInv "IsH" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
    iMod (lc_fupd_elim_later with "Lc Nodes") as "Nodes".
    iDestruct (ghost_map_lookup with "●p_all a_p↪□") as %Hptrs_a_p.
    iDestruct (get_persistent_AllPtrs with "PTRS") as "#[a_p|%HLa_p]"; [exact Hptrs_a_p| |].
    { iDestruct "a_p" as (???) "[a_p.n↪□ _]".
      iDestruct (ghost_map_elem_agree with "a_p.n↪□ a_p.n↪") as %[= ? ?].
    }
    apply elem_of_list_lookup in HLa_p as [idx_a_p HLa_p].
    iDestruct (Nodes_remove with "Nodes") as (o_a') "[(a_pM &_& a_p.n↪' & %HLa) Nodes]"; [exact HLa_p|simpl in *].
    (* TODO: fix next_not_tail_is_Some, it shouldn't need next index. Although, we may need it for unification. *)
    destruct (next_not_tail_is_Some idx_a_p L a_p_k false (a_p, γ_a_p) o_a') as [[a' γ_a'] [= ->]]; [naive_solver..|simpl in *].
    iDestruct (ghost_map_elem_agree with "a_p.n↪ a_p.n↪'") as %[= ->]; simpl in *.

    specialize HLa as HLa_2.
    apply list_lookup_fmap_Some in HLa as [[[a_k' a_t] ?] [HLa [= <-]]].
    iDestruct (Nodes_rm_idx_remove with "Nodes") as (?) "[(aM & #a↪□' & a.n↪ & %HLan) Nodes]"; [exact HLa|lia|].

    destruct (decide (a' = a)) as [->|NE_a]; last first.
    { wp_apply (wp_cmpxchg_fail_offset with "a_p↦") as "a_p↦"; [by simplify_list_eq|naive_solver..|].
      iDestruct (Nodes_rm_idx_combine with "Nodes aM [# //] a.n↪") as "Nodes"; [done..|lia|].
      iDestruct (Nodes_combine with "Nodes a_pM [# //] [a_p.n↪']") as "Nodes"; [done..|].
      iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
      { by iFrame "∗#%". } clear dependent p_all p_tag L.
      iModIntro. iDestruct (harris_node_combine_some with "a_p↦ [# //] [a_p.n↪]") as "$"; [iLeft; by iFrame|].
      wp_pures.
      iApply ("IH" $! None None 0 a_p a' 0 [] with "[%] aS cS a_pS pS [# //] AU [# //] [# //] [# //]").
      erewrite decide_True; done.
    }
    wp_apply (wp_cmpxchg_suc_offset with "a_p↦") as "a_p↦"; [by simplify_list_eq|naive_solver..|simpl in *].

    iAssert (⌜(if decide (a = prev) then γ_prev else γ_a) = γ_a'⌝)%I as %<-.
    { destruct (decide (a = prev)) as [<-|Ha_prev].
      - by iDestruct (hazptr.(shield_managed_agree) with "pS aM") as %<-.
      - by iDestruct (hazptr.(shield_managed_agree) with "aS aM") as %<-.
    }
    iDestruct (ghost_map_elem_agree with "a↪□ a↪□'") as %[= <-].
    iClear "a↪□'".
    iDestruct (Nodes_rm_idx_combine with "Nodes aM [# //] a.n↪") as "Nodes"; [done..|lia|].

    (* Get info about curr *)
    rewrite -Hγ_a in HLa_2.
    iDestruct (RetireChain_in_list with "RL Nodes") as %ElemOfL; [exact HLa_2|lia|].
    iDestruct (RetireChain_curr with "RL Nodes") as %HLc; [exact HLa_2|lia|].
    apply list_lookup_fmap_Some in HLc as [[[? c_t] ?] [HLc [= <-]]].
    iAssert (⌜length rL ≠ 0⌝)%I as %GT.
    { iIntros (Len0). by apply length_zero_iff_nil in Len0 as ->. }
    destruct a_t; last first.
    { exfalso. have [[a' γ_a'] HrLa'] : (is_Some (rL !! 0)).
      { apply lookup_lt_is_Some. lia. }
      specialize (ElemOfL _ _ _ HrLa') as [? HLa'].
      rewrite Nat.add_0_r in HLa'.
      rewrite HLa' in HLa. injection HLa as [= _ HF _ _].
      done.
    }
    (* Get pure facts. *)
    set (idx_c := idx_a_p + 1 + length rL) in *.
    set (L' := take (idx_a_p + 1) L ++ drop (idx_c) L).
    assert (idx_a_p + 1 ≤ length L); [apply lookup_lt_Some in HLa; lia|].
    assert (length (take (idx_a_p + 1) L) = idx_a_p + 1) as EQtake; [rewrite length_take_le; done|].
    assert (get_abs_state L = get_abs_state L') as ->.
    { rewrite -(take_drop (idx_a_p + 1 + length rL) L). subst L'. rewrite !get_abs_state_app. f_equal.
      rewrite -{1}(take_drop (idx_a_p + 1) L) take_app_add'; [|done].
      rewrite get_abs_state_app -{2}(app_nil_r (get_abs_state (take (idx_a_p + 1) L))). f_equal.
      apply length_zero_iff_nil, dec_stable.
      intros [n_k ElemOf%elem_of_list_lookup_2]%Nat.neq_0_lt_0%lookup_lt_is_Some.
      unfold get_abs_state in ElemOf.
      do 2 apply elem_of_list_fmap_2 in ElemOf as [[? ?] [[= <-] ElemOf]].
      apply elem_of_list_filter in ElemOf as [Hn [i_n_L [HL_n Hi_n_L]]%elem_of_take].
      rewrite lookup_drop in HL_n.
      have [[n i_n] HrLn] : is_Some (rL !! i_n_L).
      { by apply lookup_lt_is_Some. }
      specialize (ElemOfL n i_n i_n_L HrLn) as [n_k' HL_n'].
      rewrite HL_n in HL_n'. injection HL_n' as [= -> -> ->]. naive_solver.
    }
    (* Break-up Nodes *)
    iDestruct (Nodes_rm_idx_remove with "Nodes") as (c_n) "[(cM & #c↪□' & c.n↪ & %HLc_n) Nodes]"; [exact HLc|lia|].
    iDestruct (ghost_map_elem_agree with "c↪□ c↪□'") as %[= <-]; iClear "c↪□'".
    iEval (unfold Nodes_rm_idx_idx; rewrite (big_sepL_take_drop _ L idx_c)) in "Nodes".
    iDestruct "Nodes" as "[NodesTake NodesDrop]".
    iEval (rewrite -{2}(take_drop (idx_a_p + 1) L) take_app_add'; [|done]) in "NodesTake".
    iDestruct "NodesTake" as "[NodesTake Ms]".
    iEval (rewrite Nat.add_1_r (take_S_r _ _ (a_p_k,false,(a_p,γ_a_p))); [|exact HLa_p]) in "NodesTake".
    iDestruct "NodesTake" as "[NodesTake _]".
    iEval (rewrite (drop_S _ (c_k, c_t, (curr, γ_curr))); [|exact HLc]) in "NodesDrop".
    iDestruct "NodesDrop" as "[_ NodesDrop]".
    rewrite -Hγ_a in HLa.
    iEval (rewrite (drop_S _ (a_k,true,(a,γ_a))); [|exact HLa]) in "Ms".
    iEval (rewrite (take_cons' (a_k,true,(a,γ_a))); [|lia]) in "Ms".
    (* Update anchor state and get rest of managed. *)
    iDestruct "Ms" as "[a Ms]". rewrite !EQtake !Nat.add_0_r.
    iEval (rewrite !decide_False; [|lia..]) in "a".
    iDestruct "a" as (a_n) "(aM & #a↪□' & #a.n↪□ & %HLa_n)".

    iDestruct (create_delete_chain with "[a.n↪□] RL aM [Ms]") as "Chain"; [done..| |].
    { iApply (big_sepL_mono with "Ms"). iIntros (?? Ht) "H".
      apply lookup_lt_Some in Ht. rewrite length_take_le in Ht; last first.
      { rewrite length_drop. assert (idx_a_p + 1 + length rL - 1 < length L); [|lia].
        apply lookup_lt_is_Some.
        have [[r i_r] HrL] : is_Some (rL !! (length rL -1)).
        { rewrite lookup_lt_is_Some. lia. }
        specialize (ElemOfL _ _ _ HrL) as [r_k HL_r].
        exists (r_k,true,(r,i_r)). rewrite -HL_r. f_equal. lia.
      }
      iEval (rewrite !decide_False; [|lia..]) in "H".
      iFrame.
    }

    iCombine "a_p.n↪ a_p.n↪'" as "a_p.n↪".
    iMod (ghost_map_update (Some (curr,γ_curr), false) with "●p_tag a_p.n↪") as "[●p_tag [a_p.n↪ a_p.n↪']]".
    iAssert (if c_t then γ_curr ↪[ γp_t ]□ (c_n, true) else True)%I as "#c.n↪□". { destruct c_t; by iFrame. }
    (* Close invariant early *)
    iAssert (ghost_var γl (1 / 2) (get_abs_state L')
            -∗ ▷ HListInternalInv h γp_a γp_t γl γh γz)%I with "[●p_all ●p_tag NodesTake NodesDrop PTRS a_p.n↪' a_pM c↪□ c.n↪ cM]" as "INV".
    { iIntros "Linv !>". iFrame "Linv ∗#%".
      unfold AllPtrs, Nodes. iSplitL "PTRS"; [|iSplit].
      - iApply (big_sepM_mono with "PTRS").
        iIntros (i_n [n_k n] Hptrs_n) "[$ [$|%HLn]]".
        iRight. iPureIntro. apply elem_of_app.
        rewrite -(take_drop (idx_a_p + 1 + length rL) L) in HLn.
        apply elem_of_app in HLn as [HLn|HLn]; [left|by right].
        rewrite -(take_drop (idx_a_p + 1) L) take_app_add' in HLn; [|done].
        apply elem_of_app in HLn as [HLn|[i_n_L [HL_n Hi_n_L]]%elem_of_take]; [done|exfalso].
        rewrite lookup_drop in HL_n.
        apply lookup_lt_is_Some in Hi_n_L as [[n' i_n'] HrLn].
        specialize (ElemOfL n' i_n' i_n_L HrLn) as [n_k' HL_n'].
        rewrite HL_n in HL_n'. clear -HL_n'. naive_solver.
      - subst L'.
        iEval (rewrite {2}Nat.add_1_r (take_S_r _ _ (a_p_k,false,(a_p,γ_a_p))); [|exact HLa_p]).
        rewrite !big_sepL_app big_sepL_singleton /=.
        iSplitR "NodesDrop cM c↪□ c.n↪"; [iSplitR "a_pM a_p.n↪'"|].
        + iApply (big_sepL_mono with "NodesTake"). iIntros (idx_n [[n_k b_n] [l_n i_n]] HLn) "LN".
          assert (idx_n < idx_a_p) as LT; [|repeat (case_decide; [lia|])].
          { apply lookup_lt_Some in HLn as LT_take. rewrite length_take_le in LT_take; [lia|].
            apply lookup_lt_Some in HLa. lia.
          }
          iEval (rewrite !decide_False; [|lia..]) in "LN".
          iDestruct "LN" as (on) "(nM & $ & l_n.n↪ & %HLl_n)".
          iFrame. iPureIntro.
          rewrite !fmap_app lookup_app_l; last first.
          { rewrite /= length_fmap length_take_le /=; lia. }
          rewrite fmap_take lookup_take; [done|lia].
        + unfold ListNode. iExists (Some (curr,γ_curr)).
          simpl in *. iFrame "∗#". iPureIntro.
          rewrite fmap_app lookup_app_r length_fmap !length_take_le; [|lia..].
          get_third HLc. rewrite fmap_drop lookup_drop -HLc. f_equal. lia.
        + iEval (rewrite (drop_S _ (c_k, c_t, (curr, γ_curr))) /=; [|exact HLc]). iSplitR "NodesDrop"; last first.
          { iApply (big_sepL_mono with "NodesDrop"). iIntros (idx_n [[n_k b_n] [l_n i_l_n]] HLn) "LN".
            iEval (rewrite !decide_False; [|lia..]) in "LN".
            iDestruct "LN" as (on) "(l_nM & $ & l_n.n↦ & %HLl_n)".
            iExists on. iFrame. iPureIntro.
            rewrite fmap_app fmap_cons lookup_app_r length_app /= length_fmap !length_take_le /=; try lia.
            rewrite lookup_cons_ne_0; [|lia]. rewrite fmap_drop lookup_drop -HLl_n. f_equal. lia.
          }
          rewrite Nat.add_0_r length_app length_take_le /=; [|lia]. iExists c_n. iFrame "∗#%".
          iPureIntro.
          rewrite fmap_app fmap_cons lookup_app_r /= length_fmap !length_take_le /=; try lia.
          rewrite lookup_cons_ne_0; [|lia]. rewrite fmap_drop lookup_drop -HLc_n. f_equal. lia.
      - iPureIntro. subst L'. split_and!.
        + rewrite !fmap_app !fmap_take !fmap_drop. apply take_drop_inf_Z_sorted; [lia|done].
        + rewrite lookup_app_l; [|lia]. rewrite lookup_take; [done|lia].
        + destruct HLt as [t HLt]. exists t.
          rewrite lookup_app_r /= !length_app /= !length_take_le /=; try lia.
          all: rewrite length_drop; apply lookup_lt_Some in HLc; try lia.
          rewrite lookup_drop -HLt. f_equal. lia.
        + rewrite dom_insert_lookup_L; [done|]. rewrite -elem_of_dom -Hdom elem_of_dom. eauto.
    }
    (* See if tag check on curr will succeed. *)
    destruct (decide (prophecy_to_bool pvs')) as [NotCommit|Hpr_v%Is_true_false].
    { (* Tagged, do not commit. *)
      iModIntro. iSplitL "Linv INV"; [iApply "INV"; iFrame|].
      iModIntro. iDestruct (harris_node_combine_some with "a_p↦ [# //] [a_p.n↪]") as "$"; [iLeft; by iFrame|].
      clear dependent L p_all p_tag. wp_pures.

      wp_bind (Resolve _ _ _)%E.
      iInv "cS" as (lv _) "(c↦ & >node & cS)".
      iDestruct (harris_node_destruct_agree with "node [# //]") as (? c_t' ->) "[% c.n↪]".
      wp_apply (wp_resolve_load_offset with "[$pr $c↦]") as (?) "(%EQ & _ & c↦)"; [by simplify_list_eq|].
      subst pvs'; simpl in *.

      iDestruct "c.n↪" as "[[% c.n↪]|[% #c.n↪□']]"; subst c_t'; first inv NotCommit.
      iModIntro.
      iDestruct (harris_node_combine_on with "c↦ [# //] [% //] []") as "$"; [by iRight; iFrame "#"|].
      wp_pures.

      wp_apply (chain_retire_spec with "[$IHD $Chain]") as "_"; [solve_ndisj|]; wp_pures.

      iApply ("IH" $! None None 0 a_p curr 0 [] with "[%] aS cS a_pS pS [# //] AU [# //] [# //] [# //]").
      erewrite decide_True; done.
    }
    (* Assert that we are not tagged *)
    destruct c_t.
    { (* Tagged, impossible. *)
      iModIntro. iSplitL "Linv INV"; [iApply "INV"; iFrame|].
      iModIntro. iDestruct (harris_node_combine_some with "a_p↦ [# //] [a_p.n↪]") as "$"; [iLeft; by iFrame|].
      clear dependent L p_all p_tag. wp_pures.

      wp_bind (Resolve _ _ _)%E.
      iInv "cS" as (lv _) "(c↦ & >node & cS)".
      iDestruct (harris_node_destruct_agree with "node [# //]") as (? c_t' ->) "[% c.n↪]".
      wp_apply (wp_resolve_load_offset with "[$pr $c↦]") as (?) "(%EQ & _ & c↦)"; [by simplify_list_eq|].
      subst pvs'; simpl in *.

      iDestruct "c.n↪" as "[[% c.n↪]|[% #c.n↪□']]"; subst c_t'; last inv Hpr_v.
      iDestruct (ghost_map_elem_agree with "c.n↪ c.n↪□") as %[= ? ?].
    }

    (* Commit *)
    iMod "AU" as (?) "[[Labs %HLabs] [_ Commit]]".
    iDestruct (ghost_var_agree with "Labs Linv") as %->.
    set (idx' := length (get_abs_state (take idx_a_p L))).
    iMod ("Commit" $! true _ (bool_decide (c_k = k)) a_p curr _ _ idx' with "[$Labs]") as "HΦ".
    { iFrame "∗#%". iSplit; [done|]. iPureIntro. split_and!; auto; last first.
      { case_bool_decide as EQN; [done|]. destruct c_k as [|c_k|]; [naive_solver| |naive_solver].
        simpl in *. apply inf_Z.Z_lt_lt,Z.lt_nge => ?.
        apply GE,inf_Z.Z_lt_lt,Z.lt_nge => ?.
        apply EQN. f_equal. lia.
      }
      all: rewrite !get_abs_state_app /= Nat.add_1_r (take_S_r _ _ (a_p_k,false,(a_p,γ_a_p))); simplify_list_eq; auto.
      - rewrite lookup_app_r get_abs_state_snoc length_app /=; [|lia]. fold idx'.
        replace (S idx' - (idx' + 1)) with 0 by lia.
        erewrite (drop_S L (c_k, false, (curr,_))); [|done].
        by rewrite get_abs_state_cons.
      - rewrite lookup_app_l get_abs_state_snoc; last first.
        { rewrite length_app /=. lia. }
        subst idx'. by rewrite snoc_lookup.
    }
    iModIntro. iSplitL "Linv INV"; [iApply "INV"; iFrame|].
    iModIntro. iDestruct (harris_node_combine_some with "a_p↦ [# //] [a_p.n↪]") as "$"; [iLeft; by iFrame|].
    clear dependent L p_all p_tag. wp_pures.

    wp_bind (Resolve _ _ _)%E.
    iInv "cS" as (lv _) "(c↦ & >node & cS)".
    iDestruct (harris_node_destruct_agree with "node [# //]") as (? c_t' ->) "[% c.n↪]".
    wp_apply (wp_resolve_load_offset with "[$pr $c↦]") as (?) "(%EQ & _ & c↦)"; [by simplify_list_eq|].
    subst pvs'; simpl in *.

    iDestruct "c.n↪" as "[[% c.n↪]|[% #c.n↪□']]"; subst c_t'; last inv Hpr_v.
    iModIntro.
    iDestruct (harris_node_combine_on with "c↦ [# //] [% //] [c.n↪]") as "$"; [by iLeft; iFrame|].
    wp_pures.

    wp_apply (chain_retire_spec with "[$IHD $Chain]") as "_"; [solve_ndisj|]; wp_pures.

    wp_apply (hazptr.(shield_drop_spec) with "IHD pS") as "_"; [solve_ndisj|]; wp_pures.
    wp_apply (hazptr.(shield_drop_spec) with "IHD aS") as "_"; [solve_ndisj|]; wp_pures.

    iApply "HΦ". iModIntro. iFrame. done.
Qed.

Lemma harris_find_spec :
  harris_find_spec' listN hazptrN hazptr (harris_find hazptr).
Proof using All.
  intros E k h γp_a γp_t γl i_h γr l d p_sh c_sh p_st c_st HE.
  iIntros "#IHD pS cS #l.h↦□ #h↪□ #IsH" (Φ).
  set AtU := (AtU in (AtU -∗ _)%I).
  iIntros "AU".
  iLöb as "IH" forall (p_sh c_sh p_st c_st) "pS cS".
  wp_lam. wp_pure credit: "Lc". wp_pure credit: "Lc'". wp_pures.
  wp_load. wp_pures. wp_bind (! _)%E.
  iInv "IsH" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
  iMod (lc_fupd_elim_later with "Lc Nodes") as "Nodes".
  iDestruct (Nodes_remove with "Nodes") as (h_on) "[(hM & _ & h.n↪ & %HLh_n) Nodes]"; [exact HLh|]; simpl in *.
  iInv "hM" as (?) "(_ & h↦ & >node & hM)".
  iDestruct (harris_node_destruct_agree with "node [//]") as (? h_t ->) "[% [[% h.n↪']|[% #h.n↪']]]"; subst h_t.
  all: iDestruct (ghost_map_elem_agree with "h.n↪ h.n↪'") as %[= <-].
  wp_apply (wp_load_offset with "h↦") as "h↦"; [by simplify_list_eq|].
  iDestruct (Nodes_combine with "Nodes hM [# //] [h.n↪']") as "Nodes"; [done..|].
  assert (1 < length L) as [[[c_k c_b] [c γ_c]] HLh_n']%lookup_lt_is_Some.
  { assert (0 < length L); [by apply lookup_lt_Some in HLh|].
    assert (1 ≠ length L); [|lia]. intros L_EQ. destruct HLt as [t HLt].
    rewrite L_EQ Nat.sub_diag in HLt. naive_solver.
  }
  assert (h_on = Some (c,γ_c)) as ->; simpl. { get_third HLh_n'. naive_solver. }
  iDestruct (get_persistent_Nodes with "Nodes") as (h_on) "#(c↪□ & _)"; [exact HLh_n'|].
  iModIntro. iDestruct (harris_node_combine_some with "h↦ [# //] [h.n↪]") as "$"; [iLeft; by iFrame|].
  iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
  { by iFrame "∗#%". }
  rewrite HLh_n /=. clear dependent p_all p_tag L h_on c_b.
  wp_pures.
  wp_apply (hazptr.(shield_set_spec) (Some _) with "IHD pS") as "pS"; [solve_ndisj|].
  wp_apply (fupd_wp).
  iInv "IsH" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
  iMod (lc_fupd_elim_later with "Lc' Nodes") as "Nodes".
  iDestruct (Nodes_remove with "Nodes") as (h_on) "[(hM & _ & h.n↪ & %HLh_n) Nodes]"; [exact HLh|]; simpl in *.
  iMod (hazptr.(shield_validate) with "IHD hM pS") as "[hM pS]"; [solve_ndisj|].
  iDestruct (Nodes_combine with "Nodes hM [] [h.n↪]") as "Nodes"; [done..|].
  iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
  { by iFrame "∗#%". }
  clear dependent p_all p_tag L h_on.
  iModIntro.
  wp_pures.
  wp_apply (hazptr.(shield_new_spec) with "IHD [//]") as (a_p_s) "a_pS" ; [solve_ndisj|]; wp_pures.
  wp_apply (hazptr.(shield_new_spec) with "IHD [//]") as (a_s) "aS" ; [solve_ndisj|]; wp_pures.
  awp_apply (harris_find_inner_spec None None 0 with "IHD a_pS aS pS cS [# //] [# //] [# //] [//] [//]"); [done..|].

  iApply (aacc_aupd with "AU"); [done|].
  iIntros (L) "HList". iAaccIntro with "HList"; first eauto with iFrame.
  iIntros ([] ???????????) "(-> & HList & Commit)"; last first.
  { iModIntro. iLeft. iFrame. iIntros "AU !> Post".
    iDestruct "Post" as (?? _) "[pS cS]".
    wp_pures. wp_apply ("IH" with "AU pS cS").
  }
  iDestruct "Commit" as "(#ret_p↪□ & #ret_c↪□ & Post)".
  iModIntro. iRight. iFrame "Post ∗#%". iExists _,_.
  iIntros "HΦ !> Post". iDestruct "Post" as (?? [-> ->]) "[pS cS]".
  wp_pures. iApply ("HΦ" with "[$pS $cS]").
Qed.

End harris_find.

Definition harris_code_impl (hazptr : hazard_pointer_code) : code_harris_operations.harris_find_code := {|
  code_harris_operations.harris_find := harris_find hazptr;
|}.

Program Definition harris_impl Σ listN hazptrN (DISJN : listN ## hazptrN) `{!heapGS Σ, !hlG Σ} (hazptr : hazard_pointer_spec Σ hazptrN) : hfind_spec Σ listN hazptrN DISJN hazptr := {|
  proof_harris_operations.harris_find_spec_code := harris_code_impl hazptr.(hazard_pointer_spec_code);
|}.
Next Obligation. intros. apply harris_find_spec. done. Qed.
