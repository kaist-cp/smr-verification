From iris.base_logic.lib Require Import invariants ghost_var ghost_map.
From smr.program_logic Require Import atomic.
From smr.lang Require Import lang proofmode notation.
From smr Require Import sorted_list.

From smr Require Import helpers ebr.spec_rcu_traversal ebr.code_harris_operations ebr.code_harris_find.
From smr.ebr Require Export proof_harris_operations.
From iris.prelude Require Import options.

(* TODO:
  1. Combine proof of initial stage of find_inner.
  2. Combine proof of initial stage of find.
  3. Fix 20+ variable order in functions to make more sense.
  4. More helper lemmas for pure parts, e.g, when closing invariants.
*)

Section harris_find.
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

Lemma harris_find_inner_wrong_proph E (d g : loc) γg (prev curr : blk) i_c cn (k : Z) (pr_tag : proph_id) pr_v_tag Φ (anchor : tagged_loc) γp_a γp_t γr :
  ↑listN ∪ ↑rcuN ⊆ E →
  prophecy_to_bool pr_v_tag = false →
  proph pr_tag pr_v_tag -∗
  rcu.(RCUNodeInfo) γr γg curr i_c (harris_type γp_a γp_t γr) -∗
  i_c ↪[γp_t]□ (cn, true) -∗
  rcu.(Guard) γr γg g -∗
  WP (harris_find_inner rcu) #pr_tag #d #k #prev #curr #anchor @ E {{ v, Φ v}}.
Proof.
  iIntros (? Hpr) "pr #cInfo #c.n↪□ G".
  wp_lam. wp_pures.
  wp_apply (wp_new_proph with "[//]") as (??) "_". wp_pures.
  wp_bind (!_)%E.
  iInv "cInfo" as (lv) "(c↦ & node & G)".
  iDestruct (harris_node_destruct with "node") as (c_k c_on c_t) "(>% & #? & c.n↪rcu & >[[% c.n↪]|[% c.n↪]])"; subst c_t lv.
  all: wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
  all: iDestruct (ghost_map_elem_agree with "c.n↪□ c.n↪") as %[= ->]; iClear "c.n↪".
  iModIntro. iDestruct (harris_node_combine_on with "c↦ [//] c.n↪rcu [$c.n↪□]") as "$"; [by iRight|].
  wp_pures.
  wp_apply (wp_resolve_proph with "pr") as (pvs') "[%Heq _]".
  subst pr_v_tag. inversion Hpr.
Qed.

Fixpoint RetireChain γp_t anchor i_a ret_curr i_r_c (rL : list (blk * positive)) : iProp :=
  match rL with
  | [] => False
  | [(p,i_p)] => ⌜p = anchor ∧ i_p = i_a⌝ ∗ i_p ↪[γp_t]□ (Some (ret_curr,i_r_c), true)
  | (p,i_p)::rL' => ∃ (anchor' : blk) (i_a' : positive),
            ⌜p = anchor ∧ i_p = i_a⌝ ∗ i_p ↪[γp_t]□ (Some (anchor',i_a'), true) ∗
            RetireChain γp_t anchor' i_a' ret_curr i_r_c rL'
  end.

Local Lemma RetireChain_in_list anchor i_a curr i_c rL L idx_a idx γp_a γp_t γr :
  L.*2 !! idx_a = Some (anchor,i_a) →
  idx < idx_a →
  RetireChain γp_t anchor i_a curr i_c rL -∗
  Nodes_rm_idx idx L γp_a γp_t γr -∗
  ⌜∀ r i_r (idx : nat), rL !! idx = Some (r,i_r) → ∃ (r_k : inf_Z), L !! (idx_a + idx)%nat = Some (r_k, true, (r,i_r))⌝.
Proof.
  iIntros (HLa LT) "RChain Nodes". iIntros (r i_r idx_r Hr).
  destruct rL as [|[rn i_rn] rL]; try done.
  iInduction rL as [|[rn' i_rn'] rL] "IH" forall (anchor i_a rn i_rn idx_r Hr idx_a LT HLa).
  - iDestruct "RChain" as ([[= ->] [= ->]]) "#an.n↪□".
    specialize HLa as HLa'.
    apply list_lookup_fmap_Some in HLa as [[[a_k []] ?] [HLa [= <-]]]; last first.
    { iDestruct (Nodes_rm_idx_remove with "Nodes") as (??) "[(_&_&an.n↪&_&_) _]"; [exact HLa|lia|]; simpl.
      by iDestruct (ghost_map_elem_agree with "an.n↪□ an.n↪") as %[= ? ?].
    }
    iDestruct (get_persistent_Nodes_rm_idx with "Nodes") as (an_n an_p) "#(_& an.n↪ & %Han_n & %Han_p)"; [exact HLa|lia|].
    simpl. iDestruct (ghost_map_elem_agree with "an.n↪□ an.n↪") as %[= <-]; iClear "an.n↪".
    destruct idx_r; last first.
    { apply lookup_lt_Some in Hr. simpl in *. lia. }
    injection Hr as [= <- <-]. iPureIntro. rewrite Nat.add_0_r. eauto.
  - iDestruct "RChain" as (an' i_an') "(%EQ & #an.n↪□ & RChain)". destruct EQ as [-> ->].
    fold (RetireChain γp_t an' i_an' curr i_c ((rn',i_rn') :: rL)).
    apply list_lookup_fmap_Some in HLa as [[[a_k []] ?] [HLa [= <-]]]; last first.
    { iDestruct (Nodes_rm_idx_remove with "Nodes") as (??) "[(_&_&an.n↪&_) _]"; [exact HLa|lia|]; simpl.
      by iDestruct (ghost_map_elem_agree with "an.n↪□ an.n↪") as %[= ? ?].
    }
    iDestruct (get_persistent_Nodes_rm_idx with "Nodes") as (an_n an_p) "#(_& an.n↪ & %Han' & %Han'_p)"; [exact HLa|lia|].
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
        iDestruct (Nodes_rm_idx_remove with "Nodes") as (??) "[(_&_&an'.n↪&_) _]"; [exact Han'|lia|]; simpl.
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
  iInduction rL as [|[rn' i_rn'] rL] "IH" forall (rn i_rn anchor i_a idx_a LT HLa).
  { iDestruct (RetireChain_in_list with "RChain Nodes") as %ElemOfL; [exact HLa|lia|].
    simpl in *. iDestruct "RChain" as ([<- <-]) "rn.n↪".
    specialize (ElemOfL _ _ 0 ltac:(done)) as [a_k HLan].
    iDestruct (get_persistent_Nodes_rm_idx with "Nodes") as (??) "#(_ & rn.n↪' & %Hrn_n & %Hrn_p)"; [exact HLan|lia|simpl].
    iDestruct (ghost_map_elem_agree with "rn.n↪ rn.n↪'") as %[= <-]; iClear "rn.n↪'".
    iPureIntro. by rewrite -Hrn_n Nat.add_0_r.
  }
  iDestruct (RetireChain_in_list with "RChain Nodes") as %ElemOfL; [exact HLa|lia|].
  iDestruct "RChain" as (rn_n i_rn_n [<- <-]) "(rn.n↪ & RChain)". fold RetireChain.
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

Fixpoint DeletedChain γp_a γp_t γr anchor i_a ret_curr i_r_c (rL : list (blk * positive)) : iProp :=
  match rL with
  | [] => ⌜anchor = ret_curr ∧ i_a = i_r_c⌝
  | (p,i_p)::rL' => ∃ (anchor' : blk) (i_a' : positive),
      ⌜p = anchor ∧ i_p = i_a⌝ ∗ i_p ↪[γp_t]□ (Some (anchor',i_a'), true) ∗
      rcu.(Deleted) γr p i_p (harris_type γp_a γp_t γr) ∗
      DeletedChain γp_a γp_t γr anchor' i_a' ret_curr i_r_c rL'
  end.

Lemma create_delete_chain idx_p γp_a γp_t γr a_k anchor i_a curr i_c rL L E b (o_an : option (blk * positive)) d :
  ↑mgmtN rcuN ⊆ E →
  (∃ tit, L !! (length L - 1) = Some (∞ᵢ, false, tit)) →
  L !! (idx_p + 1) = Some (a_k, b, (anchor, i_a)) →
  L.*2 !! (idx_p + 1 + 1) = o_an →
  rcu.(IsRCUDomain) γr d -∗
  (if (b : bool) then i_a ↪[ γp_t ]□ (o_an, true) else i_a ↪[γp_t]{#1 / 2} (o_an, false))%I -∗
  RetireChain γp_t anchor i_a curr i_c rL -∗
  rcu.(Deleted) γr anchor i_a (harris_type γp_a γp_t γr) -∗
  ([∗ list] k↦y ∈ take (length rL - 1) (drop (S (idx_p + 1)) L),
      ListNode rcuN rcu (idx_p + 1 + S k) y L γp_a γp_t γr) ={E}=∗
  ∃ c_p i_c_p, rcu.(Deleted) γr c_p i_c_p (harris_type γp_a γp_t γr) ∗ ⌜rL !! (length rL - 1) = Some (c_p, i_c_p)⌝ ∗
  (rcu.(Deleted) γr c_p i_c_p (harris_type γp_a γp_t γr) -∗ DeletedChain γp_a γp_t γr anchor i_a curr i_c rL).
Proof.
  iIntros (? HLt HLa HLan) "#IRD a.n↪ RChain aD Ms". destruct rL as [|[r i_r] rL]; [done|].
  iInduction rL as [|[r' i_r'] rL] "IH" forall (idx_p r i_r a_k anchor i_a o_an b HLa HLan).
  { iModIntro. iDestruct "RChain" as ([-> ->]) "#a.n↪□". iExists anchor,i_a. iFrame.
    iSplit; [done|]. iIntros "aD". iExists curr,i_c. by iFrame "∗#".
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
  iDestruct "Ms" as "[an Ms]". iDestruct "an" as (ann [[a' i_a']|]) "(anM & _ & an.n↪ & %HLann & %HLanp)"; [|lia].
  iSimpl in "anM". destruct HLanp as [_ HLanp]. assert (a' = anchor ∧ i_a' = i_a) as [-> ->].
  { get_third HLa. rewrite Nat.add_1_r Nat.sub_1_r /= HLa in HLanp. by injection HLanp as [= -> ->]. }
  iMod (rcu.(deleted_clean) with "IRD aD anM") as "[aD anM]"; [solve_ndisj|]. rewrite gmultiset_difference_diag.
  iMod (rcu.(managed_delete) with "IRD anM") as "anD"; [solve_ndisj|].
  iAssert (⌜an = r' ∧ i_an = i_r'⌝)%I as %[<- <-].
  { destruct rL; simpl in *.
    - by iDestruct "RChain" as ([-> ->]) "_".
    - by iDestruct "RChain" as (?? [-> ->]) "_".
  }
  iDestruct ("IH" with "[%] [%] an.n↪ RChain anD [Ms]") as ">Rest"; [exact HLan|exact HLann|rewrite !Nat.add_1_r|].
  { iApply (big_sepL_mono with "Ms"). iIntros (???) "?". by rewrite !Nat.add_succ_comm. }
  iDestruct "Rest" as (c_p i_c_p) "(c_pD & %Last & Chain)". iModIntro. iExists c_p, i_c_p. iFrame "c_pD"; iSplit.
  { iPureIntro. rewrite lookup_cons_ne_0; simpl in *; [|lia]. by rewrite Nat.sub_0_r in Last. }
  iIntros "cD". iFrame "aD". iExists an, i_an. do 2 (iSplit; [done|]). by iApply "Chain".
Qed.

Local Lemma get_anchor_spec (o_anchor : option (blk * positive)) (curr c_n : blk) (i_c i_c_n : positive) E rL γp_t :
  {{{ match o_anchor with
      | None => ⌜rL = []⌝
      | Some (anchor,i_a) => RetireChain γp_t anchor i_a curr i_c rL
      end ∗  i_c ↪[γp_t]□ (Some (c_n,i_c_n),true)
  }}}
    get_anchor #((blk_to_loc ∘ fst <$> o_anchor) &ₜ 0) #curr @ E
  {{{ (new_anchor : blk) (i_n_a : positive),
      RET #new_anchor; RetireChain γp_t new_anchor i_n_a c_n i_c_n (rL ++ [(curr,i_c)]) ∗
      ⌜match o_anchor with
      | None => new_anchor = curr ∧ i_n_a = i_c
      | Some (anchor,i_a) => new_anchor = anchor ∧ i_n_a = i_a
      end⌝
  }}}.
Proof.
  iIntros (Φ) "[RChain #c.n↦□] HΦ".
  wp_lam. wp_pures. destruct o_anchor as [[anchor i_a]|]; wp_pures; last first.
  { iApply "HΦ". iDestruct "RChain" as %->. by iFrame "∗#". }
  iModIntro. iApply "HΦ".
  destruct rL as [|[rn i_rn] rL]; [done|].
  iInduction rL as [|[rn' i_rn'] rL] "IH" forall (rn i_rn anchor i_a) "RChain".
  - iDestruct "RChain" as ([-> ->]) "#an'.n↪". iSplit; [|done]. iExists curr,i_c. by iFrame "#".
  - iDestruct "RChain" as (an' i_an' [-> ->]) "(#an.n↪□ & RChain)". fold RetireChain; iSplit; [|done].
    iExists an',i_an'. iFrame "#". iSplit; [done|]. iDestruct ("IH" with "RChain") as "[$ ?]".
Qed.

Local Lemma chain_retire_spec d γp_a γp_t γr anchor i_a curr i_c rL E :
  ↑rcuN ⊆ E →
  {{{ rcu.(IsRCUDomain) γr d ∗ DeletedChain γp_a γp_t γr anchor i_a curr i_c rL }}}
    chain_retire rcu #d #anchor #curr @ E
  {{{ RET #(); True }}}.
Proof.
  iIntros (? Φ) "(#IRD & DChain) HΦ".
  iLöb as "IH" forall (anchor i_a rL).
  wp_lam. wp_pures. case_bool_decide as EQ.
  { wp_pures. by iApply "HΦ". }
  assert (anchor ≠ curr). { naive_solver. }
  destruct rL as [|[r i_r] rL]. { iDestruct "DChain" as %?. naive_solver. }
  iDestruct "DChain" as (a' i_a' [-> ->]) "(#a.n↪□ & aD & DChain)". fold DeletedChain.
  wp_pures. wp_bind (! _)%E.
  iInv "aD" as (lv) "(a↦ & node & aD)".
  iDestruct (harris_node_destruct with "node") as (a_k a_on a_t) "(>% & #a↪□ & a.n↪rcu & >[[% a.n↪]|[% a.n↪]])"; subst lv a_t.
  all: iDestruct (ghost_map_elem_agree with "a.n↪ a.n↪□") as %[= ->]; iClear "a.n↪"; simpl in *.
  wp_apply (wp_load_offset with "a↦") as "a↦"; [by simplify_list_eq|].
  iModIntro. iDestruct (harris_node_combine_some with "a↦ a↪□ a.n↪rcu [$a.n↪□]") as "$"; [by iRight|].
  wp_pures. wp_apply (rcu.(rcu_domain_retire_spec) with "IRD aD") as "_"; [done|by rewrite harris_type_unfold|].
  wp_pures. iApply ("IH" with "DChain HΦ").
Qed.

Lemma harris_helping_cas_spec (committing : bool) rL Φ pr pr_v h γp_a γp_t γl i_h γr γg (d g : loc) (prev anchor curr : blk) p_k c_k i_p i_a i_c (k : Z) E  :
  ↑listN ∪ ↑rcuN ⊆ E →
  (p_k < k)%inf_Z →
  {{{ inv listN (HListInternalInv h γp_a γp_t γl i_h γr) ∗
      rcu.(IsRCUDomain) γr d ∗
      rcu.(RCUNodeInfo) γr γg prev i_p (harris_type γp_a γp_t γr) ∗
      rcu.(RCUNodeInfo) γr γg anchor i_a (harris_type γp_a γp_t γr) ∗
      i_p ↪[ γp_a ]□ (p_k, prev) ∗
      i_c ↪[ γp_a ]□ (c_k, curr) ∗
      RetireChain γp_t anchor i_a curr i_c rL ∗
      (if committing then proph pr pr_v ∗ harris_find_au E γp_a γp_t γl γr k g γg Φ else True) ∗
      rcu.(Guard) γr γg g ∗
      £ 1
  }}}
    CAS #(prev +ₗ next%nat) #anchor #curr @ E
  {{{ (b : bool), RET #b;
      rcu.(Guard) γr γg g ∗
      if (negb committing) then
        (if b then
          DeletedChain γp_a γp_t γr anchor i_a curr i_c rL
        else
          True)
      else
        proph pr pr_v ∗
        (if b then
          DeletedChain γp_a γp_t γr anchor i_a curr i_c rL ∗
          rcu.(RCUNodeInfo) γr γg curr i_c (harris_type γp_a γp_t γr) ∗
          (if decide (prophecy_to_bool pr_v ∨ (c_k < k)%inf_Z) then
            (* CAS success but curr is bad. *)
            harris_find_au E γp_a γp_t γl γr k g γg Φ
          else
            (* CAS success and commit. *)
            (* Impossible case, cause contradiction. *)
            (∃ (c_n : option (blk * positive)), i_c ↪[γp_t]□ (c_n,true)) ∨
            (rcu.(Guard) γr γg g -∗ Φ (#(bool_decide (c_k = k)), #prev, #curr)%V))
        else
          harris_find_au E γp_a γp_t γl γr k g γg Φ)
  }}}.
Proof using All.
  iIntros (? p_k_LT_k Φ') "(#IsHarris & #IRD & #pInfo & #aInfo & #p↪□ & #c↪□ & RChain & prAU & G & Lc) HΦ'".
  wp_bind (CmpXchg _ _ _)%E.
  iInv "pInfo" as (lv) "(p↦ & node & G)".
  iDestruct (harris_node_destruct_agree with "p↪□ node") as (p_on p_t) "(>% & p.n↪rcu & >[[% p.n↪]|[% #p.n↪]])"; last first.
  all: subst lv; subst p_t; simpl in *.
  { (* prev tagged, cas must fail. *)
    wp_apply (wp_cmpxchg_fail_offset with "p↦") as "p↦"; [by simplify_list_eq|naive_solver..|].
    iModIntro. iDestruct (harris_node_combine_on with "p↦ p↪□ p.n↪rcu [$p.n↪]") as "$"; [by iRight|].
    wp_pures. iApply "HΦ'". destruct committing; by iFrame.
  }
  iInv "IsHarris" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
  iMod (lc_fupd_elim_later with "Lc Nodes") as "Nodes".
  iDestruct (ghost_map_lookup with "●p_all p↪□") as %Hptrs_p.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[p|%HLp]"; [exact Hptrs_p| |].
  { iDestruct "p" as (???) "[p.n↪□ _]".
    iDestruct (ghost_map_elem_agree with "p.n↪□ p.n↪") as %[= ? ?].
  }
  apply elem_of_list_lookup in HLp as [idx_p HLp].
  iDestruct (Nodes_remove with "Nodes") as (p_on' p_p) "[(pM &_& p.n↪' & %HLp_n & %HLp_p) Nodes]"; [exact HLp|simpl in *].
  (* TODO: fix next_not_tail_is_Some, it shouldn't need next index. Although, we may need it for unification. *)
  destruct (next_not_tail_is_Some idx_p L p_k false (prev, i_p) p_on') as [[p_n i_p_n] [= ->]]; [naive_solver..|simpl in *].
  iDestruct (ghost_map_elem_agree with "p.n↪ p.n↪'") as %[= ->]; simpl in *.
  destruct (decide (p_n = anchor)) as [->|NE]; last first.
  { wp_apply (wp_cmpxchg_fail_offset with "p↦") as "p↦"; [by simplify_list_eq|naive_solver..|].
    iDestruct (Nodes_combine with "Nodes [pM] [] [p.n↪]") as "Nodes"; [done..|].
    iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    iModIntro. iDestruct (harris_node_combine_some with "p↦ p↪□ p.n↪rcu [p.n↪']") as "$"; [iLeft; by iFrame|].
    wp_pures. iApply "HΦ'". destruct committing; by iFrame.
  }
  wp_apply (wp_cmpxchg_suc_offset with "p↦") as "p↦"; [by simplify_list_eq|naive_solver..|simpl in *].
  specialize HLp_n as HLa_2.
  apply list_lookup_fmap_Some in HLp_n as [[[a_k b] ?] [HLa [= <-]]].
  iDestruct (Nodes_rm_idx_remove with "Nodes") as (??) "[(aM & #a↪□ & a.n↪ & %HLan & %HLap) Nodes]"; [exact HLa|lia|].
  iDestruct (rcu.(guard_managed_agree) with "aInfo G aM") as %<-.
  iDestruct (Nodes_rm_idx_combine with "Nodes aM a↪□ a.n↪") as "Nodes"; [done..|lia|].

  (* Get info about curr *)
  iDestruct (RetireChain_in_list with "RChain Nodes") as %ElemOfL; [exact HLa_2|lia|].
  iDestruct (RetireChain_curr with "RChain Nodes") as %HLc; [exact HLa_2|lia|].
  apply list_lookup_fmap_Some in HLc as [[[? c_b] ?] [HLc [= <-]]].
  iAssert (⌜length rL ≠ 0⌝)%I as %GT.
  { iIntros (Len0). by apply length_zero_iff_nil in Len0 as ->. }
  destruct b; last first.
  { exfalso. have [[a' i_a'] HrLa'] : (is_Some (rL !! 0)).
    { apply lookup_lt_is_Some. lia. }
    specialize (ElemOfL _ _ _ HrLa') as [? HLa'].
    rewrite Nat.add_0_r in HLa'. naive_solver.
  }
  (* Get pure facts. *)
  set (idx_c := idx_p + 1 + length rL) in *.
  set (L' := take (idx_p + 1) L ++ drop (idx_c) L).
  assert (idx_p + 1 ≤ length L); [apply lookup_lt_Some in HLa; lia|].
  assert (length (take (idx_p + 1) L) = idx_p + 1) as EQtake; [rewrite take_length_le; done|].
  assert (get_abs_state L = get_abs_state L') as ->.
  { rewrite -(take_drop (idx_p + 1 + length rL) L). subst L'. rewrite !get_abs_state_app. f_equal.
    rewrite -{1}(take_drop (idx_p + 1) L) take_add_app; [|done].
    rewrite get_abs_state_app -{2}(app_nil_r (get_abs_state (take (idx_p + 1) L))). f_equal.
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
  iDestruct (Nodes_rm_idx_remove with "Nodes") as (c_n [[c_p i_c_p]|]) "[(cM & #c↪□' & c↪ & %HLc_n & %HLc_p) Nodes]"; [exact HLc|lia| |lia].
  destruct HLc_p as [_ HLc_p].
  iDestruct (ghost_map_elem_agree with "c↪□ c↪□'") as %[= <-]; iClear "c↪□'".
  iEval (unfold Nodes_rm_idx_idx; rewrite (big_sepL_take_drop _ L idx_c)) in "Nodes".
  iDestruct "Nodes" as "[NodesTake NodesDrop]".
  iEval (rewrite -{2}(take_drop (idx_p + 1) L) take_add_app; [|done]) in "NodesTake".
  iDestruct "NodesTake" as "[NodesTake Ms]".
  iEval (rewrite Nat.add_1_r (take_S_r _ _ (p_k,false,(prev,i_p))); [|exact HLp]) in "NodesTake".
  iDestruct "NodesTake" as "[NodesTake _]".
  iEval (rewrite (drop_S _ (c_k, c_b, (curr, i_c))); [|exact HLc]) in "NodesDrop".
  iDestruct "NodesDrop" as "[_ NodesDrop]".
  iEval (rewrite (drop_S _ (a_k,true,(anchor,i_a))); [|exact HLa]) in "Ms".
  iEval (rewrite (take_cons' (a_k,true,(anchor,i_a))); [|lia]) in "Ms".
  (* Update anchor state and get rest of managed. *)
  iDestruct "Ms" as "[a Ms]". rewrite !EQtake !Nat.add_0_r.
  iEval (do 2 (case_decide; [lia|])) in "a". iDestruct "a" as (a_n [[a_p i_a_p]|]) "(aM & _ & #a.n↪□ & %HLa_n & %HLa_p)"; [|lia].
  destruct HLa_p as [_ HLa_p]. assert (a_p = prev ∧ i_a_p = i_p) as [-> ->]; simpl in *.
  { get_third HLp. rewrite Nat.add_1_r Nat.sub_1_r /= HLp in HLa_p. by injection HLa_p as [= -> ->]. }
  iMod (rcu.(rcu_points_to_unlink) with "IRD p.n↪rcu aM") as "[p.n↪rcu aM]"; [solve_ndisj|].
  iMod (rcu.(managed_delete) with "IRD [aM]") as "aD"; [solve_ndisj|by rewrite gmultiset_difference_diag|].
  iMod (create_delete_chain with "IRD [a.n↪□] RChain aD [Ms]") as (c_p' i_c_p') "(c_pD & %HrLlast & Chain)"; [solve_ndisj|done..| |].
  { iApply (big_sepL_mono with "Ms"). iIntros (?? Ht) "?".
    apply lookup_lt_Some in Ht. rewrite take_length_le in Ht; last first.
    { rewrite drop_length. assert (idx_p + 1 + length rL - 1 < length L); [|lia].
      apply lookup_lt_is_Some. have [[r i_r] HrL] : is_Some (rL !! (length rL -1)). { rewrite lookup_lt_is_Some. lia. }
      specialize (ElemOfL _ _ _ HrL) as [r_k HL_r]. exists (r_k,true,(r,i_r)). rewrite -HL_r. f_equal. lia.
    }
    do 2 (case_decide; [lia|]). iFrame.
  }
  (* Update prev and curr state *)
  specialize ElemOfL as ElemOfL'. specialize (ElemOfL' _ _ _ HrLlast) as [? HLrLlast].
  get_third HLrLlast. assert (c_p' = c_p ∧ i_c_p' = i_c_p) as [-> ->].
  { subst idx_c. replace (idx_p + 1 + (length rL - 1)) with (idx_p + 1 + length rL - 1) in HLrLlast by lia. naive_solver. }
  iMod (rcu.(deleted_clean) with "IRD c_pD cM") as "[c_pD cM]"; [solve_ndisj|]. iSpecialize ("Chain" with "c_pD").
  iMod (rcu.(rcu_points_to_link) with "IRD p.n↪rcu cM") as "[p.n↪rcu cM]"; [solve_ndisj|].
  rewrite gmultiset_difference_diag (left_id ∅).
  iMod (rcu.(guard_protect_managed) with "IRD cM G") as "(cM & G & #c_nInfo)"; [solve_ndisj|].
  iCombine "p.n↪ p.n↪'" as "p.n↪". iMod (ghost_map_update (Some (curr,i_c), false) with "●p_tag p.n↪") as "[●p_tag [p.n↪ p.n↪']]".
  iAssert (if c_b then i_c ↪[ γp_t ]□ (c_n, true) else True)%I as "#c.n↪□". { destruct c_b; by iFrame. }
  (* Close invariant early *)
  iAssert (ghost_var γl (1 / 2) (get_abs_state L')
           -∗ ▷ HListInternalInv h γp_a γp_t γl i_h γr)%I with "[●p_all ●p_tag NodesTake NodesDrop PTRS p.n↪' pM c↪ cM]" as "INV".
  { iIntros "Linv !>". repeat iExists _. iFrame "Linv ∗#%".
    unfold AllPtrs, Nodes. iSplitL "PTRS"; [|iSplit].
    - iApply (big_sepM_mono with "PTRS"). iIntros (i_n [n_k n] Hptrs_n) "[$|%HLn]".
      iRight. iPureIntro. apply elem_of_app.
      rewrite -(take_drop (idx_p + 1 + length rL) L) in HLn.
      apply elem_of_app in HLn as [HLn|HLn]; [left|by right].
      rewrite -(take_drop (idx_p + 1) L) take_add_app in HLn; [|done].
      apply elem_of_app in HLn as [HLn|[i_n_L [HL_n Hi_n_L]]%elem_of_take]; [done|exfalso].
      rewrite lookup_drop in HL_n.
      apply lookup_lt_is_Some in Hi_n_L as [[n' i_n'] HrLn].
      specialize (ElemOfL n' i_n' i_n_L HrLn) as [n_k' HL_n'].
      naive_solver.
    - subst L'.
      iEval (rewrite {2}Nat.add_1_r (take_S_r _ _ (p_k,false,(prev,i_p))); [|exact HLp]).
      rewrite !big_sepL_app big_sepL_singleton /=.
      iSplitR "NodesDrop cM c↪"; [iSplitR "pM p.n↪'"|].
      + iApply (big_sepL_mono with "NodesTake"). iIntros (idx_n [[n_k b_n] [l_n i_n]] HLn) "LN".
        assert (idx_n < idx_p) as LT; [|repeat (case_decide; [lia|])].
        { apply lookup_lt_Some in HLn as LT_take. rewrite take_length_le in LT_take; [lia|].
          apply lookup_lt_Some in HLa. lia.
        }
        iDestruct "LN" as (on op) "(nM & $ & l_n.n↪ & %HLl_n & %HLl_p)".
        iExists on,op. iFrame. iPureIntro. split.
        * rewrite !fmap_app lookup_app_l; last first.
          { rewrite /= fmap_length take_length_le /=; lia. }
          rewrite fmap_take lookup_take; [done|lia].
        * destruct op as [[l_p i_l_p]|]; [|done]. destruct HLl_p as [? HLl_p]. split; [done|].
          rewrite !fmap_app lookup_app_l; last first.
          { rewrite /= fmap_length take_length_le /=; lia. }
          rewrite fmap_take lookup_take; [done|lia].
      + unfold ListNode. iExists (Some (curr,i_c)),p_p. simpl in *. iFrame "∗#". iPureIntro. split.
        * rewrite fmap_app lookup_app_r fmap_length !take_length_le; [|lia..].
          get_third HLc. rewrite fmap_drop lookup_drop -HLc. f_equal. lia.
        * destruct p_p as [[p_p i_p_p]|]; rewrite take_length_le; [|lia..].
          destruct HLp_p as [? HLp_p]. split; [lia|].
          rewrite fmap_app lookup_app_l; [|rewrite fmap_length take_length_le; lia].
          rewrite fmap_take lookup_take; [|lia]. rewrite -HLp_p. f_equal. lia.
      + iEval (rewrite (drop_S _ (c_k, c_b, (curr, i_c))) /=; [|exact HLc]). iSplitR "NodesDrop"; last first.
        { iApply (big_sepL_mono with "NodesDrop"). iIntros (idx_n [[n_k b_n] [l_n i_l_n]] HLn) "LN".
          repeat (case_decide; [lia|]).
          iDestruct "LN" as (on on_p) "(l_nM & $ & l_n.n↦ & %HLl_n & %HLl_p)".
          iExists on,on_p. iFrame. iPureIntro.
          split.
          - rewrite fmap_app fmap_cons lookup_app_r app_length /= fmap_length !take_length_le /=; try lia.
            rewrite lookup_cons_ne_0; [|lia]. rewrite fmap_drop lookup_drop -HLl_n. f_equal. lia.
          - destruct on_p as [[l_p i_l_p]|]; rewrite app_length /= take_length_le; try lia.
            destruct HLl_p as [? HLl_p]. split; [lia|].
            rewrite fmap_app fmap_cons lookup_app_r /= fmap_length !take_length_le /=; try lia.
            rewrite fmap_drop -drop_S; [|by get_third HLc]. rewrite lookup_drop -HLl_p. f_equal. lia.
        }
        rewrite Nat.add_0_r app_length take_length_le /=; [|lia]. iExists c_n,(Some (prev,i_p)). iFrame "∗#%".
        iPureIntro. split.
        * rewrite fmap_app fmap_cons lookup_app_r /= fmap_length !take_length_le /=; try lia.
          rewrite lookup_cons_ne_0; [|lia]. rewrite fmap_drop lookup_drop -HLc_n. f_equal. lia.
        * split; [lia|]. rewrite fmap_app lookup_app_l; [|rewrite fmap_length take_length_le; lia].
          get_third HLp. rewrite -HLp fmap_take lookup_take /=; [|lia]. f_equal. lia.
    - iPureIntro. subst L'. split_and!.
      + rewrite !fmap_app !fmap_take !fmap_drop. apply take_drop_inf_Z_sorted; [lia|done].
      + rewrite lookup_app_l; [|lia]. rewrite lookup_take; [done|lia].
      + destruct HLt as [t HLt]. exists t.
        rewrite lookup_app_r /= !app_length /= !take_length_le /=; try lia.
        all: rewrite drop_length; apply lookup_lt_Some in HLc; try lia.
        rewrite lookup_drop -HLt. f_equal. lia.
      + rewrite dom_insert_lookup_L; [done|]. rewrite -elem_of_dom -Hdom elem_of_dom. eauto.
  }
  (* Check if we are committing *)
  destruct committing; last first; simpl in *.
  { iModIntro. iSplitL "Linv INV"; [by iApply "INV"|].
    iModIntro. iDestruct (harris_node_combine_some with "p↦ [//] p.n↪rcu [p.n↪]") as "$"; [iLeft; by iFrame|].
    wp_pures. iApply "HΦ'". by iFrame.
  }
  iDestruct "prAU" as "[pr AU]".
  (* See if tag check on curr will succeed. *)
  destruct (decide (prophecy_to_bool pr_v ∨ (c_k < k)%inf_Z)) as [NotCommit|[Hpr_v%Is_true_false GE]%Decidable.not_or].
  { (* Tagged, do not commit. *)
    iModIntro. iSplitL "Linv INV"; [iApply "INV"; iFrame|].
    iModIntro. iDestruct (harris_node_combine_some with "p↦ p↪□ p.n↪rcu [p.n↪]") as "$"; [iLeft; by iFrame|].
    clear dependent L p_all p_tag HrLlast. wp_pures.
    iApply "HΦ'". iModIntro. iFrame "∗#".
  }
  (* Assert that we are not tagged *)
  destruct c_b.
  { (* Tagged, impossible. *)
    iModIntro. iSplitL "Linv INV"; [iApply "INV"; iFrame|].
    iModIntro. iDestruct (harris_node_combine_some with "p↦ p↪□ p.n↪rcu [p.n↪]") as "$"; [iLeft; by iFrame|].
    wp_pures. iApply "HΦ'". iModIntro. iFrame "∗#%". iLeft. by iExists _.
  }
  iMod "AU" as (?) "[[Labs %HLabs] [_ Commit]]".
  iDestruct (ghost_var_agree with "Labs Linv") as %->.
  set (idx' := length (get_abs_state (take idx_p L))).
  iMod ("Commit" $! (bool_decide (c_k = k)) i_p i_c idx' with "[$Labs]") as "HΦ".
  { iFrame "∗#%". iPureIntro. split_and!; auto; last first.
    { case_bool_decide as EQN; [done|]. destruct c_k as [|c_k|]; [naive_solver| |naive_solver].
      simpl in *. apply inf_Z.Z_lt_lt,Z.lt_nge => ?.
      apply GE,inf_Z.Z_lt_lt,Z.lt_nge => ?.
      apply EQN. f_equal. lia.
    }
    all: rewrite !get_abs_state_app /= Nat.add_1_r (take_S_r _ _ (p_k,false,(prev,i_p))); simplify_list_eq; auto.
    - rewrite lookup_app_r get_abs_state_snoc app_length /=; [|lia]. fold idx'.
      replace (S idx' - (idx' + 1)) with 0 by lia.
      rewrite (drop_S L (c_k, false, (curr,i_c))); [|done].
      by rewrite get_abs_state_cons.
    - rewrite lookup_app_l get_abs_state_snoc; last first.
      { rewrite app_length /=. lia. }
      subst idx'. by rewrite snoc_lookup.
  }
  iModIntro. iSplitL "Linv INV"; [iApply "INV"; iFrame|].
  iModIntro. iDestruct (harris_node_combine_some with "p↦ p↪□ p.n↪rcu [p.n↪]") as "$"; [iLeft; by iFrame|].
  wp_pures. iApply "HΦ'". iModIntro. iFrame "∗#%". iRight.
  iIntros "G". iApply "HΦ". iFrame "∗#%".
Qed.

Local Lemma harris_find_inner_spec  (* Auxillary, non-unifiable *) Φ (k : Z) E
                                    (* harris inv *) γp_a γp_t γl i_h (h : blk)
                                    (* reclamation *) γr d g γg
                                    (* retire chain stuff *) (o_anchor : option (blk * positive)) rL
                                    (* prophecy *) (tagged : bool) (pr_tag : proph_id) (pr_v_tag : list (val * val))
                                    (* prev, curr*) (prev curr : blk) (i_p i_c : positive) (p_k c_k : inf_Z) :
  ↑listN ∪ ↑rcuN ⊆ E →
  (p_k < k)%inf_Z →
  prophecy_to_bool pr_v_tag = tagged →
  {{{ inv listN (HListInternalInv h γp_a γp_t γl i_h γr) ∗
      rcu.(IsRCUDomain) γr d ∗
      rcu.(Guard) γr γg g ∗
      i_p ↪[γp_a]□ (p_k,prev) ∗ i_c ↪[γp_a]□ (c_k,curr) ∗
      rcu.(RCUNodeInfo) γr γg prev i_p (harris_type γp_a γp_t γr) ∗
      rcu.(RCUNodeInfo) γr γg curr i_c (harris_type γp_a γp_t γr) ∗
      proph pr_tag pr_v_tag ∗
      match o_anchor with
      | None => ⌜rL = []⌝
      | Some (anchor,i_a) => RetireChain γp_t anchor i_a curr i_c rL
      end ∗
      match o_anchor with
      | None => True
      | Some (anchor,i_a) => rcu.(RCUNodeInfo) γr γg anchor i_a (harris_type γp_a γp_t γr)
      end ∗
      (* Check if we will be going into another iteration *)
      if decide (tagged ∨ (c_k < k)%inf_Z) then
        harris_find_au E γp_a γp_t γl γr k g γg Φ
      else
        (* We are going to return. Will we do a CAS? *)
        match o_anchor with
        | None => True
        | Some _ => harris_find_au E γp_a γp_t γl γr k g γg Φ
        end
  }}}
    (harris_find_inner rcu) #pr_tag #d #k #prev #curr #((blk_to_loc ∘ fst <$> o_anchor) &ₜ 0) @ E
  {{{ v, RET v;
    if decide (tagged ∨ (c_k < k)%inf_Z) then
      (* We went into another iteration. *)
      (⌜v = NONEV⌝ ∗ rcu.(Guard) γr γg g ∗ harris_find_au E γp_a γp_t γl γr k g γg Φ) ∨
      (∃ (ret_b : bool) (ret_prev ret_curr : blk),
        ⌜v = SOMEV (#ret_b, #ret_prev, #ret_curr)⌝ ∗
        Φ (#ret_b, #ret_prev, #ret_curr)%V)
    else
      (* We didn't go into another iteration. *)
      match o_anchor with
      | None =>
        (* Didn't do cas. *)
        ⌜v = SOMEV (#(bool_decide (c_k = k)), #prev, #curr)⌝ ∗ rcu.(Guard) γr γg g
      | Some _ =>
        (* Failed cas *)
        (⌜v = NONEV⌝ ∗ rcu.(Guard) γr γg g ∗ harris_find_au E γp_a γp_t γl γr k g γg Φ) ∨
        (* cas success *)
        ⌜v = SOMEV (#(bool_decide (c_k = k)), #prev, #curr)⌝ ∗
        Φ (#(bool_decide (c_k = k)), #prev, #curr)%V
      end
  }}}.
Proof using All.
  intros ? p_k_LT_k Hpr_tag.
  iIntros (Φ') "(#IsHarris & #IRD & G & p↪□ & c↪□ & pInfo & cInfo & pr_tag & RChain & aInfo & AU) HΦ'".
  iRevert (prev curr p_k c_k i_p i_c p_k_LT_k) "p↪□ c↪□ pInfo cInfo aInfo RChain AU HΦ'".
  iLöb as "IH" forall (o_anchor rL tagged pr_tag pr_v_tag Hpr_tag).
  iIntros (prev curr p_k c_k i_p i_c p_k_LT_k) "#p↪□ #c↪□ #pInfo #cInfo aInfo RChain AU HΦ'".
  wp_lam. wp_pure credit: "Lc". wp_pure credit: "Lc'". wp_pures.
  wp_apply (wp_new_proph with "[//]") as (pr_v_tag' pr_tag') "pr_tag'".
  wp_pures. wp_bind (! _)%E. iInv "cInfo" as (lv) "(c↦ & node & G)".
  iDestruct (harris_node_destruct_agree with "c↪□ node") as (c_on c_t) "(>% & c.n↪rcu & >c.n↪)"; subst lv.
  wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
  (* Check prophecy value for tag. *)
  destruct tagged; simpl.
  { (* Tagged, so going into next iteration. *)
    (* Assert that we must be tagged. *)
    iDestruct "c.n↪" as "[[% c.n↪]|[% #c.n↪□]]"; subst c_t.
    { iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu [c.n↪]") as "$"; [iLeft; by iFrame|].
      wp_pures.
      wp_apply (wp_resolve_proph with "pr_tag") as (?) "[%Heq _]".
      rewrite Heq in Hpr_tag. inversion Hpr_tag.
    }
    (* Get information of next pointer. *)
    iInv "IsHarris" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
    iMod (lc_fupd_elim_later with "Lc Nodes") as "Nodes".
    iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_c_n.
    iDestruct (get_persistent_AllPtrs with "PTRS") as "#[c.n|%HLc]"; [exact Hptrs_c_n| |]; last first.
    { apply elem_of_list_lookup in HLc as [idx_c HLc].
      iDestruct (Nodes_remove with "Nodes") as (??) "[(_&_&c.n↪&_) _]"; [exact HLc|simpl].
      iDestruct (ghost_map_elem_agree with "c.n↪□ c.n↪") as %[= ?].
    }
    iDestruct "c.n" as (i_c_n c_n c_n_k) "[c.n↪□' c_n↪□]".
    iDestruct (ghost_map_elem_agree with "c.n↪□ c.n↪□'") as %[= ->]; iClear "c.n↪□'". simpl in *.
    iMod (guard_protect_rcu_points_to with "IRD cInfo c.n↪rcu G") as "(c.n↪rcu & G & #c_nInfo)"; [solve_ndisj|].
    iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". } clear dependent p_all p_tag L.
    iModIntro. iDestruct (harris_node_combine_some with "c↦ c↪□ c.n↪rcu [$c.n↪□]") as "$"; [by iRight|].
    wp_pures.
    wp_apply (wp_resolve_proph with "pr_tag") as (?) "_"; wp_pures.
    wp_apply (get_anchor_spec with "[$RChain $c.n↪□]") as (n_a i_n_a) "[RChain %Hnew_a]"; wp_pures.
    iApply ("IH" $! (Some (n_a, i_n_a)) with "[%] G pr_tag' [%] p↪□ c_n↪□ pInfo c_nInfo [aInfo] [RChain] [AU] [HΦ']"); try done.
    { destruct o_anchor as [[anc i_a]|]; destruct Hnew_a as [<- <-]; done. }
    { case_decide; done. }
    { case_decide; [done|]. iNext. iIntros (v) "[HΦ|[% HΦ]]"; iApply "HΦ'"; [by iLeft|iRight].
      repeat iExists _. subst v. iSplit; done.
    }
  }
  (* assert that we must not be tagged. *)
  iDestruct "c.n↪" as "[[% c.n↪]|[% #c.n↪□]]"; subst c_t; last first.
  { iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu [$c.n↪□]") as "$"; [by iRight|].
    wp_pures.
    wp_apply (wp_resolve_proph with "pr_tag") as (pvs') "[%Heq _]".
    rewrite Heq in Hpr_tag. inversion Hpr_tag.
  }
  (* Get information of next pointer. *)
  iInv "IsHarris" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
  iMod (lc_fupd_elim_later with "Lc Nodes") as "Nodes".
  iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_c_n.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[c.n|%HLc]"; [exact Hptrs_c_n| |].
  { iDestruct "c.n" as (i_c_n c_n c_n_k) "[c.n↪□ c_n↪□]".
    iDestruct (ghost_map_elem_agree with "c.n↪□ c.n↪") as %[= ?].
  }
  apply elem_of_list_lookup in HLc as [idx_c HLc].
  iDestruct (Nodes_remove with "Nodes") as (? c_p) "[(cM & _ & c.n↪' & %HLc_n & %HLc_p) Nodes]"; [exact HLc|simpl].
  iDestruct (ghost_map_elem_agree with "c.n↪ c.n↪'") as %[= <-].
  iDestruct (Nodes_combine with "Nodes cM [] [c.n↪']") as "Nodes"; [done..|].
  (* Check to see if we are going into next iteration. *)
  destruct (decide (c_k < k)%inf_Z) as [c_k_LT|c_k_GE].
  { case_decide; [|naive_solver].
    (* Will go into next iteration with adjacent pointers. Check prophecy value & check c_n_k to commit. *)
    (* Get information about c_next *)
    destruct (next_not_tail_is_Some idx_c L c_k false (curr, i_c) c_on) as [[c_n i_c_n] [= ->]]; [naive_solver..|simpl in *].
    iMod (guard_protect_rcu_points_to with "IRD cInfo c.n↪rcu G") as "(c.n↪rcu & G & #c_nInfo)"; [solve_ndisj|].
    apply list_lookup_fmap_Some in HLc_n as [[[c_n_k b] ?] [HLc_n [= <-]]].
    iDestruct (get_persistent_Nodes with "Nodes") as (c_n_n c_n_p) "#(c_n↪□ & #c_n.n↪□ & _ & _)"; [exact HLc_n|].
    destruct (decide (prophecy_to_bool pr_v_tag' ∨ (c_n_k < k)%inf_Z)) as [NotCommit|[Hpr_v'%Is_true_false GE]%Decidable.not_or].
    { (* Tagged or key too small. Do not commit. *)
      iModIntro. iSplitL "●p_all ●p_tag PTRS Nodes Linv".
      { repeat iExists _. by iFrame "∗#%". } clear dependent p_all p_tag L c_p c_n_p.
      iModIntro. iDestruct (harris_node_combine_some with "c↦ c↪□ c.n↪rcu [c.n↪]") as "$"; [iLeft; by iFrame|].
      wp_pures. wp_apply (wp_resolve_proph with "pr_tag") as (pvs') "[_ _]"; wp_pures.
      wp_bind (!_)%E.
      iInv "cInfo" as (lv) "(c↦ & node & G)".
      iDestruct (harris_node_destruct_agree with "c↪□ node") as (c_on c_t) "(>% & c.n↪rcu & >c.n↪)"; subst lv.
      wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
      iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu c.n↪") as "$".
      wp_pures. iEval (case_bool_decide; [|naive_solver]). wp_pures.
      iApply ("IH" $! None with "[%] G pr_tag' [%] c↪□ c_n↪□ cInfo c_nInfo [//] [//] [AU] [HΦ']"); try done.
      all: case_decide; done.
    }
    (* Not tagged and key value good. Commit. *)
    (* curr must not be physically tagged *)
    destruct b; [|clear dependent c_n_n].
    { iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
      { repeat iExists _. by iFrame "∗#%". } clear dependent L p_all p_tag.
      iModIntro. iDestruct (harris_node_combine_some with "c↦ c↪□ c.n↪rcu [c.n↪]") as "$"; [by ((iRight; done)||(iLeft; iFrame; done))|].
      wp_pures. wp_apply (wp_resolve_proph with "pr_tag") as (?) "_"; wp_pures.
      wp_bind (!_)%E.
      iInv "cInfo" as (lv) "(c↦ & node & G)".
      iDestruct (harris_node_destruct_agree with "c↪□ node") as (c_on c_t) "(>% & c.n↪rcu & >c.n↪)"; subst lv.
      wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
      iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu c.n↪") as "$".
      wp_pures. iEval (case_bool_decide; [|naive_solver]). wp_pures.
      iApply (harris_find_inner_wrong_proph with "pr_tag' c_nInfo c_n.n↪□ G"); done.
    }
    iMod "AU" as (?) "[[Labs %HLabs] [_ Commit]]".
    iDestruct (ghost_var_agree with "Labs Linv") as %[= ->].
    assert (L = take idx_c L ++ [(c_k, false, (curr,i_c))] ++ [(c_n_k, false, (c_n,i_c_n))] ++ drop (S (S idx_c)) L) as EQ.
    { rewrite -{1}(take_drop idx_c L). f_equal. simplify_list_eq.
      rewrite -drop_S; [|by rewrite -Nat.add_1_r].
      rewrite -drop_S; done.
    }
    set (idx' := length (get_abs_state (take idx_c L))).
    iMod ("Commit" $! (bool_decide (c_n_k = k)) i_c i_c_n idx' with "[$Labs]") as "HΦ".
    { iFrame "∗#%". iPureIntro. split_and!; auto; last first.
      { case_bool_decide as EQN; [done|]. destruct c_n_k as [|c_n_k|]; [naive_solver| |naive_solver].
        simpl in *. apply inf_Z.Z_lt_lt,Z.lt_nge => ?.
        apply GE,inf_Z.Z_lt_lt,Z.lt_nge => ?.
        apply EQN. f_equal. lia.
      }
      all: rewrite EQ !get_abs_state_app /=; simplify_list_eq; rewrite lookup_app_r; [|lia].
      all: fold idx'.
      - by replace (S idx' - idx') with 1 by lia.
      - by rewrite Nat.sub_diag.
    }
    iModIntro. iSplitL "●p_all ●p_tag PTRS Nodes Linv".
    { repeat iExists _. by iFrame "∗#%". } clear dependent L p_all p_tag.
    iModIntro. iDestruct (harris_node_combine_some with "c↦ c↪□ c.n↪rcu [c.n↪]") as "$"; [by ((iRight; done)||(iLeft; iFrame; done))|].
    wp_pures. wp_apply (wp_resolve_proph with "pr_tag") as (?) "_". wp_pures.
    wp_bind (!_)%E.
    iInv "cInfo" as (lv) "(c↦ & node & G)".
    iDestruct (harris_node_destruct_agree with "c↪□ node") as (c_on c_t) "(>% & c.n↪rcu & >c.n↪)"; subst lv.
    wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
    iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu c.n↪") as "$".
    wp_pures. iEval (case_bool_decide; [|naive_solver]). wp_pures.
    iApply ("IH" $! None with "[%] G pr_tag' [%] c↪□ c_n↪□ cInfo c_nInfo [//] [//] [] [HΦ HΦ']"); [done..| |].
    - case_decide; [naive_solver|done].
    - case_decide as EQN; [done|iNext]. iClear "IH".
      iIntros (v) "[-> G]". iApply "HΦ'". iRight.
      repeat iExists _. iSplit; [done|]. iApply "HΦ". iFrame "∗#%".
  }
  (* Curr is target node. Finish find procedure. *)
  iClear "IH". case_decide; [naive_solver|].
  iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
  { repeat iExists _. by iFrame "∗#%". } clear dependent L p_all p_tag idx_c c_p.
  iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu [c.n↪]") as "$"; [iLeft; by iFrame|].
  wp_pures.
  wp_apply (wp_resolve_proph with "pr_tag") as  (?) "_".
  wp_pures. wp_bind (!_)%E.
  iInv "cInfo" as (lv) "(c↦ & node & G)".
  iDestruct (harris_node_destruct_agree with "c↪□ node") as (c_on' c_t) "(>% & c.n↪rcu & >c.n↪)"; subst lv.
  wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
  iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu c.n↪") as "$".
  wp_pures. iEval (case_bool_decide; [naive_solver|]). wp_pures.
  (* Check if we will preform a CAS *)
  destruct o_anchor as [[anchor i_a]|]; last first.
  { wp_pures. iApply "HΦ'". iModIntro. by iFrame. }
  (* We will preform a CAS *)
  wp_pures.
  wp_apply (wp_new_proph with "[//]") as (pr_v_cas pr_cas) "pr_cas".
  wp_pures.
  wp_apply (harris_helping_cas_spec true rL with "[$pr_cas $G $AU $Lc' aInfo $RChain]") as ([]) "(G & [pr_cas AU])"; [solve_ndisj|exact p_k_LT_k|iFrame "∗#"| |]; last first.

  all: wp_pures.
  { iApply "HΦ'". iLeft. by iFrame. }
  iDestruct "AU" as "(DChain & _ & AU)".
  destruct (prophecy_to_bool pr_v_cas) eqn:Hpr_v_cas.
  { (* Tagged, do not commit. *)
    case_decide; [|naive_solver].
    wp_pures. wp_bind (!_)%E.
    iInv "cInfo" as (lv) "(c↦ & node & G)".
    iDestruct (harris_node_destruct_agree with "c↪□ node") as (? c_t') "(>% & c.n↪rcu & c.n↪)"; subst lv.
    wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
    iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu c.n↪") as "$".
    wp_pures.
    wp_apply (wp_resolve_proph with "pr_cas") as (?) "[%Heq _]"; subst pr_v_cas; simpl in *.
    case_bool_decide; [done|]. wp_pures.
    wp_apply (chain_retire_spec with "[$IRD $DChain]") as "_"; [solve_ndisj|]. wp_pures.
    iApply "HΦ'". iModIntro. iLeft. by iFrame "AU G".
  }
  case_decide; [naive_solver|].
  (* Not tagged, commit. *)
  (* Assert that we are not tagged *)
  iDestruct "AU" as "[[% #c.n↪□]|HΦ]".
  { (* Tagged, impossible. *)
    wp_bind (!_)%E.
    iInv "cInfo" as (lv) "(c↦ & node & G)".
    iDestruct (harris_node_destruct_agree with "c↪□ node") as (? c_t') "(>% & c.n↪rcu & >[[% c.n↪]|[% #c.n↪]])"; subst lv c_t'.
    all: iDestruct (ghost_map_elem_agree with "c.n↪ c.n↪□") as %[= ->]; iClear "c.n↪".
    wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
    iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu [$c.n↪□]") as "$"; [by iRight|].
    wp_pures.
    wp_apply (wp_resolve_proph with "pr_cas") as (?) "[%Heq _]".
    subst pr_v_cas. inversion Hpr_v_cas.
  }
  wp_bind (!_)%E.
  iInv "cInfo" as (lv) "(c↦ & node & G)".
  iDestruct (harris_node_destruct_agree with "c↪□ node") as (? c_t') "(>% & c.n↪rcu & c.n↪)"; subst lv.
  wp_apply (wp_load_offset with "c↦") as "c↦"; [by simplify_list_eq|].
  iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu c.n↪") as "$".
  wp_pures.
  wp_apply (wp_resolve_proph with "pr_cas") as (?) "[%Heq _]"; subst pr_v_cas; simpl in *.
  case_bool_decide; [|done]. wp_pures.
  wp_apply (chain_retire_spec with "[$IRD $DChain]") as "_"; [solve_ndisj|]. wp_pures.
  iApply "HΦ'". iModIntro. iRight. iSplit; [done|].
  iApply "HΦ". by iFrame "G".
Qed.

Lemma harris_find_spec :
  harris_find_spec' listN rcuN rcu (harris_find rcu).
Proof using All.
  intros E k h γp_a γp_t γl i_h γr l d g G ?.
  iIntros "#IRD G #l.d↦□ #h↪□ #IsHarris" (Φ) "AU".
  iLöb as "IH" forall (G).
  wp_lam. wp_pure credit: "Lc". wp_pures.
  wp_apply (wp_new_proph with "[//]") as (pr_v_tag pr_tag) "pr_tag".
  wp_pures. wp_load. wp_pures. wp_bind (! _)%E.
  iInv "IsHarris" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
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
    wp_pures. replace (None : option loc) with (blk_to_loc ∘ fst <$> (None : option (blk * positive))); [|done].
    wp_apply (harris_find_inner_spec with "[$IsHarris $IRD AU $G $pr_tag]"); [solve_ndisj|exact LT_k|done|iFrame "∗#%"|].
    { iSplit; [done|]. case_decide; iFrame; done. }
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
    wp_apply (harris_find_inner_wrong_proph with "pr_tag cInfo c.n↪□ G"); done.
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
  replace (None : option loc) with (blk_to_loc ∘ fst <$> (None : option (blk * positive))); [|done].
  wp_apply (harris_find_inner_spec (λ _, True)%I with "[$IRD $IsHarris $G $pr_tag]"); [done|exact LT_k|done|iFrame "∗#%"|].
  { iSplit; [done|]. case_decide; [naive_solver|done]. }
  case_decide; [naive_solver|].
  iIntros (v) "[-> G]". wp_pures. iApply "HΦ".
  iModIntro. by iFrame "∗#%".
Qed.

End harris_find.

Definition harris_code_impl (rcu : rcu_code) : code_harris_operations.harris_find_code := {|
  code_harris_operations.harris_find := harris_find rcu;
|}.

Program Definition harris_impl Σ listN rcuN (DISJN : listN ## rcuN) `{!heapGS Σ, !hlG Σ} (rcu : rcu_traversal_spec Σ rcuN) : hfind_spec Σ listN rcuN DISJN rcu  := {|
  proof_harris_operations.harris_find_spec_code := harris_code_impl rcu.(rcu_spec_code);
|}.
Next Obligation. intros. apply harris_find_spec. done. Qed.
Next Obligation.
  intros. intros ???????????????????????? LT.
  iIntros (Φ') "(#IsHarris & #IRD & #pInfo & #cInfo & #p↪□ & #c↪□ & #an.n↪□ & AU & G) HΦ'".
  wp_apply (harris_helping_cas_spec _ _ ltac:(solve_ndisj) _ committing [(anchor,i_a)] Φ pr with "[$AU $G]"); [solve_ndisj|exact LT|simpl; by iFrame "#"|simpl].
  iIntros (?) "(G & AU)". iApply "HΦ'". iFrame. destruct committing; simpl; iFrame.
  - iDestruct "AU" as "[$ AU]". destruct b; iFrame.
    iDestruct "AU" as "(D & $ & $)". iDestruct "D" as (??) "(_ & _ & $ & _)".
  - destruct b; iFrame. iDestruct "AU" as (??) "(_ & _ & $ & _)".
Qed.
