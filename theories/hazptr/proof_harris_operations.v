From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants ghost_var ghost_map.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr Require Import sorted_list.
From iris.prelude Require Import options.

From smr Require Import helpers hazptr.spec_hazptr hazptr.spec_ordered_set hazptr.code_harris_operations.

Set Printing Projections.

Local Open Scope nat_scope.

Class hlG Σ := HLG {
  harris_michael_list_ptrs_idG :> inG Σ (exclR unitO);
  harris_michael_list_absG :> ghost_varG Σ (list inf_Z);
  harris_michael_list_ptrs_allG :> ghost_mapG Σ gname (inf_Z * blk);
  harris_michael_list_ptrs_tagG :> ghost_mapG Σ gname (option (blk * gname) * bool);
}.

Definition hlΣ : gFunctors := #[GFunctor (exclR unitO); ghost_varΣ (list inf_Z); ghost_mapΣ gname (inf_Z * blk); ghost_mapΣ gname (option (blk * gname) * bool)].

Global Instance subG_hlΣ {Σ} :
  subG hlΣ Σ → hlG Σ.
Proof. solve_inG. Qed.

Section harris_list.
Context `{!heapGS Σ, !hlG Σ}.
Notation iProp := (iProp Σ).
Context (listN hazptrN : namespace) (DISJN : listN ## hazptrN).

Variable (hazptr : hazard_pointer_spec Σ hazptrN).

Implicit Types
  (γp_a γp_t γl γp : gname)
  (p_all : gmap gname (inf_Z * blk))
  (p_tag : gmap gname ((option (blk * gname)) * bool))
  (abs_L : list inf_Z)
  (L : list (inf_Z * bool * (blk * gname))).

Definition HList γl abs_L : iProp := ghost_var γl (1/2) abs_L ∗ ⌜Sorted_inf_Z abs_L⌝.

Global Instance HList_Timeless γl abs_L : Timeless (HList γl abs_L).
Proof. apply _. Qed.

Lemma HList_sorted γl abs_L :
  HList γl abs_L -∗ ⌜Sorted_inf_Z abs_L⌝.
Proof. iDestruct 1 as "[_ $]". Qed.

Notation node_tok γp := (own γp (Excl () : exclR unitO)).

Definition node γp_a γp_t (p : blk) lv γp : iProp :=
  ∃ (p_k : inf_Z) (p_on : option (blk * gname)) (p_t : Z), ⌜lv = [ #((blk_to_loc <$> (fst <$> p_on)) &ₜ p_t); #p_k]⌝ ∗
    γp ↪[γp_a]□ (p_k,p) ∗
    ( (* Not tagged *)
      ⌜p_t = 0⌝ ∗ γp ↪[γp_t]{# 1/2} (p_on, false) ∨
      (* Tagged *)
      ⌜p_t = 1⌝ ∗ γp ↪[γp_t]□ (p_on, true)).

Definition AllPtrs p_all L γp_a γp_t : iProp :=
  [∗ map] γp ↦ kp ∈ p_all, let '(k,p) := kp in
    node_tok γp ∗
    ((∃ (γp_n : gname) (p_n : blk) (p_n_k : inf_Z),
      γp ↪[γp_t]□ (Some (p_n,γp_n), true) ∗ γp_n ↪[γp_a]□ (p_n_k, p_n))
      ∨ ⌜(k, false, (p,γp)) ∈ L⌝).

Global Instance AllPtrs_timeless p_all L γp_a γp_t : Timeless (AllPtrs p_all L γp_a γp_t).
Proof. apply big_sepM_timeless. intros ?[??]. apply _. Qed.

Definition ListNode (i : nat) (kbpγp : inf_Z * bool * (blk * gname)) L γp_a γp_t γz : iProp :=
  ∃ (pn : option (blk * gname)), let '(k,b,pγp) := kbpγp in let '(p,γp) := pγp in
  hazptr.(Managed) γz p γp nodeSize (node γp_a γp_t) ∗
  γp ↪[γp_a]□ (k,p) ∗
  (if (b : bool) then γp ↪[γp_t]□ (pn, true) else γp ↪[γp_t]{# 1/2} (pn, false)) ∗
  ⌜L.*2 !! (i + 1)%nat = pn⌝.

Definition Nodes L γp_a γp_t γz : iProp :=
  [∗ list] i ↦ kbγnn ∈ L, ListNode i kbγnn L γp_a γp_t γz.

Definition Nodes_rm_idx idx L γp_a γp_t γz : iProp :=
  [∗ list] i ↦ kbγnn ∈ L,
    if decide (i = idx) then emp else ListNode i kbγnn L γp_a γp_t γz.

Definition Nodes_rm_idx_idx idx idx' L γp_a γp_t γz : iProp :=
  [∗ list] i ↦ kbγnn ∈ L,
  if decide (i = idx') then emp else (if decide (i = idx) then emp else ListNode i kbγnn L γp_a γp_t γz).

Global Instance case_next_node_persistent (b : bool) (γp γp_t : gname) (pn : option (blk * gname)) : Persistent (if (b : bool) then γp ↪[γp_t]□ (pn, true) else True)%I.
Proof. destruct b; apply _. Qed.

(* Note: L.*2 should be (blk,gname), HLt does not need to have two evars. *)
Definition HListInternalInv h γp_a γp_t γl γh γz : iProp :=
  ∃ p_all p_tag L,
    ghost_var γl (1/2) (get_abs_state L) ∗
    ghost_map_auth γp_a 1 p_all ∗
    ghost_map_auth γp_t 1 p_tag ∗
    AllPtrs p_all L γp_a γp_t ∗
    Nodes L γp_a γp_t γz ∗
    ⌜Sorted_inf_Z (L.*1.*1) ∧
     L !! 0 = Some (-∞ᵢ, false, (h,γh)) ∧
     (∃ t, L !! (length L - 1) = Some (∞ᵢ, false, t)) ∧
     dom p_all = dom p_tag⌝.

Definition IsHList (γp_a γp_t γl γz : gname) (l : loc) : iProp :=
  ∃ (d : loc) (h : blk) (γh : gname),
    (l +ₗ domain) ↦□ #d ∗ (l +ₗ head) ↦□ #h ∗ γh ↪[γp_a]□ (-∞ᵢ,h) ∗
    hazptr.(IsHazardDomain) γz d ∗ inv listN (HListInternalInv h γp_a γp_t γl γh γz).

Global Instance IsHList_Persistent γp_a γp_t γl γz l : Persistent (IsHList γp_a γp_t γl γz l).
Proof. apply _. Qed.

Lemma harris_node_destruct_agree γp_a γp_t p γp (p_k : inf_Z) lv :
  node γp_a γp_t (p : blk) lv γp -∗
  γp ↪[ γp_a ]□ (p_k, p) -∗
  ∃ (p_on : option (blk * positive)) (p_t : Z),
  ⌜lv = [ #((blk_to_loc <$> (fst <$> p_on)) &ₜ p_t); #p_k]⌝ ∗
  (⌜p_t = 0⌝ ∗ γp ↪[γp_t]{#1 / 2} (p_on, false) ∨ ⌜p_t = 1⌝ ∗ γp ↪[γp_t]□ (p_on, true)).
Proof.
  iIntros "node #p↪□". iDestruct "node" as (? p_on p_t ->) "(#p↪□' & p.n↪)".
  iDestruct (ghost_map_elem_agree with "p↪□ p↪□'") as %[= <-]; iClear "p↪□'".
  repeat iExists _. by iFrame "∗#%".
Qed.

Lemma harris_node_combine_on γp_a γp_t (p : blk) γp (p_k : inf_Z) (p_on : option (blk * positive)) p_t :
  (blk_to_loc p) ↦∗ [ #((blk_to_loc <$> (fst <$> p_on)) &ₜ p_t); #p_k] -∗
  γp ↪[ γp_a ]□ (p_k, p) -∗
  (⌜p_t = 0⌝ ∗ γp ↪[γp_t]{#1 / 2} (p_on, false) ∨ ⌜p_t = 1⌝ ∗ γp ↪[γp_t]□ (p_on, true)) -∗
  ∃ lv : list val, ⌜2 = length lv⌝ ∗ p ↦∗ lv ∗ ▷ node γp_a γp_t (p : blk) lv γp.
Proof.
  iIntros "p↦ #p↪□ p.n↪". iExists _. iFrame "p↦". iSplit; [done|].
  iNext. iExists p_k,p_on,p_t. by iFrame "∗#%".
Qed.

Lemma harris_node_combine_some γp_a γp_t (p : blk) γp (p_k : inf_Z) (p_n : blk) (γp_n : positive) p_t :
  (blk_to_loc p) ↦∗ [ #((Some (blk_to_loc p_n)) &ₜ p_t); #p_k] -∗
  γp ↪[ γp_a ]□ (p_k, p) -∗
  (⌜p_t = 0⌝ ∗ γp ↪[γp_t]{#1 / 2} (Some (p_n,γp_n), false) ∨ ⌜p_t = 1⌝ ∗ γp ↪[γp_t]□ (Some (p_n,γp_n), true)) -∗
  ∃ lv : list val, ⌜2 = length lv⌝ ∗ p ↦∗ lv ∗ ▷ node γp_a γp_t (p : blk) lv γp.
Proof.
  iIntros "p↦ #p↪□ p.n↪". iExists _. iFrame "p↦". iSplit; [done|].
  iNext. iExists p_k,(Some (p_n,γp_n)),p_t. by iFrame "∗#%".
Qed.

Lemma get_persistent_Nodes L idx k b γp p γp_a γp_t γz :
  L !! idx = Some (k,b,(p,γp)) →
  Nodes L γp_a γp_t γz -∗
  ∃ pn, γp ↪[γp_a]□ (k,p) ∗ (if (b : bool) then γp ↪[γp_t]□ (pn, true) else True) ∗ ⌜L.*2 !! (idx + 1)%nat = pn⌝.
Proof.
  iIntros (Hidx) "Nodes". unfold Nodes,ListNode.
  rewrite big_sepL_delete; [|exact Hidx].
  iDestruct "Nodes" as "[p _]".
  iDestruct "p" as (pn) "(M & $ & p.n↦ & %Hp)". iExists pn.
  destruct b; iFrame "∗%".
Qed.

Lemma get_persistent_Nodes_rm_idx L idx k b γp p γp_a γp_t γz idx' :
  L !! idx = Some (k,b,(p,γp)) →
  idx ≠ idx' →
  Nodes_rm_idx idx' L γp_a γp_t  γz -∗
  ∃ pn, γp ↪[γp_a]□ (k,p) ∗ (if (b : bool) then γp ↪[γp_t]□ (pn, true) else True) ∗ ⌜L.*2 !! (idx + 1)%nat = pn⌝.
Proof.
  iIntros (Hidx NE) "Nodes". unfold Nodes_rm_idx,ListNode.
  rewrite big_sepL_delete; [|exact Hidx].
  iDestruct "Nodes" as "[p _]". case_decide; [lia|].
  iDestruct "p" as (pn) "(M & $ & p.n↦ & %Hp)". iExists pn.
  destruct b; iFrame "∗%".
Qed.

Lemma get_persistent_Nodes_rm_idx_idx L idx k b γp p γp_a γp_t γz idx' idx'' :
  L !! idx = Some (k,b,(p,γp)) →
  idx ≠ idx' ∧ idx ≠ idx'' →
  Nodes_rm_idx_idx idx' idx'' L γp_a γp_t  γz -∗
  ∃ pn, γp ↪[γp_a]□ (k,p) ∗ (if (b : bool) then γp ↪[γp_t]□ (pn, true) else True) ∗ ⌜L.*2 !! (idx + 1)%nat = pn⌝.
Proof.
  iIntros (Hidx NE) "Nodes". unfold Nodes_rm_idx_idx,ListNode.
  rewrite big_sepL_delete; [|exact Hidx].
  iDestruct "Nodes" as "[p _]". repeat (case_decide; [lia|]).
  iDestruct "p" as (pn) "(M & $ & p.n↦ & %Hp)". iExists pn.
  destruct b; iFrame "∗%".
Qed.

Lemma Nodes_remove L idx k b γp p γp_a γp_t γz :
  L !! idx = Some (k,b,(p,γp)) →
  Nodes L γp_a γp_t γz -∗
  ∃ (pn : option (blk * gname)),
  (hazptr.(Managed) γz p γp nodeSize (node γp_a γp_t) ∗
  γp ↪[γp_a]□ (k,p) ∗
  (if (b : bool) then γp ↪[γp_t]□ (pn, true) else γp ↪[γp_t]{# 1/2} (pn, false))%I ∗
  ⌜L.*2 !! (idx + 1)%nat = pn⌝) ∗
  Nodes_rm_idx idx L γp_a γp_t γz.
Proof.
  iIntros (Hidx) "Nodes". unfold Nodes,ListNode.
  iEval (rewrite big_sepL_delete; [|exact Hidx]) in "Nodes".
  iDestruct "Nodes" as "[p Nodes]".
  iDestruct "p" as (pn) "($ & #$ & p.n↦ & %)". iExists pn.
  iFrame "∗#%".
Qed.

Lemma Nodes_combine L idx k b γp p γp_a γp_t γz pn :
  L !! idx = Some (k,b,(p,γp)) →
  L.*2 !! (idx + 1) = pn →
  Nodes_rm_idx idx L γp_a γp_t γz -∗
  hazptr.(Managed) γz p γp nodeSize (node γp_a γp_t) -∗
  γp ↪[γp_a]□ (k,p) -∗
  (if (b : bool) then γp ↪[γp_t]□ (pn, true) else γp ↪[γp_t]{# 1/2} (pn, false))%I -∗
  Nodes L γp_a γp_t γz.
Proof.
  iIntros (Hidx Hidx_next) "Nodes M #γp.k↪□ p.n↦". unfold Nodes,ListNode.
  iEval (rewrite big_sepL_delete; [|exact Hidx]). iFrame.
  iExists pn. iFrame "∗#%".
Qed.

Lemma Nodes_rm_idx_remove L idx k b γp p γp_a γp_t γz idx' :
  L !! idx = Some (k,b,(p,γp)) →
  idx' ≠ idx →
  Nodes_rm_idx idx' L γp_a γp_t γz -∗
  ∃ (pn : option (blk * gname)),
  (hazptr.(Managed) γz p γp nodeSize (node γp_a γp_t) ∗
  γp ↪[γp_a]□ (k,p) ∗
  (if (b : bool) then γp ↪[γp_t]□ (pn, true) else γp ↪[γp_t]{# 1/2} (pn, false))%I ∗
  ⌜L.*2 !! (idx + 1)%nat = pn⌝) ∗
  Nodes_rm_idx_idx idx' idx L γp_a γp_t γz.
Proof.
  iIntros (Hidx NE) "Nodes". unfold Nodes_rm_idx,ListNode.
  iEval (rewrite big_sepL_delete; [|exact Hidx]) in "Nodes".
  case_decide; [lia|].
  iDestruct "Nodes" as "[p Nodes]".
  iDestruct "p" as (pn) "($ & #$ & p.n↦ & %)". iExists pn.
  iFrame "∗#%".
Qed.

Lemma Nodes_rm_idx_combine L idx k b γp p γp_a γp_t γz pn idx' :
  L !! idx = Some (k,b,(p,γp)) →
  L.*2 !! (idx + 1) = pn →
  idx' ≠ idx →
  Nodes_rm_idx_idx idx' idx L γp_a γp_t γz -∗
  hazptr.(Managed) γz p γp nodeSize (node γp_a γp_t) -∗
  γp ↪[γp_a]□ (k,p) -∗
  (if (b : bool) then γp ↪[γp_t]□ (pn, true) else γp ↪[γp_t]{# 1/2} (pn, false))%I -∗
  Nodes_rm_idx idx' L γp_a γp_t γz.
Proof.
  iIntros (Hidx Hidx_next NE) "Nodes M #γp.k↪□ p.n↦". unfold Nodes_rm_idx,ListNode.
  iEval (rewrite big_sepL_delete; [|exact Hidx]).
  case_decide; [lia|]. iFrame.
  iExists pn. iFrame "∗#%".
Qed.

Lemma get_persistent_AllPtrs p_all L γp p k γp_a γp_t :
  p_all !! γp = Some (k,p) →
  AllPtrs p_all L γp_a γp_t -∗
  ((∃ (γp_n : gname) (p_n : blk) (p_n_k : inf_Z),
      γp ↪[γp_t]□ (Some (p_n, γp_n), true) ∗ γp_n ↪[γp_a]□ (p_n_k, p_n))
      ∨ ⌜(k, false, (p,γp)) ∈ L⌝).
Proof.
  iIntros (Hp) "PTRS". unfold AllPtrs. rewrite big_sepM_delete; [|exact Hp]. simpl in *.
  iDestruct "PTRS" as "[[_ $] _]".
Qed.

Definition harris_find_spec' (harris_find : val) : Prop :=
  ∀ (* Auxillary *) E (k : Z)
    (* harris inv *) (h : blk) γp_a γp_t γl γh γz
    (* other locs *) l d prev_sh curr_sh p_st c_st,
  (↑listN ∪ ↑hazptrN) ⊆ E →
  ⊢ hazptr.(IsHazardDomain) γz d -∗
  hazptr.(Shield) γz prev_sh p_st -∗
  hazptr.(Shield) γz curr_sh c_st -∗
  (l +ₗ head) ↦□ #h -∗
  γh ↪[γp_a]□ (-∞ᵢ,h) -∗
  inv listN (HListInternalInv h γp_a γp_t γl γh γz) -∗
  <<< ∀∀ (L : list inf_Z), HList γl L >>>
    harris_find #l #d #k #prev_sh #curr_sh @ E,(↑listN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
  <<< ∃∃ (b : bool) (γ_prev γ_curr : gname) (prev curr : blk) (ret_p_sh ret_c_sh : loc) (prev_k curr_k : inf_Z) (idx : nat),
      HList γl L ∗
      (* prev and curr are from the list. *)
      γ_prev ↪[γp_a]□ (prev_k, prev) ∗ γ_curr ↪[γp_a]□ (curr_k, curr) ∗
      ⌜L !! idx = Some prev_k ∧
      L !! (S idx) = Some curr_k ∧
      (* prev, c_prev_k and curr's key values are correct *)
      (prev_k < k)%inf_Z ∧ if b then curr_k = k else (k < curr_k)%inf_Z⌝,
      RET (#ret_p_sh, #ret_c_sh, (#b, #prev, #curr)),
      (* Updated shields *)
      hazptr.(Shield) γz ret_p_sh (Validated prev γ_prev (node γp_a γp_t) nodeSize) ∗
      hazptr.(Shield) γz ret_c_sh (Validated curr γ_curr (node γp_a γp_t) nodeSize)
      >>>.

(* TODO: minimize cas spec *)
Lemma harris_helping_cas_spec γz d h γp_a γp_t γl γh γ_prev γ_curr γ_c_n prev_sh curr_sh (prev curr c_n : blk) p_k c_k c_n_k (k : Z) E :
  (↑listN ∪ ↑hazptrN) ⊆ E →
  (p_k < k)%inf_Z →
  {{{ hazptr.(IsHazardDomain) γz d ∗
      inv listN (HListInternalInv h γp_a γp_t γl γh γz) ∗
      γ_prev ↪[ γp_a ]□ (p_k, prev) ∗
      γ_curr ↪[ γp_a ]□ (c_k, curr) ∗
      γ_c_n ↪[ γp_a ]□ (c_n_k, c_n) ∗
      γ_curr ↪[ γp_t ]□ (Some (c_n, γ_c_n), true) ∗
      hazptr.(Shield) γz prev_sh (Validated prev γ_prev (node γp_a γp_t) 2) ∗
      hazptr.(Shield) γz curr_sh (Validated curr γ_curr (node γp_a γp_t) 2) ∗
      £ 1
  }}}
    CAS #(prev +ₗ 0%nat) #curr #c_n @ E
  {{{ (b : bool), RET #b;
      hazptr.(Shield) γz prev_sh (Validated prev γ_prev (node γp_a γp_t) 2) ∗
      hazptr.(Shield) γz curr_sh (Validated curr γ_curr (node γp_a γp_t) 2) ∗
      if b then
        hazptr.(Managed) γz curr γ_curr nodeSize (node γp_a γp_t)
      else
        True
  }}}.
Proof using All.
  iIntros (? p_k_LT_k Φ) "(#IHD & #IsHarris & #p↪□ & #c↪□ & #c_n↪□ & #c.n↪□ & pS & cS & Lc) HΦ".
  wp_bind (CmpXchg _ _ _)%E.
  iInv "pS" as (?) "(_ & p↦ & >node & pS)".
  iDestruct (harris_node_destruct_agree with "node [//]") as (p_on p_t ->) "[[% p.n↪]|[% #p.n↪□]]"; subst p_t; last first.
  { (* tagged, CAS must fail. *)
    wp_apply (wp_cmpxchg_fail_offset with "p↦") as "p↦"; [by simplify_map_eq|done|destruct p_on as [[??]|];naive_solver|].
    iDestruct (harris_node_combine_on with "p↦ p↪□ [$p.n↪□]") as "$"; [by iRight|].
    iModIntro. wp_pures.
    iApply "HΦ". iModIntro. by iFrame.
  }
  iInv "IsHarris" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
  iMod (lc_fupd_elim_later with "Lc Nodes") as "Nodes".
  iDestruct (ghost_map_lookup with "●p_all p↪□") as %Hptrs_p.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[p.n|%HLp]"; [exact Hptrs_p| |].
  { (* curr tagged, impossible *)
    iDestruct "p.n" as (γ_p_n p_n p_n_k) "[p.n↪□ p_n↪□]".
    iDestruct (ghost_map_elem_agree with "p.n↪□ p.n↪") as %[= ?].
  }
  apply elem_of_list_lookup in HLp as [idx HLp].
  iDestruct (Nodes_remove with "Nodes") as (?) "[(pM & _ & p.n↪' & %HLp_next) Nodes]"; [exact HLp|]; simpl.
  iDestruct (ghost_map_elem_agree with "p.n↪ p.n↪'") as %[= <-].
  destruct (next_not_tail_is_Some idx L p_k false (prev,γ_prev) p_on) as [[curr' γ_curr'] [= ->]]; simpl in *; [naive_solver..|].
  specialize HLp_next as HLp_next'.
  apply list_lookup_fmap_Some in HLp_next' as [[[c_k' b] ?] [HLc [= <-]]].
  destruct (decide (curr' = curr)) as [->|NE]; last first.
  { (* Not equal, fail CAS and exit. *)
    iDestruct (Nodes_combine with "Nodes pM [//] [p.n↪']") as "Nodes"; [done..|].
    wp_apply (wp_cmpxchg_fail_offset with "p↦") as "p↦"; [by simplify_map_eq|naive_solver..|].
    iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { iModIntro. repeat iExists _. by iFrame "∗#%". }
    iModIntro. iDestruct (harris_node_combine_some with "p↦ [//] [p.n↪]") as "$"; [iLeft; by iFrame|].
    iModIntro. wp_pures.
    iApply "HΦ". iModIntro. by iFrame.
  }
  wp_apply (wp_cmpxchg_suc_offset with "p↦") as "p↦"; [by simplify_map_eq|naive_solver..|]. simpl.

  (* Get info about c *)
  iDestruct (Nodes_rm_idx_remove with "Nodes") as (?) "[(cM & c↪□' & c.n↪ & %HLc_n) Nodes]"; [exact HLc|lia|]; simpl.
  iDestruct (hazptr.(shield_managed_agree) with "cS cM") as %[= <-].
  iDestruct (ghost_map_elem_agree with "c↪□ c↪□'") as %[= <-].
  destruct b; simpl.
  all: iDestruct (ghost_map_elem_agree with "c.n↪ c.n↪□") as %[= ->].
  iClear "c.n↪ c↪□'".

  set (L' := delete (S idx) L).
  assert (get_abs_state L = get_abs_state L') as ->.
  { rewrite -(take_drop (S idx) L).
    subst L'. rewrite delete_take_drop !get_abs_state_app.
    f_equal. apply drop_S in HLc. rewrite Nat.add_1_r in HLc.
    by rewrite HLc get_abs_state_cons.
  }
  apply list_lookup_fmap_Some in HLc_n as [[[? b] ?] [HLc_n [= <-]]].
  iDestruct (get_persistent_Nodes_rm_idx_idx with "Nodes") as (?) "#(c_n↪□' & c_n.n↪ & _)"; [exact HLc_n|lia|].
  iDestruct (ghost_map_elem_agree with "c_n↪□ c_n↪□'") as %[= <-]; iClear "c_n↪□'".

  (* Update p. *)
  iCombine "p.n↪' p.n↪" as "p.n↪".
  iMod (ghost_map_update (Some (c_n,γ_c_n), false) with "●p_tag p.n↪") as "[●p_tag [p.n↪ p.n↪']]".
  iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes pM p.n↪".
  { iNext. repeat iExists _. iFrame "Linv ●p_all ●p_tag ∗#%".
    unfold AllPtrs,Nodes,Nodes_rm_idx_idx. iSplitL "PTRS"; [|iSplit].
    - iApply (big_sepM_mono with "PTRS").
      iIntros (γp' [k' p'] Hprts_p') "p'".
      iDestruct "p'" as "[$ [$|%HLp']]".
      iRight. iPureIntro. subst L'.
      apply elem_of_list_lookup in HLp' as [idx_p' HLp'].
      apply elem_of_list_lookup.
      destruct (decide (idx_p' < (S idx))) as [LT|GE].
      + exists idx_p'. rewrite lookup_delete_lt; done.
      + exists (idx_p' - 1). rewrite lookup_delete_ge; last first.
        { assert (idx_p' ≠ idx + 1); [|lia]. naive_solver. }
        rewrite -HLp'. f_equal. lia.
    - rewrite -{2}(take_drop (S idx) L).
      subst L'.
      apply drop_S in HLc. rewrite Nat.add_1_r in HLc.
      rewrite {2}delete_take_drop HLc !big_sepL_app.
      iDestruct "Nodes" as "(NodesTake & _ & NodesDrop)".
      assert (S idx <= length L).
      { assert (idx < length L); [|lia]. rewrite -lookup_lt_is_Some. eauto. }
      iSplitR "NodesDrop"; last first.
      { iApply (big_sepL_mono with "NodesDrop"). iIntros (idx' [[k' b'] [γl' l']] HLl') "l'".
        rewrite take_length_le; [|done]. repeat (case_decide; [lia|]).
        iDestruct "l'" as (l'_next) "($ & $ & l'.n↦ & %HLl'next)".
        iExists (l'_next). iFrame. iPureIntro.
        rewrite list_fmap_delete lookup_delete_ge; [|lia].
        rewrite -HLl'next. f_equal. lia.
      }
      rewrite (take_S_r L idx (p_k, false, (prev,γ_prev)) ltac:(done)) !big_sepL_app /=.
      iDestruct "NodesTake" as "[NodesTake _]". iSplitL "NodesTake"; [|iSplit; [|done]].
      { iApply (big_sepL_mono with "NodesTake"). iIntros (idx' [[k' b'] [γl' l']] HL2l') "l'".
        repeat case_decide.
        all: try (subst idx'; rewrite lookup_take_Some in HL2l'; lia).
        iDestruct "l'" as (l'_next) "($ & $ & l'.n↦ & %HL2l'next)".
        iExists (l'_next). iFrame. iPureIntro.
        apply lookup_lt_Some in HL2l' as LT. rewrite take_length_le in LT; [|lia].
        by rewrite list_fmap_delete lookup_delete_lt; [|lia].
      }
      iExists (Some (c_n,γ_c_n)). iFrame "∗#%". iPureIntro.
      rewrite Nat.add_0_r list_fmap_delete lookup_delete_ge take_length_le; [try lia..].
      get_third HLc_n.
      rewrite -HLc_n. f_equal. lia.
    - iPureIntro. subst L'. split_and!.
      + rewrite !list_fmap_delete. by apply delete_inf_Z_sorted.
      + rewrite lookup_delete_lt; [done|lia].
      + apply lookup_lt_Some in HLc as LT.
        assert (length L - 1 ≠ idx + 1) as NE.
        { intros EQ. rewrite -EQ in HLc. naive_solver. }
        rewrite Nat.add_1_r in HLc.
        rewrite lookup_delete_ge length_delete; eauto; [|lia].
        by replace (S (length L - 1 - 1)) with (length L - 1) by lia.
      + rewrite dom_insert_lookup_L; [done|].
        rewrite -elem_of_dom -Hdom elem_of_dom. eauto.
  }
  iModIntro. iDestruct (harris_node_combine_some with "p↦ [//] [p.n↪']") as "$"; [iLeft; by iFrame|].
  wp_pures.
  iApply "HΦ". iModIntro. iFrame.
Qed.

End harris_list.

Record hfind_spec {Σ} `{!heapGS Σ, !hlG Σ} {listN hazptrN : namespace}
    {DISJN : listN ## hazptrN}
    {hazptr : hazard_pointer_spec Σ hazptrN}
  : Type := HarrisFindSpec {
  harris_find_spec_code :> harris_find_code;
  harris_find_spec : harris_find_spec' listN hazptrN hazptr harris_find_spec_code.(harris_find);
}.

Global Arguments hfind_spec : clear implicits.
Global Arguments hfind_spec _ {_ _} _ _ _ _ : assert.

Section proof.
Context `{!heapGS Σ, !hlG Σ}.
Context (listN hazptrN : namespace) (DISJN : listN ## hazptrN).
Variable (hazptr : hazard_pointer_spec Σ hazptrN) (harris_find : hfind_spec Σ listN hazptrN DISJN hazptr).
Notation iProp := (iProp Σ).
Notation IsHList := (IsHList listN hazptrN hazptr).
Notation harris_find_spec := (harris_find.(harris_find_spec)).
Notation harris_helping_cas_spec := (harris_helping_cas_spec listN hazptrN DISJN hazptr).

Lemma harris_new_spec E γz d :
  ↑hazptrN ⊆ E →
  {{{ hazptr.(IsHazardDomain) γz d }}}
      harris_new #d @ E
  {{{ (l : loc) γp_a γp_t γl, RET #l; IsHList γp_a γp_t γl γz l ∗ HList γl [-∞ᵢ; ∞ᵢ] }}}.
Proof.
  iIntros (? Φ) "#IHD HΦ". wp_lam.
  wp_alloc pos as "pos↦" "†pos". wp_pures.
  wp_alloc neg as "neg↦" "†neg". wp_pures.
  do 2 (wp_apply (wp_store_offset with "neg↦") as "neg↦"; [by simplify_list_eq|]; wp_pures).
  do 2 (wp_apply (wp_store_offset with "pos↦") as "pos↦"; [by simplify_list_eq|]; wp_pures).
  wp_alloc l as "l↦" "†l". iClear "†l"; wp_pures.
  do 2 (wp_apply (wp_store_offset with "l↦") as "l↦"; [by simplify_list_eq|]; wp_pures).

  (* Allocate ghosts *)
  iMod (ghost_var_alloc [-∞ᵢ; ∞ᵢ]) as (γl) "[Labs Linv]".
  iMod (ghost_map_alloc (∅ : gmap gname (inf_Z * blk))) as (γp_a) "[●p_all _]".
  iMod (ghost_map_alloc (∅ : gmap gname (option (blk * gname) * bool))) as (γp_t) "[●p_tag _]".
  iApply "HΦ". iSplitR "Labs"; last first.
  { iFrame. iPureIntro. repeat constructor. }

  (* Allocate resource for sentinels *)
  iMod (own_alloc (Excl ())) as (γ_pos) "pos"; [done|].
  iMod (own_alloc (Excl ())) as (γ_neg) "neg"; [done|].
  iAssert (⌜γ_pos ≠ γ_neg⌝)%I as %NE.
  { iIntros (->). by iCombine "pos neg" gives %?. }
  iMod (ghost_map_insert_persist γ_neg (-∞ᵢ,neg) with "●p_all") as "[●p_all #neg↪□]"; [by simplify_map_eq|].
  iMod (ghost_map_insert_persist γ_pos (∞ᵢ,pos) with "●p_all") as "[●p_all #pos↪□]"; [by simplify_map_eq|].
  iMod (ghost_map_insert γ_pos (None, false) with "●p_tag") as "[●p_tag [pos.n↪ pos.n↪']]"; [set_solver|].
  iMod (ghost_map_insert γ_neg (Some (pos,γ_pos), false) with "●p_tag") as "[●p_tag [neg.n↪ neg.n↪']]"; [rewrite -not_elem_of_dom; set_solver|].

  (* Make managed for sentinels *)
  iMod (hazptr.(hazard_domain_register) (node γp_a γp_t) with "IHD [$neg↦ $†neg neg.n↪']") as "negM"; [solve_ndisj| |].
  { iExists _,(Some (_,_)),_. iSplit; [done|]. iFrame "∗#". iLeft. by iFrame. }
  iMod (hazptr.(hazard_domain_register) (node γp_a γp_t) with "IHD [$pos↦ $†pos pos.n↪']") as "posM"; [solve_ndisj| |].
  { iExists _,None,_. iSplit; [done|]. iFrame "∗#". iLeft. by iFrame. }

  iMod (array_persist with "l↦") as "l↦□".
  iEval (rewrite array_cons array_singleton) in "l↦□". iDestruct "l↦□" as "[l.h↦□ l.d↦□]".
  repeat iExists _. rewrite loc_add_0. iFrame "∗#%".

  iMod (inv_alloc listN _ (HListInternalInv _ _ _ _ _ _ _ _) with "[Linv ●p_all ●p_tag neg negM neg.n↪ pos posM pos.n↪]") as "$"; [|done].
  iNext. repeat iExists _.
  set (L := [(-∞ᵢ,false,(neg,γ_neg));(∞ᵢ,false,(pos,γ_pos))]).
  assert ([-∞ᵢ; ∞ᵢ] = get_abs_state L) as -> by done.
  iFrame "∗#". rewrite big_sepL_nil. iSplitL "neg pos"; [|iSplit].
  - rewrite /AllPtrs big_sepM_insert; [|by simplify_map_eq].
    rewrite big_sepM_singleton. iFrame. iSplit; iRight; iPureIntro.
    all: apply elem_of_list_lookup.
    + by exists 1.
    + by exists 0.
  - iSplitL "neg.n↪ negM"; [|iSplit; [|done]]; iExists _; by iFrame.
  - iPureIntro. split_and!.
    + repeat constructor.
    + done.
    + by eexists.
    + set_solver.
Qed.

Lemma harris_lookup_spec E γp_a γp_t γz γl l (k : Z) :
  (↑listN ∪ ↑hazptrN) ⊆ E →
  IsHList γp_a γp_t γl γz l -∗
  <<< ∀∀ (L : list inf_Z), HList γl L >>>
    (harris_lookup harris_find hazptr) #l #k @ E,(↑listN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
  <<< ∃∃ b, HList γl L ∗ ⌜lookup_post L b k⌝, RET #b >>>.
Proof using DISJN.
  intros ?.
  iIntros "IsHarris" (Φ) "AU". iDestruct "IsHarris" as (d h γh) "#(l.d↦□ & l.h↦□ & h↪□ & IHD & IsHarris)".
  wp_lam. wp_pures. wp_load. wp_pures.
  wp_apply (hazptr.(shield_new_spec) with "IHD [//]") as (p_s) "pS"; [solve_ndisj|]. wp_let.
  wp_apply (hazptr.(shield_new_spec) with "IHD [//]") as (c_s) "cS"; [solve_ndisj|]. wp_let.
  awp_apply (harris_find_spec with "IHD pS cS l.h↦□ h↪□ IsHarris"); [solve_ndisj|].
  iApply (aacc_aupd with "AU"); [done|].
  iIntros (L) "HList". iAaccIntro with "HList"; first eauto with iFrame.
  iIntros (b γ_p γ_c p c r_p_s r_c_s p_k c_k idx) "(HList & #p↪□ & #c↪□ & %Hp & %Hc & %Hp_k & %Hc_p_k) !>".
  iDestruct (HList_sorted with "HList") as %LSort.
  iRight. iExists b. iFrame. iSplit; [iPureIntro|]; last first.
  { iIntros "HΦ !> [pS cS]". wp_pures.
    wp_apply (hazptr.(shield_drop_spec) with "IHD pS") as "_"; [solve_ndisj|]; wp_pures.
    wp_apply (hazptr.(shield_drop_spec) with "IHD cS") as "_"; [solve_ndisj|]; wp_pures.
    by iApply "HΦ".
  }
  apply (prove_lookup_post idx p_k c_k); done.
Qed.

Lemma harris_insert_spec E γp_a γp_t γl γz l (k : Z) :
  (↑listN ∪ ↑hazptrN) ⊆ E →
  IsHList γp_a γp_t γl γz l -∗
  <<< ∀∀ (L : list inf_Z), HList γl L >>>
    (harris_insert harris_find hazptr) #l #k @ E,(↑listN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
  <<< ∃∃ (b : bool) (L' : list inf_Z), HList γl L' ∗
      ⌜if b then
        insert_succ_post L L' k
      else
        insert_fail_post L L' k⌝,
      RET #b
      >>>.
Proof using DISJN.
  intros ?.
  iIntros "IsHarris" (Φ) "AU". iDestruct "IsHarris" as (d h γh) "#(l.d↦□ & l.h↦□ & h↪□ & IHD & IsHarris)".
  wp_lam. wp_load. wp_pures.
  wp_apply (hazptr.(shield_new_spec) with "IHD [//]") as (p_s) "pS"; [solve_ndisj|]. wp_let.
  wp_apply (hazptr.(shield_new_spec) with "IHD [//]") as (c_s) "cS"; [solve_ndisj|]. wp_let.
  wp_alloc n as "n↦" "†n". wp_pures.
  wp_apply (wp_store_offset with "n↦") as "n↦"; [by simplify_list_eq|]; wp_seq. simpl.
  wp_bind (harris_insert_loop _ _ _ _ _)%E.
  move: #0 {1}Deactivated {2}Deactivated => next p_st c_st.
  iLöb as "IH" forall (next p_st c_st p_s c_s).
  wp_lam. wp_pure credit: "Lc". wp_pures.
  awp_apply (harris_find_spec with "IHD pS cS [//] [//] [//]"); [solve_ndisj|].
  iApply (aacc_aupd with "AU"); [solve_ndisj|]. iIntros (L) "HList". iAaccIntro with "HList"; first eauto with iFrame.
  iIntros ([] γ_p γ_c p c r_p_s r_c_s p_k c_k idx) "(HList & #p↪□ & #c↪□ & %Hp & %Hc & %Hp_k & %Hc_p_k) !>".
  { (* key found *)
    iRight. iExists false, L. iFrame. iSplit; [iPureIntro|]; last first.
    { iIntros "HΦ !> [pS cS]". wp_pures. wp_free; [done|]; wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "IHD pS") as "_"; [solve_ndisj|]; wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "IHD cS") as "_"; [solve_ndisj|]; wp_pures.
      by iApply "HΦ".
    }
    by apply (prove_insert_fail_post (S idx) c_k).
  }
  (* key not found *)
  iLeft. iFrame. iIntros "AU !> [pS cS]". wp_pures. clear dependent idx L p_st c_st.
  wp_apply (wp_store_offset with "n↦") as "n↦"; [by simplify_list_eq|]. wp_seq.
  simpl; clear next. wp_pures. wp_bind (CmpXchg _ _ _)%E.
  iInv "pS" as (?) "(_ & p↦ & >node & pS)".
  iDestruct (harris_node_destruct_agree with "node [//]") as (p_on ? ->) "[[% p.n↪]|[% #p.n↪□]]"; subst p_t; last first.
  { (* prev tagged, fail CAS and retry *)
    wp_apply (wp_cmpxchg_fail_offset with "p↦") as "p↦"; [done..|destruct p_on; simpl; auto|].
    iModIntro. iDestruct (harris_node_combine_on with "p↦ [//] [$p.n↪□]") as "$"; [by iRight|].
    wp_pures. wp_apply ("IH" with "AU pS cS †n n↦").
  }
  iInv "IsHarris" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
  iMod (lc_fupd_elim_later with "Lc Nodes") as "Nodes".
  iDestruct (ghost_map_lookup with "●p_all p↪□") as %Hptrs_p.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[p.n|%HLp]"; [exact Hptrs_p| |].
  { (* prev tagged, impossible *)
    iDestruct "p.n" as (γp_n p_n p_n_k) "[p.n↪□ p_n↪□]".
    iDestruct (ghost_map_elem_agree with "p.n↪□ p.n↪") as %[= ?].
  }
  (* prev not tagged, obtain next and check if it is still c. *)
  apply elem_of_list_lookup in HLp as [idx HLp].
  iDestruct (Nodes_remove with "Nodes") as (?) "[(pM & _ & p.n↪' & %HLp_next) Nodes]"; [exact HLp|]; simpl.
  iDestruct (ghost_map_elem_agree with "p.n↪ p.n↪'") as %[= <-].
  destruct (next_not_tail_is_Some idx L p_k false (p,γ_p) p_on) as [[p_n γ_p_n] [= ->]]; [naive_solver..|].
  destruct (decide (p_n = c)) as [->|NE]; last first.
  { (* curr changed from c, CAS must fail *)
    wp_apply (wp_cmpxchg_fail_offset with "p↦") as "p↦"; [done|simpl in *; naive_solver..|].
    iDestruct (Nodes_combine with "Nodes pM [] [p.n↪']") as "Nodes"; [done..|].
    iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    iModIntro. iDestruct (harris_node_combine_some with "p↦ [//] [p.n↪]") as "$"; [iLeft; by iFrame|].
    wp_pures. wp_apply ("IH" with "AU pS cS †n n↦").
  }
  (* curr is still c, CAS succeed *)
  iClear "IH".
  wp_apply (wp_cmpxchg_suc_offset with "p↦") as "p↦"; [simpl;auto..|]. simpl.
  apply list_lookup_fmap_Some in HLp_next as [[[c_k' b] [??]] [HLc [= <- <-]]].
  iAssert (⌜γ_p_n = γ_c ∧ c_k' = c_k⌝)%I with "[Nodes cS]" as %[-> ->].
  { iDestruct (Nodes_rm_idx_remove with "Nodes") as (?) "[(cM & c↪ & _) _]"; [exact HLc|lia|].
    iDestruct (hazptr.(shield_managed_agree) with "cS cM") as %->.
    by iDestruct (ghost_map_elem_agree with "c↪□ c↪") as %[= <-].
  }

  iMod (own_alloc (Excl ())) as (γ_n) "n"; [done|].

  set (L' := insert_middle_nbl (S idx) k false (n,γ_n) L) in *.
  iMod "AU" as (?) "[[Labs %HLabs] [_ Commit]]".
  iDestruct (ghost_var_agree with "Labs Linv") as %->.
  iMod (ghost_var_update_halves (get_abs_state L') with "Labs Linv") as "[Labs Linv]".
  assert (Sorted_inf_Z L'.*1.*1).
  { subst L'. rewrite insert_middle_nbl_insert_middle. apply insert_middle_inf_Z_sorted; [done| |].
    - intros z'. get_first HLp. rewrite take_last; [naive_solver|eauto].
    - intros z'. get_first HLc. rewrite lookup_drop Nat.add_0_r -Nat.add_1_r. naive_solver.
  }
  iMod ("Commit" $! true with "[$Labs]") as "HΦ".
  { iPureIntro. split.
    - by apply sorted_inf_Z_get_abs_state_sorted.
    - by apply (prove_insert_succ_post p_k c_k (p,γ_p) (c,γ_c) (n,γ_n) idx b).
  }

  iAssert (⌜p_all !! γ_n = None⌝)%I as %NotIn.
  { rewrite -not_elem_of_dom. iIntros (ElemOf).
    apply elem_of_dom in ElemOf as [[k' n'] ElemOf]. unfold AllPtrs.
    rewrite big_sepM_delete /=; [|exact ElemOf].
    iDestruct "PTRS" as "[[n' _] _]".
    by iCombine "n n'" gives %?.
  }
  assert (p_tag !! γ_n = None) as NotIn' by (rewrite -not_elem_of_dom -Hdom not_elem_of_dom; done).
  iCombine "p.n↪ p.n↪'" as "p.n↪".
  iMod (ghost_map_update (Some (n,γ_n),false) with "●p_tag p.n↪") as "[●p_tag [p.n↪ p.n↪']]".
  iMod (ghost_map_insert_persist γ_n with "●p_all") as "[●p_all #n↪□]"; [done|].
  iMod (ghost_map_insert γ_n (Some (c,γ_c), false) with "●p_tag") as "[●p_tag [n.n↪ n.n↪']]".
  { rewrite lookup_insert_ne; [done|]. intros ->. naive_solver. }
  iMod (hazptr.(hazard_domain_register) (node γp_a γp_t) with "IHD [$n↦ $†n n.n↪']") as "nM"; [solve_ndisj|..].
  { iExists _,(Some (_,_)),_. iFrame "#". iSplit; [done|]. iLeft. by iFrame. }
  iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes n n.n↪ nM pM p.n↪".
  { iNext. repeat iExists _. iFrame "Linv ●p_all ●p_tag #%".
    assert (idx + 1 < length L); [by apply lookup_lt_Some in HLc|].
    iSplitL "PTRS n".
    - rewrite /AllPtrs big_sepM_insert; [|by simplify_map_eq].
      iFrame "∗#%". iSplitR "PTRS".
      + iRight. iFrame. iPureIntro. rewrite elem_of_list_lookup.
        exists (S idx). subst L'. unfold insert_middle_nbl. simpl.
        rewrite lookup_app_r take_length_le; [|lia..].
        by rewrite Nat.sub_diag.
      + iApply (big_sepM_mono with "PTRS").
        iIntros (γ_l' [k' l'] H_ptrs_l) "l'".
        iDestruct "l'" as "[$ [$|%HLl']]".
        iRight. iPureIntro.
        subst L'. unfold insert_middle_nbl.
        rewrite -(take_drop (S idx) L) in HLl'.
        apply elem_of_app. apply elem_of_app in HLl' as [HLl'|HLl'].
        * by left.
        * right. apply elem_of_app. by right.
    - iSplitL; last first.
      { iPureIntro. split_and!; [done|..].
        - subst L'. unfold insert_middle_nbl. rewrite lookup_app_l; [|rewrite take_length_le; lia].
          rewrite lookup_take; [done|lia].
        - destruct HLt as [t HLt]. exists t.
          subst L'. unfold insert_middle_nbl. rewrite !app_length drop_length take_length_le; [|lia].
          rewrite /= Nat.sub_0_r lookup_app_r take_length_le; [|lia..].
          rewrite lookup_cons_ne_0; [|lia]. rewrite lookup_drop -HLt. f_equal. lia.
        - rewrite 2!dom_insert_L Hdom dom_insert_lookup_L; eauto.
          rewrite -elem_of_dom -Hdom elem_of_dom. eauto.
      }
      simpl.
      (* Split into three parts. *)
      iEval (rewrite -{1}(take_drop_middle L idx (p_k, false, (p,γ_p))); [|done]) in "Nodes".
      rewrite {1}(_ : take (S idx) L = take idx L ++ [(p_k, false, (p,γ_p))]); [|by apply take_S_r].
      rewrite !big_sepL_app. simpl.
      iDestruct "Nodes" as "(NodesTake & _ & NodesDrop)".
      assert (idx <= length L) by lia.
      rewrite !Nat.add_0_r !take_length_le /=; [|lia|done].
      iSplitL "NodesTake p.n↪ pM"; [iSplitR "p.n↪ pM"|iSplitL "n.n↪ nM"].
      + iApply (big_sepL_mono with "NodesTake"); iIntros (idx' [[z' b'] [γl' l']] Hidx') "idx'".
        apply lookup_take_Some in Hidx' as [_ LE].
        case_decide; [lia|].
        iDestruct "idx'" as (on) "($ & $ & l'.n↦ & %HLl'_next)".
        iExists on. iFrame. iPureIntro.
        assert (idx' + 1 < length (take (S idx) L.*2)).
        { rewrite take_length_le; [lia|]. rewrite fmap_length. lia. }
        rewrite !fmap_app /= fmap_take lookup_app_l; [|done].
        rewrite take_drop_middle in HLl'_next; [|done].
        rewrite -(take_drop (S idx) L) fmap_app lookup_app_l fmap_take in HLl'_next; done.
      + iSplit; [|done]. iExists (Some (n,γ_n)). iFrame "∗#". iPureIntro. subst L'.
        rewrite !fmap_app lookup_app_r /= fmap_length take_length_le; try lia.
        by rewrite Nat.add_1_r Nat.sub_diag.
      + iSplit; [|done]. iExists (Some (c,γ_c)). iFrame "∗#". iPureIntro. subst L'.
        rewrite !fmap_app lookup_app_r /= fmap_length take_length_le; try lia.
        rewrite /= (_: idx + 1 - idx = 1); [|lia].
        rewrite /= fmap_drop lookup_drop Nat.add_0_r -Nat.add_1_r.
        by get_third HLc.
      + iApply (big_sepL_mono with "NodesDrop"). iIntros (idx' [[z' b'] [γl' l']] Hidx') "idx'".
        case_decide; [lia|].
        iDestruct "idx'" as (on) "($ & $ & l'.n↦ & %HLl'_next)".
        iExists on. iFrame. iPureIntro.
        rewrite !fmap_app lookup_app_r /= fmap_length take_length_le /=; try lia.
        rewrite take_drop_middle in HLl'_next; [|done].
        rewrite (_ : idx + S idx' + 1 - idx = S (S idx')) /=; [|lia].
        rewrite fmap_drop lookup_drop -HLl'_next. f_equal. lia.
  }
  iModIntro. iDestruct (harris_node_combine_some with "p↦ [//] [p.n↪']") as "$"; [iLeft; by iFrame|].
  wp_pures.
  wp_apply (hazptr.(shield_drop_spec) with "IHD pS") as "_"; [solve_ndisj|]; wp_pures.
  wp_apply (hazptr.(shield_drop_spec) with "IHD cS") as "_"; [solve_ndisj|]; wp_pures.
  by iApply "HΦ".
Qed.

Lemma harris_delete_spec E γp_a γp_t γl γz l (k : Z) :
  (↑listN ∪ ↑hazptrN) ⊆ E →
  IsHList γp_a γp_t γl γz l -∗
  <<< ∀∀ (L : list inf_Z), HList γl L >>>
    (harris_delete harris_find hazptr) #l #k @ E,(↑listN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
  <<< ∃∃ (b : bool) (L' : list inf_Z), HList γl L' ∗
      ⌜if b then
        delete_succ_post L L' k
      else
        delete_fail_post L L' k⌝,
      RET #b
      >>>.
Proof using DISJN.
  intros ?.
  iIntros "#IsHarris" (Φ) "AU". iDestruct "IsHarris" as (d h γh) "#(l.d↦□ & l.h↦□ & h↪□ & IHD & IsHarris)".
  wp_lam. wp_load. wp_pures.
  wp_apply (hazptr.(shield_new_spec) with "IHD [//]") as (p_s) "pS"; [solve_ndisj|]. wp_let.
  wp_apply (hazptr.(shield_new_spec) with "IHD [//]") as (c_s) "cS"; [solve_ndisj|]. wp_let.
  wp_bind (harris_delete_loop _ _ _ _ _)%E.
  move: {1}Deactivated {2}Deactivated => p_st c_st.
  iLöb as "IH" forall (p_st c_st p_s c_s).
  wp_lam. wp_pures.
  awp_apply (harris_find_spec with "IHD pS cS [//] [//] IsHarris"); [solve_ndisj|].
  iApply (aacc_aupd with "AU"); [solve_ndisj|].
  iIntros (L) "HList". iAaccIntro with "HList"; first eauto with iFrame.
  iIntros (b γ_p γ_c p c r_p_s r_p_c p_k c_k idx) "(HList & #p↪□ & #c↪□ & %Hp & %Hc & %Hp_k & %Hc_p_k) !>".
  destruct b; last first.
  { (* key not found *)
    iRight. iDestruct (HList_sorted with "HList") as %LSort.
    iExists false, L. iFrame. iSplit; [iPureIntro|]; last first.
    { iIntros "HΦ !> [pS cS]". wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "IHD pS") as "_"; [solve_ndisj|]; wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "IHD cS") as "_"; [solve_ndisj|]; wp_pures.
      by iApply "HΦ".
    }
    by apply (prove_delete_fail_post idx p_k c_k).
  }
  (* key found *)
  subst c_k. iLeft. iFrame. iIntros "AU !> [pS cS]". wp_pures. clear dependent idx L p_st c_st.
  wp_bind (!_)%E.
  iInv "cS" as (?) "(_ & c↦ & >node & cS)".
  iDestruct (harris_node_destruct_agree with "node [//]") as (c_on c_t ->) "[[% c.n↪]|[% #c.n↪□]]"; subst c_t; last first.
  all: wp_apply (wp_load_offset with "c↦") as "c↦"; [done|].
  { (* tagged, retry delete *)
    iModIntro. iDestruct (harris_node_combine_on with "c↦ [//] [$c.n↪□]") as "$"; [by iRight|].
    wp_pures. wp_apply ("IH" with "AU pS cS").
  }
  iModIntro. iDestruct (harris_node_combine_on with "c↦ [//] [c.n↪]") as "$"; [iLeft; by iFrame|].
  wp_pures.
  wp_bind (CmpXchg _ _ _)%E.
  iInv "cS" as (?) "(_ & c↦ & >node & cS)".
  iDestruct (harris_node_destruct_agree with "node [//]") as (c_on' c_t ->) "[[% c.n↪]|[% #c.n↪□]]"; subst c_t; last first.
  { (* tagged, CAS must fail *)
    wp_apply (wp_cmpxchg_fail_offset with "c↦") as "c↦"; [done..|simpl;auto|].
    iModIntro. iDestruct (harris_node_combine_on with "c↦ [//] [$c.n↪□]") as "$"; [iRight; by iFrame|].
    wp_pures. wp_apply ("IH" with "AU pS cS").
  }
  (* Check if next changed. *)
  destruct (decide (fst <$> c_on = fst <$> c_on')) as [EQ|NE]; last first.
  { (* next changed, CAS must fail. *)
    wp_apply (wp_cmpxchg_fail_offset with "c↦") as "c↦"; [done|simpl;naive_solver..|].
    iModIntro. iDestruct (harris_node_combine_on with "c↦ [//] [c.n↪]") as "$"; [iLeft; by iFrame|].
    wp_pures. wp_apply ("IH" with "AU pS cS").
  }
  (* next same, CAS succeed and commit. *)
  iInv "IsHarris" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
  iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_c.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[c.n|%HLc]"; [exact Hptrs_c| |].
  { (* curr tagged, impossible *)
    iDestruct "c.n" as (γ_c_n c_n c_n_k) "[c.n↪□ c_n↪□]".
    iDestruct (ghost_map_elem_agree with "c.n↪□ c.n↪") as %[= ?].
  }
  wp_apply (wp_cmpxchg_suc_offset with "c↦") as "c↦"; [done|rewrite EQ;auto|simpl;auto..|]. simpl.
  apply elem_of_list_lookup in HLc as [i_c HLc].
  iDestruct (Nodes_remove with "Nodes") as (?) "[(cM & _ & c.n↪' & %HLc_next) Nodes]"; [exact HLc|]; simpl.
  iDestruct (ghost_map_elem_agree with "c.n↪ c.n↪'") as %[= <-].
  destruct (next_not_tail_is_Some i_c L (FinInt k) false (c,γ_c) c_on') as [[c_n γ_c_n] [= ->]]; [naive_solver..|].
  destruct c_on as [[? ?]|]; [|inversion EQ]. injection EQ as [= ->].
  iCombine "c.n↪ c.n↪'" as "c.n↪".
  iMod ((ghost_map_update (Some (c_n,γ_c_n), true)) with "●p_tag c.n↪") as "[●p_tag c.n↪]".
  iMod (ghost_map_elem_persist with "c.n↪") as "#c.n↪□".
  set (L' := <[i_c := (FinInt k, true, (c,γ_c))]> L).
  iMod "AU" as (?) "[[Labs %HLabs] [_ Commit]]".
  iDestruct (ghost_var_agree with "Labs Linv") as %[= ->].
  iMod (ghost_var_update_halves (get_abs_state L') with "Labs Linv") as "[Labs Linv]".
  assert (Sorted_inf_Z L'.*1.*1).
  { rewrite !list_fmap_insert /= list_insert_id; [done|]. by get_first HLc. }
  assert (i_c < length L) as i_c_LT; [by apply lookup_lt_Some in HLc|].
  iMod ("Commit" $! true with "[$Labs]") as "HΦ".
  { iPureIntro. split.
    - by apply sorted_inf_Z_get_abs_state_sorted.
    - by apply (prove_delete_succ_post (c,γ_c) i_c L k).
  }
  iModIntro.
  apply list_lookup_fmap_Some in HLc_next as [[[c_n_k b] ?] [HLc_next [= <-]]].
  iDestruct (get_persistent_Nodes_rm_idx with "Nodes") as (?) "#(c_n↪ & _)"; [exact HLc_next|lia|].
  iSplitL "Linv ●p_all ●p_tag PTRS Nodes cM".
  { iNext. repeat iExists _. iFrame "Linv ●p_tag ∗#%".
    iSplitL "PTRS"; [|iSplit].
    - unfold AllPtrs. repeat (rewrite (big_sepM_delete _ p_all); [|exact Hptrs_c]).
      iDestruct "PTRS" as "[c PTRS]". iSplitL "c".
      + iDestruct "c" as "[$ [$|%HL2c]]". iLeft.
        repeat iExists _. iFrame "#".
      + iApply (big_sepM_mono with "PTRS"). iIntros (γl' [z' l'] Hl') "l'".
        iDestruct "l'" as "[$ [$|%HLl']]".
        iRight. iPureIntro. subst L'. rewrite insert_take_drop; [|done].
        rewrite -(take_drop i_c L) elem_of_app in HLl'.
        apply elem_of_app. destruct HLl' as [HLl'|HLl'].
        * by left.
        * right. apply elem_of_cons. right.
          rewrite (drop_S L (FinInt k, false, (c,γ_c))) in HLl'; [|done].
          apply elem_of_cons in HLl' as [[= -> -> ->]|?]; [|done].
          by rewrite lookup_delete in Hl'.
    - unfold Nodes.
      rewrite (big_sepL_delete _ L' i_c); last first.
      { subst L'. rewrite list_lookup_insert; done. }
      iSplitR "Nodes".
      { unfold ListNode. iExists (Some (_,_)). iFrame "∗#". iPureIntro.
        subst L'. rewrite list_fmap_insert /= list_lookup_insert_ne; [|lia].
        by get_third HLc_next.
      }
      subst L'. rewrite {2}insert_take_drop; [|done].
      unfold Nodes_rm_idx.
      iEval (rewrite -{2}(take_drop_middle L i_c (FinInt k,false,(c,γ_c))); [|done]) in "Nodes".
      rewrite !big_sepL_app /=.
      iDestruct "Nodes" as "(NodesTake & _ & NodesDrop)".
      iSplitL "NodesTake"; [|iSplitR].
      + iApply (big_sepL_mono with "NodesTake").
        iIntros (i' [[z' b'] [γp' p']] Hi') "p'".
        apply lookup_take_Some in Hi' as [Hi' LT_i'].
        repeat case_decide; try lia.
        iDestruct "p'" as (on) "($ & $ & p'.n↦ & %HL2_i'_next)".
        iExists on. iFrame. iPureIntro. rewrite list_fmap_insert /=.
        destruct (decide (i_c = i' + 1)) as [->|NE].
        { get_third HLc. simplify_list_eq. rewrite list_lookup_insert; [done|].
          by rewrite fmap_length.
        }
        rewrite list_lookup_insert_ne; [done|lia].
      + rewrite take_length_le; last first.
        { apply lookup_lt_Some in HLc. lia. }
        case_decide; naive_solver.
      + iApply (big_sepL_mono with "NodesDrop").
        iIntros (i' [[z' b'] [γp' p']] Hi') "p'".
        rewrite take_length. case_decide; [lia|].
        iDestruct "p'" as (on) "($ & $ & p'.n↦ & %HL2_i'_next)".
        iExists on. iFrame. iPureIntro.
        by rewrite list_fmap_insert /= list_lookup_insert_ne; [|lia].
    - iPureIntro. subst L'. split_and!; [done|..].
      + rewrite list_lookup_insert_ne; [done|]. intros ->. naive_solver.
      + destruct HLt as [t HL2t]. exists t. rewrite insert_length.
        rewrite list_lookup_insert_ne; [done|]. intros ->. naive_solver.
      + rewrite dom_insert_lookup_L; [done|].
        rewrite -elem_of_dom -Hdom elem_of_dom. eauto.
  }
  iModIntro. iDestruct (harris_node_combine_some with "c↦ [//] [$c.n↪□]") as "$"; [by iRight|].
  wp_pure credit: "Lc". wp_pures.
  wp_pures. wp_apply (harris_helping_cas_spec with "[pS cS Lc]") as ([]) "(pS & cS & cM)"; [done|done|iFrame "∗#"|..]; wp_pures.

  1: wp_apply (hazptr.(hazard_domain_retire_spec) with "IHD cM") as "_"; [solve_ndisj|]; wp_pures.
  all: wp_apply (hazptr.(shield_drop_spec) with "IHD pS") as "_"; [solve_ndisj|]; wp_pures.
  all: wp_apply (hazptr.(shield_drop_spec) with "IHD cS") as "_"; [solve_ndisj|]; wp_pures.
  all: by iApply "HΦ".
Qed.

(* Ordered set definition *)
Definition HSet (γs : gname) (abs_S : gset Z) : iProp :=
  ∃ (γp_a γp_t γl γz : gname) abs_L, ⌜γs = encode (γp_a, γp_t, γl, γz)⌝ ∗
    ⌜abs_S = harris_list_into_set abs_L⌝ ∗ HList γl abs_L.

Global Instance HSet_timeless γs abs_S : Timeless (HSet γs abs_S).
Proof. apply _. Qed.

Definition IsHSet (γs : gname) (l : loc) : iProp :=
  ∃ (γp_a γp_t γl γz : gname), ⌜γs = encode (γp_a, γp_t, γl, γz)⌝ ∗
    IsHList γp_a γp_t γl γz l.

Global Instance IsHSet_persistent γs l : Persistent (IsHSet γs l).
Proof. apply _. Qed.

Lemma hset_new_spec :
  ordset_new_spec' listN hazptrN harris_new hazptr HSet IsHSet.
Proof.
  iIntros (γz d Φ) "!> #IHD HΦ".
  wp_apply (harris_new_spec with "IHD") as (l γp_a γp_t γl) "[#IsHarris Harris]"; [solve_ndisj|].

  remember (encode (γp_a, γp_t, γl, γz)) as γs eqn:Hγs.
  iApply "HΦ".
  iSplit.
  all: repeat iExists _; iFrame (Hγs) "∗#"; done.
Qed.

Lemma hset_lookup_spec :
  ordset_lookup_spec' listN hazptrN (harris_lookup harris_find hazptr) HSet IsHSet.
Proof using DISJN.
  iIntros (???).
  iDestruct 1 as (???? Hγs) "#IsHarris".
  iIntros (Φ) "AU".

  awp_apply (harris_lookup_spec with "IsHarris"); [solve_ndisj|].
  iApply (aacc_aupd with "AU"); [done|]. iIntros (abs_S) "Harris".
  iDestruct "Harris" as (?????? Habs_S) "Harris". encode_agree Hγs.

  iAaccIntro with "Harris".
  { iIntros "Harris !>". iSplitL "Harris".
    { repeat iExists _. iFrame (Hγs) "∗%". }
    eauto with iFrame.
  }

  iIntros (b) "[Harris %Habs_L] !>".
  iDestruct (HList_sorted with "Harris") as %HLSort.

  iRight. iExists b. iSplitL "Harris"; last first.
  { iIntros "$ !>". done. }
  iSplit.
  { repeat iExists _. iFrame (Hγs) "∗". done. }
  iPureIntro. subst abs_S.
  eapply lookup_list_post_to_set_post; done.
Qed.

Lemma hset_insert_spec :
  ordset_insert_spec' listN hazptrN (harris_insert harris_find hazptr) HSet IsHSet.
Proof using DISJN.
  iIntros (???).
  iDestruct 1 as (???? Hγs) "#IsHarris".
  iIntros (Φ) "AU".

  awp_apply (harris_insert_spec with "IsHarris"); [solve_ndisj|].
  iApply (aacc_aupd with "AU"); [done|]. iIntros (abs_S) "Harris".
  iDestruct "Harris" as (?????? Habs_S) "Harris". encode_agree Hγs.

  iAaccIntro with "Harris".
  { iIntros "Harris !>". iSplitL "Harris".
    { repeat iExists _. iFrame (Hγs) "∗%". }
    eauto with iFrame.
  }

  iIntros (b abs_L') "[Harris %Habs_L] !>".

  iRight. iExists b,_. iSplitL "Harris"; last first.
  { iIntros "$ !>". done. }
  iSplit.
  { repeat iExists _. iFrame (Hγs) "∗". done. }
  iPureIntro. subst abs_S.
  eapply insert_list_post_to_set_post. done.
Qed.

Lemma hset_delete_spec :
  ordset_delete_spec' listN hazptrN (harris_delete harris_find hazptr) HSet IsHSet.
Proof using DISJN.
  iIntros (???).
  iDestruct 1 as (???? Hγs) "#IsHarris".
  iIntros (Φ) "AU".

  awp_apply (harris_delete_spec with "IsHarris"); [solve_ndisj|].
  iApply (aacc_aupd with "AU"); [done|]. iIntros (abs_S) "Harris".
  iDestruct "Harris" as (?????? Habs_S) "Harris". encode_agree Hγs.
  iDestruct (HList_sorted with "Harris") as %HLSort.

  iAaccIntro with "Harris".
  { iIntros "Harris !>". iSplitL "Harris".
    { repeat iExists _. iFrame (Hγs) "∗%". }
    eauto with iFrame.
  }

  iIntros (b abs_L') "[Harris %Habs_L] !>".

  iRight. iExists b,_. iSplitL "Harris"; last first.
  { iIntros "$ !>". done. }
  iSplit.
  { repeat iExists _. iFrame (Hγs) "∗". done. }
  iPureIntro. subst abs_S.
  eapply delete_list_post_to_set_post; done.
Qed.

#[export] Typeclasses Opaque HSet IsHSet.

End proof.
