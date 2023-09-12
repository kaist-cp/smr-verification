From iris.base_logic.lib Require Import invariants ghost_var ghost_map.
From smr.program_logic Require Import atomic.
From smr.lang Require Import lang proofmode notation.
From smr Require Import sorted_list.
From iris.prelude Require Import options.

From smr Require Import helpers no_recl.spec_ordered_set no_recl.code_harris_operations.

Set Printing Projections.

Local Open Scope nat_scope.

Class hlG Σ := HLG {
  harris_list_absG :> ghost_varG Σ (list inf_Z);
  harris_list_ptrs_allG :> ghost_mapG Σ loc inf_Z;
}.

Definition hlΣ : gFunctors := #[ghost_varΣ (list inf_Z); ghost_mapΣ loc inf_Z].

Global Instance subG_hlΣ {Σ} :
  subG hlΣ Σ → hlG Σ.
Proof. solve_inG. Qed.

Section harris_list.
Context `{!heapGS Σ, !hlG Σ}.
Notation iProp := (iProp Σ).
Context (listN : namespace).

Implicit Types
  (γp_a γl : gname)
  (p_all : gmap loc inf_Z)
  (L : list inf_Z).

Definition HList γl L : iProp := ghost_var γl (1/2) L ∗ ⌜Sorted_inf_Z L⌝.

Global Instance HList_Timeless γl L : Timeless (HList γl L).
Proof. apply _. Qed.

Lemma HList_sorted γl L :
  HList γl L -∗ ⌜Sorted_inf_Z L⌝.
Proof. iDestruct 1 as "[_ $]". Qed.

Definition AllPtrs p_all (L : list (inf_Z * bool * loc)) γp_a : iProp :=
  [∗ map] p ↦ k ∈ p_all,
    (p +ₗ key) ↦□ #(LitInt k) ∗
    ((∃ (p_n : loc) (p_n_k : inf_Z),
      (p +ₗ next) ↦□ #(Some p_n &ₜ 1) ∗ p_n ↪[γp_a]□ p_n_k)
      ∨ ⌜(k, false, p) ∈ L⌝).

Global Instance AllPtrs_timeless p_all (L : list (inf_Z * bool * loc)) γp_a : Timeless (AllPtrs p_all L γp_a).
Proof. apply _. Qed.

Definition ListNode (i : nat) (kbp : inf_Z * bool * loc) (L : list (inf_Z * bool * loc)) γp_a : iProp :=
  ∃ (on : option loc), let '(k,b,p) := kbp in
    (p +ₗ key) ↦□ #(LitInt k) ∗
    p ↪[γp_a]□ k ∗
    (if (b : bool) then
      (p +ₗ next) ↦□ #(on &ₜ 1)
      else
      (p +ₗ next) ↦ #(on &ₜ 0)) ∗
    ⌜L.*2 !! (i + 1)%nat = on⌝.

Definition Nodes (L : list (inf_Z * bool * loc)) γp_a : iProp :=
  [∗ list] i ↦ kbp ∈ L, ListNode i kbp L γp_a.

Definition Nodes_rm_idx idx (L : list (inf_Z * bool * loc)) γp_a : iProp :=
  [∗ list] i ↦ kbp ∈ L,
    if decide (i = idx) then emp else ListNode i kbp L γp_a.

Definition Nodes_rm_idx_idx idx idx' (L : list (inf_Z * bool * loc)) γp_a : iProp :=
  [∗ list] i ↦ kbp ∈ L,
  if decide (i = idx') then emp else (if decide (i = idx) then emp else ListNode i kbp L γp_a).

Definition HListInternalInv h γp_a γl : iProp :=
  ∃ p_all (L : list (inf_Z * bool * loc)),
    ghost_var γl (1/2) (get_abs_state L) ∗
    ghost_map_auth γp_a 1 p_all ∗
    AllPtrs p_all L γp_a ∗
    Nodes L γp_a ∗
    ⌜Sorted_inf_Z (L.*1.*1) ∧
     L !! 0 = Some (-∞ᵢ, false, h) ∧
     (∃ t, L !! (length L - 1) = Some (∞ᵢ, false, t))⌝.

Definition IsHList (γp_a γl : gname) (l : loc) : iProp :=
  ∃ (h : loc), (l +ₗ head) ↦□ #h ∗ h ↪[γp_a]□ -∞ᵢ ∗
    inv listN (HListInternalInv h γp_a γl).

Global Instance IsHList_Persistent γp_a γl l : Persistent (IsHList γp_a γl l).
Proof. apply _. Qed.

Lemma get_persistent_Nodes (L : list (inf_Z * bool * loc)) idx k b p γp_a :
  L !! idx = Some (k,b,p) →
  Nodes L γp_a -∗
  ∃ pn, (p +ₗ key) ↦□ #(LitInt k) ∗ p ↪[γp_a]□ k ∗ (if (b : bool) then (p +ₗ next) ↦□ #(pn &ₜ 1) else True) ∗ ⌜L.*2 !! (idx + 1)%nat = pn⌝.
Proof.
  iIntros (Hidx) "Nodes". unfold Nodes,ListNode.
  rewrite big_sepL_delete; [|exact Hidx].
  iDestruct "Nodes" as "[p _]".
  iDestruct "p" as (pn) "($ & $ & p.n↦ & %Hp)". iExists pn.
  destruct b; iFrame "∗%".
Qed.

Lemma get_persistent_Nodes_rm_idx (L : list (inf_Z * bool * loc)) idx k b p γp_a idx' :
  L !! idx = Some (k,b,p) →
  idx ≠ idx' →
  Nodes_rm_idx idx' L γp_a -∗
  ∃ pn, (p +ₗ key) ↦□ #(LitInt k) ∗ p ↪[γp_a]□ k ∗ (if (b : bool) then (p +ₗ next) ↦□ #(pn &ₜ 1) else True) ∗ ⌜L.*2 !! (idx + 1)%nat = pn⌝.
Proof.
  iIntros (Hidx NE) "Nodes". unfold Nodes_rm_idx,ListNode.
  rewrite big_sepL_delete; [|exact Hidx].
  iDestruct "Nodes" as "[p _]". case_decide; [lia|].
  iDestruct "p" as (pn) "($ & $ & p.n↦ & %Hp)". iExists pn.
  destruct b; iFrame "∗%".
Qed.

Lemma Nodes_remove (L : list (inf_Z * bool * loc)) idx k b p γp_a :
  L !! idx = Some (k,b,p) →
  Nodes L γp_a -∗
  ∃ (on : option loc),
  ((p +ₗ key) ↦□ #(LitInt k) ∗
    p ↪[γp_a]□ k ∗
    (if (b : bool) then
      (p +ₗ next) ↦□ #(on &ₜ 1)
      else
      (p +ₗ next) ↦ #(on &ₜ 0))%I ∗
    ⌜L.*2 !! (idx + 1)%nat = on⌝) ∗
  Nodes_rm_idx idx L γp_a.
Proof.
  iIntros (Hidx) "Nodes". unfold Nodes,ListNode.
  iEval (rewrite big_sepL_delete; [|exact Hidx]) in "Nodes".
  iDestruct "Nodes" as "[p Nodes]".
  iDestruct "p" as (pn) "(#$ & #$ & p.n↦ & %)". iExists pn.
  iFrame "∗#%".
Qed.

Lemma Nodes_combine (L : list (inf_Z * bool * loc)) idx k b p γp_a on :
  L !! idx = Some (k,b,p) →
  L.*2 !! (idx + 1) = on →
  Nodes_rm_idx idx L γp_a -∗
  (p +ₗ key) ↦□ #(LitInt k) -∗
  p ↪[γp_a]□ k -∗
  (if (b : bool) then
    (p +ₗ next) ↦□ #(on &ₜ 1)
  else
    (p +ₗ next) ↦ #(on &ₜ 0))%I -∗
  Nodes L γp_a.
Proof.
  iIntros (Hidx Hidx_next) "Nodes #p.k↦□ #p↪□ p.n↦". unfold Nodes,ListNode.
  iEval (rewrite big_sepL_delete; [|exact Hidx]). iFrame.
  iExists on. iFrame "∗#%".
Qed.

Lemma Nodes_rm_idx_remove (L : list (inf_Z * bool * loc)) idx' idx k b p γp_a :
  L !! idx = Some (k,b,p) →
  idx' ≠ idx →
  Nodes_rm_idx idx' L γp_a -∗
  ∃ (on : option loc),
  ((p +ₗ key) ↦□ #(LitInt k) ∗
    p ↪[γp_a]□ k ∗
    (if (b : bool) then
      (p +ₗ next) ↦□ #(on &ₜ 1)
      else
      (p +ₗ next) ↦ #(on &ₜ 0))%I ∗
    ⌜L.*2 !! (idx + 1)%nat = on⌝) ∗
  Nodes_rm_idx_idx idx' idx L γp_a.
Proof.
  iIntros (Hidx ?) "Nodes". unfold Nodes_rm_idx,ListNode.
  iEval (rewrite big_sepL_delete; [|exact Hidx]) in "Nodes".
  case_decide; [lia|].
  iDestruct "Nodes" as "[p Nodes]".
  iDestruct "p" as (pn) "(#$ & #$ & p.n↦ & %)". iExists pn.
  iFrame "∗#%".
Qed.

Lemma Nodes_rm_idx_combine (L : list (inf_Z * bool * loc)) idx k b p γp_a on idx' :
  L !! idx = Some (k,b,p) →
  L.*2 !! (idx + 1) = on →
  idx' ≠ idx →
  Nodes_rm_idx_idx idx' idx L γp_a -∗
  (p +ₗ key) ↦□ #(LitInt k) -∗
  p ↪[γp_a]□ k -∗
  (if (b : bool) then
    (p +ₗ next) ↦□ #(on &ₜ 1)
  else
    (p +ₗ next) ↦ #(on &ₜ 0))%I -∗
  Nodes_rm_idx idx' L γp_a.
Proof.
  iIntros (Hidx Hidx_next ?) "Nodes #p.k↦□ #p↪□ p.n↦". unfold Nodes_rm_idx,ListNode.
  iEval (rewrite big_sepL_delete; [|exact Hidx]).
  case_decide; [lia|]. iFrame.
  iExists on. iFrame "∗#%".
Qed.

Lemma get_persistent_AllPtrs p_all (L : list (inf_Z * bool * loc)) p k γp_a :
  p_all !! p = Some k →
  AllPtrs p_all L γp_a -∗
  (p +ₗ key) ↦□ #(LitInt k) ∗
  ((∃ (p_n : loc) (p_n_k : inf_Z), (p +ₗ next) ↦□ #(Some p_n &ₜ 1) ∗ p_n ↪[γp_a]□ p_n_k) ∨
  ⌜(k, false, p) ∈ L⌝).
Proof.
  iIntros (Hp) "PTRS". unfold AllPtrs. rewrite big_sepM_delete; [|exact Hp].
  iDestruct "PTRS" as "[$ _]".
Qed.

Global Instance case_next_node_persistent (b : bool) (p : loc) (pn : option loc) : Persistent (if (b : bool) then (p +ₗ next) ↦□ #(pn &ₜ 1) else True)%I.
Proof. destruct b; apply _. Qed.

Definition harris_find_spec' (harris_find : val) : Prop :=
  ∀ (* Auxillary *) E (k : Z)
    (* harris inv *) (h : loc) γp_a γl
    (* other locs *) l,
  ↑listN ⊆ E →
  ⊢(l +ₗ head) ↦□ #h -∗
  h ↪[γp_a]□ -∞ᵢ -∗
  inv listN (HListInternalInv h γp_a γl) -∗
  <<< ∀∀ L, HList γl L >>>
    harris_find #l #k @ E,↑listN,∅
  <<< ∃∃ (b : bool) (prev curr : loc) (prev_k curr_k : inf_Z) (idx : nat),
      HList γl L ∗
      (* prev and curr are from the list. *)
      prev ↪[γp_a]□ prev_k ∗ curr ↪[γp_a]□ curr_k ∗
      ⌜L !! idx = Some prev_k ∧
      L !! (S idx) = Some curr_k ∧
      (* prev, c_prev_k and curr's key values are correct *)
      (prev_k < k)%inf_Z ∧ if b then curr_k = k else (k < curr_k)%inf_Z⌝,
      RET (#b, #prev, #curr)
      >>>.

Definition harris_find_au E γp_a γl (k : Z) (Φ : val → iProp) : iProp :=
  AU << ∃∃ L, HList γl L >> @ E ∖ ↑listN, ∅
     << ∀∀ (b : bool) (prev curr : loc) (prev_k curr_k : inf_Z) (idx : nat),
        HList γl L ∗
        prev ↪[ γp_a ]□ prev_k ∗ curr ↪[ γp_a ]□ curr_k ∗
        ⌜L !! idx = Some prev_k ∧
        L !! (S idx) = Some curr_k ∧
        (prev_k < k)%inf_Z ∧ if b then curr_k = k else (k < curr_k)%inf_Z⌝,
      COMM (True -∗ Φ (#b, #prev, #curr)%V) >>.

Definition harris_helping_cas_spec' : Prop :=
  ∀ (committing : bool) Φ pr pr_v h γp_a γl (prev anchor curr : loc) p_k c_k (k : Z) E,
  ↑listN ⊆ E →
  (p_k < k)%inf_Z →
  {{{ inv listN (HListInternalInv h γp_a γl) ∗
      prev ↪[ γp_a ]□ p_k ∗
      curr ↪[ γp_a ]□ c_k ∗
      (anchor +ₗ next) ↦□ #(Some curr &ₜ 1) ∗
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

End harris_list.

Record hfind_spec {Σ} `{!heapGS Σ, !hlG Σ} {listN} : Type := HarrisFindSpec {
  harris_find_spec_code :> harris_find_code;
  harris_find_spec : harris_find_spec' listN harris_find_spec_code.(harris_find);
  harris_helping_cas_spec : harris_helping_cas_spec' listN;
}.

Global Arguments hfind_spec : clear implicits.
Global Arguments hfind_spec _ {_ _} _ : assert.

Section proof.
Context `{!heapGS Σ, !hlG Σ}.
Context (listN : namespace).
Variable (harris_find : hfind_spec Σ listN).
Notation iProp := (iProp Σ).
Notation IsHList := (IsHList listN).
Notation harris_find_spec := (harris_find.(harris_find_spec)).
Notation harris_helping_cas_spec := (harris_find.(harris_helping_cas_spec)).

Lemma harris_new_spec E :
  {{{ True }}}
      harris_new #() @ E
  {{{ (l : loc) γp_a γl, RET #l; IsHList γp_a γl l ∗ HList γl [-∞ᵢ; ∞ᵢ] }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_alloc pos as "pos↦" "†pos". iClear "†pos". wp_pures.
  wp_alloc neg as "neg↦" "†neg". iClear "†neg". wp_pures.
  iAssert (⌜blk_to_loc pos ≠ blk_to_loc neg⌝)%I as %NE.
  { iIntros ([= ->]). rewrite !array_cons. iDestruct "pos↦" as "[pos↦ _]".
    iDestruct "neg↦" as "[neg↦ _]". by iDestruct (mapsto_ne with "pos↦ neg↦") as %?.
  }
  do 2 (wp_apply (wp_store_offset with "neg↦") as "neg↦"; [by simplify_list_eq|]; wp_pures).
  do 2 (wp_apply (wp_store_offset with "pos↦") as "pos↦"; [by simplify_list_eq|]; wp_pures).
  wp_alloc l as "l↦" "†l". iClear "†l"; wp_pures.
  simpl. rewrite array_singleton !array_cons.
  iDestruct "neg↦" as "(neg.n↦ & neg.k↦ & _)".
  iDestruct "pos↦" as "(pos.n↦ & pos.k↦ & _)".
  wp_store.
  iMod (ghost_var_alloc [-∞ᵢ; ∞ᵢ]) as (γl) "[Labs Linv]".
  iMod (ghost_map_alloc ∅) as (γp_a) "[●p_all _]".
  iAssert (HList _ _) with "[Labs]" as "HList".
  { repeat iExists _. iFrame. iPureIntro. repeat constructor. }
  set (L := [(-∞ᵢ,false,blk_to_loc neg);(∞ᵢ,false,blk_to_loc pos)]).
  assert ([-∞ᵢ; ∞ᵢ] = get_abs_state L) as HLabs. { unfold get_abs_state. simpl. naive_solver. }
  iMod (mapsto_persist with "l↦") as "#l↦□".
  iMod (mapsto_persist with "neg.k↦") as "#neg.k↦□".
  iMod (mapsto_persist with "pos.k↦") as "#pos.k↦□".
  iMod ((ghost_map_insert_persist (blk_to_loc neg) -∞ᵢ) with "●p_all") as "[●p_all #neg↪□]"; [by simplify_map_eq|].
  iMod ((ghost_map_insert_persist (blk_to_loc pos) ∞ᵢ) with "●p_all") as "[●p_all #pos↪□]"; [by simplify_map_eq|].
  iMod (inv_alloc listN _ (HListInternalInv _ _ _) with "[Linv ●p_all neg.n↦ pos.n↦]") as "#?".
  { repeat iExists _. rewrite HLabs. iFrame "∗#". rewrite big_sepL_nil. iSplitR; [|iSplit].
    - unfold AllPtrs. iNext.
      do 2 (rewrite big_sepM_delete; [|by simplify_map_eq]; rewrite delete_insert; [|by simplify_map_eq]).
      rewrite big_sepM_empty. iFrame "∗#". iSplit; iRight; iPureIntro; apply elem_of_list_lookup.
      + by exists 1.
      + by exists 0.
    - iSplitL "neg.n↦"; [|iSplit; [|done]].
      all: iExists _; iFrame; iPureIntro; by simplify_list_eq.
    - iPureIntro. split_and!.
      + repeat constructor.
      + by simplify_list_eq.
      + eexists. by simplify_list_eq.
  }
  iAssert (IsHList _ _ _) as "#IsHarris".
  { repeat iExists _. iFrame "∗#%". }
  iApply "HΦ". by iFrame "∗#".
Qed.

Lemma harris_lookup_spec E γp_a γl l (k : Z) :
  ↑listN ⊆ E →
  IsHList γp_a γl l -∗
  <<< ∀∀ L, HList γl L >>>
    harris_lookup harris_find #l #k @ E,↑listN,∅
  <<< ∃∃ b, HList γl L ∗ ⌜lookup_post L b k⌝, RET #b >>>.
Proof.
  intros ?.
  iIntros "#IsHarris" (Φ) "AU". iDestruct "IsHarris" as (h) "(l.h↦□ & h↪□ & IsHarris)".
  wp_lam. wp_pures.
  awp_apply (harris_find_spec with "l.h↦□ h↪□ IsHarris"); [solve_ndisj|].
  iApply (aacc_aupd with "AU"); [solve_ndisj|].
  iIntros (L) "HList". iAaccIntro with "HList"; first eauto with iFrame.
  iIntros (b p c p_k c_k idx) "(HList & #p↪□ & #c↪□ & %Hp & %Hc & %Hp_k & %Hc_p_k) !>".
  iDestruct (HList_sorted with "HList") as %LSort.
  iRight. iExists b. iFrame.
  iSplit; [iPureIntro|]; last first.
  { iIntros "HΦ !> _". wp_pures. by iApply "HΦ". }
  apply (prove_lookup_post idx p_k c_k); done.
Qed.

Lemma harris_insert_spec E γp_a γl l (k : Z) :
  ↑listN ⊆ E →
  IsHList γp_a γl l -∗
  <<< ∀∀ L, HList γl L >>>
    harris_insert harris_find #l #k @ E,↑listN,∅
  <<< ∃∃ (b : bool) L', HList γl L' ∗
      ⌜if b then
        insert_succ_post L L' k
      else
        insert_fail_post L L' k⌝,
      RET #b
      >>>.
Proof.
  intros ?.
  iIntros "#IsHarris" (Φ) "AU". iDestruct "IsHarris" as (h) "(l.h↦□ & h↪□ & IsHarris)".
  wp_lam. wp_pures.
  wp_alloc n' as "n↦" "†n"; set (n := blk_to_loc n') in *. wp_pures.
  wp_apply (wp_store_offset with "n↦") as "n↦"; [by simplify_list_eq|]; wp_seq.
  simpl.
  move: {1}#0 => next.
  iLöb as "IH" forall (next).
  wp_lam. wp_pures.
  awp_apply (harris_find_spec with "l.h↦□ h↪□ IsHarris"); [solve_ndisj|].
  iApply (aacc_aupd with "AU"); [solve_ndisj|].
  iIntros (L) "HList". iDestruct (HList_sorted with "HList") as %LSort.
  iAaccIntro with "HList"; first eauto with iFrame.
  iIntros (b p c p_k c_k idx) "(HList & #p↪□ & #c↪□ & %Hp & %Hc & %Hp_k & %Hc_p_k) !>".
  destruct b.
  { (* key found *)
    iRight. iExists false, L. iFrame.
    iSplit; [iPureIntro|]; last first.
    { iIntros "HΦ !> _". wp_pures. wp_free; [done|]. by iApply "HΦ". }
    by apply (prove_insert_fail_post (S idx) c_k).
  }
  (* key not found *)
  iLeft. iFrame. iIntros "AU !> _". wp_pures. clear dependent idx L.
  wp_apply (wp_store_offset with "n↦") as "n↦"; [by simplify_list_eq|].
  simpl; clear next.
  wp_pures. wp_bind (CmpXchg _ _ _)%E.
  iInv "IsHarris" as (p_all L) "(>Linv & >●p_all & >PTRS & Nodes & >(%HL & %HLh & %HLt))".
  iDestruct (ghost_map_lookup with "●p_all p↪□") as %Hptrs_p.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[p.k↦□ [p.n|%HLp]]"; [exact Hptrs_p| |].
  { (* prev tagged, fail CAS and retry *)
    iDestruct "p.n" as (p_n p_n_k) "[p.n↦□ p_n↪□]".
    wp_cmpxchg_fail.
    iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    wp_pures. iApply ("IH" with "AU †n n↦").
  }
  (* prev not tagged, obtain next and check if it is still c. *)
  apply elem_of_list_lookup in HLp as [idx HLp].
  iDestruct (Nodes_remove with "Nodes") as (on) "[(_ & _ & p.n↦ & >%HLp_next) Nodes]"; [exact HLp|].
  destruct (decide (on = Some c)) as [->|NE]; last first.
  { (* curr changed from c, CAS must fail *)
    wp_cmpxchg_fail. iDestruct (Nodes_combine with "Nodes [] [] [p.n↦]") as "Nodes"; [done..|].
    iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    wp_pures. iApply ("IH" with "AU †n n↦").
  }
  (* curr is still c, CAS succeed *)
  iClear "IH". wp_cmpxchg_suc; [done|].
  apply list_lookup_fmap_Some in HLp_next as [[[c_k' b] ?] [HLc [= <-]]].
  iAssert (⌜c_k' = c_k⌝)%I with "[Nodes]" as %[= ->].
  { iDestruct (get_persistent_Nodes_rm_idx with "Nodes") as (?) "#(_ & c↪ & _)"; [exact HLc|lia|].
    by iDestruct (ghost_map_elem_agree with "c↪□ c↪") as %[= <-].
  }

  set (L' := insert_middle_nbl (S idx) k false n L) in *.
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
    - by apply (prove_insert_succ_post p_k c_k p c n idx b).
  }
  iSplitL "Linv ●p_all PTRS Nodes †n n↦ p.n↦".
  {  repeat iExists _.
    iAssert (⌜p_all !! n = None⌝)%I as %NotIn.
    { rewrite -not_elem_of_dom. iIntros (ElemOf).
      apply elem_of_dom in ElemOf as [k' ElemOf].
      iDestruct (get_persistent_AllPtrs with "PTRS") as "[n.k↦□ _]"; [exact ElemOf|].
      rewrite !array_cons. iDestruct "n↦" as "(_ & n.k↦ & _)".
      by iDestruct (mapsto_ne with "n.k↦ n.k↦□") as %?.
    }
    iMod (ghost_map_insert_persist n with "●p_all") as "[$ #n↪□]"; [done|].
    iFrame "Linv #%".
    iEval (rewrite array_cons array_singleton) in "n↦".
    iDestruct "n↦" as "[n.n↦ n.k↦]".
    iMod (mapsto_persist with "n.k↦") as "#n.k↦□".
    assert (idx + 1 < length L); [by apply lookup_lt_Some in HLc|].
    iSplitL "PTRS †n".
    - repeat iModIntro. unfold AllPtrs.
      iEval (rewrite (big_sepM_insert _ _ n); [|by simplify_map_eq]).
      iFrame "∗#%". iSplitR "PTRS".
      + iRight. iFrame. iPureIntro. rewrite elem_of_list_lookup.
        exists (S idx). subst L'. unfold insert_middle_nbl. simpl.
        rewrite lookup_app_r take_length_le; [|lia..].
        by rewrite Nat.sub_diag.
      + iApply (big_sepM_mono with "PTRS").
        iIntros (l' k' H_ptrs_l) "l'".
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
      }
      simpl.
      (* Split into three parts. *)
      iEval (rewrite -{1}(take_drop_middle L idx (p_k, false, p)); [|done]) in "Nodes".
      rewrite {1}(_ : take (S idx) L = take idx L ++ [(p_k, false, p)]); [|by apply take_S_r].
      rewrite !big_sepL_app. simpl.
      iDestruct "Nodes" as "(NodesTake & _ & NodesDrop)".
      repeat iModIntro.
      assert (idx <= length L) by lia.
      rewrite !Nat.add_0_r !take_length_le /=; [|lia|done].
      iSplitL "NodesTake p.n↦"; [iSplitR "p.n↦"|iSplitL "n.n↦"].
      + iApply (big_sepL_mono with "NodesTake"); iIntros (idx' [[z' b'] l'] Hidx') "idx'".
        apply lookup_take_Some in Hidx' as [_ LE].
        case_decide; [lia|].
        iDestruct "idx'" as (on) "($ & $ & l'.n↦ & %HLl'_next)".
        iExists on. iFrame. iPureIntro.
        assert (idx' + 1 < length (take (S idx) L.*2)).
        { rewrite take_length_le; [lia|]. rewrite fmap_length. lia. }
        rewrite !fmap_app /= fmap_take lookup_app_l; [|done].
        rewrite take_drop_middle in HLl'_next; [|done].
        rewrite -(take_drop (S idx) L) fmap_app lookup_app_l fmap_take in HLl'_next; done.
      + iSplit; [|done]. iExists (Some n). iFrame "∗#". iPureIntro. subst L'.
        rewrite !fmap_app lookup_app_r /= fmap_length take_length_le; try lia.
        by rewrite Nat.add_1_r Nat.sub_diag.
      + iSplit; [|done]. iExists (Some c). rewrite !loc_add_0. iFrame "∗#". iPureIntro. subst L'.
        rewrite !fmap_app lookup_app_r /= fmap_length take_length_le; try lia.
        rewrite /= (_: idx + 1 - idx = 1); [|lia].
        rewrite /= fmap_drop lookup_drop Nat.add_0_r -Nat.add_1_r.
        by get_third HLc.
      + iApply (big_sepL_mono with "NodesDrop"). iIntros (idx' [[z' b'] l'] Hidx') "idx'".
        case_decide; [lia|].
        iDestruct "idx'" as (on) "($ & $ & l'.n↦ & %HLl'_next)".
        iExists on. iFrame. iPureIntro.
        rewrite !fmap_app lookup_app_r /= fmap_length take_length_le /=; try lia.
        rewrite take_drop_middle in HLl'_next; [|done].
        rewrite (_ : idx + S idx' + 1 - idx = S (S idx')) /=; [|lia].
        rewrite fmap_drop lookup_drop -HLl'_next. f_equal. lia.
  }
  iModIntro. wp_pures. by iApply "HΦ".
Qed.

Lemma harris_delete_spec E γp_a γl l (k : Z) :
  ↑listN ⊆ E →
  IsHList γp_a γl l -∗
  <<< ∀∀ L, HList γl L >>>
    harris_delete harris_find #l #k @ E,↑listN,∅
  <<< ∃∃ (b : bool) L', HList γl L' ∗
      ⌜if b then
        delete_succ_post L L' k
      else
        delete_fail_post L L' k⌝,
      RET #b
      >>>.
Proof.
  intros ?.
  iIntros "#IsHarris" (Φ) "AU". unfold IsHList. iDestruct "IsHarris" as (h) "(l.h↦□ & h↪□ & IsHarris)".
  iLöb as "IH".
  wp_lam. wp_pures.
  awp_apply (harris_find_spec with "l.h↦□ h↪□ IsHarris"); [solve_ndisj|].
  iApply (aacc_aupd with "AU"); [solve_ndisj|].
  iIntros (L) "HList". iAaccIntro with "HList"; first eauto with iFrame.
  iIntros (b p c p_k c_k idx) "(HList & #p↪□ & #c↪□ & %Hp & %Hc & %Hp_k & %Hc_p_k) !>".
  destruct b; last first.
  { (* key not found *)
    iDestruct (HList_sorted with "HList") as %LSort.
    iRight. iExists false, L. iFrame.
    iSplit; [iPureIntro|]; last first.
    { iIntros "HΦ !> _". wp_pures. by iApply "HΦ". }
    by apply (prove_delete_fail_post idx p_k c_k).
  }
  (* key found *)
  subst c_k. iLeft. iFrame. iIntros "AU !> _". wp_pures. clear dependent idx L.
  wp_bind (!_)%E.
  iInv "IsHarris" as (p_all L) "(>Linv & >●p_all & >PTRS & Nodes & >(%HL & %HLh & %HLt))".
  iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_curr.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[c.k↦□ [c.n|%HL_curr]]"; [exact Hptrs_curr| |].
  { (* tagged, retry delete *)
    iDestruct "c.n" as (c_next ?) "[c.n↦□ _]".
    wp_load.
    iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    wp_pures. iApply ("IH" with "AU").
  }
  (* not tagged, continue and try CAS *)
  apply elem_of_list_lookup in HL_curr as [idx' HL_curr].
  iDestruct (Nodes_remove with "Nodes") as (c_next) "[(_ & _ & c.n↦ & >%HL_curr_next) Nodes]"; [exact HL_curr|].
  wp_load.
  iDestruct (Nodes_combine with "Nodes [] [] [c.n↦]") as "Nodes"; [done..|].
  iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
  { repeat iExists _. by iFrame "∗#%". }
  clear dependent p_all L.
  wp_pures. wp_bind (CmpXchg _ _ _)%E.
  iInv "IsHarris" as (p_all L) "(>Linv & >●p_all & >PTRS & Nodes & >(%HL & %HLh & %HLt))".
  iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_curr.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[_ [c.n|%HL_curr]]"; [exact Hptrs_curr| |].
  { (* tagged, CAS must fail *)
    iDestruct "c.n" as (c_next' ?) "[c.n↦□ _]".
    wp_cmpxchg_fail.
    iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    wp_pures. iApply ("IH" with "AU").
  }
  (* not tagged. Obtain points-to. *)
  apply elem_of_list_lookup in HL_curr as [idx'' HL_curr].
  iDestruct (Nodes_remove with "Nodes") as (c_next') "[(_ & _ & c.n↦ & >%HL_curr_next) Nodes]"; [exact HL_curr|].
  (* Check if next changed. *)
  destruct (decide (c_next = c_next')) as [->|NE]; last first.
  { (* next changed, CAS must fail. *)
    wp_cmpxchg_fail. iDestruct (Nodes_combine with "Nodes [] [] [c.n↦]") as "Nodes"; [done..|].
    iModIntro. iSplitL "Linv ●p_all PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    wp_pures. iApply ("IH" with "AU").
  }
  (* next same, CAS succeed and commit. *)
  wp_cmpxchg_suc.
  iMod (mapsto_persist with "c.n↦") as "#c.n↦□".
  set (L' := <[idx'' := (FinInt k, true, c )]> L).
  iMod "AU" as (?) "[[Labs %HLabs] [_ Commit]]".
  iDestruct (ghost_var_agree with "Labs Linv") as %[= ->].
  iMod (ghost_var_update_halves (get_abs_state L') with "Labs Linv") as "[Labs Linv]".
  assert (Sorted_inf_Z L'.*1.*1).
  { rewrite !list_fmap_insert /= list_insert_id; [done|]. by get_first HL_curr. }
  assert (idx'' < length L) as idx''_LT; [by apply lookup_lt_Some in HL_curr|].
  iMod ("Commit" $! true with "[$Labs]") as "HΦ".
  { iPureIntro. split.
    - by apply sorted_inf_Z_get_abs_state_sorted.
    - by apply (prove_delete_succ_post c idx'' L k).
  }
  iModIntro.
  destruct (next_not_tail_is_Some idx'' L (FinInt k) false c c_next') as [c_next [= ->]]; [naive_solver..|].
  apply list_lookup_fmap_Some in HL_curr_next as [[[c_n_k b] ?] [HLc [= <-]]].
  iDestruct (get_persistent_Nodes_rm_idx with "Nodes") as (?) "#(_ & c↪ & _)"; [exact HLc|lia|].
  iSplitL "Linv ●p_all PTRS Nodes".
  { iNext. repeat iExists _. iFrame "Linv ∗#%".
    rewrite assoc. iSplitL "PTRS Nodes"; [iSplitL "PTRS"|].
    - unfold AllPtrs. repeat (rewrite (big_sepM_delete _ p_all); [|exact Hptrs_curr]).
      iDestruct "PTRS" as "[c PTRS]". iSplitL "c".
      + iDestruct "c" as "[$ [$|%HLc']]". iLeft.
        repeat iExists _. iFrame "#".
      + iApply (big_sepM_mono with "PTRS"). iIntros (l' z' Hl') "l'".
        iDestruct "l'" as "[$ [$|%HLl']]".
        iRight. iPureIntro. subst L'. rewrite insert_take_drop; [|done].
        rewrite -(take_drop idx'' L) elem_of_app in HLl'.
        apply elem_of_app. destruct HLl' as [HLl'|HLl'].
        * by left.
        * right. apply elem_of_cons. right.
          rewrite (drop_S L (FinInt k, false, c)) in HLl'; [|done].
          apply elem_of_cons in HLl' as [[= -> ->]|?]; [|done].
          by rewrite lookup_delete in Hl'.
    - unfold Nodes.
      rewrite (big_sepL_delete _ L' idx''); last first.
      { subst L'. rewrite list_lookup_insert; done. }
      iSplitR.
      { unfold ListNode. iExists (Some c_next). iFrame "#". iPureIntro.
        subst L'. rewrite list_fmap_insert /= list_lookup_insert_ne; [|lia].
        by get_third HLc.
      }
      subst L'. rewrite {2}insert_take_drop; [|done].
      unfold Nodes_rm_idx.
      iEval (rewrite -{2}(take_drop_middle L idx'' (FinInt k,false,c)); [|done]) in "Nodes".
      rewrite !big_sepL_app /=.
      iDestruct "Nodes" as "(NodesTake & _ & NodesDrop)".
      iSplitL "NodesTake"; [|iSplitR].
      + iApply (big_sepL_mono with "NodesTake").
        iIntros (i' [[z' b'] p'] Hi') "p'".
        apply lookup_take_Some in Hi' as [Hi' LT_i'].
        repeat case_decide; try lia.
        iDestruct "p'" as (on) "($ & $ & p'.n↦ & %HL_i'_next)".
        iExists on. iFrame. iPureIntro. rewrite list_fmap_insert /=.
        destruct (decide (idx'' = i' + 1)) as [->|NE].
        { get_third HL_curr. simplify_list_eq. rewrite list_lookup_insert; [done|].
          by rewrite fmap_length.
        }
        rewrite list_lookup_insert_ne; [done|lia].
      + rewrite take_length_le; last first.
        { apply lookup_lt_Some in HLc. lia. }
        case_decide; naive_solver.
      + iApply (big_sepL_mono with "NodesDrop").
        iIntros (i' [[z' b'] p'] Hi') "p'".
        rewrite take_length. case_decide; try lia.
        iDestruct "p'" as (on) "($ & $ & p'.n↦ & %HL_i'_next)".
        iExists on. iFrame. iPureIntro.
        by rewrite list_fmap_insert /= list_lookup_insert_ne; [|lia].
    - iPureIntro. subst L'. split_and!; [done|..].
      + rewrite list_lookup_insert_ne; [done|]. intros ->. naive_solver.
      + destruct HLt as [t HLt]. exists t. rewrite insert_length.
        rewrite list_lookup_insert_ne; [done|]. intros ->. naive_solver.
  }
  wp_pures.
  wp_apply (harris_helping_cas_spec false Φ 1%positive []) as (?) "_"; [done|exact Hp_k|by iFrame "#"|].
  wp_pures.
  by iApply "HΦ".
Qed.

(* Ordered set definition *)
Definition HSet (γs : gname) (abs_S : gset Z) : iProp :=
  ∃ (γp_a γl : gname) abs_L, ⌜γs = encode (γp_a, γl)⌝ ∗
    ⌜abs_S = harris_list_into_set abs_L⌝ ∗ HList γl abs_L.

Global Instance HSet_timeless γs abs_S : Timeless (HSet γs abs_S).
Proof. apply _. Qed.

Definition IsHSet (γs : gname) (l : loc) : iProp :=
  ∃ (γp_a γl : gname), ⌜γs = encode (γp_a, γl)⌝ ∗
    IsHList γp_a γl l.

Global Instance IsHSet_persistent γs l : Persistent (IsHSet γs l).
Proof. apply _. Qed.

Lemma hset_new_spec :
  ordset_new_spec' listN harris_new HSet IsHSet.
Proof.
  iIntros (Φ) "!> _ HΦ".
  wp_apply (harris_new_spec with "[//]") as (l γp_a γl) "[#IsHarris Harris]".

  remember (encode (γp_a, γl)) as γs eqn:Hγs.
  iApply "HΦ".
  iSplit.
  all: repeat iExists _; iFrame (Hγs) "∗#"; done.
Qed.

Lemma hset_lookup_spec :
  ordset_lookup_spec' listN (harris_lookup harris_find) HSet IsHSet.
Proof.
  iIntros (???).
  iDestruct 1 as (?? Hγs) "#IsH".
  iIntros (Φ) "AU".

  awp_apply (harris_lookup_spec with "IsH"); [naive_solver|].
  iApply (aacc_aupd with "AU"); [done|]. iIntros (abs_S) "Harris".
  iDestruct "Harris" as (???? Habs_S) "Harris". encode_agree Hγs.

  iAaccIntro with "Harris".
  { iIntros "Harris !>". iSplitL "Harris".
    { repeat iExists _. iFrame (Hγs) "∗%". }
    eauto with iFrame.
  }

  iIntros (b) "[Harris %Habs_L] !>".

  iRight. iExists b. iSplitL "Harris"; last first.
  { iIntros "$ !>". done. }
  iSplit.
  { repeat iExists _. iFrame (Hγs) "∗". done. }
  iPureIntro. subst abs_S.
  eapply lookup_list_post_to_set_post; done.
Qed.

Lemma hset_insert_spec :
  ordset_insert_spec' listN (harris_insert harris_find) HSet IsHSet.
Proof.
  iIntros (???).
  iDestruct 1 as (?? Hγs) "#IsHarris".
  iIntros (Φ) "AU".

  awp_apply (harris_insert_spec with "IsHarris"); [solve_ndisj|].
  iApply (aacc_aupd with "AU"); [done|]. iIntros (abs_S) "Harris".
  iDestruct "Harris" as (???? Habs_S) "Harris". encode_agree Hγs.

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
  ordset_delete_spec' listN (harris_delete harris_find) HSet IsHSet.
Proof.
  iIntros (???).
  iDestruct 1 as (?? Hγs) "#IsHarris".
  iIntros (Φ) "AU".

  awp_apply (harris_delete_spec with "IsHarris"); [solve_ndisj|].
  iApply (aacc_aupd with "AU"); [done|]. iIntros (abs_S) "Harris".
  iDestruct "Harris" as (???? Habs_S) "Harris". encode_agree Hγs.
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
