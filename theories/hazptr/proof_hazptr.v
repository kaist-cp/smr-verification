From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var.
From smr.base_logic.lib Require Import coP_ghost_map ghost_vars coP_cancellable_invariants.
From smr.program_logic Require Import atomic.
From smr.logic Require Import token2.
From smr.lang Require Import proofmode notation.

From smr Require Import hazptr.spec_hazptr spec_slot_bag_oloc spec_retired_list.
From smr Require Import hazptr.code_hazptr code_slot_bag_oloc code_retired_list.
From smr Require Import helpers logic.reclamation.

From iris.prelude Require Import options.

Set Printing Projections.

Section hazptr.
Context `{!heapGS Σ, !reclamationG Σ} (N : namespace).
Implicit Types (R : resource Σ).
Notation iProp := (iProp Σ).

Context (sbs : slot_bag_spec Σ) (rls : retired_list_spec Σ).

Implicit Types
  (γsb γtok γinfo γdata γptrs γU γR γV : gname)
  (info : gmap positive (alloc * gname))
  (data : gmap positive gname)
  (ptrs : gmap blk positive)
  (sbvmap : gmap loc (bool * option blk))
  (slist : list loc)
  (rs : list (blk * nat * nat)).

Local Ltac exfr := (repeat iExists _); iFrame "∗#"; eauto.
Local Ltac tspd := try (iSplit; [done|]); try (iSplit; [|done]).

(* NOTE: γU ghost is actually not necessary in HP, because Managed can directly assert γR flag. *)

(* NOTE: Maybe γV ghost could've been 1D `slot ↦ Some ptr`.

  [∗ list] si ↦ slot ∈ slist, ∃ (b : bool) v (oi : option positive),
    ⌜ sbvmap !! slot = Some (b, v) ⌝ ∗
    (sid si) ↦p[γV]{1/2} oi ∗
    match oi with
    | Some i =>
        ⌜∃ info_i, info !! i = Some info_i ∧ b = true ∧ v = Some info_i.1.(addr) ⌝
        toknes for all ptrs except i
    | None =>
        all tokens

But what about γR?
*)

(*
|        | slist | ⊤∖slist |
|--------|-------|---------|
| info   | CC    | CU      |
| ⊤∖info | UC    | UU      |
*)
Definition CC γtok γinfo γptrs γU γR γV info sbvmap slist : iProp :=
  [∗ map] i ↦ info_i ∈ info, ∃ (U : bool),
    i ↦p[γU]{ 1/2/2 } U ∗
    [∗ list] si ↦ slot ∈ slist, ∃ (b : bool) v (V R : bool),
      ⌜ sbvmap !! slot = Some (b, v) ⌝ ∗
      (i,sid si) ↦p2[γV]{ 1/2 } V ∗
      (i,sid si) ↦p2[γR]{ 1/2 } R ∗
      ⌜ V → b = true ∧ v = Some info_i.1.(addr) ⌝ ∗
      ⌜ R → U ⌝ ∗
      match V, R with
      | true, true => False
      | true,_ | _,true => emp
      | _,_ => stok γtok i si
      end
  .

Definition CU γtok γinfo γptrs γU γR γV info sbvmap slist : iProp :=
  [∗ map] i ↦ info_i ∈ info, ∃ (U R : bool),
    i ↦p[γU]{ 1/2/2 } U ∗
    ({[i]},sids_from (length slist)) ↦P2[γR]{ 1/2 } R ∗
    ({[i]},sids_from (length slist)) ↦P2[γV] false ∗
    (if R then emp else toks γtok {[i]} (sids_from (length slist))) ∗
    ⌜R → U⌝.

Definition UC γtok γinfo γptrs γU γR γV info sbvmap slist : iProp :=
  ([∗ list] si ↦ slot ∈ slist, ∃ (b : bool) v,
    ⌜ sbvmap !! slot = Some (b, v) ⌝) ∗
  (⊤ ∖ gset_to_coPset (dom info)) ↦P[γU]{ 1/2 } false ∗
  (⊤ ∖ gset_to_coPset (dom info),sids_to (length slist)) ↦P2[γR] false ∗
  (⊤ ∖ gset_to_coPset (dom info),sids_to (length slist)) ↦P2[γV]{ 1/2 } false ∗
  toks γtok (⊤ ∖ gset_to_coPset (dom info)) (sids_to (length slist)).

Definition UU γtok γinfo γptrs γU γR γV info sbvmap slist : iProp :=
  (⊤ ∖ gset_to_coPset (dom info)) ↦P[γU]{ 1/2 } false ∗
  (⊤ ∖ gset_to_coPset (dom info),sids_from (length slist)) ↦P2[γR] false ∗
  (⊤ ∖ gset_to_coPset (dom info),sids_from (length slist)) ↦P2[γV] false ∗
  toks γtok (⊤ ∖ gset_to_coPset (dom info)) (sids_from (length slist)).

Definition GhostQuadrants γtok γinfo γptrs γU γR γV info sbvmap slist : iProp :=
  CC γtok γinfo γptrs γU γR γV info sbvmap slist ∗
  CU γtok γinfo γptrs γU γR γV info sbvmap slist ∗
  UC γtok γinfo γptrs γU γR γV info sbvmap slist ∗
  UU γtok γinfo γptrs γU γR γV info sbvmap slist.

Definition InactiveShield γV sbvmap slist : iProp :=
  [∗ list] si ↦ slot ∈ slist,
    match sbvmap !! slot with
    | Some (false, _) => (⊤,{[sid si]}) ↦P2[γV]{ 1/2 } false
    | _ => emp
    end.

Definition HazardDomain γsb γtok γinfo γdata γptrs γU γR γV (d hBag rSet : loc) : iProp :=
  ∃ info data ptrs sbvmap slist rs,

    ghost_map_auth γinfo 1 info ∗
    ghost_map_auth γdata 1 data ∗
    coP_ghost_map_auth γptrs 1 ptrs ∗

    sbs.(SlotBag) γsb hBag sbvmap slist ∗
    rls.(RetiredList) rSet rs ∗

    GhostQuadrants γtok γinfo γptrs γU γR γV info sbvmap slist ∗
    InactiveShield γV sbvmap slist ∗

    ([∗ map] p ↦ i ∈ ptrs, ∃ info_i,
      ⌜info !! i = Some info_i⌝ ∗
      (* Permission for freeing the pointer with this length.
      This is used for proving [hazard_domain_register]. *)
      †(Loc.blk_to_loc p)…info_i.1.(len)) ∗

    ([∗ list] rle ∈ rs, let '(r,len,_) := rle in ∃ i R,
      Retired (mgmtN N) (ptrsN N) γtok γinfo γdata γptrs γU γR r i len R) ∗

    ⌜dom info = dom data⌝ ∗
    ⌜∀ p i, ptrs !! p = Some i → ∃ z, info !! i = Some z ∧ z.1.(addr) = p ⌝
  .

Definition hazptrInvN := mgmtN N .@ "inv".

Definition IsHazardDomain γz (d : loc) : iProp :=
  ∃ γsb γtok γinfo γdata γptrs γU γR γV (hBag rSet : loc),
    ⌜γz = encode (γsb, γtok, γinfo, γdata, γptrs, γU, γR, γV)⌝ ∗
    (d +ₗ domHBag) ↦□ #hBag ∗
    (d +ₗ domRSet) ↦□ #rSet ∗
    inv hazptrInvN (HazardDomain γsb γtok γinfo γdata γptrs γU γR γV d hBag rSet).


Global Instance IsHazardDomain_Persistent γz d : Persistent (IsHazardDomain γz d).
Proof. apply _. Qed.

Definition Managed γz (p : blk) (data_i : gname) (size_i : nat) R : iProp :=
  ∃ γsb γtok γinfo γdata γptrs γU γR γV (i : positive),
    ⌜γz = encode (γsb, γtok, γinfo, γdata, γptrs, γU, γR, γV)⌝ ∗
    i ↪[γdata]□ data_i ∗
    ManagedBase (mgmtN N) (ptrsN N) γtok γinfo γptrs γU γR p i size_i (wrap_resource γdata R data_i).

Definition Protected γtok γinfo γdata γptrs γV (s : nat) (i : positive) (p : blk) (data_i : gname) R size_i : iProp :=
  i ↪[γdata]□ data_i ∗
  ProtectedBase (mgmtN N) (ptrsN N) γtok γinfo γptrs γV s i p (wrap_resource γdata R data_i) size_i.

Definition Shield γz (s : loc) (st : shield_state Σ) : iProp :=
  ∃ γsb γtok γinfo γdata γptrs γU γR γV
    (slot : loc) (idx : nat) (v : option blk),
    ⌜γz = encode (γsb, γtok, γinfo, γdata, γptrs, γU, γR, γV)⌝ ∗
    (s +ₗ shieldSlot) ↦ #slot ∗
    †s…shieldSize ∗
    sbs.(Slot) γsb slot idx v ∗
    match st with
    | Deactivated =>
        ⌜v = None⌝ ∗
        (⊤,{[sid idx]}) ↦P2[γV]{ 1/2 } false
    | NotValidated p =>
        ⌜v = Some p⌝ ∗
        (⊤,{[sid idx]}) ↦P2[γV]{ 1/2 } false
    | Validated p data_i R size_i => ∃ i,
        ⌜v = Some p⌝ ∗
        Protected γtok γinfo γdata γptrs γV idx i p data_i R size_i ∗
        (⊤ ∖ {[i]},{[sid idx]}) ↦P2[γV]{ 1/2 } false
    end.

(* Helper *)

Lemma big_sepL_seq {A} (Φ : nat → iProp) (l : list A) :
  ([∗ list] i ∈ seq 0 (length l), Φ i) ⊣⊢
  ([∗ list] i ↦ _ ∈ l, Φ i).
Proof.
  induction l as [|x l IH] using rev_ind; auto.
  rewrite length_app seq_app; simpl.
  do 2 rewrite big_sepL_app. rewrite IH.
  do 2 rewrite big_sepL_singleton. rewrite -plus_n_O.
  auto.
Qed.

(* Timelessnesses *)

Global Instance GhostQuadrants_timeless γtok γinfo γptrs γU γR γV info sbvmap slist:
  Timeless (GhostQuadrants γtok γinfo γptrs γU γR γV info sbvmap slist).
Proof. apply _. Qed.

Global Instance inactive_shield_timeless γV sbvmap slist :
  Timeless (InactiveShield γV sbvmap slist).
Proof. apply _. Qed.

(* Ghost maintenance lemmas *)

Lemma ghost_quadrants_alloc γinfo γptrs :
  ⊢ |==> ∃ γtok γU γR γV,
  GhostQuadrants γtok γinfo γptrs γU γR γV ∅ ∅ [].
Proof.
  iIntros.
  iMod (ghost_vars_top_alloc false) as (γU) "[●γUC ●γUU]".
  iMod (ghost_vars2_top_alloc false) as (γR) "●γR".
  iMod (ghost_vars2_top_alloc false) as (γV) "●γV".
  iMod (token2_alloc ⊤ ⊤) as (γtok) "●γtok".
  iExists γtok, γU, γR, γV.
  unfold GhostQuadrants, CC, CU, UC, UU.
  rewrite !big_sepM_empty /= !sids_to_0 !sids_from_0
          dom_empty_L gset_to_coPset_empty difference_empty_L.
  iFrame.
  (* Create empty ghosts *)
  do 2 (iMod ghost_vars2_get_empty_2 as "$").
  iApply token2_get_empty_2.
Qed.

Lemma ghost_quadrants_register i p γc_i size_p γtok γinfo γptrs γU γR γV info hmap slist :
  info !! i = None →
  GhostQuadrants γtok γinfo γptrs γU γR γV info hmap slist ==∗
  GhostQuadrants γtok γinfo γptrs γU γR γV (<[i := ({|addr:=p; len:=size_p|}, γc_i)]> info) hmap slist ∗
  i ↦p[γU]{1/2} false ∗
  ({[i]},⊤) ↦P2[γR]{ 1/2 } false ∗
  toks γtok {[i]} ∅.
Proof.
  iIntros (NotIn) "(●CC & ●CU & ●UC & ●UU)".
  (** Move from [UC] to [CC] *)
  iAssert (|==> CC _ _ _ _ _ _ _ _ _ ∗ UC _ _ _ _ _ _ _ _ _ ∗ toks γtok {[i]} ∅ ∗
    ({[i]},sids_to (length slist)) ↦P2[γR]{ 1/2 } false ∗
    i ↦p[γU]{1/2/2} false)%I with "[●CC ●UC]" as ">($ & $ & $ & ●Cr & ●Cu)".
  { iDestruct "●UC" as "(#hmap & ●UCu & ●UCr & ●UCv & ●toks)".
    rewrite -(top_difference_dom_union_not_in_singleton i info); last done.
    rewrite !ghost_vars2_insert_1; [|set_solver..].
    rewrite ghost_vars_insert; [|set_solver].
    unfold toks.
    rewrite token2_insert_1; [|set_solver].
    rewrite -gset_to_coPset_singleton -gset_to_coPset_union.
    rewrite -(dom_insert_L info i ({|addr:=p; len:=size_p|}, γc_i)).
    iDestruct "●UCr" as "[$ [●CCr $]]". iDestruct "●UCv" as "[$ ●CCv]".
    iDestruct "●UCu" as "[$ [●CCu $]]". iDestruct "●toks" as "[$ ●toks_i]".
    rewrite gset_to_coPset_singleton.

    iMod token2_get_empty_2 as "$".

    unfold CC. rewrite big_sepM_insert; last by done. iFrame "∗#".
    iInduction slist as [|si slist IH] using rev_ind; [by rewrite !big_sepL_nil|].
    rewrite length_app Nat.add_1_r sids_to_S.
    rewrite !big_sepL_snoc. iDestruct "hmap" as "[hmap %Hsi]".
    rewrite -!ghost_vars2_union_2; [|by apply sids_to_sid_disjoint..].
    rewrite -token2_union_2; [|by apply sids_to_sid_disjoint].
    unfold stok, toks.
    iDestruct "●CCr" as "[●CCr_s ●CCr]". iDestruct "●CCv" as "[●CCv_s ●CCv]".
    iDestruct "●toks_i" as "[●toks_i_s ●toks_i]".
    iDestruct ("IH" with "hmap ●CCr_s ●CCv_s ●toks_i_s") as ">$". iClear "IH".
    destruct Hsi as (b & oloc & ?). repeat iExists _. repeat iFrame.
    iPureIntro. split_and!; [by simplify_map_eq|inversion 1..].
  }
  (** Move from [UU] to [CU] *)
  iAssert (CU _ _ _ _ _ _ _ _ _ ∗ UU _ _ _ _ _ _ _ _ _ ∗
    ({[i]},sids_from (length slist)) ↦P2[γR]{ 1/2 } false ∗
    i ↦p[γU]{1/2/2} false)%I with "[●CU ●UU]" as "($ & $ & ●Ur & ●Uu)".
  { unfold CU. rewrite big_sepM_insert; last by done. iFrame.
    iDestruct "●UU" as "(●UUu & ●UUr & ●UUv & ●UUt)". unfold toks.
    do 2 (rewrite bi.sep_exist_r; iExists _).
    rewrite -(top_difference_dom_union_not_in_singleton i info); last by done.
    rewrite -ghost_vars_union; [|set_solver].
    rewrite -!ghost_vars2_union_1; [|set_solver..].
    rewrite -!token2_union_1; [|set_solver..].
    rewrite -gset_to_coPset_singleton -gset_to_coPset_union.
    rewrite -(dom_insert_L info i ({|addr:=p; len:=size_p|}, γc_i)).
    iDestruct "●UUr" as "[$ [$ $]]". iDestruct "●UUv" as "[$ $]".
    iDestruct "●UUt" as "[$ $]".
    rewrite gset_to_coPset_singleton.
    iDestruct "●UUu" as "[$ [$ $]]".
    done.
  }
  iCombine "●Cu ●Uu" as "$". iCombine "●Cr ●Ur" as "●r".
  rewrite ghost_vars2_union_2; last apply sids_to_sids_from_disjoint.
  rewrite sids_to_sids_from_union. by iFrame.
Qed.

Lemma ghost_quadrants_new_slot slot γtok γinfo γptrs γU γR γV info hmap slist :
  slot ∉ slist →
  hmap !! slot = None →
  GhostQuadrants γtok γinfo γptrs γU γR γV info hmap slist -∗
  GhostQuadrants γtok γinfo γptrs γU γR γV info (<[slot := (true, None)]> hmap) (slist ++ [slot]) ∗
  (⊤,{[sid (length slist)]}) ↦P2[γV]{ 1/2 } false.
Proof.
  iIntros (NotIn NotElem) "(●CC & ●CU & ●UC & ●UU)".
  (** Move from [UU] to [UC] *)
  iAssert (UC _ _ _ _ _ _ _ _ _ ∗ UU _ _ _ _ _ _ _ _ _ ∗
    (⊤ ∖ gset_to_coPset (dom info),{[sid (length slist)]}) ↦P2[γV]{ 1/2 } false
    )%I with "[●UC ●UU]" as "($ & $ & ●Uv)".
  { unfold UC, UU.
    iDestruct "●UC" as "(#hmap & $ & ●UCr & ●UCv & ●UCt)".
    iDestruct "●UU" as "($ & ●UUr & ●UUv & ●UUt)".
    (* Move validation flag for [slot] from [UU] to [UC] *)
    iAssert(
      (⊤ ∖ gset_to_coPset (dom info),sids_to (length (slist ++ [slot]))) ↦P2[γV]{ 1/2 } false ∗
      (⊤ ∖ gset_to_coPset (dom info),sids_from (length (slist ++ [slot]))) ↦P2[γV] false ∗
      (⊤ ∖ gset_to_coPset (dom info),{[sid (length slist)]}) ↦P2[γV]{ 1/2 } false
    )%I with "[●UCv ●UUv]" as "($ & $ & $)".
    { rewrite length_app /= Nat.add_1_r sids_from_S.
      rewrite ghost_vars2_insert_2; [|apply sids_from_not_elem_of; lia].
      iDestruct "●UUv" as "[$ [$ ●UUv]]".
      iCombine "●UCv ●UUv" as "●Uv".
      rewrite -ghost_vars2_insert_2; [|apply sids_to_not_elem_of; lia].
      by rewrite sids_to_S.
    }
    (* Move reclaim flag for [slot] from [UU] to [UC] *)
    iAssert(
      (⊤ ∖ gset_to_coPset (dom info),sids_to (length (slist ++ [slot]))) ↦P2[γR] false ∗
      (⊤ ∖ gset_to_coPset (dom info),sids_from (length (slist ++ [slot]))) ↦P2[γR] false
    )%I with "[●UCr ●UUr]" as "[$ $]".
    { rewrite length_app /= Nat.add_1_r sids_from_S.
      rewrite ghost_vars2_insert_2; [|apply sids_from_not_elem_of; lia].
      iDestruct "●UUr" as "[$ ●UUr]".
      iCombine "●UCr ●UUr" as "●Ur".
      rewrite -ghost_vars2_insert_2; [|apply sids_to_not_elem_of; lia].
      by rewrite sids_to_S.
    }
    (* Move token for [slot] from [UU] to [UC] *)
    iAssert(
      toks γtok (⊤ ∖ gset_to_coPset (dom info)) (sids_to (length (slist ++ [slot]))) ∗
      toks γtok (⊤ ∖ gset_to_coPset (dom info)) (sids_from (length (slist ++ [slot])))
    )%I with "[●UCt ●UUt]" as "[$ $]".
    { rewrite length_app /= Nat.add_1_r sids_from_S.
      unfold toks.
      rewrite token2_insert_2; [|apply sids_from_not_elem_of; lia].
      iDestruct "●UUt" as "[$ ●UUt]".
      iCombine "●UCt ●UUt" as "●Ut".
      rewrite -token2_insert_2; [|apply sids_to_not_elem_of; lia].
      by rewrite sids_to_S.
    }
    (* Restore Information about [hmap] *)
    rewrite big_sepL_snoc. iSplit; last first.
    { repeat iExists _. by simplify_map_eq. }
    iApply (big_sepL_mono with "hmap"). iIntros (si p Hsi) "%Hp".
    iPureIntro. destruct Hp as [? [? ?]]. repeat eexists.
    rewrite lookup_insert_ne; [done|intros <-; congruence].
  }
  (** Move from [CU] to [CC] *)
  rewrite -assoc.
  iInduction info as [|loc v info Hinfo IH] using map_ind.
  { unfold CC, CU. rewrite dom_empty_L gset_to_coPset_empty difference_empty_L !big_sepM_empty. iFrame. }
  iDestruct (big_sepM_delete with "●CC") as "[●CCloc ●CC]"; [by simplify_map_eq|].
  rewrite delete_insert; [|done].
  iDestruct (big_sepM_delete with "●CU") as "[●CUloc ●CU]"; [by simplify_map_eq|].
  rewrite delete_insert; [|done].
  iSpecialize ("IH" with "●CC ●CU").
  iDestruct "●CCloc" as (U) "[●loc↦pC ●CCloc]".
  iDestruct "●CUloc" as (? R) "(●loc↦pU & ●CUr & ●CUv & ●CUt & %CUru)".
  iDestruct (ghost_vars_agree with "●loc↦pC ●loc↦pU") as %<-; [set_solver|].
  iAssert(
    ({[loc]},sids_from (length (slist ++ [slot]))) ↦P2[γV] false ∗
    (loc,sid (length slist)) ↦p2[γV]{ 1/2 } false ∗
    (loc,sid (length slist)) ↦p2[γV]{ 1/2 } false
  )%I with "[●CUv]" as "(●CUv & ●v & ●CCv)".
  { rewrite length_app /= Nat.add_1_r sids_from_S.
    rewrite ghost_vars2_insert_2; [|apply sids_from_not_elem_of; lia].
    iDestruct "●CUv" as "[$ [$ $]]".
  }
  iCombine "●Uv ●v" as "●Uv".
  rewrite dom_insert_L.
  rewrite -ghost_vars2_insert_1; last first.
  { rewrite gset_to_coPset_union gset_to_coPset_singleton. set_solver. }
  rewrite gset_to_coPset_union gset_to_coPset_singleton.
  rewrite top_difference_dom_union_not_in_singleton; last done.
  iDestruct ("IH" with "●Uv") as "(●CC & ●CU & $)".
  iEval (rewrite sids_from_S) in "●CUr".
  rewrite ghost_vars2_insert_2; last by apply sids_from_not_elem_of; lia.
  iDestruct "●CUr" as "[●CUr ●CCr]".
  iAssert (
    (if R then emp else toks γtok {[loc]} ({[sid (length slist)]})) ∗
    if R then emp else toks γtok {[loc]} (sids_from (length (slist ++ [slot])))
  )%I with "[●CUt]" as "[●CCt ●CUt]".
  { iEval (rewrite sids_from_S) in "●CUt".
    destruct R; [done|]. unfold toks.
    rewrite length_app Nat.add_1_r.
    rewrite token2_insert_2; last by apply sids_from_not_elem_of; lia.
    iDestruct "●CUt" as "[$ $]".
  }
  iSplitR "●loc↦pU ●CUt ●CU ●CUv ●CUr".
  - unfold CC. rewrite big_sepM_insert; last by done.
    iSplitR "●CC"; [|iFrame].
    iExists U. iFrame "∗#%". rewrite !Nat.add_0_r.
    iSplitL "●CCloc"; last first.
    + iSplitL; [|done]. repeat iExists _. simplify_map_eq. iSplit; [done|].
      iFrame. iFrame "●CCt". iPureIntro. done.
    + iApply (big_sepL_mono with "●CCloc"). iIntros (i slot' Hslot') "●loc".
      iDestruct "●loc" as (?? V R') "(%&?&?&%F&%&?)".
      destruct (decide (slot' = slot)) as [->|NE].
      * iExists true,None. exfr. iPureIntro. simplify_map_eq.
      * exfr. iPureIntro. rewrite lookup_insert_ne; done.
  - unfold CU. rewrite big_sepM_insert; last by done.
    iSplitR "●CU"; [|iFrame].
    iExists U, R. iFrame "∗#%".
    by rewrite length_app /= Nat.add_1_r.
Qed.

Lemma ghost_quadrants_activate slot v γtok γinfo γptrs γU γR γV info hmap slist :
  slot ∈ slist →
  NoDup slist →
  hmap !! slot = Some (false, None) →
  GhostQuadrants γtok γinfo γptrs γU γR γV info hmap slist -∗
  GhostQuadrants γtok γinfo γptrs γU γR γV info (<[slot:=(true, v)]> hmap) slist.
Proof.
  iIntros (ElemOf NoDup Hslot) "(●CC & $ & (#hmap & $ & $) & $)".
  iSplit; last first.
  { iApply (big_sepL_mono with "hmap"). iIntros (si p Hsi) "%Hp".
    iPureIntro. destruct Hp as [? [? ?]].
    destruct (decide (p = slot)) as [->|NE]; repeat eexists; [by simplify_map_eq|].
    rewrite lookup_insert_ne; [done|intros <-; congruence]. }
  iClear "hmap". unfold CC.

  iInduction info as [|loc v' info Hinfo IH] using map_ind; first by rewrite !big_sepM_empty.
  rewrite big_sepM_insert; last done.
  iDestruct "●CC" as "[●CCloc ●CC]".
  iSpecialize ("IH" with "●CC").
  rewrite big_sepM_insert; last done.
  iSplitR "IH"; last iFrame.

  iDestruct "●CCloc" as (U) "[loc↦pC ●CCloc]".
  iExists U. iFrame.

  iApply (big_sepL_mono with "●CCloc"). iIntros (i slot' Hslot') "●loc".
  iDestruct "●loc" as (?? V R) "(%&?&?&%F&%&?)".

  destruct (decide (slot' = slot)) as [->|NE].
  - exfr. iPureIntro. simplify_map_eq. split_and!; [done| |done].
    intro. destruct F as [_ F]; [done|inversion F].
  - exfr. iPureIntro. rewrite lookup_insert_ne; [|done].
    split_and!; [by simplify_map_eq|done..].
Qed.

Lemma ghost_quadrants_validate E γtok γinfo γptrs γU γR γV
    info hmap slist i idx slot z :
  info !! i = Some z →
  slist !! idx = Some slot →
  hmap !! slot = Some (true, Some z.1.(addr)) →
  GhostQuadrants γtok γinfo γptrs γU γR γV info hmap slist -∗
  (⊤,{[sid idx]}) ↦P2[γV]{ 1/2 } false -∗
  (i,sid idx) ↦p2[γR]{ 1/2 } false -∗
  |={E}=>
  GhostQuadrants γtok γinfo γptrs γU γR γV info hmap slist ∗
  (⊤ ∖ {[i]},{[sid idx]}) ↦P2[γV]{ 1/2 } false ∗
  (i,sid idx) ↦p2[γV]{ 1/2 } true ∗
  (i,sid idx) ↦p2[γR]{ 1/2 } false ∗
  stok γtok i idx.
Proof.
  iIntros (Hi Hl Hm) "(●CC & ●CU & ●UC & ●UU) ●TI R".
  iDestruct (big_sepM_delete with "●CC") as "[●Ci ●CC]"; eauto.
    iDestruct "●Ci" as (U) "[U ●Ci]".
    iDestruct (big_sepL_delete with "●Ci") as "[●Cis ●Ci]"; eauto.
    iDestruct "●Cis" as (b v V R) "(%Hm' & ●II & R2 & %HV & %HRU & T)".
    rewrite Hm in Hm'. injection Hm' as [= <- <-].

  (* agree & update *)
  iDestruct (ghost_vars2_agree with "R R2") as %<-; [set_solver..|].
  iDestruct (ghost_vars2_delete_1 _ i with "●TI") as "[●II2 ●TxI]"; [done|].
  iDestruct (ghost_vars2_agree with "●II ●II2") as %->; [set_solver..|].
  iMod (ghost_vars2_update_halves' true with "●II ●II2") as "[●II ●II2]".

  (* close *)
  iModIntro. iFrame. unfold CC.
  iApply big_sepM_delete; eauto. do 2 exfr.
  iApply big_sepL_delete; eauto. do 2 exfr.
Qed.

Lemma ghost_quadrants_set idx slot v b v' b' γtok γinfo γptrs γU γR γV info hmap slist :
  NoDup slist →
  slist !! idx = Some slot →
  hmap !! slot = Some (b', v') →
  GhostQuadrants γtok γinfo γptrs γU γR γV info hmap slist -∗
  (⊤,{[sid idx]}) ↦P2[γV]{ 1/2 } false -∗
  GhostQuadrants γtok γinfo γptrs γU γR γV info (<[slot:=(b, v)]> hmap) slist ∗
  (⊤,{[sid idx]}) ↦P2[γV]{ 1/2 } false.
Proof.
  iIntros (NoDup Hidx Hslot) "(●CC & $ & (#hmap & $ & $) & $) ●v".
  rewrite -assoc bi.sep_comm -assoc.
  iSplit.
  { iApply (big_sepL_mono with "hmap"). iIntros (si p Hsi) "%Hp".
    iPureIntro. destruct Hp as [? [? ?]].
    destruct (decide (p = slot)) as [->|NE]; repeat eexists; [by simplify_map_eq|].
    rewrite lookup_insert_ne; [done|intros <-; congruence]. }
  iClear "hmap". unfold CC.

  iInduction info as [|i info_i info Hinfo IH] using map_ind.
  { rewrite !big_sepM_empty right_id //. }
  rewrite big_sepM_insert //.
  iDestruct "●CC" as "[●CCloc ●CC]".
  iSpecialize ("IH" with "●CC ●v").
  iDestruct "IH" as "[●v IH]".
  rewrite big_sepM_insert; last done.
  rewrite bi.sep_comm -!assoc.

  iDestruct "●CCloc" as (U) "[●loc↦pC ●CCloc]".
  rewrite bi.sep_exist_r. iExists U. iFrame "●loc↦pC IH".
  iInduction slist as [|slot' slist IH] using rev_ind.
  { rewrite !big_sepL_nil. iFrame. }
  rewrite -NoDup_snoc in NoDup. destruct NoDup as [NoDup NotIn].
  destruct (decide (slot' = slot)) as [->|NE].
  - iClear "IH". rewrite !big_sepL_snoc.
    iDestruct "●CCloc" as "[●CCloc ●loc_slot]".
    rewrite -assoc. iSplitL "●CCloc".
    { iApply (big_sepL_mono with "●CCloc"). iIntros (idx' slot' Hslot') "●CCloc".
      iDestruct "●CCloc" as (b'' oloc V R) "(%&?&?&%&%&?)".
      exfr. iPureIntro. rewrite lookup_insert_ne; last first.
      { intros <-. apply NotIn. rewrite elem_of_list_lookup. eauto. }
      by simplify_map_eq.
    }
    iDestruct "●loc_slot" as (b'' oloc V R) "(%&●iv&●ir&%&%&IF)".
    assert (idx = (length slist)) as ->.
    { apply lookup_lt_Some in Hidx as LE. rewrite length_app /= in LE.
      assert (¬ (idx < (length slist))).
      { intro LT. rewrite lookup_app_l in Hidx; last done.
        apply NotIn. rewrite elem_of_list_lookup. eauto. }
      lia.
    }
    iDestruct (ghost_vars2_agree with "●iv ●v") as %->; [set_solver..|].
    iFrame. iExists b,v. iFrame "∗#%".
    iPureIntro. split; [by simplify_map_eq|inversion 1].
  - apply lookup_snoc_ne in Hidx; last done.
    rewrite !big_sepL_snoc.
    iDestruct "●CCloc" as "[●CCloc ●loc_slot]".
    iSpecialize ("IH" $! NoDup Hidx with "●CCloc ●v").
    iDestruct "IH" as "[$ $]".
    iDestruct "●loc_slot" as (b'' oloc V R) "(%&?&?&%&%&?)".
    iExists b'',oloc,V,R. iFrame "∗#%".
    iPureIntro. rewrite lookup_insert_ne; [by simplify_map_eq|done].
Qed.

Lemma ghost_quadrants_invalidate E γtok γinfo γptrs γU γR γV info hmap slist idx slot i info_i :
  info !! i = Some info_i →
  slist !! idx = Some slot →
  hmap !! slot = Some (true, Some info_i.1.(addr)) →
  GhostQuadrants γtok γinfo γptrs γU γR γV info hmap slist -∗
  (i,sid idx) ↦p2[γV]{ 1/2 } true -∗
  stok γtok i idx -∗
  |={E}=>
  GhostQuadrants γtok γinfo γptrs γU γR γV info hmap slist ∗
  (i,sid idx) ↦p2[γV]{ 1/2 } false.
Proof.
  iIntros (Hi Hidx Hslot) "[●CC $] ●v T". unfold CC.
  iDestruct (big_sepM_delete with "●CC") as "[●Ci ●CC]"; eauto.
  iDestruct "●Ci" as (U) "[U ●Ci]".
  iDestruct (big_sepL_delete with "●Ci") as "[●Cis ●Ci]"; eauto.
  iDestruct "●Cis" as (????) "(%Hslot' & ●iv & ●R2 & %HV & %HRU & OT)".
  rewrite Hslot in Hslot'. injection Hslot' as [= <- <-].

  (* agree & update *)
  iDestruct (ghost_vars2_agree with "●v ●iv") as %<-; [set_solver..|].
  iMod (ghost_vars2_update_halves' false with "●v ●iv") as "[●v ●iv]".

  (* close *)
  iModIntro. iFrame.
  iApply big_sepM_delete; eauto. do 2 exfr.
  iApply big_sepL_delete; eauto. do 2 exfr.
  destruct R; [iAssumption|].
  iFrame. iPureIntro. split_and!; [by simplify_map_eq|inversion 1..].
Qed.

Lemma ghost_quadrants_retire E γtok γinfo γptrs γU γR γV
    info hmap slist i :
  NoDup slist →
  is_Some (info !! i) →
  ({[i]},⊤) ↦P2[γR]{ 1/2 } false -∗
  GhostQuadrants γtok γinfo γptrs γU γR γV info hmap slist -∗
  i ↦p[γU]{1/2} false -∗
  |={E}=>
  ({[i]},⊤) ↦P2[γR]{ 1/2 } false ∗
  GhostQuadrants γtok γinfo γptrs γU γR γV info hmap slist ∗
  i ↦p[γU]{1/2} true.
Proof.
  iIntros (ND [info_i Hinfo_i]) "●IT (●CC & ●CU & ●UC & ●UU) U".
  iDestruct (big_sepM_delete with "●CC") as "[CCi ●CC]"; eauto.
    iDestruct "CCi" as (U) "[U2 CCi]".
  iDestruct (big_sepM_delete with "●CU") as "[CUi ●CU]"; eauto.
    iDestruct "CUi" as (U' R) "[U3 CUi]".
  iDestruct (ghost_vars_agree with "U U2") as %<-; [set_solver|].
  iDestruct (ghost_vars_agree with "U U3") as %<-; [set_solver|].
  iCombine "U U2 U3" as "U".
  iMod (ghost_vars_update true with "U") as "[U [U2 U3]]".

  iModIntro.
  iFrame "●UC ●UU U".
  rewrite (top_union_difference (sids_to (length slist))).
  iDestruct (ghost_vars2_union_2 with "●IT") as "[●IE ●IL]"; first set_solver.
  iApply bi.wand_frame_r.
  { iIntros. iApply ghost_vars2_union_2; first set_solver. eauto. }

  assert ( ∀ (P Q R S : iProp),
    ((Q ∗ R) ∗ (P ∗ S))  ⊢ ((P ∗ Q) ∗ R ∗ S)
  ) as COMM.
  { iIntros (????) "([$ $]&$&$)". }
  iApply COMM.

  iSplitL "U2 ●CC CCi ●IL".
  - destruct (decide (slist = [])) as [->|NonNill].
    { unfold CC; simpl. exfr.
      iApply big_sepM_delete; eauto. exfr. }

    iDestruct (ghost_vars2_big_sepM_2 with "●IL") as "●IL".
    { apply NoDup_fmap; [apply sid_injective|apply NoDup_seq]. }
    iApply bi.wand_frame_r.
    { iApply ghost_vars2_big_sepM_2'.
      - apply NoDup_fmap; [apply sid_injective|apply NoDup_seq].
      - intro sids. apply fmap_nil_inv, seq_nil_inv in sids.
        by destruct slist. }
    iApply bi.wand_frame_l.
    { iIntros. iApply big_sepM_delete; eauto. }

    iFrame "●CC".
    iApply bi.sep_exist_l. iExists true. iFrame "U2".
    rewrite big_sepL_fmap big_sepL_seq.
    iCombine "CCi ●IL" as "CC". do 2 rewrite -big_sepL_sep.
    iApply big_sepL_mono; last auto.

    iIntros (i' p' Hp) "[CCi R]".
      iDestruct "CCi" as (????) "(% & ● & R2 & % & % & T)".
    iDestruct (ghost_vars2_agree with "R R2") as %<-; [set_solver..|].
    repeat exfr.
  - exfr.
    iApply big_sepM_delete; eauto. repeat exfr.
    iDestruct "CUi" as "(C1 & C2 & C3 & %)". exfr.
Qed.

(* Inactive shield lemmas *)

Lemma inactive_shield_alloc γV :
  ⊢ InactiveShield γV ∅ [].
Proof.
  iIntros.
  unfold InactiveShield.
  by rewrite big_sepL_nil.
Qed.

Lemma inactive_shield_insert γV sbvmap slist slot :
  sbvmap !! slot = None →
  InactiveShield γV sbvmap slist -∗
  InactiveShield γV (<[slot:=(true, None)]> sbvmap) (slist ++ [slot]).
Proof.
  iIntros "%Hslot ISh".
  iApply big_sepL_snoc. iSplitL "ISh".
  - iApply big_sepL_mono; last auto.
    iIntros (i p Hp) "SS".
    destruct (decide (p = slot)) as [->|NE].
    + by rewrite lookup_insert.
    + by rewrite lookup_insert_ne.
  - by rewrite lookup_insert.
Qed.

Lemma inactive_shield_unset γV sbvmap slist si slot v :
  NoDup slist →
  slist !! si = Some slot →
  sbvmap !! slot = Some (true, v) →
  InactiveShield γV sbvmap slist -∗
  InactiveShield γV (<[slot:=(true, None)]> sbvmap) slist.
Proof.
  iIntros "%NoDup %HL %HM ISh".
  unfold InactiveShield.
  iDestruct (big_sepL_delete with "ISh") as "[ISlot ISh]"; first apply HL.
  iApply big_sepL_delete; [apply HL|].
  iSplitR "ISh"; last first.
  { iApply (big_sepL_mono with "ISh"). iIntros (si' slot' Hsi) "Sh".
    case_decide as Eqn; auto. rewrite lookup_insert_ne; [iFrame|].
    intros <-. destruct Eqn. rewrite NoDup_ListNoDup NoDup_nth in NoDup.
    apply (NoDup si' si); [by apply (lookup_lt_Some _ _ slot)..|].
    apply (nth_lookup_Some _ _ slot _) in HL.
    apply (nth_lookup_Some _ _ slot _) in Hsi.
    rewrite -{2}HL in Hsi. done.
  }
  by rewrite lookup_insert.
Qed.

Lemma inactive_shield_drop γV sbvmap slist si slot v :
  NoDup slist →
  slist !! si = Some slot →
  sbvmap !! slot = Some (true, v) →
  InactiveShield γV sbvmap slist -∗
  (⊤,{[sid si]}) ↦P2[γV]{ 1/2 } false -∗
  InactiveShield γV (<[slot:=(false, None)]> sbvmap) slist.
Proof.
  iIntros "%NoDup %HL %HM ISh ●si".
  unfold InactiveShield.
  iDestruct (big_sepL_delete with "ISh") as "[ISlot ISh]"; first apply HL.
  iApply big_sepL_delete; [apply HL|].
  iSplitR "ISh"; last first.
  { iApply (big_sepL_mono with "ISh"). iIntros (si' slot' Hsi) "Sh".
    case_decide as Eqn; auto. rewrite lookup_insert_ne; [iFrame|].
    intros <-. destruct Eqn. rewrite NoDup_ListNoDup NoDup_nth in NoDup.
    apply (NoDup si' si); [by apply (lookup_lt_Some _ _ slot)..|].
    apply (nth_lookup_Some _ _ slot _) in HL.
    apply (nth_lookup_Some _ _ slot _) in Hsi.
    rewrite -{2}HL in Hsi. done.
  }
  by rewrite lookup_insert.
Qed.


Lemma inactive_shield_activate γV sbvmap slist si slot v :
  slist !! si = Some slot →
  sbvmap !! slot = Some (false, None) →
  InactiveShield γV sbvmap slist -∗
  InactiveShield γV (<[slot:=(true, v)]> sbvmap) slist ∗
  (⊤,{[sid si]}) ↦P2[γV]{ 1/2 } false.
Proof.
  iIntros "%HL %HM ISh".
  iDestruct (big_sepL_delete with "ISh") as "[ISlot ISh]"; first apply HL.
  rewrite HM. iFrame. iApply big_sepL_mono; last auto.
  iIntros (k y Hky) "SS".
  destruct (decide (y = slot)).
  - subst. by rewrite lookup_insert.
  - rewrite lookup_insert_ne; auto.
    destruct (decide (k = si)); auto.
    subst. rewrite HL in Hky. naive_solver.
Qed.

Lemma inactive_shield_reactivate v γV sbvmap slist si slot v' :
  slist !! si = Some slot →
  sbvmap !! slot = Some (true, v') →
  InactiveShield γV sbvmap slist -∗
  InactiveShield γV (<[slot:=(true, v)]> sbvmap) slist.
Proof.
  iIntros "%HL %HM ISh".
  iApply big_sepL_mono; last auto.
  iIntros (k y Hky) "SS".
  destruct (decide (y = slot)).
  - subst. by rewrite lookup_insert.
  - rewrite lookup_insert_ne; auto.
Qed.

(** Domain specs *)

Lemma hazard_domain_new_spec :
  hazard_domain_new_spec' N hazard_domain_new IsHazardDomain.
Proof.
  intros ??.
  iIntros "_ HΦ".
  wp_lam. wp_alloc d as "d↦" "†d".
  rewrite array_cons array_singleton.
  iDestruct "d↦" as "[d.s↦ d.r↦]".
  wp_let.
  wp_apply sbs.(slot_bag_new_spec); auto.
  iIntros (γsb slotbag) "SlotBag".
  wp_pures. rewrite Loc.add_0. wp_store.
  wp_apply rls.(retired_list_new_spec); auto.
  iIntros (rList) "RList".
  wp_store.
  (* Prepare rest of ghosts. *)
  iMod (ghost_map_alloc_empty (K:=positive) (V:=alloc*gname)) as (γinfo) "●γinfo".
  iMod (ghost_map_alloc_empty (K:=positive) (V:=gname)) as (γdata) "●γdata".
  iMod coP_ghost_map_alloc_empty as (γptrs) "●γptrs".
  iMod (ghost_quadrants_alloc γinfo γptrs) as (γtok γU γR γV) "GQ".
  iDestruct (inactive_shield_alloc γV) as "InactSh".
  remember (encode (γsb, γtok, γinfo, γdata, γptrs, γU, γR, γV)) as γz eqn:Hγz.
  iAssert (HazardDomain _ _ _ _ _ _ _ _ _ _ _)%I with "[SlotBag RList ●γinfo ●γdata ●γptrs GQ]" as "HD".
  { repeat iExists _. iFrame "∗#". rewrite big_sepM_empty big_sepL_nil.
    iPureIntro. split_and!; [done..|by rewrite !dom_empty_L|]. intros l i Hli.
    rewrite lookup_empty in Hli. congruence.  }
  iMod (inv_alloc hazptrInvN _ (HazardDomain _ _ _ _ _ _ _ _ _ _ _) with "HD") as "#HDInv".
  iMod (pointsto_persist with "d.s↦") as "#d.s↦".
  iMod (pointsto_persist with "d.r↦") as "#d.r↦".
  iModIntro. iApply "HΦ".
  repeat iExists _. rewrite Loc.add_0. iFrame "∗#%".
Qed.

Lemma hazard_domain_register :
  hazard_domain_register' N IsHazardDomain Managed.
Proof.
  intros ????????. intros.
  iIntros "#IHD (p↦ & †p & R)".
  iDestruct "IHD" as (??????????) "(%Hγ & ↦hBag & ↦rSet & InvHD)".
  iInv "InvHD" as (??? hmap slist rs)
  "(>M & >datM & >coM & >B & >RS & >●Q & >●X & >Reg & Ret & >%Hdom & >%HInfo)".

  (* Get a new id for p *)
  set i := fresh (dom info).
  assert (info !! i = None) as Freshi.
  { rewrite eq_None_not_Some -elem_of_dom. apply is_fresh. }

  (* Prove that [p ∉ dom ptrs] using two freeables, one in [Reg] and [†p]. *)
  iAssert (⌜p ∉ dom ptrs⌝)%I as %PNew.
  { iIntros (In). rewrite elem_of_dom in In.
    destruct In as [idx Some].
    rewrite big_sepM_lookup_acc; last done.
    iDestruct "Reg" as "[Reg_p _]".
    iDestruct "Reg_p" as (?) "(_ & †p')".
    iApply (heap_freeable_valid with "†p †p'").
  }
  rewrite elem_of_dom -eq_None_not_Some in PNew.

  (* get [p] element from [coM] and split. *)
  iMod ((coP_ghost_map_insert p i) with "coM") as "[coM p↪i]"; first by apply PNew.
  rewrite (top_complement_singleton gid).
  rewrite coP_ghost_map_elem_fractional; last first.
  { rewrite -coPneset_disj_elem_of. set_solver. }
  iDestruct "p↪i" as "[p↪i_gid p↪i]".

  (* Allocate and split [coP_cinv]. *)
  iMod (ghost_map_insert_persist i γ_p with "datM") as "[datM #i↪γdata]".
  { rewrite -not_elem_of_dom -Hdom not_elem_of_dom //. }
  iMod ((coP_cinv_alloc _ (resN (ptrsN N) p i) (∃ vl, ⌜length vl = length lv⌝ ∗ (wrap_resource γdata R γ_p) _ vl _ ∗ p ↦∗ vl)) with "[R p↦]") as "●γc_i".
  { iNext. iExists lv. iFrame "∗#". auto. }
  iDestruct "●γc_i" as (γc_i) "[#Inv ●γc_i]".
  rewrite (top_complement_singleton gid).
  rewrite coP_cinv_own_fractional; last first.
  { rewrite -coPneset_disj_elem_of. set_solver. }
  iDestruct "●γc_i" as "[●γc_i_gid ●γc_i]".

  (* Update ghost quadrants *)
  iMod (ghost_quadrants_register with "●Q") as "(●Q & ●u_i & ●r_i & ●toks_∅)"; [done|].

  (* Update [M] *)
  iMod (ghost_map_insert_persist i ({|addr:=p; len:=length lv|},γc_i) with "M") as "[M #i↪γinfo]"; [done|].

  (* Make [Exchanges'] *)
  iAssert (Exchanges' _ _ _ _ _)%I with "[●toks_∅ ●γc_i p↪i]" as "Exchanges'".
  { unfold Exchanges'. iRight. iLeft.
    iExists ∅. rewrite union_empty_l_L. rewrite set_map_empty gset_to_coPset_empty. iFrame.
  }
  (* Make [Exchanges] *)
  iMod (inv_alloc (exchN (mgmtN N) p i) _ (Exchanges' _ _ _ _ _) with "Exchanges'") as "Exchanges".

  (* Close invariant *)
  iModIntro. iSplitR "i↪γinfo p↪i_gid ●γc_i_gid ●u_i ●r_i Exchanges".
  { iNext. repeat iExists _. iFrame. iSplit; last first.
    { iPureIntro. split.
      { rewrite !dom_insert_L Hdom //. }
      intros p' i' Hp'. destruct (decide (p = p')) as [<-|NE].
      - eexists. by simplify_map_eq.
      - rewrite lookup_insert_ne in Hp'; last done.
        specialize (HInfo p' i' Hp'). destruct HInfo as [info_i' [? ?]].
        exists info_i'.
        rewrite lookup_insert_ne; [done|congruence].
    }
    rewrite big_sepM_insert; last done.
    iSplitR "Reg".
    (* Coq is not smart enough to do partial resolution of evars,
       so we need to give it two evars as a pair to work with. *)
    - iExists ({|addr:=p; len:=length lv|},_). iFrame "†p". by simplify_map_eq.
    - iApply (big_sepM_mono with "Reg"). iIntros (p' i' Hp') "Reg".
      iDestruct "Reg" as (info_i') "[%Hi' †p']". iExists info_i'. iFrame.
      iPureIntro. rewrite lookup_insert_ne; [auto|congruence].
  }

  (* Make managed *)
  iModIntro.
  repeat iExists _. iFrame (Hγ) "i↪γdata".
  repeat iExists _. iFrame "∗#%".
Qed.

(** Shield specs *)

Lemma shield_new_spec :
  shield_new_spec' N shield_new IsHazardDomain Shield.
Proof.
  intros ????.
  iIntros "#IHD" (Φ) "!> _ HΦ".
    iDestruct "IHD" as (??????????) "(%Hγ & ↦hBag & ↦rSet & IHD)".
  wp_lam. wp_pures. wp_load. wp_let.

  awp_apply sbs.(slot_bag_acquire_slot_spec) without "HΦ".
  iInv "IHD" as (??? hmap slist rs)
    "(>M & >datM & >coM & >B & >RS & >●Q & >●X & >Reg & Ret & >%Hdom & >%HInfo)".
  iAaccIntro with "B".
  { iIntros "? !>". tspd. exfr. }

  iIntros (slist' slot idx) "(B & S & %Hslist')".
  destruct Hslist' as [[-> [Hm ->]]|[-> [Hm Hl]]].
  - (* new slot added *)
    iModIntro.
    iDestruct (SlotBag_NoDup with "B") as "%ND".

    iDestruct (ghost_quadrants_new_slot slot with "●Q") as "[●Q ●TS]"; [|done|].
    { rewrite -NoDup_snoc in ND. by destruct ND. }
    iDestruct (inactive_shield_insert with "●X") as "●X"; eauto.

    iSplitR "●TS S"; [exfr|].
    iIntros "HΦ". wp_pures.
    wp_alloc shield as "Sh" "†shield". wp_pures.
    rewrite -{1}(Loc.add_0 shield) array_singleton.
    wp_store.
    iModIntro. iApply "HΦ". exfr.
  - (* old slot reacquired *)
    iModIntro.
    iDestruct (SlotBag_NoDup with "B") as "%ND".
    iDestruct (ghost_quadrants_activate with "●Q") as "●Q"; eauto.
    { rewrite elem_of_list_lookup. eauto. }
    iDestruct (inactive_shield_activate with "●X") as "[●X ●TI]"; eauto.

    iSplitR "S ●TI"; [exfr|].
    iIntros "HΦ". wp_pures.
    wp_alloc shield as "Sh" "†shield".
    wp_pures.
    rewrite -{1}(Loc.add_0 shield) array_singleton.
    wp_store.
    iModIntro. iApply "HΦ". unfold Shield.
    repeat iExists _. iFrame. iSplit; auto.
Qed.

Lemma shield_set_spec :
  shield_set_spec' N shield_set IsHazardDomain Shield.
Proof.
  intros ???????.
  iIntros "#IHD". iIntros (Φ) "!> Sh HΦ".
    iDestruct "IHD" as (??????????) "(%Hγ & ↦hBag & ↦rSet & IHD)".
    iDestruct "Sh" as (????????) "Sh".
    iDestruct "Sh" as (slot idx v) "(%Hγ' & Shs↦ & †Sh & ShSlot & ShSt)".
    encode_agree Hγ'.
  wp_lam. wp_pures. wp_load. wp_let.
  iAssert ((s +ₗ 0) ↦ #slot -∗ †s…shieldSize -∗
    sbs.(Slot) γsb slot idx v -∗
    (⊤,{[sid idx]}) ↦P2[γV]{ 1/2 } false -∗
    (Shield γd s
         match p with
         | Some p' => NotValidated p'
         | None => Deactivated
         end -∗ Φ #()) -∗
    WP slot_set #slot #(oblk_to_lit p) @ E {{ v, Φ v }}
  )%I as "slot_set".
  { iIntros "Shs↦ †Sh ShSlot ●TI HΦ".
    awp_apply (sbs.(slot_set_spec) with "ShSlot") without "HΦ".
    iInv "IHD" as (??? hmap1 slist1 rs1)
      "(>M & >datM & >coM & >B & >RS & >●Q & >●X & >Reg & Ret & >%Hdom & >%HInfo)".
    iAaccIntro with "B".
    { iIntros "? !>". do 2 exfr. }
    iIntros "([%Hl %Hm] & B & ShSlot)".

    iDestruct (SlotBag_NoDup with "B") as "%ND".
    iModIntro.
    iDestruct (ghost_quadrants_set idx slot p with "●Q ●TI") as "[●Q ●TI]"; [done..|].
    iSplitR "Shs↦ †Sh ShSlot ●TI"; last first.
    { iIntros "HΦ". iApply "HΦ". exfr. iSplit; auto. destruct p; auto. }
    iNext. exfr. iSplit; auto.
    iApply inactive_shield_reactivate; done.
  }
  destruct s_st as [|p'|p']; simpl.
  - (* was Deactivated *)
    iDestruct "ShSt" as "[-> ●TI]".
    iApply ("slot_set" with "Shs↦ †Sh ShSlot ●TI HΦ").
  - (* was NotValidated *)
    iDestruct "ShSt" as "[-> ●TI]".
    iApply ("slot_set" with "Shs↦ †Sh ShSlot ●TI HΦ").
  - (* was Validated *)
    iDestruct "ShSt" as (i) "(-> & Prot & ●ShX)".
    awp_apply (sbs.(slot_set_spec) with "ShSlot") without "HΦ".
    iInv "IHD" as (??? hmap1 slist1 rs1)
      "(>M & >datM & >coM & >B & >RS & >●Q & >●X & >Reg & Ret & >%Hdom & >%HInfo)".
    iAaccIntro with "B".
    { iIntros "? !>". do 2 exfr. }
    iIntros "([%Hl %Hm] & B & ShSlot)".

    iDestruct (SlotBag_NoDup with "B") as "%ND".
    iDestruct "Prot" as "[#i_data Prot]".
    iDestruct "Prot" as (γc_i) "(#i□ & pc & cinv & #Ex & #RCI & ●Shi)".
    iDestruct (coP_ghost_map_lookup with "coM pc") as %Hp.
    apply HInfo in Hp as [info_i [Hinfo_i info_i_eq]].
    iMod (exchange_stok_get with "Ex pc cinv") as "T"; first solve_ndisj.
    iMod (ghost_quadrants_invalidate with "●Q ●Shi T") as "[●Q ●Shi]"; [done..|subst p'; done|].

    iModIntro.

    iDestruct (ghost_quadrants_set idx slot p with "●Q [●Shi ●ShX]") as "[●Q ●ShiX]"; [done..| |].
    { iCombine "●ShX ●Shi" as "●TI". simpl.
      rewrite -ghost_vars2_insert_1; last by set_solver.
      by rewrite -top_union_difference. }

    (* Get the resource for old validated pointer *)
    iSplitR "●ShiX Shs↦ †Sh ShSlot"; last first.
    { iIntros "HΦ". iApply "HΦ". exfr. iSplit; auto. destruct p; by iFrame. }

    iExists info, data, ptrs, _, _, _. iFrame. iNext.
    iSplit; [|done].
    iApply inactive_shield_reactivate; done.
Qed.

Lemma shield_validate :
  shield_validate' N IsHazardDomain Managed Shield.
Proof.
  intros ?????????.
  iIntros "#IHD G Sh".
    iDestruct "IHD" as (??????????) "(%Hγ & ↦hBag & ↦rSet & IHD)".
    iDestruct "G" as (?????????) "(%Hγ' & #i_data & G)". encode_agree Hγ'.
    iDestruct "G" as (?) "(Gcinv & #G□ & Gpi & #Ex & #Cinv & GU & GR)".
    iDestruct "Sh" as (????????) "Sh".
    iDestruct "Sh" as (slot idx v) "(%Hγ' & ShH & †Sh & S & Shst)".
    iDestruct "Shst" as "[-> ●Sh]".
    encode_agree Hγ.
  iInv "IHD" as (??? hmap1 slist1 rs1)
    "(>M & >datM & >coM & >B & >RS & >●Q & >●X & >Reg & Ret & >%Hdom & >%HInfo)".
  iDestruct (SlotBag_lookup with "B S") as "[%Hl %Hm]".

  iDestruct (coP_ghost_map_lookup with "coM Gpi") as %Hp.
    apply HInfo in Hp as [info_i [Hinfo_i <-]].
  iDestruct (ghost_vars2_delete_2 _ (sid idx) with "GR") as "[R Rx]"; [done|].
  iMod (ghost_quadrants_validate with "●Q ●Sh R") as
    "(●Q & ●TxI & ●II & R & T)"; eauto.
  iCombine "R Rx" as "GR".
  rewrite -ghost_vars2_delete_2; [|done].
  iMod (exchange_stok_give with "Ex T") as "[zc cinv]"; [solve_ndisj|].

  iModIntro. iSplitL "M datM coM B RS ●Q ●X Reg Ret"; [exfr|].
  iModIntro. iSplitL "Gcinv Gpi GU GR"; do 3 (exfr; tspd).
Qed.

Lemma shield_drop_spec :
  shield_drop_spec' N shield_drop IsHazardDomain Shield.
Proof.
  intros ??????.
  iIntros "#IHD". iIntros (Φ) "!> Sh HΦ".
  iDestruct "IHD" as (??????????) "(%Hγ & ↦hBag & ↦rSet & IHD)".
  iDestruct "Sh" as (????????) "Sh".
  iDestruct "Sh" as (slot idx v) "(%Hγ' & ShH & †Sh & S & Shst)".
  encode_agree Hγ.
  wp_lam. wp_op. wp_load. wp_let.
  iAssert ((s +ₗ 0) ↦ #slot -∗ †s…shieldSize -∗
    sbs.(Slot) γsb slot idx None -∗
    (⊤,{[sid idx]}) ↦P2[γV]{ 1/2 } false -∗
    (True -∗ Φ #()) -∗
    WP slot_drop #slot;; Free #shieldSize #s @ E {{ v, Φ v }}
  )%I as "drop".
  { iIntros "ShH †Sh S ●Sh HΦ".
    awp_apply (sbs.(slot_drop_spec) with "S") without "HΦ".
    iInv "IHD" as (??? hmap slist rs)
      "(>M & >datM & >coM & >B & >RS & >●Q & >●X & >Reg & Ret & >%Hdom & >%HInfo)".
    iAaccIntro with "B".
    { iFrame. iIntros "B". iModIntro. iNext. repeat iExists _. iFrame "∗#%". }
    iIntros "(%Hslot & B)". destruct Hslot. iModIntro.
    iDestruct (SlotBag_NoDup with "B") as %NoDup.
    iDestruct (ghost_quadrants_set idx slot None false with "●Q ●Sh") as "[●Q ●Sh]"; [done..|].
    iDestruct (inactive_shield_drop with "●X ●Sh") as "●X"; [done..|].
    iSplitR "ShH †Sh".
    { iNext. repeat iExists _. iFrame "∗#%". }
    iIntros "HΦ". wp_seq. rewrite !Loc.add_0 -!array_singleton.
    wp_free; first done. by iApply "HΦ".
  }
  iAssert ((s +ₗ 0) ↦ #slot -∗ †s…shieldSize -∗
    sbs.(Slot) γsb slot idx v -∗
    (⊤,{[sid idx]}) ↦P2[γV]{ 1/2 } false -∗
    (True -∗ Φ #()) -∗
    WP slot_unset #slot;; slot_drop #slot;; Free #1 #s @ E {{ v, Φ v }}
  )%I as "unset_drop".
  { iIntros "ShH †Sh S ●Sh HΦ".
    awp_apply (sbs.(slot_unset_spec) with "S").
    iInv "IHD" as (??? hmap slist rs)
      "(>M & >datM & >coM & >B & >RS & >●Q & >●X & >Reg & Ret & >%Hdom & >%HInfo)".
    iAaccIntro with "B".
    { iFrame. iIntros "B". iModIntro. iNext. repeat iExists _. iFrame "∗#%". }
    iIntros "(%Hslot & B & S)". destruct Hslot. iModIntro.
    iDestruct (SlotBag_NoDup with "B") as %NoDup.
    iDestruct (ghost_quadrants_set idx slot None with "●Q ●Sh") as "[●Q ●Sh]"; [done..|].

    iDestruct (inactive_shield_unset with "●X") as "●X"; [done..|].
    iSplitR "ShH †Sh S ●Sh HΦ".
    { iNext. repeat iExists _. iFrame "∗#%". }
    wp_seq. by iApply ("drop" with "ShH †Sh S ●Sh HΦ").
  }
  destruct s_st.
  - (* Deactivated Shield *)
    iDestruct "Shst" as "[-> ●Sh]".
    iApply ("unset_drop" with "ShH †Sh S ●Sh HΦ").
  - (* NotValidated Shield *)
    iDestruct "Shst" as "[-> ●Sh]".
    iApply ("unset_drop" with "ShH †Sh S ●Sh HΦ").
  - (* Validated Shield *)
    iDestruct "Shst" as (i) "(-> & [#i_data Prot] & ●Shx)".
    awp_apply (sbs.(slot_unset_spec) with "S").

    iInv "IHD" as (??? hmap1 slist1 rs1)
      "(>M & >datM & >coM & >B & >RS & >●Q & >●X & >Reg & Ret & >%Hdom1 & >%HInfo1)".
    iAaccIntro with "B".
    { iIntros "? !>". repeat exfr. }
    iIntros "([%Hl1 %Hm1] & B & S)".
      iCombine "M RS Reg Ret S" as "__REST__".

    iDestruct (SlotBag_NoDup with "B") as "%ND".
    iDestruct "Prot" as (γc_i) "(#i□ & pc & cinv & #Ex & #RCI & ●Shi)".
    iDestruct (coP_ghost_map_lookup with "coM pc") as %Hp.
    apply HInfo1 in Hp as [info_i [HInfo_i <-]].
    iMod (exchange_stok_get with "Ex pc cinv") as "T"; first solve_ndisj.
    iMod (ghost_quadrants_invalidate with "●Q ●Shi T") as "[●Q ●Shi]"; eauto.

    (* same as shield_set *)
    iDestruct "__REST__" as "(M & RS & Reg & Ret & S)".
    iModIntro.

    iDestruct (ghost_quadrants_set idx slot None with "●Q [●Shi ●Shx]") as "[●Q ●Sh]"; [done..| |].
    { iCombine "●Shi ●Shx" as "?".
      rewrite comm -ghost_vars2_insert_1; last by set_solver.
      by rewrite -top_union_difference.
    }

    (* Get the resource for old validated pointer *)
    iSplitR "ShH †Sh ●Sh S HΦ".
    { iExists info, data, ptrs, _, _, _. iFrame. iNext.
      iSplit; [|done].
      iApply inactive_shield_reactivate; done.
    }

    wp_seq. by iApply ("drop" with "ShH †Sh S ●Sh HΦ").
Qed.

Lemma shield_unset_spec :
  shield_unset_spec' N shield_unset IsHazardDomain Shield.
Proof.
  intros ??????.
  iIntros "#IHD" (Φ) "!> Sh HΦ".
    iDestruct "IHD" as (??????????) "(%Hγ & ↦hBag & ↦rSet & IHD)".
    iDestruct "Sh" as (????????) "Sh".
    iDestruct "Sh" as (slot idx v) "(%Hγ' & ShH & †Sh & S & Shst)".
    encode_agree Hγ.
  unfold shield_unset. wp_pures. wp_load. wp_let.

  iAssert ((s +ₗ 0) ↦ #slot -∗ †s…shieldSize -∗
    sbs.(Slot) γsb slot idx v -∗
    (⊤,{[sid idx]}) ↦P2[γV]{ 1/2 } false -∗
    (Shield γd s Deactivated -∗ Φ #()) -∗
    WP slot_unset #slot @ E {{ v, Φ v }}
  )%I as "slot_unset".
  { iIntros "ShH †Sh S ●Sh HΦ".
    awp_apply (sbs.(slot_unset_spec) with "S") without "HΦ".
    iInv "IHD" as (??? hmap1 slist1 rs1)
      "(>M & >datM & >coM & >B & >RS & >●Q & >●X & >Reg & Ret & >%Hdom & >%HInfo)".
    iAaccIntro with "B".
    { iIntros "? !>". repeat exfr. }
    iIntros "([%Hl %Hm] & B & S)".

    (* same as shield_set *)
    iDestruct (SlotBag_NoDup with "B") as "%ND".
    iDestruct (ghost_quadrants_set idx slot None with "●Q ●Sh") as "[●Q ●Sh]"; [done..|].

    iModIntro. iSplitR "ShH †Sh S ●Sh"; last first.
    { iIntros "HΦ". iApply "HΦ". exfr. }
    iNext. exfr. iSplit; auto.
    iApply inactive_shield_reactivate; done.
  }
  destruct s_st.
  - (* was deactivated, nothing changes *)
    iDestruct "Shst" as "[-> ●Sh]".
    iApply ("slot_unset" with "ShH †Sh S ●Sh HΦ").
  - (* was not validated *)
    iDestruct "Shst" as "[-> ●Sh]".
    iApply ("slot_unset" with "ShH †Sh S ●Sh HΦ").
  - (* was Validated *)
    iDestruct "Shst" as (i) "(-> & [#i_data Prot] & ●Shx)".
    awp_apply (sbs.(slot_unset_spec) with "S") without "HΦ".
    iInv "IHD" as (??? hmap1 slist1 rs1)
      "(>M & >datM & >coM & >B & >RS & >●Q & >●X & >Reg & Ret & >%Hdom & >%HInfo)".
    iAaccIntro with "B".
    { iIntros "? !>". repeat exfr. }
    iIntros "([%Hl %Hm] & B & S)".
      iCombine "M RS Reg Ret ShH S" as "__REST__".

    iDestruct (SlotBag_NoDup with "B") as "%ND".
    iDestruct "Prot" as (γc_i) "(#i□ & pc & cinv & #Ex & #RCI & ●Shi)".
    iDestruct (coP_ghost_map_lookup with "coM pc") as %Hp.
    apply HInfo in Hp as [info_i [Hinfo_i <-]].
    iMod (exchange_stok_get with "Ex pc cinv") as "T"; first solve_ndisj.
    iMod (ghost_quadrants_invalidate with "●Q ●Shi T") as "[●Q ●Shi]"; eauto.

    (* same as shield_set *)
    iDestruct "__REST__" as "(M & RS & Reg & Ret & Shs↦ & ShSlot)".
    iModIntro.

    iDestruct (ghost_quadrants_set idx slot None with "●Q [●Shi ●Shx]") as "[●Q ●ShiX]"; [done..| |].
    { iCombine "●Shi ●Shx" as "●TI".
      rewrite comm -ghost_vars2_insert_1; last by set_solver.
      by rewrite -top_union_difference. }

    (* Get the resource for old validated pointer *)
    iSplitR "●ShiX Shs↦ †Sh ShSlot"; last first.
    { iIntros "HΦ". iApply "HΦ". exfr. }

    iExists info, data, ptrs, _, _, _. iFrame. iNext.
    iSplit; [|done].
    iApply inactive_shield_reactivate; done.
Qed.

Lemma shield_protect_spec :
  shield_protect_spec' N shield_protect IsHazardDomain Managed Shield.
Proof.
  intros ????????.
  iIntros "#IHD Sh" (Φ) "AU".
  wp_lam. wp_pures.

  wp_bind (! _)%E. iMod "AU" as (pa1 γ1 size1 R1) "[[a↦ pa1↦] [Abort _]]".
  wp_load. iMod ("Abort" with "[$a↦ $pa1↦]") as "AU".
  iModIntro. wp_let.

  unfold shield_protect_loop. iLöb as "IH" forall (pa1 s_st). wp_rec. wp_pures.
  wp_apply (shield_set_spec with "IHD [$Sh]") as "Sh"; [solve_ndisj..|].
  wp_seq.

  wp_bind (! _)%E. iMod "AU" as (pa2 γ2 size2 R2) "[[a↦ pa2↦] CloseAU]".
  case (decide (pa1 = pa2)) as [->|NE]; [destruct pa2|]; wp_load.
  - iMod (shield_validate with "IHD pa2↦ Sh") as "[pa2↦ S]"; [solve_ndisj|].
    iDestruct "CloseAU" as "[_ Commit]".
    iMod ("Commit" with "[$a↦ $pa2↦ $S]") as "HΦ".
    iModIntro. wp_pures.
    by iApply "HΦ".
  - iDestruct "CloseAU" as "[_ Commit]".
    iMod ("Commit" with "[$a↦ $Sh]") as "HΦ".
    iModIntro. wp_let. wp_op. wp_if. by iApply "HΦ".
  - iDestruct "CloseAU" as "[Abort _]".
    iMod ("Abort" with "[$a↦ $pa2↦]") as "AU".
    iModIntro. wp_let. wp_op.
    rewrite bool_decide_eq_false_2 //. wp_if.
    iApply ("IH" with "Sh"). auto.
Qed.

Lemma shield_acc :
  shield_acc' N Shield.
Proof.
  intros ????????.
  iDestruct 1 as (????????) "Sh".
  iDestruct "Sh" as (???) "(%Hγ & ShH & †Sh & S & (% & %Hv & [#i_data Prot] & ●TxI))".
  iDestruct "Prot" as (?) "(#i□ & pc & cinv & #Ex & #RCI & ●II)".

  iInv "RCI" as "[R cinv]" "Close1".
  iDestruct "R" as (?) "(>%Hsize_i & [_ R] & >p↦)".
  iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Close2".
  iExists vl. iFrame "p↦ R"; iSplit; [done|].
  iSplitR "Close1 Close2". { repeat (exfr; tspd). }

  iIntros (vl') "(%Hvl' & p↦ & R)".
  iMod "Close2".
  iMod ("Close1" with "[p↦ R]"); exfr. iPureIntro. lia.
Qed.

Lemma managed_acc :
  managed_acc' N Managed.
Proof.
  intros ???????.
  iIntros "G".
    iDestruct "G" as (?????????) "(%Hγ & [#i_data G])".
    iDestruct "G" as (?) "(Gcinv & #i□ & pc & #Ex & #RCI & GU & GR)".
  iInv "RCI" as "[R cinv]" "Close1".
  iDestruct "R" as (?) "(>%Hsize_i & [_ R] & >p↦)".
  iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Close2".

  iExists vl. iFrame "p↦ R %".
  iSplitR "Close1 Close2". { repeat (exfr; tspd). }

  iIntros (vl') "(%Hvl' & p↦ & R)".
  iMod "Close2".
  iMod ("Close1" with "[p↦ R]"); exfr. iPureIntro. lia.
Qed.

Lemma managed_exclusive :
  managed_exclusive' N Managed.
Proof.
  intros ????????.
  iIntros "M M'".
  iDestruct "M" as (?????????) "(%Hγd & [_ M])".
  iDestruct "M'" as (?????????) "(% & [_ M'])".
  encode_agree Hγd.
  iApply (managed_base_exclusive with "M M'").
Qed.

Lemma shield_managed_agree :
  shield_managed_agree' N Managed Shield.
Proof.
  intros ?????????.
  iIntros "Sh G".
    iDestruct "Sh" as (????????) "Sh".
    iDestruct "Sh" as (???) "(%Hγ & ShH & †Sh & S & (% & %Hv & [#i_data Prot] & ●TxI))".
    iDestruct "Prot" as (?) "(#i□ & pc & cinv & #Ex & #RCI & ●II)".
    iDestruct "G" as (?????????) "(%Hγ' & [#i_data' G])".
    encode_agree Hγ'.
    iDestruct "G" as (?) "(Gcinv & #i□2 & pc2 & #Ex2 & CInv & GU & GR)".
  iDestruct (coP_ghost_map_elem_agree with "pc pc2") as "<-".
  by iDestruct (ghost_map_elem_agree with "i_data i_data'") as %<-.
Qed.

Lemma hazard_domain_retire_spec :
  hazard_domain_retire_spec' N hazard_domain_retire IsHazardDomain Managed.
Proof.
  intros ????????.
  iIntros "#IHD" (Φ) "!> G HΦ".
    iDestruct "IHD" as (??????????) "(%Hγ & ↦hBag & ↦rSet & IHD)".
    iDestruct "G" as (?????????) "(%Hγ' & [#i_data G])".
    encode_agree Hγ'.
    iDestruct "G" as (?) "(Gcinv & #i□ & pc & #Ex & #RCI & GU & GR)".
  wp_lam. wp_pures. wp_load. wp_let.

  wp_apply (rls.(retired_node_new_spec)); auto.
  iIntros (rNode) "RN". wp_let.
  awp_apply (rls.(retired_list_push_spec) with "RN") without "HΦ".

  iInv "IHD" as (??? hmap1 slist1 rs1)
    "(>M & >datM & >coM & >B & >RS & >●Q & >●X & >Reg & Ret & >%Hdom & >%HInfo)".
  iDestruct (SlotBag_NoDup with "B") as "%ND".
  iDestruct (coP_ghost_map_lookup with "coM pc") as %Hp.
  apply HInfo in Hp as Hinfo_i. destruct Hinfo_i as [info_i [Hinfo_i <-]].

  iAaccIntro with "RS"; iIntros "RS".
  { iModIntro. repeat exfr. }
  iMod (ghost_quadrants_retire with "GR ●Q GU") as "(GR & ●Q & GU)"; auto.

  iModIntro. iSplitL; last first.
  { iIntros "HΦ". by iApply "HΦ". }
  repeat (exfr; tspd).
Qed.

(** * Proof of snapshot *)
Definition SnapshotLoopInv_r γtok γinfo γdata γptrs γU γR
    (slist : list loc) (slen := length slist)
    (rem : nat) (snap : list (option blk)) (r : blk) (len : nat) : iProp :=
  ∃ i R,
    Reclaiming (mgmtN N) (ptrsN N) γtok γinfo γdata γptrs γU r i len R ∗
    (* tokens that we've taken from hazard bag head *)
    ({[i]},sids_from slen) ↦P2[γR]{ 1/2 } true ∗
    toks γtok {[i]} (sids_from slen) ∗
    (* slots that we haven't checked yet *)
    ({[i]},sids_to rem) ↦P2[γR]{ 1/2 } false ∗
    (* tokens taken from shields that were not protecting [i]. *)
    if bool_decide (Some r ∈ snap) then
      ({[i]},sids_range rem slen) ↦P2[γR]{ 1/2 } false
    else
      ({[i]},sids_range rem slen) ↦P2[γR]{ 1/2 } true ∗
      toks γtok {[i]} (sids_range rem slen)
  .

Definition SnapshotLoopInv γtok γinfo γdata γptrs γU γR
    (slist : list loc) (slen := length slist)
    (rem : nat) (snap : list (option blk)) (rs : list (blk * nat * nat)) : iProp :=
  [∗ list] rle ∈ rs, let '(r,len,_) := rle in
    SnapshotLoopInv_r γtok γinfo γdata γptrs γU γR slist rem snap r len.

Definition AddIfActivePost_r γtok γinfo γdata γptrs γU γR
    (slist : list loc) (slen := length slist)
    (rem' : nat) (snap : list (option blk))
    (act : bool) (hz : option blk) (r : blk) (len : nat) : iProp :=
  ∃ i R,
    Reclaiming (mgmtN N) (ptrsN N) γtok γinfo γdata γptrs γU r i len R ∗
    (* tokens that we've taken from hazard bag head *)
    ({[i]},sids_from slen) ↦P2[γR]{ 1/2 } true ∗
    toks γtok {[i]} (sids_from slen) ∗
    (* slots that we haven't checked yet *)
    ({[i]},sids_to rem') ↦P2[γR]{ 1/2 } false ∗
    if bool_decide (Some r ∈ snap) || (act && bool_decide (hz = Some r)) then
      (* protected by any of checkd slots *)
      ({[i]},sids_range rem' slen) ↦P2[γR]{ 1/2 } false
    else
      (* not protected *)
      ({[i]},sids_range rem' slen) ↦P2[γR]{ 1/2 } true ∗
      toks γtok {[i]} (sids_range rem' slen) %I .

Definition AddIfActivePost γtok γinfo γdata γptrs γU γR
    (slist : list loc) (slen := length slist)
    (rem' : nat) (snap : list (option blk))
    (act : bool) (hz : option blk) (rs : list (blk * nat * nat)) : iProp :=
  [∗ list] rle ∈ rs, let '(r,len,_) := rle in
    AddIfActivePost_r γtok γinfo γdata γptrs γU γR slist rem' snap act hz r len.

Lemma add_if_active_already_protected_r γtok γinfo γdata γptrs γU γR
    (slist1 : list loc) (slen := length slist1) (* slist of read_head *)
    (rem' : nat) (snap : list (option blk))
    (act : bool) (hz : option blk) (r : blk) (len : nat)
    (Hrem : S rem' ≤ slen)
    (Hsnap_r : Some r ∈ snap) :
  SnapshotLoopInv_r γtok γinfo γdata γptrs γU γR slist1 (S rem') snap r len
  -∗
  AddIfActivePost_r γtok γinfo γdata γptrs γU γR slist1 rem' snap act hz r len.
Proof.
  unfold SnapshotLoopInv_r, AddIfActivePost_r.
  rewrite bool_decide_eq_true_2 //. rewrite orb_true_l.
  iDestruct 1 as (i R) "(R & γR_from1 & toks_from1 & γR_R_to_rem'1 & range_rem'1_1)".
  iExists i,R. iFrame.
  rewrite (sids_range_cons rem'); last lia.
  rewrite -ghost_vars2_union_2; last by apply sid_sids_range_disjoint_cons.
  rewrite sids_to_S. rewrite -ghost_vars2_union_2; last by apply sids_to_sid_disjoint.
  rewrite -Nat.add_1_r. iDestruct "γR_R_to_rem'1" as "[$ $]". iFrame.
Qed.

Lemma add_if_active_new_protection_r γtok γinfo γdata γptrs γU γR γV
    info sbvmap
    (slist1 : list loc) (slen1 := length slist1) (* slist of read_head *)
    (slist2 : list loc) (* current slist *)
    (rem' : nat) (snap : list (option blk))
    (act : bool) (hz : option blk) (r : blk) (len : nat)
    (Hrem : S rem' ≤ slen1)
    (PF12 : slist1 `prefix_of` slist2)
    (Hsnap_r : Some r ∉ snap)
    (Hact : act = true)
    (Hhz : hz = Some r) :
  ghost_map_auth γinfo 1 info -∗
  CC γtok γinfo γptrs γU γR γV info sbvmap slist2 -∗
  SnapshotLoopInv_r γtok γinfo γdata γptrs γU γR slist1 (S rem') snap r len
  ==∗
  ghost_map_auth γinfo 1 info ∗
  CC γtok γinfo γptrs γU γR γV info sbvmap slist2 ∗
  AddIfActivePost_r γtok γinfo γdata γptrs γU γR slist1 rem' snap act hz r len.
Proof.
  have [slist12 Hslist2] := PF12.
  unfold SnapshotLoopInv_r, AddIfActivePost_r. subst act hz.
  rewrite bool_decide_eq_false_2 //. rewrite bool_decide_eq_true_2 //=.
  iIntros "●info CC R".
  iDestruct "R" as (i R) "(R & γR_from1 & toks_from1 & γR_R_to_rem'1 & range_rem'1_1)".
  iDestruct "R" as (data_i γc_i) "(? & ◯i & ? & ? & ? & γU_R)".
  iDestruct (ghost_map_lookup with "●info ◯i") as %Hi. iFrame "●info".
  iDestruct (big_sepM_lookup_acc _ _ _ _ Hi with "CC") as "[CC_i CC]". simpl.
  iDestruct "CC_i" as (U_i) "(γU_CC & CC_i)".
  rewrite sids_to_S. rewrite -ghost_vars2_union_2; last by apply sids_to_sid_disjoint.
  iDestruct "γR_R_to_rem'1" as "[γR_R_to_rem' γR_R_rem']".
  iDestruct (ghost_vars_agree with "γU_R γU_CC") as %<-; [set_solver|].
  iEval (rewrite Hslist2 big_opL_app) in "CC_i".
  iDestruct "CC_i" as "[CC_i_to1 CC_i_from1]".
  iDestruct (big_sepL_take_drop _ _ rem' with "CC_i_to1") as "[CC_i_to_rem' CC_i_rem'_1]".

  iAssert ( |==>
    ([∗ list] k↦y ∈ drop rem' slist1, ∃ b v (V R : bool),
      ⌜sbvmap !! y = Some (b, v)⌝ ∗
      (i,sid (rem' + k)) ↦p2[γV]{ 1/2 } V ∗
      (i,sid (rem' + k)) ↦p2[γR]{ 1/2 } R ∗
      ⌜V → b = true ∧ v = Some r⌝ ∗
      ⌜R → true⌝ ∗
      (if V then if R then False else emp else if R then emp else stok γtok i (rem' + k)) ) ∗
      ({[i]},sids_range rem' slen1) ↦P2[γR]{ 1/2 } false
  )%I with "[CC_i_rem'_1 γR_R_rem' range_rem'1_1]" as ">[CC_i_rem'_1 range_rem'_1]".
  { rewrite -Nat.add_1_r.
    rewrite (sids_range_cons rem'); last lia.
    rewrite -ghost_vars2_union_2; last by apply sid_sids_range_disjoint_cons.
    iDestruct "range_rem'1_1" as "[γR_R_rem'1_1 toks_rem'1_1]".
    rewrite (big_sepL_take_drop _ _ 1) drop_drop.
    iDestruct "CC_i_rem'_1" as "[CC_i_rem' CC_i_rem'1_1]".
    iFrame "γR_R_rem' CC_i_rem'".

    (* for [big_sepL_sids_range_2] *)
    have {}Hrem : rem' + 1 = slen1 ∨ rem' + 1 < slen1 by lia. destruct Hrem as [Hrem|Hrem].
    { (* identity of ghost_vars2 *)
      rewrite Hrem drop_all big_opL_nil sids_range_empty.
      iFrame. iApply ghost_vars2_get_empty_2.
    }
    set dropped := drop (rem' + 1) slist1.
    have ? : length dropped = slen1 - (rem' + 1).
    { by rewrite length_drop. }
    have ? : dropped ≠ [].
    { move => /(f_equal length) /=. lia. }
    iDestruct (big_sepL_sids_range_1 (λ E, ({[i]},E) ↦P2[γR]{ 1/2 } true)
      _ _ dropped with "γR_R_rem'1_1") as "γR_R_rem'1_1";
      [by auto using ghost_vars2_union_2 | done | ].
    iDestruct (big_sepL_sids_range_1 (λ E, toks γtok {[i]} E)
      _ _ dropped with "toks_rem'1_1") as "toks_rem'1_1";
      [by auto using toks_union_2 | done | ].
    set LEFT := (LEFT in (|==> LEFT ∗ _)%I).
    iAssert (|==> LEFT ∗
      [∗ list] k↦x ∈ dropped, (i,sid (rem' + 1 + k)) ↦p2[γR]{ 1/2 } false
    )%I with "[-]" as ">[$ γR_R_rem'1_1]"; last first.
    { iModIntro.
      iApply (big_sepL_sids_range_2 (λ E, ({[i]},E) ↦P2[γR]{ 1/2 } false)
        _ _ dropped with "γR_R_rem'1_1");
        [by auto using ghost_vars2_union_2 | done | done]. }
    subst LEFT.
    iCombine "CC_i_rem'1_1 γR_R_rem'1_1 toks_rem'1_1" as "X".
    rewrite -!big_sepL_sep.
    iApply big_sepL_bupd. iApply (big_sepL_mono with "X"). simpl.
    iIntros (???) "(CC_i_k & γR_R_k & toks_k)".
    iDestruct "CC_i_k" as (???? Hslot') "(? & γR_CC_k & ? & ? & ?)".
    replace (rem' + 1 + k) with (rem' + S k) by lia.
    iDestruct (ghost_vars2_agree with "γR_R_k γR_CC_k") as %<-; [set_solver..|].
    destruct V; [done|].
    iMod (ghost_vars2_update_halves' false with "γR_R_k γR_CC_k") as "[? $]".
    iModIntro. iFrame "%∗". unfold stok. iFrame. done. }

  iModIntro.
  (* Reassemble the resources and process the remaining retired pointers. *)
  iAssert (CC γtok γinfo γptrs γU γR γV info sbvmap slist2)
    with "[CC_i_to_rem' CC_i_rem'_1 CC_i_from1 γU_CC CC]" as "$".
  { iApply "CC". iExists _. iFrame "γU_CC".
    rewrite Hslist2. iApply big_sepL_app. iFrame "CC_i_from1".
    iApply (big_sepL_take_drop _ _ rem'). iFrame. }

  iExists i,R. iFrame.
Qed.

Lemma add_if_active_still_not_protected γtok γinfo γdata γptrs γU γR γV
    info sbvmap
    (slist1 : list loc) (slen1 := length slist1) (* slist of read_head *)
    (slist2 : list loc) (* current slist *)
    (rem' : nat) (snap : list (option blk))
    (* [act] is the active flag that we first saw, and [act'] is the current active flag.
    If [act] is false, then we use [act] as the current active flag [act'].  *)
    (act act' : bool) (hz : option blk) (r : blk) (len : nat) (slot : loc)
    (Hrem : S rem' ≤ slen1)
    (PF12 : slist1 `prefix_of` slist2)
    (Hsnap_r : Some r ∉ snap)
    (Hachz : (act = false ∧ act' = act) ∨ hz ≠ Some r)
    (Hrem' : slist1 !! rem' = Some slot)
    (Hslot : sbvmap !! slot = Some (act', hz)) :
  ghost_map_auth γinfo 1 info -∗
  CC γtok γinfo γptrs γU γR γV info sbvmap slist2 -∗
  SnapshotLoopInv_r γtok γinfo γdata γptrs γU γR slist1 (S rem') snap r len
  ==∗
  ghost_map_auth γinfo 1 info ∗
  CC γtok γinfo γptrs γU γR γV info sbvmap slist2 ∗
  AddIfActivePost_r γtok γinfo γdata γptrs γU γR slist1 rem' snap act hz r len.
Proof.
  have [slist12 Hslist2] := PF12.
  unfold SnapshotLoopInv_r, AddIfActivePost_r.
  rewrite bool_decide_eq_false_2 //.
  replace (act && bool_decide (hz = Some r)) with false; last first.
  { destruct Hachz as [[-> ->]|?]; [done|].
    rewrite bool_decide_eq_false_2 //. rewrite andb_false_r //. }
  iIntros "●info CC R".
  iDestruct "R" as (i R) "(R & γR_from1 & toks_from1 & γR_R_to_rem'1 & range_rem'1_1)".
  iDestruct "R" as (data_i γc_i) "(? & ◯i & ? & ? & ? & γU_R)".
  iDestruct (ghost_map_lookup with "●info ◯i") as %Hi. iFrame "●info".
  iDestruct (big_sepM_lookup_acc _ _ _ _ Hi with "CC") as "[CC_i CC]". simpl.
  iDestruct "CC_i" as (U_i) "(γU_CC & CC_i)".
  rewrite sids_to_S. rewrite -ghost_vars2_union_2; last by apply sids_to_sid_disjoint.
  iDestruct "γR_R_to_rem'1" as "[γR_R_to_rem' γR_R_rem']".
  iDestruct (ghost_vars_agree with "γU_R γU_CC") as %<-; [set_solver|].
  (* rewrite -ghost_vars2_set. *)
  iEval (rewrite Hslist2 big_opL_app) in "CC_i".
  iDestruct "CC_i" as "[CC_i_to1 CC_i_from1]".
  iDestruct (big_sepL_take_drop _ _ rem' with "CC_i_to1") as "[CC_i_to_rem' CC_i_rem'_1]".

  iAssert ( |==>
    ([∗ list] k↦y ∈ drop rem' slist1, ∃ b v (V R : bool),
      ⌜sbvmap !! y = Some (b, v)⌝ ∗
      (i,sid (rem' + k)) ↦p2[γV]{ 1/2 } V ∗
      (i,sid (rem' + k)) ↦p2[γR]{ 1/2 } R ∗
      ⌜V → b = true ∧ v = Some r⌝ ∗
      ⌜R → true⌝ ∗
      (if V then if R then False else emp else if R then emp else stok γtok i (rem' + k)) ) ∗
      ({[i]},sids_range rem' slen1) ↦P2[γR]{ 1/2 } true ∗
      toks γtok {[i]} (sids_range rem' slen1)
  )%I with "[CC_i_rem'_1 γR_R_rem' range_rem'1_1]" as ">[CC_i_rem'_1 range_rem'_1]".
  { rewrite -Nat.add_1_r.
    rewrite (sids_range_cons rem'); last lia.
    rewrite -ghost_vars2_union_2; last by apply sid_sids_range_disjoint_cons.
    rewrite -toks_union_2; last by apply sid_sids_range_disjoint_cons.
    iDestruct "range_rem'1_1" as "[γR_R_rem'1_1 toks_rem'1_1]".
    rewrite (big_sepL_take_drop _ _ 1) drop_drop.
    rewrite (_ : take 1 (drop rem' slist1) = [slot]); simpl; last first.
    { apply take_drop_middle in Hrem'. rewrite -Hrem'.
      have Htakerem' : length (take rem' slist1) = rem'.
      { rewrite length_take. lia. }
      rewrite drop_app_ge; last lia.
      rewrite Htakerem' Nat.sub_diag drop_0 /= take_0 //. }
    rewrite (right_id emp%I) Nat.add_0_r.

    iDestruct "CC_i_rem'_1" as "[CC_i_rem' CC_i_rem'1_1]".
    iFrame "γR_R_rem'1_1 toks_rem'1_1 CC_i_rem'1_1".
    iDestruct "CC_i_rem'" as (???? Hslot') "(? & γR_CC_rem' & %HV & _ & ?)".
    rewrite Hslot in Hslot'. injection Hslot' as [= <- <-].
    destruct V.
    { exfalso. specialize (HV ltac:(done)) as [-> ->]. naive_solver. }
    iDestruct (ghost_vars2_agree with "γR_R_rem' γR_CC_rem'") as %<-; [set_solver..|].
    iMod (ghost_vars2_update_halves' true with "γR_R_rem' γR_CC_rem'") as "[γR_R_rem' γR_CC_rem']".
    iModIntro. iFrame. iExists _,_. iFrame "%∗". done. }


  iModIntro.
  (* Reassemble the resources and process the remaining retired pointers. *)
  iAssert (CC γtok γinfo γptrs γU γR γV info sbvmap slist2)
    with "[CC_i_to_rem' CC_i_rem'_1 CC_i_from1 γU_CC CC]" as "$".
  { iApply "CC". iExists _. iFrame "γU_CC".
    rewrite Hslist2. iApply big_sepL_app. iFrame "CC_i_from1".
    iApply (big_sepL_take_drop _ _ rem'). iFrame. }

  iExists i,R. iFrame.
Qed.

Lemma hazard_bag_snapshot_spec :
  ∀ E (d hBag rSet : loc) γsb γtok γinfo γdata γptrs γU γR γV rs (_ : ↑N ⊆ E), ⊢
  {{{ (d +ₗ domHBag) ↦□ #hBag ∗
      inv hazptrInvN (HazardDomain γsb γtok γinfo γdata γptrs γU γR γV d hBag rSet) ∗
      (* Retired pointers to consider reclamation, popped from retire list. *)
      ([∗ list] rle ∈ rs, let '(r,len,_) := rle in ∃ i R,
        Retired (mgmtN N) (ptrsN N) γtok γinfo γdata γptrs γU γR r i len R)
  }}}
    slot_bag_snapshot #hBag @ E
  {{{ (seqBag : loc) (snap : list (option blk)), RET #seqBag;
      sbs.(SeqBag) seqBag snap ∗
      ([∗ list] rle ∈ rs, let '(r,len,_) := rle in ∃ i R,
        if bool_decide (Some r ∈ snap) then
          Retired (mgmtN N) (ptrsN N) γtok γinfo γdata γptrs γU γR r i len R
        else
          Reclaiming (mgmtN N) (ptrsN N) γtok γinfo γdata γptrs γU r i len R ∗
          ({[i]},⊤) ↦P2[γR]{ 1/2 } true ∗
          toks γtok {[i]} ⊤)
  }}}.
Proof.
  intros. iIntros (Φ) "!> (#d.hBag↦ & #Inv & Reclaiming) HΦ".
  wp_lam.
  wp_apply (sbs.(seq_bag_new_spec) with "[//]") as (seqBag) "Bag".

  wp_pures.

  (* 1. Read hazard bag head *)
  wp_bind (! _)%E.
  iInv "Inv" as "HD".
  iDestruct "HD" as (info1 data1 ptrs1 sbvmap1 slist1 rs1)
    "(>●info & >●data & >●ptrs & >SB & >RL & >(CC & CU & UC & UU) & >IS & >Free & Retired & >%Hdom1 & >%Hinfo1)".
  wp_apply (sbs.(slot_bag_read_head_spec) with "[$SB]") as "(SB & #SL)".


  set slen1 := length slist1.
  (* Take tokens (rs, ⊤∖slist) from CU. *)
  iAssert (|==>
    ghost_map_auth γinfo 1 info1 ∗ (* for lookup *)
    CU γtok γinfo γptrs γU γR γV info1 sbvmap1 slist1 ∗
    ([∗ list] rle ∈ rs, let '(r,len,_) := rle in ∃ i R,
      Reclaiming (mgmtN N) (ptrsN N) γtok γinfo γdata γptrs γU r i len R ∗
      ({[i]},sids_to slen1) ↦P2[γR]{ 1/2 } false ∗
      ({[i]},sids_from slen1) ↦P2[γR]{ 1/2 } true ∗
      toks γtok {[i]} (sids_from slen1))
  )%I with "[●info CU Reclaiming]" as ">(●info & CU & Reclaiming)".
  { (* Can use [big_sepL_mono], but need to fully spell out the goal since I need the update. *)
    iInduction rs as [|[[r len] ?] rs' IH].
    { rewrite !big_sepL_nil. by iFrame. }
    rewrite !big_sepL_cons.
    iDestruct "Reclaiming" as "[R Reclaiming']".
    iDestruct "R" as (? data_i γc_i R) "(? & ◯i & ? & ? & ? & γU_R & γR_R_⊤)".
    iDestruct (ghost_map_lookup with "●info ◯i") as %Hi.
    iEval (unfold CU) in "CU".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hi with "CU") as "[CU_i CU]".
    iDestruct "CU_i" as (U_i R_i) "(γU_CU & γR_CU_ex & γV & toks_ex & %HUR)".
    iDestruct (ghost_vars_agree with "γU_R γU_CU") as %<-; [set_solver|].
    iEval (rewrite (top_union_difference (sids_to slen1))) in "γR_R_⊤".
    iEval (rewrite -ghost_vars2_union_2; last set_solver) in "γR_R_⊤".
    iDestruct "γR_R_⊤" as "[γR_R_ex γR_R_s]".
    iDestruct (ghost_vars2_eq_agree with "γR_R_ex γR_CU_ex") as %<-.
      { set_solver. } { apply sids_from_nonempty. }
    iMod (ghost_vars2_update_halves' true with "γR_R_ex γR_CU_ex") as "[γR_R_ex γR_CU_ex]".
    iSpecialize ("CU" with "[γU_CU γR_CU_ex γV]").
    { iExists true,true. by iFrame. }
    fold (CU γtok γinfo γptrs γU γR γV info1 sbvmap1 slist1).
    iMod ("IH" with "●info CU Reclaiming'") as "{IH} ($ & $ & $)".
    iModIntro. iExists i. iFrame "toks_ex γR_R_ex γR_R_s".
    iExists data_i,γc_i,R. iFrame. }

  (* Close invariant *)
  iModIntro. iSplitR "Reclaiming HΦ Bag".
  { repeat iExists _. by iFrame. }
  clear dependent info1 ptrs1 sbvmap1 (* slist1 *) rs1.

  wp_let.

  have hazard_bag_snapshot_loop_spec snap (rem : nat) (Hrem : rem ≤ slen1) :
    {{{ inv hazptrInvN (HazardDomain γsb γtok γinfo γdata γptrs γU γR γV d hBag rSet) ∗
        sbs.(SlotList) γsb slist1 ∗
        sbs.(SeqBag) seqBag snap ∗
        SnapshotLoopInv γtok γinfo γdata γptrs γU γR slist1 rem snap rs
    }}}
      slot_bag_snapshot_loop #seqBag #(oloc_to_lit (last (take rem slist1))) @ E
    {{{ snap', RET #();
        sbs.(SeqBag) seqBag snap' ∗
        ([∗ list] rle ∈ rs, let '(r,len,_) := rle in ∃ i R,
          Reclaiming (mgmtN N) (ptrsN N) γtok γinfo γdata γptrs γU r i len R ∗
          if bool_decide (Some r ∈ snap') then
            ({[i]},⊤) ↦P2[γR]{ 1/2 } false
          else
            ({[i]},⊤) ↦P2[γR]{ 1/2 } true ∗
            toks γtok {[i]} ⊤)
    }}}; last first.
  { (* loop postcondition implies snapshot postcondition *)
    iPoseProof (hazard_bag_snapshot_loop_spec [] slen1 ltac:(done)
      with "[$Bag Reclaiming]") as "Loop"; clear hazard_bag_snapshot_loop_spec.
    { simpl. iFrame "#". iApply (big_sepL_mono with "Reclaiming").
      iIntros (k [[r len] ?] Hk). iDestruct 1 as (i R) "(R & γR_to & γR_from & toks_from)".
      iExists i,R. iFrame "R γR_to".
      rewrite sids_range_empty.
      iEval (rewrite -(right_id_L ∅ (∪) (sids_from slen1))) in "γR_from toks_from".
      rewrite -ghost_vars2_union_2; last set_solver.
      rewrite -toks_union_2; last set_solver.
      iDestruct "γR_from" as "[$ $]". iDestruct "toks_from" as "[$ $]". }
    rewrite firstn_all. wp_apply "Loop".
    iIntros (snap) "[Bag Reclaiming]".
    wp_pures.

    iApply ("HΦ" with "[$Bag Reclaiming]").
    iApply (big_sepL_mono with "Reclaiming").
    iIntros (? [[r len] ?] ?).
    iDestruct 1 as (i R) "[R toks]". iExists i,R.
    case_bool_decide; last by iFrame.
    iDestruct "R" as (??) "(? & ? & ? & ?)".
    iExists _,_. iFrame. }

  (* Proof of the loop spec *)
  iIntros (Φ') "(#Inv & #SL & Bag & Reclaiming) HΦ'".
  iInduction rem as [|rem' IH] forall (snap).
  { (* Finished snapshot. *)
    clear Hrem. unfold SnapshotLoopInv, SnapshotLoopInv_r.
    rewrite sids_range_0_sids_to. simpl.
    wp_lam. wp_pures. iApply "HΦ'". iFrame "Bag".
    iInduction rs as [|[[r len] ?] rs' IHrs].
    { rewrite big_sepL_nil //. }
    rewrite !big_sepL_cons.
    iDestruct "Reclaiming" as "[R Reclaiming']".
    iSplitR "IHrs Reclaiming'"; last by iApply ("IHrs" with "Reclaiming'"). iClear "IHrs".
    iDestruct "R" as (i R) "(R & γR_from1 & toks_from1 & _ & checked)". fold (sids_to slen1).
    iExists i,R.
    case_bool_decide as Hr; last first.
    { (* Not protected. Took all tokens. *)
      iModIntro. fold (sids_to slen1). iDestruct "checked" as "[γR_to1 toks_to1]".
      iCombine "toks_to1 toks_from1" as "toks". rewrite toks_union_2; last set_solver.
      iCombine "γR_to1 γR_from1" as "γR". rewrite ghost_vars2_union_2; last set_solver.
      rewrite sids_to_sids_from_union. iFrame. }

    (* Protected. Should return toks_from1. *)
    iInv "Inv" as "HD". iClear "Inv".
    iDestruct "HD" as (info2 data2 ptrs2 sbvmap2 slist2 rs2)
      "(>●info & >●data & >●ptrs & >SB & >RL & >Q & >IS & >Free & Retired & >%Hdom2 & >%Hinfo2)".

    (* split flags/tokens: 0...slist1...slist2...⊤. *)
    set slen2 := length slist2.
    iDestruct (SlotBag_prefix with "SB SL") as %PF12. iClear "SL".
    have LE12 : slen1 ≤ slen2 by apply prefix_length.
    have [slist12 Hslist2] := PF12.
    have Hslen12 : length slist12 = slen2 - slen1.
    { subst slist2 slen1 slen2. rewrite length_app. lia. }
    rewrite (sids_from_prefix _ _ LE12).
    rewrite -ghost_vars2_union_2; last by apply sids_range_sids_from_disjoint.
    rewrite -toks_union_2; last by apply sids_range_sids_from_disjoint.
    iDestruct "γR_from1" as "[γR_range12 γR_from2]".
    iDestruct "toks_from1" as "[toks_range12 toks_from2]".
    iDestruct (big_sepL_sids_range_1 (λ E, ({[i]},E) ↦P2[γR]{ 1/2 } true)
      slen1 slen2 slist12 with "γR_range12") as "γR_range12";
      [by auto using ghost_vars2_union_2 | done | ].
    iDestruct (big_sepL_sids_range_1 (λ E, toks γtok {[i]} E)
      slen1 slen2 slist12 with "toks_range12") as "toks_range12";
      [by auto using toks_union_2 | done | ].
    iDestruct (big_sepL_sep with "[$γR_range12 $toks_range12]") as "R_range12".

    (* prep *)
    iDestruct "R" as (data_i γc_i) "(? & ◯i & ? & ? & ? & γU_R)".
    iDestruct (ghost_map_lookup with "●info ◯i") as %Hi.
    iDestruct "Q" as "(CC & CU & UC & UU)".

    (* Return toks_range12 to CC *)
    iAssert ( |==>
      CC γtok γinfo γptrs γU γR γV info2 sbvmap2 slist2 ∗
      [∗ list] k↦x ∈ slist12, (i,sid (slen1 + k)) ↦p2[γR]{ 1/2 } false
    )%I with "[CC R_range12]" as ">[CC γR_range12]".
    { unfold CC.
      rewrite (big_sepM_delete _ _ _ _ Hi) /=.
      iDestruct "CC" as "[CC_i $]". iDestruct "CC_i" as (U) "[γU CC_i]".
      rewrite bi.sep_exist_r. iExists U. iFrame "γU".
      rewrite Hslist2 big_sepL_app -/slen1.
      iDestruct "CC_i" as "[$ CC_i_range12]".
      iCombine "CC_i_range12 R_range12" as "range12".
      rewrite -!big_sepL_sep.
      iApply big_sepL_bupd. iApply (big_sepL_mono with "range12").
      iIntros (k slot Hk) "(CC_i_k & γR_i_k & toks_i_k)".
      iDestruct "CC_i_k" as (?????) "(γV & γR_CC & %HV & %HUR & emp)".
      iDestruct (ghost_vars2_agree with "γR_i_k γR_CC") as %<-; [set_solver..|].
      specialize (HUR ltac:(done)). destruct U,V; [done| |done|done].
      clear HUR. iClear "emp".
      iMod (ghost_vars2_update_halves' false with "γR_i_k γR_CC") as "[γR_i_k γR_CC]".
      iFrame.
      iModIntro. iExists _,_. iFrame. done.
    }

    (* Return toks_from2 *)
    iAssert ( |==>
      CU γtok γinfo γptrs γU γR γV info2 sbvmap2 slist2 ∗
      ({[i]},sids_from slen2) ↦P2[γR]{ 1/2 } false
    )%I with "[CU γR_from2 toks_from2]" as ">[CU γR_from2]".
    { unfold CU.
      rewrite (big_sepM_delete _ _ _ _ Hi) /=.
      iDestruct "CU" as "[CU_i $]".
      iDestruct "CU_i" as (U ?) "(γU & γR_CU & ? & _ & %HUR)".
      rewrite bi.sep_exist_r. iExists U. iFrame "γU".
      rewrite bi.sep_exist_r. iExists false.
      iDestruct (ghost_vars2_eq_agree with "γR_from2 γR_CU") as %<-.
        { set_solver. } { apply sids_from_nonempty. }
      iMod (ghost_vars2_update_halves' false with "γR_from2 γR_CU") as "[γR_from2 γR_CU]".
      iModIntro. iFrame. done.
    }

    (* Close invariant *)
    iModIntro. iSplitL "●info ●data ●ptrs SB RL CC CU UC UU IS Free Retired".
    { iNext. repeat iExists _. iFrame. done. }

    (* Make postcondition *)
    iModIntro. iSplitR "checked γR_range12 γR_from2".
    { repeat iExists _. iFrame. }
    rewrite -(sids_to_sids_from_union slen1) -ghost_vars2_union_2; last set_solver.
    iFrame "checked".
    (* The annoying part. Can't convert [big_opL] to [ghost_vars2_set] if empty. *)
    destruct slist12.
    { list_simplifier. assert (slen1 = slen2) as -> by lia. iFrame. }
    iPoseProof (big_sepL_sids_range_2 (λ E, ({[i]},E) ↦P2[γR]{ 1/2 } false)
      slen1 slen2 with "γR_range12") as "γR_range12";
      [by auto using ghost_vars2_union_2 | done | done | ].
    rewrite (sids_from_prefix slen1 slen2); last done.
    rewrite -ghost_vars2_union_2; last by apply sids_range_sids_from_disjoint.
    iFrame.
  } (* end of "Finished snapshot" *)

  (* Read the current slot and add to snapshot. *)

  (* [rem'] is the index of the current slot. *)
  have [slot Hrem'] : is_Some (slist1 !! rem').
  { apply lookup_lt_is_Some_2. lia. }
  rewrite take_last; last done. rewrite Hrem' /=.
  wp_lam. wp_pures.

  (* 2. Check if the slot is active. *)
  wp_bind (! _)%E.
  iInv "Inv" as "HD".
  iDestruct "HD" as (info2 data2 ptrs2 sbvmap2 slist2 rs2)
    "(>●info & >●data & >●ptrs & >SB & >RL & >(CC & CU & UC & UU) & >IS & >Free & Retired & >%Hdom2 & >%Hinfo2)".
  iDestruct (sbs.(SlotBag_prefix) with "SB SL") as %PF12.
  have {}Hrem'2 : slist2 !! rem' = Some slot.
  { by eapply prefix_lookup_Some. }
  wp_apply (sbs.(slot_read_active_spec) $! _ _ _ _ _ _ _ Hrem'2 with "SB") as (act hz) "[% SB]".


  destruct act; last first.
  { (* Slot is not active. If I have some tokens, then revoke them. *)
    iAssert ( |={E ∖ ↑hazptrInvN}=>
      ghost_map_auth γinfo 1 info2 ∗ (* for lookup *)
      CC γtok γinfo γptrs γU γR γV info2 sbvmap2 slist2 ∗
      SnapshotLoopInv γtok γinfo γdata γptrs γU γR slist1 rem' snap rs
    )%I with "[●info CC Reclaiming]" as ">(●info & CC & Reclaiming)".
    { iClear "#".
      unfold SnapshotLoopInv, AddIfActivePost.
      iInduction rs as [|[[r len] ?] rs' IH].
      { rewrite !big_sepL_nil. iModIntro. iFrame. }
      rewrite !big_sepL_cons /=.
      iDestruct "Reclaiming" as "[R Reclaiming']".
      iAssert ( |==>
        ghost_map_auth γinfo 1 info2 ∗
        CC γtok γinfo γptrs γU γR γV info2 sbvmap2 slist2 ∗
        AddIfActivePost_r γtok γinfo γdata γptrs γU γR slist1 rem' snap false hz r len
      )%I with "[●info CC R]" as ">(●info & CC & R)".
      { case (decide (Some r ∈ snap)) as [Hsnap_r|Hsnap_r].
        - iModIntro. iFrame.
          iDestruct (add_if_active_already_protected_r with "R") as "R"; done.
        - iMod (add_if_active_still_not_protected with "●info CC R") as "($ & $ & $)"; try done.
          by left. }
      iDestruct ("IH" with "●info CC Reclaiming'") as "{IH} >(●info & CC & Post)".
      iModIntro. iFrame.
      unfold SnapshotLoopInv_r, AddIfActivePost_r.
      rewrite andb_false_l orb_false_r. iFrame. }

    (* Close invariant *)
    iModIntro. iSplitR "Bag Reclaiming HΦ'".
    { iNext. repeat iExists _. iFrame. done. }
    clear dependent info2 ptrs2 sbvmap2 slist2 rs2 hz.
    wp_pures.

    (* 4. Proceed to next slot. *)
    wp_bind (! _)%E.
    iInv "Inv" as "HD".
    iDestruct "HD" as (info4 data4 ptrs4 sbvmap4 slist4 rs4)
      "(>●info & >●data & >●ptrs & >SB & >RL & >(CC & CU & UC & UU) & >IS & >Free & Retired & >%Hdom4 & >%Hinfo4)".
    iDestruct (sbs.(SlotBag_prefix) with "SB SL") as %PF14.
    have [slist14 Hslist4] := PF14.
    have {}Hrem'4 : slist4 !! rem' = Some slot.
    { by eapply prefix_lookup_Some. }
    wp_apply (sbs.(slot_read_next_spec) $! _ _ _ _ _ _ _ Hrem'4 with "SB") as "SB".

    (* Close invariant *)
    iModIntro. iSplitR "Bag Reclaiming HΦ'".
    { iNext. repeat iExists _. iFrame. done. }
    wp_let.

    rewrite Hslist4. rewrite take_app_le; last lia.
    iSpecialize ("IH" with "[%]"); first lia.
    wp_apply ("IH" with "Bag [Reclaiming] HΦ'"). iClear "#".
    unfold AddIfActivePost, SnapshotLoopInv.
    iApply (big_sepL_mono with "Reclaiming").
    iIntros (k [[r len] ?] Hk) "R".
    unfold AddIfActivePost_r, SnapshotLoopInv_r.
    iDestruct "R" as (i R) "(? & ? & ? & ? & ?)".
    iExists i,R. iFrame. }


  (* Close invariant *)
  iModIntro. iSplitR "Bag Reclaiming HΦ'".
  { iNext. repeat iExists _. iFrame. done. }
  clear dependent info2 ptrs2 sbvmap2 slist2 rs2 hz.

  wp_pures.

  (* 3. Slot is active. Read the slot value. *)
  wp_bind (! _)%E.
  iInv "Inv" as "HD".
  iDestruct "HD" as (info3 data3 ptrs3 sbvmap3 slist3 rs3)
    "(>●info & >●data & >●ptrs & >SB & >RL & >(CC & CU & UC & UU) & >IS & >Free & Retired & >%Hdom3 & >%Hinfo3)".
  iDestruct (sbs.(SlotBag_prefix) with "SB SL") as %PF13.
  have [slist13 Hslist3] := PF13.
  have Hrem'3 : slist3 !! rem' = Some slot.
  { by eapply prefix_lookup_Some. }
  wp_apply (sbs.(slot_read_value_spec) $! _ _ _ _ _ _ _ Hrem'3 with "SB") as (act' hz) "[%Hslot SB]".
  (* NOTE: we don't care about this ['act] *)

  iAssert ( |==>
      ghost_map_auth γinfo 1 info3 ∗ (* for lookup *)
      CC γtok γinfo γptrs γU γR γV info3 sbvmap3 slist3 ∗
      AddIfActivePost γtok γinfo γdata γptrs γU γR slist1 rem' snap true hz rs
  )%I with "[●info CC Reclaiming]" as ">(●info & CC & Reclaiming)".
  { iClear "#".
    unfold SnapshotLoopInv, AddIfActivePost.
    iInduction rs as [|[[r len] ?] rs' IH].
    { rewrite !big_sepL_nil. by iFrame. }

    (* Process the retired pointer [r]. *)
    rewrite !big_sepL_cons /=.
    iDestruct "Reclaiming" as "[R Reclaiming']".

    iAssert ( |==>
      ghost_map_auth γinfo 1 info3 ∗
      CC γtok γinfo γptrs γU γR γV info3 sbvmap3 slist3 ∗
      AddIfActivePost_r γtok γinfo γdata γptrs γU γR slist1 rem' snap true hz r len
    )%I with "[●info CC R]" as ">(●info & CC & R)".
    { case (decide (Some r ∈ snap)) as [Hsnap_r|Hsnap_r];
        last case (decide (hz = Some r)) as [->|NE].
      - iModIntro. iFrame.
        iDestruct (add_if_active_already_protected_r with "R") as "$"; done.
      - iMod (add_if_active_new_protection_r with "●info CC R") as "($ & $ & $)"; done.
      - iMod (add_if_active_still_not_protected with "●info CC R") as "($ & $ & $)"; try done.
        by right. }

    iDestruct ("IH" with "●info CC Reclaiming'") as "{IH} >(●info & CC & Post)".
    iModIntro. iFrame.
  }

  (* Close invariant *)
  iModIntro. iSplitR "Bag Reclaiming HΦ'".
  { iNext. repeat iExists _. iFrame. done. }
  clear dependent info3 ptrs3 sbvmap3 slist3 rs3.

  wp_let.

  wp_apply (sbs.(seq_bag_add_spec) with "Bag") as "Bag".
  wp_pures.

  (* 4. Proceed to next slot. *)
  wp_bind (! _)%E.
  iInv "Inv" as "HD".
  iDestruct "HD" as (info4 data4 ptrs4 sbvmap4 slist4 rs4)
    "(>●info & >●data & >●ptrs & >SB & >RL & >(CC & CU & UC & UU) & >IS & >Free & Retired & >%Hdom4 & >%Hinfo4)".
  iDestruct (sbs.(SlotBag_prefix) with "SB SL") as %PF14.
  have [slist14 Hslist4] := PF14.
  have {}Hrem'4 : slist4 !! rem' = Some slot.
  { by eapply prefix_lookup_Some. }
  wp_apply (sbs.(slot_read_next_spec) $! _ _ _ _ _ _ _ Hrem'4 with "SB") as "SB".

  (* Close invariant *)
  iModIntro. iSplitR "Bag Reclaiming HΦ'".
  { iNext. repeat iExists _. iFrame. done. }
  wp_let.

  rewrite Hslist4. rewrite take_app_le; last lia.
  iSpecialize ("IH" with "[%]"); first lia.
  wp_apply ("IH" with "Bag [Reclaiming] HΦ'"). iClear "#".
  unfold AddIfActivePost, SnapshotLoopInv.
  iApply (big_sepL_mono with "Reclaiming").
  iIntros (k [[r len] ?] Hk) "R".
  unfold AddIfActivePost_r, SnapshotLoopInv_r.
  iDestruct "R" as (i R) "(? & ? & ? & ? & ?)".
  iExists i,R. iFrame.
  rewrite andb_true_l.
  replace (bool_decide (Some r ∈ hz :: snap))
    with (bool_decide (Some r ∈ snap) || bool_decide (hz = Some r)); first done.
  rewrite -bool_decide_or. apply bool_decide_ext. set_solver +.
Qed.

Lemma hazard_domain_do_reclamation_spec :
  hazard_domain_do_reclamation_spec' N hazard_domain_do_reclamation IsHazardDomain.
Proof.
  intros ????.
  iIntros "#IHD" (Φ) "!> _ HΦ".
    iDestruct "IHD" as (??????????) "(%Hγ & ↦hBag & ↦rSet & IHD)".
  unfold hazard_domain_do_reclamation. wp_lam.
  wp_op. wp_load. wp_let.

  (* pop all *)
  awp_apply rls.(retired_list_pop_all_spec) without "HΦ".
  iInv "IHD" as (??? hmap1 slist1 rs1)
    "(>M & >datM & >coM & >B & >RS & >●Q & >●X & >Reg & Ret & >%Hdom1 & >%HInfo1)".
  (*iDestruct (SlotBag_NoDup with "B") as "%ND".*)
  iAaccIntro with "RS". { iIntros "? !>". tspd. exfr. }
  iIntros (rNode1) "[RS RNs]".
  iModIntro.
  iSplitL "RS B M datM coM ●Q ●X Reg".
  { iExists info,data,ptrs,hmap1,slist1,[]. exfr. }
  iIntros "HΦ". wp_pures.
  wp_load. wp_let.

  (* snapshot *)
  wp_apply (hazard_bag_snapshot_spec _ d _ rSet
    γsb γtok γinfo γdata γptrs γU γR γV rs1 with "[Ret]"); auto.
  iIntros (??) "[Seq ◯]". wp_let.

  (* loop *)
  iLöb as "IH" forall (rNode1 rs1).
  wp_lam. wp_pures.
  destruct rNode1 as [rNode1|]; simpl; last first.
  { wp_pures. iModIntro. by iApply "HΦ". }

  wp_if.
  iDestruct (rls.(retired_nodes_cons) with "RNs") as
    (r1 rs1' next1 size1 epoch1) "[-> [RN RNs]]".
  wp_apply (rls.(retired_node_ptr_spec) with "RN") as "RN".
  wp_let.
  wp_apply (rls.(retired_node_next_spec) with "RN") as "RN".
  wp_let.

  simpl. iDestruct "◯" as "[[%i ◯i] ◯rs1']".
  wp_apply (sbs.(seq_bag_contains_spec) seqBag snap (Some r1) with "Seq") as "Seq".

  case_bool_decide as Hhazard.
  - (* hazard: r1 is in snap. put it back to retired set *)
    wp_if.
    awp_apply (retired_list_push_spec with "RN") without "◯rs1' HΦ RNs Seq".
    iInv "IHD" as (??? hmap2 slist2 rs2)
      "(>M & >datM & >coM & >B & >RS & >●Q & >●X & >Reg & Ret & >%Hdom2 & >%HInfo2)".
    iAaccIntro with "RS".
    { iIntros "? !>". iFrame "◯i". iNext. exfr. }
    iIntros "RS".
    iModIntro.
    iSplitL "◯i M datM coM B ●Q ●X Reg Ret RS".
    { iNext. exfr. }
    iIntros "(◯ & HΦ & [RN Seq])". wp_seq.
    wp_apply ("IH" with "RN HΦ Seq"); auto.

  - (* not hazard: r1 is not in snap. can free. *)
    (* Get full shields *)
    iDestruct "◯i" as (R) "(Recl & ●IT & T)".
      iDestruct "Recl" as (??) "(Gcinv & #i□ & r1i & #Ex & #CInv & U)".

    wp_if.
    wp_apply (rls.(retired_node_size_spec) with "RN") as "RN".
    wp_let.

    (* free *)
    wp_bind (Free _ _)%E.
    iInv "IHD" as (??? hmap2 slist2 rs2)
      "(>M & >datM & >coM & >B & >RS & >●Q & >●X & >Reg & Ret & >%Hdom2 & >%HInfo2)".
    iDestruct (coP_ghost_map_lookup with "coM r1i") as %Hr1.
    iDestruct (big_sepM_delete with "Reg") as "[Regr1 Reg]"; eauto.
      iDestruct ("Regr1") as (?) "(%Hi & †r1)".

    (* eject freeable info from the invariant *)
    iMod (exchange_toks_give_all with "Ex T") as "[rei cinv]"; [solve_ndisj|].
    iCombine "Gcinv cinv" as "cinv".
    rewrite -coP_cinv_own_fractional; last set_solver.
    rewrite -top_complement_singleton.
    iMod (coP_cinv_cancel with "CInv cinv") as "P"; [solve_ndisj|].
      iDestruct "P" as (?) "(><- & R & >r1↦)".
    iDestruct (ghost_map_lookup with "M i□") as %Hi'.
      rewrite Hi in Hi'. injection Hi' as [= ->]. simpl.

    (* close *)
    iDestruct (coP_ghost_map_elem_combine with "r1i rei") as "[ri _]".
    rewrite -top_complement_singleton.
    iMod (coP_ghost_map_delete with "coM ri") as "coM".
    wp_free.
    iModIntro. iSplitL "M datM coM B RS ●Q ●X Ret Reg".
    { exfr. iModIntro. iPureIntro. split; [done|].
      intros p' i' Hp'. specialize (HInfo2 p' i').
      rewrite lookup_delete_Some in Hp'. destruct Hp' as [Hr1p' Hp'].
      auto.
    }

    wp_seq.
    wp_apply (rls.(retired_node_drop_spec) with "RN") as "_".
    wp_seq. iApply ("IH" with "RNs HΦ Seq ◯rs1'").
Qed.

End hazptr.
