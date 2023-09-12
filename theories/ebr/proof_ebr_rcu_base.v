From iris.algebra Require Import auth gset gmap.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var.
From smr.base_logic.lib Require Import coP_ghost_map ghost_vars coP_cancellable_invariants mono_nats.
From smr.program_logic Require Import atomic.
From smr.logic Require Import token2 epoch_history.
From smr.lang Require Import proofmode notation.

From smr Require Import ebr.spec_rcu_base spec_slot_bag_onat spec_retired_list.
From smr Require Import ebr.code_ebr code_slot_bag_onat code_retired_list.
From smr Require Import helpers logic.reclamation.

From iris.prelude Require Import options.

Set Printing Projections.

(* TODO: Fix names. e.g, info or Im? ptrs or ptrs? rL or Rs? *)

Class ebrG Σ := EBRG {
  ebr_reclG :> reclamationG Σ;
  ebr_epoch_historyG :> epoch_historyG Σ;
  (* Epoch history is
     (1) not fractional
     (2) may be updated with the retire set not being updated.
     hence we use a separate ghost for the retire set.
   *)
  ebr_epoch_rsetG :> ghost_varG Σ (gset positive);
  ebr_epoch_gmapG :> ghost_mapG Σ blk positive;
  ebr_mono_natsG :> mono_natsG Σ;
}.

Definition ebrΣ : gFunctors := #[ reclamationΣ; epoch_historyΣ; ghost_varΣ (gset positive); ghost_mapΣ blk positive; mono_natsΣ ].

Global Instance subG_ebrΣ Σ :
  subG ebrΣ Σ → ebrG Σ.
Proof. solve_inG. Qed.

Section ebr.
Context `{!heapGS Σ, !ebrG Σ}.
Notation iProp := (iProp Σ).
Notation resource := (resource Σ).
Implicit Types (R : resource).

Context (mgmtN ptrsN : namespace) (DISJN : mgmtN ## ptrsN).
Set Default Proof Using "DISJN".

Context (sbs : slot_bag_spec Σ) (rls : retired_list_spec Σ).

Implicit Types
  (γsb γtok γinfo γptrs γeh γrs γU γR γV γe_nums : gname)
  (info : gmap positive (alloc * gname))
  (ptrs : gmap blk positive)
  (sbvmap : gmap loc (bool * option nat))
  (slist : list loc)
  (rL : list (blk * nat * nat))
  (ehist : list (gset positive))
  (Syn retired unlinked : gset positive)
.

(* TODO: Check if the description is still accurate.
Summary of notable differences:
* Guard-Activate (validating the local epoch)
    1. obtains the tokens of all potentially reachable pointers (i.e. have not been unlinked until the current epoch)
    2. obtains the permission to retire pointers at the current epoch ("epoch ownership")
* Guard-Validate:
    1. Should show that the guard already has token for the pointer.
    2. The guard will activate the validation flag for its slot for its local epoch.
* `may_advance`: check the lower bound of epoch numbers for each slot.  Mostly need to check validated guards.
* `try_advance`
    1. If we are the one advancing the epoch, domain should have all ownerships
       needed to advance epoch, as there are no past guard.
    2. for fully collected epoch, collect tokens for unlinked pointers
* `do_reclamation` just takes already collected tokens

Details (read along with epoch consensus digram, PEBR figure 3):
* invariants
    0. record epoch unlink history (master-snapshot)
    1. for each ptr id `i`, unlink flag is true iff it's in the auth unlink history
        * 1-1. If there's a retired node of `i` with epoch `e`, then `i` is in unlink history at `e`.
        * 1-2. If `i` is in unlink history at `e`, then unlink flag is true.
    2. local epoch ≤ global epoch ≤ local epoch + 1
    3. If global epoch is `e`, then ownership of epoch `e-2` has been collected ("finalized"), i.e. no more pointers can be retired at `e-2`
    4. If global epoch is `e`, then all tokens for pointers unlinked at `e-3` have been collected
        * for convenience, start the epoch from `3`, let global epoch be `e+3`
    5. Mutex
        * If a pointer `i` is validated, then the slot `s`'s value is `e` such that `i` is not unlinked in `e-1`
        * If reclamed, then unlinked
        * Can't be both validated and reclaimed
    6. Monotonicity of epoch number at each slot.
* guard activation of slot `s` at epoch `e`
    1. take a snapshot of **finalized history** (up to `e-2`)
        * **NOTE**: Guard at `e` can access pointer retired at `e-1`. So don't snapshot epochs ≥ `e-1`
    2. take all tokens that are not in the snapshot
    3. take ownership of epoch `e ↪{s} ∅`
    4. take ownership of slot number so cannot advance.
* guard deactivation of slot `s` at epoch `e`
    * give up all the tokens
        * **NOTE** This includes the token of pointers retired at `e-1`
    * epoch `e+2` can now finalize
* pointer protection:
    1. BaseManaged of `i` has `{i} ↪[U]{1/2} false`
    2. auth unlink history doesn't contain it (∵ invariant 1)
    3. my history snapshot doesn't contain it (by monotonicity)
    4. I have token for it
    * note: GPS RCU's reasoning is much more complicated.
* retire (unlink):
    1. get BaseManaged `i`, **local epoch** `e` of slot `s`
    2. set unlink flag
    3. add `e ↪{s} {i}` to unlink history
* global epoch advancement `e` → `e+1`:
    * Finalize epoch `e-1`: take ownership of epoch `e-1` (= learning about pointers retired in `e-1`; no more pointers can be retired at `e-1`)
        * If slot value is `e`, then it has given up the ownership of `e-1`
    * Take tokens of pointers retired at `e-2` (the last finalized epoch)
        * If slot is inactive, can take all tokens for `e-2` (finalize tokens). This maintains invariant 4.
* reclamation: at local epoch `e`, reclaim pointers retired at local epoch `e-3`
    1. `e` ≤ global epoch
    2. by invariant 4, we have all the tokens we need
*)

(* NOTE: When advancing e → e+1, take ownership of epoch e-1. *)

Definition GE_minus_2_et_al γV γeh ge slist : iProp :=
  (* NOTE: We will throw away [γV] for ({[1]}, ⊤) *)
  (sids_to (ge-1),sids_from (length slist)) ↦P2[γV] false ∗
  (sids_to (ge-1),sids_to (length slist)) ↦P2[γV]{ 1/2 } false ∗
  [∗ list] e ∈ seq 0 (ge-1),
    epoch_history_frag γeh e ⊤.

Definition GE_minus γV γeh γe_nums e slist sbvmap : iProp :=
  ({[sid e]},sids_from (length slist)) ↦P2[γV] false ∗
  epoch_history_frag γeh e (sids_from' (length slist)) ∗
  [∗ list] si ↦ slot ∈ slist, ∃ (b : bool) v (V : bool),
    ⌜ sbvmap !! slot = Some (b, v) ⌝ ∗
    (sid e,sid si) ↦p2[γV]{ 1/2 } V ∗
    ⌜ V → b = true ∧ v = Some e ⌝ ∗
    match V with
    | true => mono_nats_auth γe_nums {[sid si]} (1/2) e
    | false => epoch_history_frag γeh e {[sid si]}
    end.

Definition GhostEpochInformations γV γeh γe_nums ge slist sbvmap : iProp :=
  GE_minus_2_et_al γV γeh ge slist ∗
  GE_minus γV γeh γe_nums (ge - 1) slist sbvmap ∗
  GE_minus γV γeh γe_nums ge slist sbvmap ∗
  ([∗ list] si ↦ slot ∈ slist, ∃ (b : bool) v,
    ⌜ sbvmap !! slot = Some (b, v) ⌝) ∗
  (sids_from (ge + 1),sids_to (length slist)) ↦P2[γV]{ 1/2 } false ∗
  (sids_from (ge + 1),sids_from (length slist)) ↦P2[γV] false.

Global Instance ghost_epoch_informations_timeless γV γeh γe_nums ge slist sbvmap :
  Timeless (GhostEpochInformations γV γeh γe_nums ge slist sbvmap).
Proof.
  repeat (
    intros ||
    apply bi.sep_timeless || apply bi.exist_timeless ||
    apply big_sepM_timeless || apply big_sepL_timeless ||
    apply _ || case_match
  ).
Qed.

(* NOTE: Suppose we want to advance [ge] → [ge+1]. If a guard was at epoch
[ge], then it's epoch will never decrease. So we can take [frag]s at once when
we write the new global epoch. *)

(* BaseManaged should assert that it's not unlinked. *)
(* NOTE: Should keep this even in the epoch ownership model. *)
Definition UnlinkFlags γU info ehist : iProp :=
  (⊤ ∖ gset_to_coPset (dom info)) ↦P[γU] false ∗
  [∗ map] i ↦ info_i ∈ info, ∃ (U : bool),
    i ↦p[γU]{1/2} U ∗
    let retired := fold_hist ehist in
    ⌜ U ↔ i ∈ retired ⌝
  .

Definition SlotInfos γV γtok γeh γe_nums slist sbvmap ehist (ge := length ehist - 1)  : iProp :=
  mono_nats_lb γe_nums ⊤ (ge - 1) ∗
  mono_nats_auth γe_nums (sids_from (length slist)) 1 ge ∗
  let reclaimable := gset_to_coPset (fold_hist (take (ge - 2) ehist)) in
  toks γtok (⊤ ∖ reclaimable) (sids_from (length slist)) ∗
  [∗ list] si ↦slot ∈ slist,
    match sbvmap !! slot with
    | Some (false, _) =>
      toks γtok (⊤ ∖ reclaimable) {[sid si]} ∗
      (⊤,{[sid si]}) ↦P2[γV]{ 1/2 } false ∗
      mono_nats_auth γe_nums {[sid si]} 1 ge
    | Some (true, None) =>
      toks γtok (⊤ ∖ reclaimable) {[sid si]} ∗
      (⊤,{[sid si]}) ↦P2[γV]{ 1/2/2 } false ∗
      mono_nats_auth γe_nums {[sid si]} 1 ge
    | Some (true, Some e) => ∃ (V : bool),
      (⊤ ∖ {[sid e]},{[sid si]}) ↦P2[γV]{ 1/2/2 } false ∗
      (sid e,sid si) ↦p2[γV]{ 1/2/2 } V ∗
      if V then ∃ ehistF,
        ⌜length ehistF = e - 1⌝ ∗
        epoch_history_finalized γeh ehistF ∗
        let finalized := gset_to_coPset (fold_hist ehistF) in
        toks γtok (finalized ∖ reclaimable) {[sid si]} ∗
        mono_nats_auth γe_nums {[sid si]} (1/2/2) e
      else
        toks γtok (⊤ ∖ reclaimable) {[sid si]} ∗
        mono_nats_auth γe_nums {[sid si]} 1 ge
    | None => False
    end.

Global Instance slot_infos_timeless γV γtok γeh γe_nums slist sbvmap ge:
  Timeless (SlotInfos γV γtok γeh γe_nums slist sbvmap ge).
Proof.
  repeat (
    intros ||
    apply bi.sep_timeless || apply bi.exist_timeless ||
    apply big_sepM_timeless || apply big_sepL_timeless ||
    apply _ || case_match
  ).
Qed.

Definition ReclaimInfo γR γtok ehist info (ge := length ehist - 1): iProp :=
  ∃ reclaimed,
  let reclaimable := gset_to_coPset (fold_hist (take (ge - 2) ehist)) in
  (gset_to_coPset reclaimed,⊤) ↦P2[γR]{ 1/2 } true ∗
  (gset_to_coPset (dom info ∖ reclaimed),⊤) ↦P2[γR]{ 1/2 } false ∗
  (⊤ ∖ gset_to_coPset (dom info),⊤) ↦P2[γR] false ∗
  toks γtok (reclaimable ∖ (gset_to_coPset reclaimed)) ⊤.

Definition BaseManaged γe (p : blk) (i_p : gname) (size_i : nat) R : iProp :=
  ∃ γsb γtok γinfo γptrs γeh γrs γU γV γR γe_nums (d : loc),
    ⌜γe = encode (γsb, γtok, γinfo, γptrs, γeh, γrs, γU, γV, γR, γe_nums, d)⌝ ∗
    ManagedBase mgmtN ptrsN γtok γinfo γptrs γU γR p i_p size_i R.

Definition BaseNodeInfo γe (p : blk) (i_p : positive) (size_i : nat) R : iProp :=
  ∃ γsb γtok γinfo γptrs γeh γrs γU γV γR γe_nums (d : loc),
    ⌜γe = encode (γsb, γtok, γinfo, γptrs, γeh, γrs, γU, γV, γR, γe_nums, d)⌝ ∗
    NodeInfoBase mgmtN ptrsN γtok γinfo γptrs p i_p size_i R.

Global Instance BaseNodeInfo_persistent γe p i_p size_p R : Persistent (BaseNodeInfo γe p i_p size_p R).
Proof. apply _. Qed.
Global Instance BaseNodeInfo_contractive γe p i_p size_p :
  Contractive (λ (R : blk -d> list val -d> gname -d> iPropO Σ), BaseNodeInfo γe p i_p size_p R).
Proof.
  intros ??? Hxy. rewrite /BaseNodeInfo /NodeInfoBase.
  repeat apply bi.exist_ne => ?. repeat apply bi.sep_ne; try done.
  repeat apply bi.exist_ne => ?. repeat apply bi.sep_ne; try done.
  apply coP_cinv_contractive, dist_later_fin_iff.
  destruct n; [done|]. simpl in *.
  repeat apply bi.exist_ne => ?. repeat apply bi.sep_ne; try done.
  apply Hxy. lia.
Qed.

Definition BaseGuardedNodeInfo γe γg (p : blk) (i_p : positive) (size_i : nat) R : iProp :=
  BaseNodeInfo γe (p : blk) (i_p : gname) (size_i : nat) R ∗ p ↪[γg]□ i_p.

Global Instance BaseGuardedNodeInfo_persistent γe γg p i_p size_p R : Persistent (BaseGuardedNodeInfo γe γg p i_p size_p R).
Proof. apply _. Qed.

(* not using [ProtectedBase], because [γV] is not necessary here. *)
Definition Protected γtok γinfo γptrs (s : nat) (i_p : positive) (p : blk) : iProp :=
  ∃ γc_i size_i,
    i_p ↪[γinfo]□ ({| addr := p; len := size_i |}, γc_i) ∗
    p ↪c[γptrs]{{[ssid s]}} i_p ∗
    coP_cinv_own γc_i {[ssid s]} ∗
    Exchanges mgmtN γtok γptrs p i_p γc_i.

Definition EBRAuth γe info_a retired : iProp :=
  ∃ info γsb γtok γinfo γptrs γeh γrs γU γV γR γe_nums (d : loc),
    ⌜γe = encode (γsb, γtok, γinfo, γptrs, γeh, γrs, γU, γV, γR, γe_nums, d)⌝ ∗
    ghost_map_auth γinfo (1/2) info ∗
    ghost_var γrs (1/2) retired ∗
    ⌜info_a = fst <$> info⌝.

Global Instance EBRAuth_timeless γe info_a retired : Timeless (EBRAuth γe info_a retired).
Proof. apply _. Qed.

Definition EBRDomain γsb γtok γinfo γptrs γeh γrs γU γV γR γe_nums (d lBag rList : loc) : iProp :=
  ∃ info ptrs sbvmap slist rL ehist,
    let retired := fold_hist ehist in
    ghost_map_auth γinfo (1/2) info ∗
    coP_ghost_map_auth γptrs 1 ptrs ∗
    epoch_history_auth γeh ehist ∗
    ghost_var γrs (1/2) retired ∗

    (* NOTE: need Invariant 2? *)
    sbs.(SlotBag) γsb lBag sbvmap slist ∗
    rls.(RetiredList) rList rL ∗

    (* NOTE: we have monotonicity of global epoch by mono_list *)
    let ge := length ehist - 1 in

    GhostEpochInformations γV γeh γe_nums ge slist sbvmap ∗
    SlotInfos γV γtok γeh γe_nums slist sbvmap ehist ∗
    UnlinkFlags γU info ehist ∗
    ⌜retired ⊆ (dom info)⌝ ∗

    ⌜ge ≥ 3⌝ ∗
    (d +ₗ domGEpoch) ↦ #ge ∗

    ([∗ map] p ↦ i ∈ ptrs, ∃ info_i,
      ⌜info !! i = Some info_i⌝ ∗
      (* Permission for freeing the pointer with this length.
      This is used for proving [rcu_domain_register]. *)
      †(blk_to_loc p)…info_i.1.(len)) ∗

    ReclaimInfo γR γtok ehist info ∗

    ([∗ list] rle ∈ rL, let '(r,len,epoch) := rle in ∃ i R unlinked_e,
      RetiredBase mgmtN ptrsN γtok γinfo γptrs γU γR r i len R ∗
      (* Invariant 1-1 *)
      epoch_history_snap γeh epoch unlinked_e ∗
      ⌜ i ∈ unlinked_e ⌝) ∗

    ⌜∀ p i, ptrs !! p = Some i → ∃ z, info !! i = Some z ∧ z.1.(addr) = p ⌝ ∗
    ⌜∀ i p, i ∉ fold_hist (take (ge - 2) ehist) → (∃ z, info !! i = Some z ∧ z.1.(addr) = p) → ptrs !! p = Some i ⌝
  .

Definition ebrInvN := (to_baseN mgmtN) .@ "inv".

Definition IsEBRDomain γe (d : loc) : iProp :=
  ∃ γsb γtok γinfo γptrs γeh γrs γU γV γR γe_nums (lBag rList : loc),
    ⌜γe = encode (γsb, γtok, γinfo, γptrs, γeh, γrs, γU, γV, γR, γe_nums, d)⌝ ∗
    (d +ₗ domLBag) ↦□ #lBag ∗
    (d +ₗ domRSet) ↦□ #rList ∗
    inv ebrInvN (EBRDomain γsb γtok γinfo γptrs γeh γrs γU γV γR γe_nums d lBag rList).

Global Instance IsEBRDomain_Persistent γe d : Persistent (IsEBRDomain γe d).
Proof. repeat (apply bi.exist_persistent; intros). apply _. Qed.

Definition BaseInactive γe (g : loc) : iProp :=
  ∃ γsb γtok γinfo γptrs γeh γrs γU γV γR γe_nums
    (d slot : loc) (idx : nat) (v : option nat),
    ⌜γe = encode (γsb, γtok, γinfo, γptrs, γeh, γrs, γU, γV, γR, γe_nums, d)⌝ ∗
    (g +ₗ guardSlot) ↦ #slot ∗
    (g +ₗ guardDom) ↦ #d ∗
    †g…guardSize ∗
    sbs.(Slot) γsb slot idx v ∗
    (* corresponds to Shield's Deactivated and NotValidated *)
    (⊤,{[sid idx]}) ↦P2[γV]{ 1/2/2 } false.

Definition BaseGuard γe γg (g : loc) Syn G : iProp :=
  ∃ γsb γtok γinfo γptrs γeh γrs γU γV γR γe_nums
    (d slot : loc) (idx : nat) (v : option nat),
    ⌜γe = encode (γsb, γtok, γinfo, γptrs, γeh, γrs, γU, γV, γR, γe_nums, d)⌝ ∗
    (g +ₗ guardSlot) ↦ #slot ∗
    (g +ₗ guardDom) ↦ #d ∗
    †g…guardSize ∗
    sbs.(Slot) γsb slot idx v ∗
    ∃ e ehistF,
      ⌜v = Some e⌝ ∗
      mono_nats_auth γe_nums {[sid idx]} (1/2/2) e ∗

      (sid e,sid idx) ↦p2[γV]{ 1/2/2 } true ∗
      (⊤∖{[sid e]},{[sid idx]}) ↦P2[γV]{ 1/2/2 } false ∗
      epoch_history_frag γeh e {[sid idx]} ∗

      let finalized := fold_hist ehistF in

      ghost_map_auth γg 1 G ∗
      ⌜Syn = finalized ∧ length ehistF = e - 1⌝ ∗
      epoch_history_finalized γeh ehistF ∗
      toks γtok ((⊤ ∖ (gset_to_coPset finalized)) ∖ (gset_to_coPset (range G))) {[sid idx]} ∗
      ⌜(range G) ## finalized⌝ ∗
      [∗ map] p ↦ i_p ∈ G,
        p ↪[γg]□ i_p ∗
        Protected γtok γinfo γptrs idx i_p p
  .

(** Helper Lemmas  *)

Lemma do_unprotect E γtok γinfo γptrs γg idx G :
  ↑(to_baseN mgmtN) ⊆ E →
  ( [∗ map] p ↦ i_p ∈ G, p ↪[γg]□ i_p ∗ Protected γtok γinfo γptrs idx i_p p)
  ={E}=∗
    toks γtok (gset_to_coPset (range G)) {[sid idx]}.
Proof.
  iIntros (?) "Prot".
  iInduction (G) as [|p i_p G FRESH_l] "IH" using map_ind.
  { rewrite range_empty gset_to_coPset_empty. iApply token2_get_empty_1. }

  iDestruct (big_sepM_delete _ _ p  with "Prot") as "[[#p P] Prot]"; [apply lookup_insert|simpl].
  iDestruct "P" as (??) "(#i↪ & pc & cinv & #Ex)".
  iMod (exchange_stok_get with "Ex pc cinv") as "T"; [solve_ndisj|].

  rewrite delete_insert; auto.
  iMod ("IH" with "Prot") as "T'". iClear "IH".
  rewrite range_insert // gset_to_coPset_union gset_to_coPset_singleton.
  iModIntro.
  iDestruct (toks_valid_1 with "T T'") as %Di; first set_solver.
  rewrite -toks_union_1 //. iFrame.
Qed.

(** UnlinkFlags Lemmas  *)

Lemma UnlinkFlags_alloc :
  ⊢ |==> ∃ γU, UnlinkFlags γU ∅ [∅; ∅; ∅; ∅].
Proof.
  iMod (ghost_vars_top_alloc false) as (γU) "U⊤".
  iModIntro. iExists γU. unfold UnlinkFlags.
  rewrite dom_empty_L gset_to_coPset_empty difference_empty_L. iFrame.
  by iApply big_sepM_empty.
Qed.

Lemma UnlinkFlags_lookup i info γU q (U : bool) ehist :
  i ∈ dom info →
  i ↦p[γU]{q} U -∗ UnlinkFlags γU info ehist -∗
  let retired := fold_hist ehist in
  ⌜ U ↔ i ∈ retired ⌝.
Proof.
  intros [? ElemOf]%elem_of_dom. iIntros "γU_i [_ γU]".
  rewrite big_sepM_delete; last done.
  iDestruct "γU" as "[[% [γU %]] _]".
  by iDestruct (ghost_vars_agree with "γU_i γU") as %<-; [set_solver|].
Qed.

Lemma UnlinkFlags_lookup_false i info γU q ehist :
  i ∈ dom info →
  i ↦p[γU]{q} false -∗ UnlinkFlags γU info ehist -∗
  let retired := fold_hist ehist in
  ⌜ i ∉ retired ⌝.
Proof.
  iIntros (ElemOf) "γU_i γU".
  iDestruct (UnlinkFlags_lookup with "γU_i γU") as %Hi; [done|].
  destruct Hi as [_ Hi]. auto.
Qed.

Lemma UnlinkFlags_lookup_true i info γU q ehist :
  i ∈ dom info →
  i ↦p[γU]{q} true -∗ UnlinkFlags γU info ehist -∗
  let retired := fold_hist ehist in
  ⌜ i ∈ retired ⌝.
Proof.
  iIntros (ElemOf) "γU_i γU".
  iDestruct (UnlinkFlags_lookup with "γU_i γU") as %Hi; [done|].
  destruct Hi as [Hi _]. auto.
Qed.

Lemma UnlinkFlags_update_in γU γc_i info ehist i p k :
  is_Some (info !! i) →
  UnlinkFlags γU info ehist -∗
  UnlinkFlags γU (<[i:=({| addr := p; len := k |}, γc_i)]> info) ehist.
Proof.
  iIntros ([x Hi]) "[U UF]".
  unfold UnlinkFlags. rewrite dom_insert_L.
  rewrite subseteq_union_1_L; last first.
  { apply singleton_subseteq_l. by rewrite elem_of_dom. }
  iFrame.
  iDestruct (big_sepM_delete with "UF") as "[U UF]"; eauto.
  iApply (big_sepM_delete _ _ i); first by rewrite lookup_insert.
  rewrite delete_insert_delete. iFrame.
Qed.

Lemma UnlinkFlags_update_notin γU γc_i info ehist i p k :
  info !! i = None →
  i ∉ fold_hist ehist →
  UnlinkFlags γU info ehist -∗
  UnlinkFlags γU (<[i:=({| addr := p; len := k |}, γc_i)]> info) ehist ∗
  i ↦p[γU]{1/2} false.
Proof.
  iIntros (Hi Hfe) "[U_rest U_info]".
  unfold UnlinkFlags. rewrite dom_insert_L.
  rewrite (union_difference_singleton_L i (⊤ ∖ gset_to_coPset (dom info))); last first.
  { apply elem_of_complement. by rewrite not_elem_of_gset_to_coPset elem_of_dom Hi. }
  rewrite -ghost_vars_union; last set_solver.
  iDestruct "U_rest" as "[[Ui $] U_rest]".
  rewrite !difference_difference_l_L union_comm_L -!gset_to_coPset_singleton -gset_to_coPset_union.
  iFrame.
  iApply big_sepM_insert; [done|]. iFrame.
  iExists false. rewrite gset_to_coPset_singleton. iFrame. auto.
Qed.

(** GhostEpochInformation Lemmas *)

Lemma ghost_slot_unlink_reclaim_alloc :
  ⊢ |==> ∃ γeh γtok γR γV γe_nums,
  epoch_history_auth γeh [∅; ∅; ∅; ∅] ∗
  GhostEpochInformations γV γeh γe_nums 3 [] ∅ ∗
  SlotInfos γV γtok γeh γe_nums [] ∅ [∅; ∅; ∅; ∅] ∗
  ReclaimInfo γR γtok [∅; ∅; ∅; ∅] ∅.
Proof.
  iMod epoch_history_alloc as (γeh) "(ehist & ◯eh1 & ◯eh2 & ◯eh3 & ◯eh4)".

  iMod (ghost_vars2_top_alloc false) as (γV) "●V".
  iEval (rewrite -{1}(sids_to_sids_from_union 2)) in "●V".
    rewrite -ghost_vars2_union_1; last apply sids_to_sids_from_disjoint.
    iDestruct "●V" as "[●Vt2T ●Vf2T]".
  rewrite sids_from_S; auto.
    rewrite -ghost_vars2_union_1; last apply sids_from_sid_disjoint; auto.
    iDestruct "●Vf2T" as "[●Vf3T ●V2T]".
  rewrite sids_from_S; auto.
    rewrite -ghost_vars2_union_1; last apply sids_from_sid_disjoint; auto.
    iDestruct "●Vf3T" as "[●Vf4T ●V3T]".

  iMod (ghost_vars2_top_alloc false) as (γR) "●R".
  iMod (mono_nats_own_alloc 2) as (γe_nums) "[●L ◯L]".
  iMod (mono_nats_auth_update 3 with "●L") as "[●L ◯L']"; auto.
  iMod (token2_alloc ⊤ ⊤) as (γtok) "T".

  (* iModIntro. *)
  iExists γeh, γtok, γR, γV, γe_nums. iFrame. unfold GE_minus, ReclaimInfo.
  rewrite !big_sepL_nil !sids_to_0 !sids_from_0 !sids_from'_0 !dom_empty_L gset_to_coPset_empty !difference_empty_L.
  iFrame.
  do 2 (iMod ghost_vars2_get_empty_2 as "$").
  iExists ∅. rewrite gset_to_coPset_empty !difference_empty_L.
  do 2 (iMod ghost_vars2_get_empty_1 as "$").
  iApply token2_get_empty_1.
Qed.

Lemma ghost_epoch_informations_new_slot slot γV γeh γe_nums ge slist sbvmap
  (idx := length slist) :
  (3 ≤ ge) →
  sbvmap !! slot = None →
  GhostEpochInformations γV γeh γe_nums ge slist sbvmap -∗
  GhostEpochInformations γV γeh γe_nums ge (slist ++ [slot]) (<[slot:=(true, None)]> sbvmap) ∗
  (⊤,{[sid idx]}) ↦P2[γV]{ 1/2 } false.
Proof.
  iIntros (LE3 Fresh) "EInfo".
  iDestruct "EInfo" as "(GE_2_et_al & GE_1 & GE_0 & #slist & γV_to & γV_from)".
  unfold GhostEpochInformations.
  rewrite !app_length !Nat.add_1_r.
  iEval (rewrite (sids_from_S (length slist))) in "γV_from".
  iEval (rewrite -(sids_to_sids_from_union (S ge))).
  rewrite -ghost_vars2_union_2; [|apply sids_from_sid_disjoint; lia].
  rewrite -ghost_vars2_union_1; [|apply sids_to_sids_from_disjoint].
  iDestruct "γV_from" as "[$ [γV_from $]]".
  iEval (rewrite sids_to_S).
  rewrite -ghost_vars2_union_2; [|apply sids_to_sid_disjoint;lia].
  iFrame.
  iAssert (GE_minus_2_et_al γV γeh ge (slist ++ [slot])
    ∗ (sids_to (ge -1),{[sid idx]}) ↦P2[γV]{ 1/2 } false)%I
    with "[GE_2_et_al]" as "[$ γV_2_et_al]".
  { iDestruct "GE_2_et_al" as "(γV_from & γV_to & $)".
    rewrite !app_length !Nat.add_1_r !(sids_from_S (length slist)).
    rewrite -ghost_vars2_union_2; [|apply sids_from_sid_disjoint; lia].
    iDestruct "γV_from" as "[$ [γV $]]".
    iCombine "γV_to γV" as "γV_to".
    rewrite ghost_vars2_union_2; [|apply sids_to_sid_disjoint; lia].
    rewrite sids_to_S. iFrame.
  }
  iAssert(∀ e,
    GE_minus γV γeh γe_nums e slist sbvmap -∗
    GE_minus γV γeh γe_nums e (slist ++ [slot]) (<[slot:=(true, None)]> sbvmap)
    ∗ (sid e,sid idx) ↦p2[γV]{ 1/2 } false)%I
    as "GE_update".
  { iIntros (e) "GE_minus". unfold GE_minus.
    iDestruct "GE_minus" as "(γV & ◯ehist & slist_info)".
    rewrite app_length Nat.add_1_r (sids_from_S (length slist)).
    rewrite -ghost_vars2_union_2; [|apply sids_from_sid_disjoint; lia].
    iDestruct "γV" as "[$ [γV $]]".
    rewrite (sids_from'_S (length slist)).
    rewrite -epoch_history_frag_union; [|apply sids_from'_sid_disjoint; lia].
    iDestruct "◯ehist" as "[$ ◯ehist]".
    rewrite big_sepL_snoc. iSplitL "slist_info".
    - iApply (big_sepL_mono with "slist_info").
      iIntros (si' slot' Hsi') "slot'".
      iDestruct "slot'" as (b v V) "(% & ? & ? & ?)".
      iExists b,v,V. iFrame. iPureIntro.
      rewrite lookup_insert_ne; [done|intros <-; congruence].
    - iExists true,None,false. iFrame. iPureIntro.
      split; [by simplify_map_eq|inversion 1].
  }
  iDestruct ("GE_update" with "GE_1") as "[$ γV_1]".
  iDestruct ("GE_update" with "GE_0") as "[$ γV_0]".
  iCombine "γV_2_et_al γV_1" as "γV".
  iEval (rewrite ghost_vars2_union_1; [|apply sids_to_sid_disjoint; lia]) in "γV".
  rewrite -sids_to_S. assert (S (ge -1) = ge) as -> by lia.
  iCombine "γV γV_0" as "γV".
  iEval (rewrite ghost_vars2_union_1; [|apply sids_to_sid_disjoint; lia]) in "γV".
  rewrite -sids_to_S. iFrame.
  rewrite big_sepL_snoc. iSplit.
  - iApply (big_sepL_mono with "slist").
    iIntros (si slot' Hsi) "%Hslot'".
    destruct Hslot' as (b & v & Hslot'). iExists b,v. iPureIntro.
    rewrite lookup_insert_ne; [done|intros <-; congruence].
  - iExists true,None. iPureIntro. by simplify_map_eq.
Qed.

Lemma ghost_epoch_informations_set idx slot v b v' b' γeh γtok γV γe_nums ge slist sbvmap :
  NoDup slist →
  slist !! idx = Some slot →
  sbvmap !! slot = Some (b',v') →
  GhostEpochInformations γV γeh γe_nums ge slist sbvmap -∗
  (⊤,{[sid idx]}) ↦P2[γV]{ 1/2/2 } false -∗
  GhostEpochInformations γV γeh γe_nums ge slist (<[slot:=(b,v)]> sbvmap) ∗
  (⊤,{[sid idx]}) ↦P2[γV]{ 1/2/2 } false.
Proof.
  iIntros (ND Hidx Hslot) "GEI ●VTI".
    iDestruct "GEI" as "(GE2 & GE1 & GE0 & #sbvmap & γV_to & γV_from)".

  iAssert (∀ e,
    (⊤,{[sid idx]}) ↦P2[γV]{ 1/2/2 } false -∗
    GE_minus γV γeh γe_nums e slist sbvmap -∗
    (⊤,{[sid idx]}) ↦P2[γV]{ 1/2/2 } false ∗
    GE_minus γV γeh γe_nums e slist (<[slot:=(b, v)]> sbvmap)
  )%I as "GEupd".
  { iIntros (e) "●VTI GE".
      iDestruct "GE" as "(●V1E & ◯H1E & GE1)".
    iDestruct (big_sepL_delete with "GE1") as "[Gi GE1]"; eauto.
      iDestruct "Gi" as (bi vi Vi) "(%Hi' & ●V1I & %HV & Ho)".
      rewrite Hslot in Hi'. injection Hi' as [= <- <-].
    iDestruct (ghost_vars2_agree with "●VTI ●V1I") as %<-; [set_solver..|].
    iFrame.

    iApply big_sepL_delete; eauto.
    iSplitL "●V1I Ho".
    { iExists b,v,false. iFrame. iPureIntro.
      split; [by rewrite lookup_insert|inversion 1]. }
    iApply (big_sepL_mono with "GE1"); last auto.
    iIntros (i l Hi) "GEi".
    case_decide as EQi; auto.
    iDestruct "GEi" as (bi vi Vi) "(%Hl & ●Vi & %HVi & Ho)".
    repeat iExists _. iFrame. iPureIntro. split; [|done].
    rewrite lookup_insert_ne; auto. intros ->.
    eapply EQi, NoDup_lookup; eauto. }

  iDestruct ("GEupd" with "●VTI GE1") as "[●VTI GE1]".
  iDestruct ("GEupd" with "●VTI GE0") as "[●VTI GE0]".
  iFrame.
  iApply (big_sepL_mono with "sbvmap"); last auto.
  iIntros (si' slot') "%Hslist %Hsi'".
  destruct (decide (slot' = slot)) as [->|NE].
  - repeat iExists _. iPureIntro. by simplify_map_eq.
  - destruct Hsi' as (? & ? & ?). iExists _,_. iPureIntro.
    rewrite lookup_insert_ne; [by simplify_map_eq|done].
Qed.

Lemma ghost_epoch_informations_slot_infos_activate idx slot γeh γtok γV γe_nums slist sbvmap ehist
  ehistF (finalized := gset_to_coPset (fold_hist ehistF)) (ge := length ehist - 1) :
  3 ≤ ge →
  NoDup slist →
  slist !! idx = Some slot →
  length ehistF = ge - 1 →
  sbvmap !! slot = Some (true, Some ge) →
  ehistF `prefix_of` (take (length ehist - 2) ehist) →

  GhostEpochInformations γV γeh γe_nums ge slist sbvmap -∗
  SlotInfos γV γtok γeh γe_nums slist sbvmap ehist -∗
  (⊤,{[sid idx]}) ↦P2[γV]{ 1/2/2 } false -∗
  epoch_history_finalized γeh ehistF
  ==∗
  GhostEpochInformations γV γeh γe_nums ge slist sbvmap ∗
  SlotInfos γV γtok γeh γe_nums slist sbvmap ehist ∗
  (⊤ ∖ {[sid ge]},{[sid idx]}) ↦P2[γV]{ 1/2/2 } false ∗
  (sid ge,sid idx) ↦p2[γV]{ 1/2/2 } true ∗
  epoch_history_frag γeh ge {[sid idx]} ∗
  (* (1/2) for GEI. (1/2/2) for SlotInfos. This is for Guard *)
  mono_nats_auth γe_nums {[sid idx]} (1/2/2) ge ∗
  toks γtok (⊤ ∖ finalized) {[sid idx]}.
Proof.
  iIntros (LE_ge ND Hidx HlenF Hslot PF) "GEI SI ●VTI Fin".
    iDestruct "GEI" as "(GE2 & GE1 & GE0 & #sbvmap & γV_to & γV_from)".
    iDestruct "GE0" as "(●V0E & ◯H0E & GE0)".
    iDestruct "SI" as "(◯LT & ●LE & TTE & SI)".
  iDestruct (big_sepL_delete with "GE0") as "[Gi GE0]"; eauto.
    iDestruct "Gi" as (bi vi Vi) "(%Hsl' & ●V0I & _ & T)".
    rewrite Hslot in Hsl'. injection Hsl' as [= <- <-].
  iDestruct (big_sepL_delete with "SI") as "[Si SI]"; eauto.
    rewrite Hslot.
    iDestruct "Si" as (Vi') "(●VTxI & ●V0I' & T')".
  set reclaimable := fold_hist (take (ge-2) ehist).

  (* update ghost *)
  iDestruct (ghost_vars2_agree with "●VTI ●V0I") as %<-; [set_solver..|].
  iDestruct (ghost_vars2_agree with "●V0I ●V0I'") as %<-; [set_solver..|].
  iEval (rewrite (top_union_difference {[sid ge]})) in "●VTI".
  rewrite -ghost_vars2_union_1; last set_solver.
  iDestruct "●VTI" as "[●VTxI' ●V0I'']".
  iCombine "●V0I' ●V0I''" as "●V0I'".
  iRename "T" into "H0I".
  iDestruct "T'" as "[TTI ●LI]".
  iMod (ghost_vars2_update_halves' true with "●V0I ●V0I'") as "[●V0I ●V0I']".

  (* redistribute *)
  iDestruct "●V0I'" as "[●V0I' ●V0I'']".
  iDestruct "●LI" as "[●LI [●LI' ●LI'']]".

  assert ((fold_hist ehistF ∖ reclaimable) ## reclaimable).
  { apply disjoint_difference_l1. set_solver. }
  iEval (rewrite (gset_to_coPset_top_difference reclaimable (fold_hist ehistF ∖ reclaimable)); last done) in "TTI".
  rewrite -toks_union_1; last first.
  { apply gset_to_coPset_top_disjoint. }
  iDestruct "TTI" as "[TEI TFI]".

  (* close *)
  iModIntro. iFrame.
  iSplitL "GE0 ●V0I ●LI".
  { iFrame "∗#%". iApply big_sepL_delete; eauto. iFrame.
    repeat (iExists _). iSplit; auto with iFrame. }
  iSplitR "TEI"; last first.
  { rewrite -union_comm_L -union_difference_L; first done.
    apply prefix_cut in PF. rewrite drop_ge in PF; last first.
    { rewrite take_length. lia. }
    rewrite app_nil_r in PF. rewrite -PF.
    apply fold_hist_prefix, take_prefix_le. lia.
  }
  iApply big_sepL_delete; eauto. iFrame.
  rewrite Hslot. iExists _. iFrame. iExists ehistF. unfold reclaimable, ge.
  rewrite gset_to_coPset_difference. iFrame. eauto.
Qed.

Lemma ghost_epoch_informations_slot_infos_deactivate
    idx slot γeh γtok γV γR γe_nums slist sbvmap ehist ehistF e
    (finalized := gset_to_coPset (fold_hist ehistF))
    (ge := length ehist - 1) :
  e ≤ ge →
  NoDup slist →
  slist !! idx = Some slot →
  length ehistF = e - 1 →
  sbvmap !! slot = Some (true, Some e) →
  ehistF `prefix_of` ehist →

  GhostEpochInformations γV γeh γe_nums ge slist sbvmap -∗
  SlotInfos γV γtok γeh γe_nums slist sbvmap ehist -∗
  (⊤ ∖ {[sid e]},{[sid idx]}) ↦P2[γV]{ 1/2/2 } false -∗
  (sid e,sid idx) ↦p2[γV]{ 1/2/2 } true -∗
  epoch_history_frag γeh e {[sid idx]} -∗
  (* (1/2) for GEI. (1/2/2) for SlotInfos. This is for Guard *)
  mono_nats_auth γe_nums {[sid idx]} (1/2/2) e -∗
  toks γtok (⊤ ∖ finalized) {[sid idx]} -∗
  epoch_history_finalized γeh ehistF
  ==∗
  GhostEpochInformations γV γeh γe_nums ge slist sbvmap ∗
  SlotInfos γV γtok γeh γe_nums slist sbvmap ehist ∗
  (⊤,{[sid idx]}) ↦P2[γV]{ 1/2/2 } false
.
Proof.
  iIntros (Hle ND Hidx HlenF Hslot Hpref)
    "GEI SI ●VTxI ●V0I F ●MI TTxI #Fin".
    iDestruct "GEI" as "(GE2 & GE1 & GE0 & #sbvmap & GEI_REST)".
  iDestruct "SI" as "(#◯MT & ●ME & TTE & SI)".
  iDestruct (mono_nats_auth_lb_valid with "●MI ◯MT") as %Hge; first set_solver.
  iDestruct (big_sepL_delete with "SI") as "[Si SI]"; eauto.
    rewrite Hslot.
    iDestruct "Si" as (Vi') "(●VTxI' & ●V0I' & T')".
    iCombine "●ME TTE ●VTxI' SI" as "SI_REST".

  (* update ghost *)
  (* we need γV {[sid e]} {[sid idx]} 1.
    1/4 is from ●V0I
    1/4 is from ●V0I'
    1/2 is from GE1 or GE0, whichever matches e
  *)
  iDestruct (ghost_vars2_agree with "●V0I ●V0I'") as %<-; try set_solver.
  iCombine "●V0I ●V0I'" as "●V0I".
  remember ((ge-1)+ge-e) as e'.
  assert ((e = ge-1 ∧ e' = ge) ∨ (e = ge ∧ e' = ge-1)) as He by lia.
  iAssert (
    GE_minus γV γeh γe_nums e slist sbvmap ∗
    GE_minus γV γeh γe_nums e' slist sbvmap
  )%I with "[GE1 GE0]" as "[GEe GEe']".
  { destruct He as [[He He']|[He He']]. all: rewrite He He'; iFrame. }

  iDestruct "GEe" as "(●VEI & FeE & GEe)".
  iDestruct (big_sepL_delete with "GEe") as "[Gi GEe]"; eauto.
    iDestruct "Gi" as (bi vi Vi) "(%Hslot' & ●V0I' & %HVi & ●MI')".
    rewrite Hslot in Hslot'. injection Hslot' as [= <- <-].
  iDestruct (ghost_vars2_agree with "●V0I ●V0I'") as %<-; [set_solver..|].
  iMod (ghost_vars2_update_halves' false with "●V0I ●V0I'") as "[●V0I ●V0I']".

  (* update mono nats *)
  iDestruct "T'" as (ehistF') "(%HlenF' & #Fin' & TEEI & ●MI'')".
    iDestruct (epoch_finalized_agree with "Fin Fin'") as %<-.
    { by rewrite HlenF HlenF'. }
  iCombine "●MI' ●MI ●MI''" as "●MI".
  iMod (mono_nats_auth_update ge with "●MI") as "[●MI #◯MI+]"; first lia.

  (* redistribute *)
  iDestruct "●V0I'" as "[●V0I' ●V0I'']".
    iCombine "●VTxI ●V0I''" as "●VTI".
    rewrite ghost_vars2_union_1; last set_solver.
    rewrite -top_union_difference.
  iAssert (
    GE_minus γV γeh γe_nums ge slist sbvmap ∗
    GE_minus γV γeh γe_nums (ge-1) slist sbvmap
  )%I with "[GEe' ●VEI FeE ●V0I GEe F]" as "[GEe GEe']".
  { destruct He as [[He He']|[He He']]. all: rewrite He He'; iFrame.
    all: iApply big_sepL_delete; eauto. all: iFrame.
    all: repeat iExists _; iFrame. all: iSplit; auto.
  }
  iDestruct "SI_REST" as "(●ME & TTE & ●VTxI' & SI)".
  iCombine "TTxI TEEI" as "TEI".
    rewrite toks_union_1; last set_solver.

  (* close *)
  iModIntro. iFrame. fold ge. repeat iSplit; auto.
  iApply big_sepL_delete; eauto. iFrame.
  rewrite Hslot. iExists _. iFrame. iFrame.

  rewrite difference_difference_r; [|set_solver|done]. unfold finalized.
  rewrite -!gset_to_coPset_difference difference_diag_single; [done|].
  apply prefix_cut in Hpref. rewrite Hpref.
  apply fold_hist_prefix, take_app_prefix. lia.
Qed.

(** SlotInfos Lemmas *)

Lemma slot_infos_new_slot slot γV γtok γeh γe_nums slist sbvmap ge (idx := length slist) :
  sbvmap !! slot = None →
  SlotInfos γV γtok γeh γe_nums slist sbvmap ge -∗
  (⊤,{[sid idx]}) ↦P2[γV]{ 1/2 } false -∗
  SlotInfos γV γtok γeh γe_nums (slist ++ [slot]) (<[slot:=(true,None)]> sbvmap) ge ∗
  (⊤,{[sid idx]}) ↦P2[γV]{ 1/2/2 } false.
Proof.
  iIntros (Fresh) "SInfo [$ γV]".
  iDestruct "SInfo" as "($ & ●γe_nums & ●toks & SInfo)".
  rewrite (sids_from_S (length slist)) app_length Nat.add_1_r.
  rewrite mono_nats_auth_union; [|apply sids_from_sid_disjoint; lia].
  rewrite -toks_union_2; [|apply sids_from_sid_disjoint; lia].
  iDestruct "●γe_nums" as "[$ ●γe_num]".
  iDestruct "●toks" as "[$ ●tok]".
  rewrite big_sepL_snoc. iSplitL "SInfo".
  - iApply (big_sepL_mono with "SInfo"). iIntros (si slot' Hsi) "slot'".
    destruct (sbvmap !! slot') as [e|] eqn:Hslot'; [|done].
    rewrite lookup_insert_ne; [|intros ->; congruence].
    rewrite Hslot'. iFrame.
  - rewrite lookup_insert. iFrame.
Qed.

Lemma slot_infos_reactivate_slot slot γV γtok γeh γe_nums slist sbvmap si ge v':
  NoDup slist →
  slist !! si = Some slot →
  sbvmap !! slot = Some (false, v') →
  SlotInfos γV γtok γeh γe_nums slist sbvmap ge -∗
  SlotInfos γV γtok γeh γe_nums slist (<[slot:= (true,None)]> sbvmap) ge ∗
  (⊤,{[sid si]}) ↦P2[γV]{ 1/2/2 } false.
Proof.
  iIntros (NoDup Hsi Hslot) "SInfo".
  iDestruct "SInfo" as "($ & $ & $ & SInfo)".
  iInduction slist as [|slot' slist] "IH" using rev_ind; [done|].
  rewrite !big_sepL_snoc. iDestruct "SInfo" as "[SInfo slot']".
  destruct (decide (slot' = slot)) as [->|NE].
  { iClear "IH". rewrite -assoc. iSplitL "SInfo".
    - iApply (big_sepL_mono with "SInfo"). iIntros (si' slot' Hsi') "slot'".
      rewrite lookup_insert_ne; [iFrame|].
      intros <-. rewrite -NoDup_snoc in NoDup.
      destruct NoDup as [NoDup NotIn]. apply NotIn.
      rewrite elem_of_list_lookup. eauto.
    - simplify_map_eq. assert (si = length slist) as ->.
      { eapply NoDup_lookup; [done..|]. apply snoc_lookup. }
      iDestruct "slot'" as "($ & [$ $] & $)".
  }
  rewrite -NoDup_snoc in NoDup.
  destruct NoDup as [NoDup NotIn].
  assert (si < length slist) as LE.
  { rewrite Nat.lt_nge. intro le. apply NE.
    assert (si = length slist) as ->.
    { apply lookup_lt_Some in Hsi. rewrite app_length Nat.add_1_r in Hsi. lia. }
    rewrite snoc_lookup in Hsi. by injection Hsi. }
  rewrite lookup_app_l in Hsi; [|done].
  iSpecialize ("IH" with "[] [] [SInfo]"); [done..|].
  iDestruct "IH" as "[$ $]".
  rewrite lookup_insert_ne; [|done].
  iFrame.
Qed.

(* Change the slot [si] to "NotValidated" state. *)
Lemma slot_infos_set v γV γtok γeh γe_nums slist sbvmap si slot ehist (ge := length ehist - 1) v' :
  NoDup slist →
  slist !! si = Some slot →
  sbvmap !! slot = Some (true, v') →
  SlotInfos γV γtok γeh γe_nums slist sbvmap ehist -∗
  (⊤,{[sid si]}) ↦P2[γV]{ 1/2/2 } false -∗
  SlotInfos γV γtok γeh γe_nums slist (<[slot:=(true, v)]> sbvmap) ehist ∗
  (⊤,{[sid si]}) ↦P2[γV]{ 1/2/2 } false.
Proof.
  iIntros (ND Hi Hsl) "SI ●VTI".
    iDestruct "SI" as "(◯MT & ●ME & TTE & SI)".
  iDestruct (big_sepL_delete with "SI") as "[Si SI]"; eauto. rewrite Hsl.
  set reclaimable := gset_to_coPset (fold_hist (take (ge-2) ehist)).
  iAssert (
    toks γtok (⊤ ∖ reclaimable) {[sid si]} ∗
    (⊤,{[sid si]}) ↦P2[γV]{ 1/2/2 } false ∗
    (⊤,{[sid si]}) ↦P2[γV]{ 1/2/2 } false ∗
    mono_nats_auth γe_nums {[sid si]} 1 ge
  )%I with "[Si ●VTI]" as "(TTI & ●VTI & ●VTI' & ●MI)".
  { destruct v'; last iFrame.
    iDestruct "Si" as (Vi) "(●VTxI & ●VNI & Ho)".
    iDestruct (ghost_vars2_agree with "●VTI ●VNI") as %<-; try set_solver.
    iCombine "●VTxI ●VNI" as "●VTI'".
    rewrite ghost_vars2_union_1; last set_solver.
    rewrite -top_union_difference. iFrame. }

  destruct v; iFrame.
  - iApply big_sepL_delete; eauto. rewrite lookup_insert.
    iSplitL "●VTI TTI ●MI".
    { iExists false. iFrame.
      rewrite ghost_vars2_union_1; last set_solver.
      by rewrite -top_union_difference. }
    iApply big_sepL_mono; last auto.
    iIntros (i p Hp) "SI". case_decide as Eqn; auto.
    rewrite lookup_insert_ne; auto.
    intro; subst. eapply Eqn, NoDup_lookup; eauto.
  - iApply big_sepL_delete; eauto. rewrite lookup_insert. iFrame.
    iApply big_sepL_mono; last auto.
    iIntros (i p Hp) "SI". case_decide as Eqn; auto.
    rewrite lookup_insert_ne; auto.
    intro; subst. eapply Eqn, NoDup_lookup; eauto.
Qed.

Lemma slot_infos_unset v γV γtok γeh γe_nums slist sbvmap si slot ehist (ge := length ehist - 1) v' :
  NoDup slist →
  slist !! si = Some slot →
  sbvmap !! slot = Some (true, v') →
  SlotInfos γV γtok γeh γe_nums slist sbvmap ehist -∗
  (⊤,{[sid si]}) ↦P2[γV]{ 1/2/2 } false -∗
  SlotInfos γV γtok γeh γe_nums slist (<[slot:=(false, v)]> sbvmap) ehist.
Proof.
  iIntros (ND Hi Hsl) "SI ●VTI".
    iDestruct "SI" as "(◯MT & ●ME & TTE & SI)".
  iDestruct (big_sepL_delete with "SI") as "[Si SI]"; eauto. rewrite Hsl.
  set reclaimable := gset_to_coPset (fold_hist (take (ge-2) ehist)).
  iAssert (
    toks γtok (⊤ ∖ reclaimable) {[sid si]} ∗
    (⊤,{[sid si]}) ↦P2[γV]{ 1/2/2 } false ∗
    (⊤,{[sid si]}) ↦P2[γV]{ 1/2/2 } false ∗
    mono_nats_auth γe_nums {[sid si]} 1 ge
  )%I with "[Si ●VTI]" as "(TTI & ●VTI & ●VTI' & ●MI)".
  { destruct v'; last iFrame.
    iDestruct "Si" as (Vi) "(●VTxI & ●VNI & Ho)".
    iDestruct (ghost_vars2_agree with "●VTI ●VNI") as %<-; try set_solver.
    iCombine "●VTxI ●VNI" as "●VTI'".
    rewrite ghost_vars2_union_1; last set_solver.
    rewrite -top_union_difference. iFrame. }
  iCombine "●VTI ●VTI'" as "●VTI". iFrame.

  iApply big_sepL_delete; eauto. rewrite lookup_insert. iFrame.
  iApply big_sepL_mono; last auto.
  iIntros (i p Hp) "SI". case_decide as Eqn; auto.
  rewrite lookup_insert_ne; auto.
  intro; subst. eapply Eqn, NoDup_lookup; eauto.
Qed.

Lemma slot_infos_retire γV γtok γeh γe_nums slist sbvmap ehist i (ge := length ehist - 1) e:
  ge - 1 ≤ e →
  SlotInfos γV γtok γeh γe_nums slist sbvmap ehist -∗
  SlotInfos γV γtok γeh γe_nums slist sbvmap (alter (union {[i]}) e ehist).
Proof.
  iIntros (e_GE_ge) "SInfo".
  iDestruct "SInfo" as "(●γe_nums & ◯γe_nusm & toks & SInfo)".
  set reclaimable := gset_to_coPset (fold_hist (take (ge - 2) ehist)).
  unfold SlotInfos.
  rewrite alter_length.
  set reclaimable' := gset_to_coPset (fold_hist (take (ge - 2) (alter (union {[i]}) e ehist))).
  assert (reclaimable' = reclaimable) as ->; last iFrame.
  unfold reclaimable, reclaimable'. f_equal.
  rewrite take_alter; [done|lia].
Qed.

Lemma slot_infos_get_inactive_lb slot γV γtok γeh γe_nums slist sbvmap ehist (ge := length ehist - 1) si v:
  slist !! si = Some slot →
  sbvmap !! slot = Some (false, v) →
  SlotInfos γV γtok γeh γe_nums slist sbvmap ehist -∗
  mono_nats_lb γe_nums {[sid si]} ge.
Proof.
  iIntros (Hsi HSlot).
  iDestruct 1 as "(_ & _ & _ & SInfo)".
  rewrite (big_sepL_delete); last done.
  iDestruct "SInfo" as "[slot _]".
  rewrite HSlot. iDestruct "slot" as "(_ & _ & ●γe_nums)".
  iDestruct (mono_nats_lb_get with "●γe_nums") as "$".
Qed.

Lemma slot_infos_get_not_validated_lb slot γV γtok γeh γe_nums slist sbvmap ehist (ge := length ehist - 1) si b:
  slist !! si = Some slot →
  sbvmap !! slot = Some (b, None) →
  SlotInfos γV γtok γeh γe_nums slist sbvmap ehist -∗
  mono_nats_lb γe_nums {[sid si]} ge.
Proof.
  iIntros (Hsi HSlot).
  iDestruct 1 as "(_ & _ & _ & SInfo)".
  rewrite (big_sepL_delete); last done.
  iDestruct "SInfo" as "[slot _]".
  rewrite HSlot. destruct b.
  all: iDestruct "slot" as "(_ & _ & ●γe_nums)".
  all: iDestruct (mono_nats_lb_get with "●γe_nums") as "$".
Qed.

Lemma slot_infos_get_possibly_validated_lb slot γV γtok γeh γe_nums slist sbvmap ehist (ge := length ehist - 1) si b e:
  e ≤ ge →
  slist !! si = Some slot →
  sbvmap !! slot = Some (b, Some e) →
  SlotInfos γV γtok γeh γe_nums slist sbvmap ehist -∗
  mono_nats_lb γe_nums {[sid si]} e.
Proof.
  iIntros (LE Hsi HSlot).
  iDestruct 1 as "(_ & _ & _ & SInfo)".
  rewrite (big_sepL_delete); last done.
  iDestruct "SInfo" as "[slot _]".
  rewrite HSlot. destruct b; last first.
  { iDestruct "slot" as "(_ & _ & ●γe_nums)".
    iDestruct (mono_nats_lb_get with "●γe_nums") as "◯γe_nums".
    iDestruct ((mono_nats_lb_le e) with "◯γe_nums") as "$"; done.
  }
  iDestruct "slot" as (V) "(_ & _ & slot)".
  destruct V; last first.
  { iDestruct "slot" as "[_ ●γe_nums]".
    iDestruct (mono_nats_lb_get with "●γe_nums") as "◯γe_nums".
    iDestruct ((mono_nats_lb_le e) with "◯γe_nums") as "$"; done.
  }
  iDestruct "slot" as (?) "(_ & _ & _ & ●γe_nums)".
  iDestruct (mono_nats_lb_get with "●γe_nums") as "$".
Qed.

Lemma slot_infos_mono_nats_auth_lb γV γtok γeh γe_nums slist sbvmap ehist (ge := length ehist - 1) idx q e :
  SlotInfos γV γtok γeh γe_nums slist sbvmap ehist -∗
  mono_nats_auth γe_nums {[sid idx]} q e -∗
  ⌜ge-1 ≤ e⌝.
Proof.
  iIntros "[◯γe_nums _] ●γe_nums".
  iDestruct (mono_nats_auth_lb_valid with "●γe_nums ◯γe_nums") as "$".
  set_solver.
Qed.

Lemma slot_infos_get_lbs γV γtok γeh γe_nums slist sbvmap ehist (ge := length ehist - 1) :
  SlotInfos γV γtok γeh γe_nums slist sbvmap ehist -∗
  mono_nats_lb γe_nums (sids_from (length slist)) ge ∗
  mono_nats_lb γe_nums ⊤ (ge -1).
Proof.
  iDestruct 1 as "($ & ●γe_nums & _)".
  iDestruct (mono_nats_lb_get with "●γe_nums") as "$".
Qed.

(** ReclaimInfo Lemmas  *)
Lemma recl_infos_retire γR γtok ehist info i (ge := length ehist - 1) e :
  ge - 1 ≤ e →
  ReclaimInfo γR γtok ehist info -∗
  ReclaimInfo γR γtok (alter (union {[i]}) e ehist) info.
Proof.
  iIntros (e_GE_ge) "Recl".
  iDestruct "Recl" as (reclaimed) "(γR_recl & γR_alive & γR_not_created & toks)".
  unfold ReclaimInfo.
  iExists reclaimed. rewrite alter_length. iFrame.
  rewrite take_alter; [done|lia].
Qed.

(*** Main EBR Lemmas ***)

Lemma rcu_domain_new_spec :
  rcu_domain_new_spec' mgmtN ptrsN ebr_domain_new IsEBRDomain EBRAuth.
Proof.
  intros ?.
  iIntros (Φ) "!> _ IED".
  wp_lam. wp_alloc d as "d↦" "†d". move: (blk_to_loc d) => {}d.
  do 2 rewrite array_cons. rewrite array_singleton.
  iDestruct "d↦" as "(d.b↦ & d.rs↦ & d.e↦)".

  wp_let. wp_apply (sbs.(slot_bag_new_spec) with "[//]") as (γsb slotbag) "SB".
  wp_pures. rewrite loc_add_0. wp_store.
  wp_apply (rls.(retired_list_new_spec) with "[//]") as (rList) "RL".
  wp_store. wp_op. rewrite loc_add_assoc. wp_store.

  (* alloc other info *)
  iMod (ghost_map_alloc_empty (K:=positive) (V:=alloc*gname)) as (γinfo) "[●γinfo ●γinfo_au]".
  iMod coP_ghost_map_alloc_empty as (γptrs) "●γptrs".
  iMod (ghost_var_alloc (∅ : gset positive)) as (γrs) "[●γrs ●γrs_au]".
  iMod ghost_slot_unlink_reclaim_alloc as
    (γeh γtok γR γV γe_nums) "(ehist & GEI & SI & Rec)".
  iMod (UnlinkFlags_alloc) as (γU) "UF".
  remember (encode (γsb, γtok, γinfo, γptrs, γeh, γrs, γU, γV, γR, γe_nums, d)) as γe eqn:Hγe.
  iAssert (EBRDomain _ _ _ _ _ _ _ _ _ _ _ _ _)%I
    with "[SB RL d.e↦ †d ●γinfo ●γrs ●γptrs ehist GEI SI UF Rec]" as "EBR".
  { repeat iExists _. iFrame "∗#". simpl. rewrite !union_empty_l_L. repeat (iSplit; auto).
    iPureIntro. intros ???. set_solver.
  }
  iMod (inv_alloc ebrInvN _ (EBRDomain _ _ _ _ _ _ _ _ _ _ _ _ _) with "EBR") as "#EBR_Inv".
  iMod (mapsto_persist with "d.b↦") as "#d.b↦".
  iMod (mapsto_persist with "d.rs↦") as "#d.rs↦".
  iModIntro. iApply "IED".
  iSplitR.
  all: repeat (iExists _); try rewrite loc_add_0; iFrame (Hγe) "∗#%".
  by rewrite fmap_empty.
Qed.

Lemma rcu_domain_register :
  rcu_domain_register' mgmtN ptrsN IsEBRDomain EBRAuth BaseManaged.
Proof.
  intros ???????????.
  iIntros "IED EBR p↦ †p R".
  iDestruct "IED" as (??????????) "(%&%& %Hγe & #d.l↦ & #d.r↦ & IED)".
  iDestruct "EBR" as (??????????) "(%&%&% & info_au & ret_au & %EQ)".
  encode_agree Hγe. rewrite {}EQ.

  (* Get a new id for p *)
  set i := fresh (dom (fst <$> info) ∪ I).
  assert (info !! i = None) as Freshi.
  { rewrite eq_None_not_Some -elem_of_dom -(dom_fmap_L fst).
    intros InDom. apply (is_fresh (dom (fst <$> info) ∪ I)). set_solver.
  }

  iMod ("R" $! i with "[%]") as "[R Ms]".
  { intros In. apply (is_fresh (dom (fst <$> info) ∪ I)). set_solver. }

  iInv "IED" as (? ? sbvmap slist rL ehist)
                  "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo
                                & >γU & >%Hdom_i & >%Hehist & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".
  iDestruct (ghost_map_auth_agree with "info_au info") as %<-.
  iDestruct (ghost_var_agree with "ret_au ret") as %->.

  (* Prove that [p ∉ dom ptrs] using two freeables, one in [Reg] and [†p]. *)
  iAssert (⌜p ∉ dom ptrs⌝)%I as %PNew.
  { iIntros (In). rewrite elem_of_dom in In.
    destruct In as [idx Some].
    rewrite big_sepM_lookup_acc; last done.
    iDestruct "Reg" as "[Reg_p _]".
    iDestruct "Reg_p" as (?) "(_ & †p')".
    iApply (heap_freeable_valid with "†p †p'"); done.
  }
  rewrite elem_of_dom -eq_None_not_Some in PNew.

  (* get [p] element from [coM] and split. *)
  iMod ((coP_ghost_map_insert p i) with "ptrs") as "[ptrs p↪i]"; first by apply PNew.
  rewrite (top_complement_singleton gid).
  rewrite coP_ghost_map_elem_fractional; last first.
  { rewrite -coPneset_disj_elem_of. set_solver. }
  iDestruct "p↪i" as "[p↪i_gid p↪i]".

  (* Allocate and split [coP_cinv]. *)
  iMod ((coP_cinv_alloc _ (resN ptrsN p i) (∃ vl, ⌜length vl = length lv⌝ ∗ R _ vl _ ∗ p ↦∗ vl)) with "[R p↦]") as (γc_i) "[#Inv ●γc_i]".
  { iExists lv. iFrame. eauto. }
  rewrite (top_complement_singleton gid).
  rewrite coP_cinv_own_fractional; last first.
  { rewrite -coPneset_disj_elem_of. set_solver. }
  iDestruct "●γc_i" as "[●γc_i_gid ●γc_i]".

  (* Update unlink flags *)
  iDestruct (UnlinkFlags_update_notin with "γU") as "[γU U]"; eauto.
  { eapply not_in_info; eauto. }

  (* Update [M] *)
  iCombine "info info_au" as "info".
  iMod (ghost_map_insert_persist i ({| addr := p; len := length lv |}, γc_i) with "info") as "[[info info_au] #i↪□]"; first by apply Freshi.

  (* Update [Recl] *)
  iAssert (ReclaimInfo γR γtok ehist (<[i:=({| addr := p; len := length lv |}, γc_i)]> info) ∗
    ({[i]},⊤) ↦P2[γR]{ 1/2 } false
    )%I with "[Recl]" as "[Recl γR]".
  { iDestruct "Recl" as (reclaimed) "(γR_recl & γR_alive & γR_not_created & toks)".
    unfold ReclaimInfo. rewrite bi.sep_exist_r.
    iExists reclaimed.
    rewrite !dom_insert_L.
    assert (⊤ ∖ gset_to_coPset (dom info) = ⊤ ∖ ({[i]} ∪ gset_to_coPset (dom info)) ∪ {[i]}) as ->.
    { rewrite top_difference_dom_union_not_in_singleton; done. }
    rewrite -!ghost_vars2_union_1; last set_solver.
    rewrite gset_to_coPset_union !gset_to_coPset_singleton.
    iDestruct "γR_not_created" as "[$ [γR $]]".
    iAssert (⌜i ∉ reclaimed⌝)%I as %NotIn.
    { iIntros (ElemOf). iDestruct (ghost_vars2_agree with "γR_recl γR") as %TF; [|done..].
      rewrite -gset_to_coPset_singleton -gset_to_coPset_intersection.
      rewrite -gset_to_coPset_empty.
      intro EQ. rewrite gset_to_coPset_eq in EQ. set_solver. }
    rewrite difference_union_distr_l_L.
    assert ({[i]} ∖ reclaimed = {[i]}) as -> by set_solver.
    iCombine "γR γR_alive" as "γR".
    rewrite ghost_vars2_union_1; last first.
    { rewrite disjoint_singleton_l.
      intros ElemOf. rewrite elem_of_gset_to_coPset elem_of_difference elem_of_dom in ElemOf.
      destruct ElemOf as [[? Hi] _]. congruence.  }
    rewrite gset_to_coPset_union !gset_to_coPset_singleton. iFrame.
  }

  iAssert (|==> Exchanges' _ _ _ _ _)%I with "[●γc_i p↪i]" as ">Exchanges'".
  { unfold Exchanges'. iRight. iLeft.
    iExists ∅. rewrite union_empty_l_L. rewrite set_map_empty. iFrame.
    rewrite gset_to_coPset_empty. iApply token2_get_empty_2. }
  (* Make [Exchanges] *)
  iMod (inv_alloc (exchN mgmtN p i) _ (Exchanges' _ _ _ _ _) with "Exchanges'") as "#Exchanges".

  (* Close invariant *)
  iModIntro. iSplitL "info ptrs ehist ret SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret †p".
  { iNext. repeat iExists _. iFrame "∗#%". iSplit; [iPureIntro|repeat iSplit].
    - rewrite dom_insert_L. set_solver.
    - rewrite big_sepM_insert; [|done]. iSplitL "†p".
      + iExists _. rewrite lookup_insert. iSplit; done.
      + iApply (big_sepM_mono with "Reg").
        iIntros (p' i' Hp') "[%info_i' [%Hinfo_i' †p]]". iExists _. iFrame.
        iPureIntro. rewrite lookup_insert_ne; [done|naive_solver].
    - iPureIntro. intros p' i' Hp'. destruct (decide (p = p')) as [->|NE].
      + rewrite lookup_insert in Hp'. injection Hp' as [= <-].
        rewrite lookup_insert. eauto.
      + rewrite lookup_insert_ne in Hp'; auto.
        apply HInfo in Hp' as [info_i' [Hi' Hinfo_i']]. subst.
        rewrite lookup_insert_ne; eauto. naive_solver.
    - iPureIntro. intros i' p' Hi' [[[? size_i'] γc_i'] [Hp' [= ->]]].
      destruct (decide (i = i')) as [->|NE].
      + rewrite lookup_insert in Hp'. injection Hp' as [= <-].
        by rewrite lookup_insert.
      + rewrite lookup_insert_ne in Hp'; auto.
        specialize (HPtrs i' p' Hi'
                    ltac:(exists ({| addr := p'; len := size_i'|},γc_i'); naive_solver)).
        rewrite lookup_insert_ne; eauto. naive_solver.
  }

  iModIntro. iExists i. iFrame. iSplit.
  { iPureIntro. apply is_fresh. }

  iSplitL "ret_au info_au".
  { repeat iExists _. iFrame "∗%". iPureIntro. by rewrite fmap_insert. }

  (* Make managed *)
  repeat iExists _. iFrame "∗#%".
  repeat iExists _. iFrame "∗#%".
Qed.

Lemma guard_new_spec :
  guard_new_spec' mgmtN ptrsN ebr_guard_new IsEBRDomain BaseInactive.
Proof.
  intros ????.
  iIntros "#IED" (Φ) "!> _ HΦ".
  iDestruct "IED" as (??????????) "(%&%& %Hγe & #d.l↦ & #d.r↦ & IED)".

  wp_lam. wp_pures. wp_load. wp_pures.

  awp_apply sbs.(slot_bag_acquire_slot_spec).
  iInv "IED" as (info ptrs sbvmap slist rL ehist)
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".
  iAaccIntro with "SB".
  { iIntros "SB !>". iFrame. repeat iExists _. by iFrame "∗#%". }
  iIntros (slist' slot idx) "(SB & S & %Hslist')".

  (* Spec for common parts *)
  iAssert((⊤,{[sid idx]}) ↦P2[γV]{ 1/2/2 } false -∗
    (∀ g: loc, BaseInactive γe g -∗ Φ #g) -∗
    WP let: "guard" := AllocN #2 #0 in
        "guard" +ₗ #guardSlot <- #slot;;
        "guard" +ₗ #guardDom <- #d;;
        "guard" @ E {{ v, Φ v }})%I with "[S]" as "make_guard".
  { iIntros "γV HΦ". wp_alloc g as "g↦" "†g".
    rewrite array_cons array_singleton.
    iDestruct "g↦" as "[g.s↦ g.d↦]". wp_pures.
    rewrite !loc_add_0. wp_store. wp_op. wp_store.
    iApply "HΦ". iModIntro. repeat iExists _. rewrite !loc_add_0.
    iFrame "∗#%".
  }
  destruct Hslist' as [[-> [Hm ->]]|[-> [Hm Hl]]].
  - (* New slot added*)
    (* Update [EInfo] and [SInfo], and get validation flag for slot *)
    iDestruct ((ghost_epoch_informations_new_slot slot) with "EInfo") as "[EInfo γV]"; [done..|].
    iDestruct ((slot_infos_new_slot slot) with "SInfo γV") as "[SInfo γV]"; [done..|].

    iModIntro.
    iSplitL "info ptrs ehist ret SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
    { repeat iExists _. by iFrame "∗#%". }
    iIntros "_". wp_let.
    wp_apply ("make_guard" with "γV HΦ").
  - (* Slot Reused *)
    (* Update [EInfo] and [SInfo], and get validation flag for slot *)
    iDestruct (SlotBag_NoDup with "SB") as %NoDup.
    iDestruct ((slot_infos_reactivate_slot slot) with "SInfo") as "[SInfo γV]"; [done..|].
    iDestruct ((ghost_epoch_informations_set idx slot None true) with "EInfo γV")
      as "[EInfo γV]"; [done..|].
    iModIntro.
    iSplitL "info ptrs ehist ret SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
    { repeat iExists _. by iFrame "∗#%". }
    iIntros "_". wp_let.
    wp_apply ("make_guard" with "γV HΦ").
Qed.

Lemma guard_activate_spec :
  guard_activate_spec' mgmtN ptrsN ebr_guard_activate IsEBRDomain BaseInactive BaseGuard.
Proof.
  intros ?????.
  iIntros "#IED" (Φ) "!> G HΦ".
  iDestruct "IED" as (??????????) "#(%&%& %Hγe & d.l↦ & d.r↦ & IED)".
  iDestruct "G" as (??????????) "(%&%&%&%&% & g.slot↦ & g.dom↦ & †g & S & γV)".
  encode_agree Hγe.
  wp_lam. wp_load. wp_pures. wp_load. wp_pures.
  wp_bind (!_)%E.
  iInv "IED" as (info ptrs sbvmap slist rL ehist)
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".

  wp_load.

  iModIntro. iSplitR "g.slot↦ g.dom↦ †g S γV HΦ".
  { repeat iExists _. by iFrame "∗#%". }
  move: (length ehist - 1) => e.
  clear dependent info ptrs sbvmap slist rL ehist.

  wp_let.
  iAssert(∀ (e : nat) (v : option nat),
  {{{ sbs.(Slot) γsb slot idx v ∗
      (⊤,{[sid idx]}) ↦P2[γV]{ 1/2/2 } false }}}
      activate_loop # slot #d #e @ E
  {{{ ge ehistF, RET #();
      sbs.(Slot) γsb slot idx (Some ge) ∗
      epoch_history_frag γeh ge {[sid idx]} ∗
      ⌜ length ehistF = ge -1 ⌝ ∗
      epoch_history_finalized γeh ehistF ∗
      let retired := gset_to_coPset (fold_hist ehistF) in
      (sid ge,sid idx) ↦p2[γV]{ 1/2/2 } true ∗
      (⊤ ∖ {[sid ge]},{[sid idx]}) ↦P2[γV]{ 1/2/2 } false ∗
      toks γtok (⊤ ∖ retired) {[sid idx]} ∗
      mono_nats_auth γe_nums {[sid idx]} (1/2/2) ge
    }}}
    )%I as "activate_loop".
  { (* Activate guard [s] at epoch [e]. *)
    clear e v Φ. iIntros (e v Φ) "!> (S & γV) HΦ".
    iLöb as "IH" forall (e v).
    wp_lam. wp_pures.
    (* 0. write [e] to slot, then validate *)
    awp_apply (sbs.(slot_set_spec) $! _ _ _ _ _ (Some e) with "S") without "HΦ".

    iInv "IED" as (info ptrs sbvmap slist rL ehist)
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".
    iAaccIntro with "SB".
    { iIntros "SB !>". iFrame "γV". do 2 (repeat iExists _; iFrame "∗#%"). }
    iIntros "([%Hl %Hm] & SB & S)".
    iDestruct (SlotBag_NoDup with "SB") as %ND.
    iModIntro.
    iDestruct (ghost_epoch_informations_set idx slot (Some e) true with "EInfo γV") as "[EInfo γV]"; [done..|].
    iDestruct (slot_infos_set with "SInfo γV") as "[SInfo γV]"; [done..|].
    iSplitL "info ptrs ehist ret SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
    { repeat iExists _. iFrame "∗#%". }
    clear dependent info ptrs sbvmap slist rL ehist.
    iIntros "_ HΦ".
    wp_pures. wp_bind (!_)%E.
    iInv "IED" as (info ptrs sbvmap slist rL ehist)
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".
    wp_load.
    set ge := length ehist - 1. simpl.
    destruct (decide (e = ge)) as [->|NE].
    - (* Validation succeeds *) iClear "IH".
      (* Get Finalized locations *)
      iMod (epoch_history_get_finalized with "ehist") as "[ehist #◯ehist_fin]"; [lia|].
      set ehistF := (take (length ehist - 2) ehist).
      set retired := fold_hist ehistF.
      iDestruct (SlotBag_NoDup with "SB") as %ND.
      iDestruct (SlotBag_lookup with "SB S") as %[Hslist Hsvbmap].
      assert (length ehistF = ge - 1).
      { unfold ge, ehistF. rewrite take_length. lia. }
      (* Update nessecary [ghost_vars2 γV] by syncing with EInfo. *)
      iMod (ghost_epoch_informations_slot_infos_activate with "EInfo SInfo γV ◯ehist_fin") as "H"; [try done..|].
      iDestruct "H" as "(EInfo & SInfo & γV_not_ge & γV_ge & ◯ehist_ge & ●γe_nums_idx & toks)".
      iModIntro.
      iSplitL "info ptrs ehist ret SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
      { repeat iExists _. iFrame "∗#%". }
      clear dependent info ptrs sbvmap slist rL.
      wp_pures. rewrite bool_decide_eq_true_2; [|done]. wp_pures.
      iApply "HΦ". iModIntro. iFrame "S". iFrame "∗#%".
    - (* Validation fails. Do induction *)
      iModIntro. iSplitL "info ptrs ehist ret SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
      { repeat iExists _. iFrame "∗%#". }
      wp_pures. rewrite bool_decide_eq_false_2; [|injection as ?;lia].
      wp_if. iApply ("IH" with "S γV HΦ").
  }
  iMod ghost_map_alloc_empty as (γg) "I".
  wp_apply ("activate_loop" with "[$S $γV]")
    as (ge ehistF) "(S & ehist & % & #◯ehistF & γV_true & γV_false & toks & ◯γe_nums)".
  iApply "HΦ". repeat iExists _. iFrame "∗#%".
  iExists ge, ehistF. rewrite range_empty gset_to_coPset_empty difference_empty_L big_sepM_empty.
  iFrame "∗#%". done.
Qed.

Lemma guard_managed_agree :
  guard_managed_agree' mgmtN ptrsN BaseManaged BaseGuard BaseGuardedNodeInfo.
Proof.
  intros ????????????.
  iIntros "[_ #p] G M".
    iDestruct "G" as (??????????)
      "(%&%&%&%& %Hγe & _ & _ & _ & _ & γV)".
    iDestruct "γV" as (e ehist_fin ->)
      "(_ & _ & _ & _ & I & _ & _ & _ & _ & Prot)".
    iDestruct "M" as (??????????)
      "(%&%&% & _ & _ & p2↪ & _)".
  encode_agree Hγe.

  iDestruct (ghost_map_lookup with "I p") as %Lookup_p.

  iDestruct (big_sepM_lookup with "Prot") as "[_ P]"; [exact Lookup_p|].
  iDestruct "P" as (??) "(_ & p1↪ & _)".

  by iDestruct (coP_ghost_map_elem_agree with "p1↪ p2↪") as %->.
Qed.

(* 1. BaseManaged of `i` has `{i} ↪[U]{1/2} false`
    2. auth unlink history doesn't contain it (∵ invariant 1)
    3. my history snapshot doesn't contain it (by monotonicity)
    4. I have token for it
    * note: GPS RCU's reasoning is much more complicated. *)
Lemma guard_protect :
  guard_protect' mgmtN ptrsN IsEBRDomain BaseManaged BaseGuard.
Proof.
  intros ????????????.
  iDestruct 1 as (??????????) "#(% & % & %Hγe & d.rBag↦ & d.rSet↦ & IED)".
  iDestruct 1 as (??????????) "(% & % & % & Gcinv & #◯info_i & γp_i & #Ex & #Cinv & γU_i & γR_i)".
  iDestruct 1 as (??????????) "(% & % & % & % & % & g.slot↦ & g.dom↦ & †g & S & Act_st)".
  iDestruct "Act_st" as (e ehist_fin ->) "(◯γe_nums & γV_true & γV_false & ◯ehist & I & [-> %Hehist_fin] & ◯ehist_fin & toks & %Disj & Prot)".
  do 2 encode_agree Hγe.

  (* Check if it's already protected. *)
  destruct (G !! p) as [i_p'|] eqn:HGp.
  { (* Reuse the existing protection. *)
    iModIntro.
    iDestruct (big_sepM_insert_acc with "Prot") as "[[#p Prot_p] Prot]"; [exact HGp|].
    iSpecialize ("Prot" $! i_p).
    iDestruct "Prot_p" as (??) "(#◯info_i' & γp_i' & γc_i & #Ex')".
    iDestruct (coP_ghost_map_elem_agree with "γp_i γp_i'") as %<-.
    rewrite insert_id; [|done].
    iDestruct (ghost_map_elem_agree with "◯info_i ◯info_i'") as %[= <- <-].
    iSplitL "Gcinv γp_i γU_i γR_i".
    { repeat iExists _. iFrame (Hγe) "∗#". iExists _. iFrame "∗#". }
    iSplitL; [|iSplit;[|done]].
    - repeat iExists _. iFrame (Hγe) "∗#".
      repeat iExists _. iFrame. repeat (iSplitR; [done|]).
      iApply "Prot". iFrame "#". iExists _,_. iFrame "∗#".
    - iPureIntro. assert (i_p ∈ range G); [|set_solver].
      apply range_correct. eauto.
  }

  iInv "IED" as (info ptrs sbvmap slist rL ehist)
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".

  (* Get that [i_p] is not in unlinked history *)
  iDestruct (ghost_map_lookup with "info ◯info_i") as %Hinfo_i.
  apply (elem_of_dom_2 (D:= gset positive)) in Hinfo_i.
  iDestruct (UnlinkFlags_lookup_false with "γU_i γU") as %NotIn; [done|].
  iDestruct (epoch_history_finalized_lookup with "ehist ◯ehist_fin") as %NotIn_G; [done|].

  (* Get that i_p ∉ range G. *)
  iAssert (⌜i_p ∉ range G⌝)%I as %i_not_in_guarded.
  { (* How: *)
    (* 1. assume otherwise. *)
    iIntros (IdInG). rewrite range_correct in IdInG.
    (* 2. Then there is a p' s.t p' ↦ γ_p'; i ∈ G;  *)
    destruct IdInG as [p' Hp_id'].
    (* 3. Hence get [i ↪[γinfo]□ (p', γ_p', γc_i', size_i')] *)
    iDestruct (big_sepM_lookup with "Prot") as "[_ (%&%& ◯info_i_p' & _)]"; [exact Hp_id'|].
    (* 4. Then [p = p'], contradiction since [p ∉ dom G]. *)
    iDestruct (ghost_map_elem_agree with "◯info_i ◯info_i_p'") as %[= <- <- <-].
    iPureIntro. subst. rewrite HGp in Hp_id'. naive_solver.
  }
  (* Now split the token and validation flag from guard. *)
  assert (i_p ∈ ⊤ ∖ gset_to_coPset (fold_hist ehist_fin) ∖ gset_to_coPset (range G)) as i_fresh.
  { rewrite !elem_of_difference. split_and!; [done|rewrite elem_of_gset_to_coPset; done..]. }

  iMod (ghost_map_insert_persist p i_p with "I") as "[I #p]"; [done|].

  set G_new := <[p := i_p]> G.
  assert (i_p ∈ range G_new).
  { subst G_new. rewrite range_insert; [set_solver|done]. }

  assert (⊤ ∖ gset_to_coPset (fold_hist ehist_fin) ∖ gset_to_coPset (range G)
    = (⊤ ∖ gset_to_coPset (fold_hist ehist_fin) ∖ gset_to_coPset (range G_new) ∪ {[i_p]})) as ->.
  { rewrite -!difference_union_difference.
    rewrite difference_difference_r; [| |done]; last first.
    { rewrite singleton_subseteq_l. apply elem_of_union_r.
      rewrite elem_of_gset_to_coPset range_correct /G_new.
      exists p. by simplify_map_eq.
    }
    f_equal. rewrite difference_union_distr_l_L.
    rewrite -!gset_to_coPset_singleton -!gset_to_coPset_difference. repeat f_equal.
    - set_solver.
    - rewrite /G_new range_insert //.
      rewrite difference_union_distr_l_L difference_diag_L union_empty_l_L.
      rewrite -difference_not_in_singletion_L //.
  }

  rewrite /toks -token2_union_1; last first.
  { rewrite disjoint_singleton_r elem_of_difference. intros [_ i_not_in_gid].
    apply i_not_in_gid. rewrite elem_of_gset_to_coPset //.
  }
  iDestruct "toks" as "[toks toks_i]".
  iDestruct (coP_ghost_map_lookup with "ptrs γp_i") as %Hptrs_p.

  apply HInfo in Hptrs_p as [info_i [Hinfo_i_p <-]].
  iMod (exchange_stok_give with "Ex toks_i") as "[zc cinv]"; [solve_ndisj|].

  iModIntro. iSplitL "info ptrs ret ehist SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
  { repeat iExists _. iFrame "∗#%". }
  iModIntro. iSplitL "Gcinv γp_i γU_i γR_i".
  { repeat iExists _. iFrame (Hγe) "∗#". repeat iExists _. by iFrame "∗#". }

  iSplitL.
  - repeat iExists _. iFrame (Hγe) "∗#".
    repeat iExists _. iFrame. repeat (iSplitR; [done|]).
    subst G_new. iSplit; [iPureIntro|].
    + rewrite range_insert // disjoint_union_l. set_solver.
    + rewrite big_sepM_insert //. iFrame. repeat iExists _. iFrame "∗#%".
      repeat iExists _. iFrame "∗#".
  - iPureIntro. split; [done|]. by inversion 1.
Qed.

(* TODO: stupid proof repetition. *)
Lemma guard_protect_node_info :
  guard_protect_node_info' mgmtN ptrsN IsEBRDomain BaseGuard BaseNodeInfo BaseGuardedNodeInfo.
Proof.
  intros ???????????? NotIn.
  iDestruct 1 as (??????????) "#(% & % & %Hγe & d.rBag↦ & d.rSet↦ & IED)".
  iDestruct 1 as (??????????) "(% & % & #Info)".
  iDestruct "Info" as (?) "(#◯info_i & Ex & CInv)".
  iDestruct 1 as (??????????) "(% & % & % & % & % & g.slot↦ & g.dom↦ & †g & S & Act_st)".
  iDestruct "Act_st" as (e ehist_fin ->) "(◯γe_nums & γV_true & γV_false & ◯ehist & I & [-> %Hehist_fin] & ◯ehist_fin & toks & %Disj & Prot)".
  do 2 encode_agree Hγe.

  (* Check if it's already protected. *)
  destruct (G !! p) as [i_p'|] eqn:HGp.
  { (* Reuse the existing protection. *)
    iDestruct (big_sepM_insert_acc with "Prot") as "[[#p Prot_p] Prot]"; [exact HGp|].
    iSpecialize ("Prot" $! i_p).
    iDestruct "Prot_p" as (??) "(#◯info_i' & γp_i' & γc_i & #Ex')".

    iInv "IED" as (info ptrs sbvmap slist rL ehist)
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".

    iDestruct (ghost_map_lookup with "info ◯info_i") as %Hi.
    iDestruct (slot_infos_mono_nats_auth_lb with "SInfo ◯γe_nums") as %LE.
    set (ge := length ehist - 1) in *.
    iDestruct (epoch_history_prefix_strong with "ehist ◯ehist_fin") as %PF; [lia|].

    assert (ptrs !! p = Some i_p) as Hp.
    { apply HPtrs; last first.
      { eexists. split; [exact Hi|]; auto. }
      assert (ge ≥ e) as GE.
      { apply prefix_length in PF. rewrite take_length in PF. lia. }
      rewrite prefix_cut (_ : length ehist - 2  = ge - 1) in PF; [|lia].
      apply (f_equal (take (ge - 2))) in PF.
      rewrite take_take Nat.min_l in PF; [|lia].
      rewrite take_app_le in PF; [|lia].
      specialize (fold_hist_prefix (take (ge - 2) ehist_fin) ehist_fin
            ltac:(apply take_prefix)) as SubTake.
      rewrite -PF in SubTake.
      set_solver.
    }

    iDestruct (coP_ghost_map_lookup with "ptrs γp_i'") as %?.
    assert (i_p = i_p') as <- by naive_solver.
    iDestruct (ghost_map_elem_agree with "◯info_i ◯info_i'") as %[= <- <-].
    rewrite insert_id; [|done].

    iModIntro. iSplitL "info ptrs ret ehist SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
    { repeat iExists _. by iFrame "∗#". }
    iModIntro. iSplitL; [|iSplit;[|done]].
    - repeat iExists _. iFrame (Hγe) "∗#".
      repeat iExists _. iFrame. repeat (iSplitR; [done|]).
      iApply "Prot". iFrame "#". iExists _,_. iFrame "∗#".
    - iFrame "p". repeat iExists _. iFrame "∗%#".
      repeat iExists _. iFrame "∗#".
  }

  (* Get that i_p ∉ range G. *)
  iAssert (⌜i_p ∉ range G⌝)%I as %i_not_in_guarded.
  { (* How: *)
    (* 1. assume otherwise. *)
    iIntros (IdInG). rewrite range_correct in IdInG.
    (* 2. Then there is a p' s.t p' ↦ γ_p'; i ∈ G;  *)
    destruct IdInG as [p' Hp_id'].
    (* 3. Hence get [i ↪[γinfo]□ (p', γ_p', γc_i', size_i')] *)
    iDestruct (big_sepM_lookup with "Prot") as "[_ (%&%& #◯info_i_p' & _)]"; [exact Hp_id'|].
    (* 4. Then [p = p'], contradiction since [p ∉ dom G]. *)
    iDestruct (ghost_map_elem_agree with "◯info_i ◯info_i_p'") as %[= <- <- <-].
    iPureIntro. subst. rewrite HGp in Hp_id'. naive_solver.
  }
  (* Now split the token and validation flag from guard. *)
  assert (i_p ∈ ⊤ ∖ gset_to_coPset (fold_hist ehist_fin) ∖ gset_to_coPset (range G)) as i_fresh.
  { rewrite !elem_of_difference. split_and!; [done|rewrite elem_of_gset_to_coPset; done..]. }

  iMod (ghost_map_insert_persist p i_p with "I") as "[I #p]"; [done|].

  set G_new := <[p := i_p]> G.
  assert (i_p ∈ range G_new).
  { subst G_new. rewrite range_insert; [set_solver|done]. }

  assert (⊤ ∖ gset_to_coPset (fold_hist ehist_fin) ∖ gset_to_coPset (range G)
    = (⊤ ∖ gset_to_coPset (fold_hist ehist_fin) ∖ gset_to_coPset (range G_new) ∪ {[i_p]})) as ->.
  { rewrite -!difference_union_difference.
    rewrite difference_difference_r; [| |done]; last first.
    { rewrite singleton_subseteq_l. apply elem_of_union_r.
      rewrite elem_of_gset_to_coPset range_correct /G_new.
      exists p. by simplify_map_eq.
    }
    f_equal. rewrite difference_union_distr_l_L.
    rewrite -!gset_to_coPset_singleton -!gset_to_coPset_difference. repeat f_equal.
    - set_solver.
    - rewrite /G_new range_insert //.
      rewrite difference_union_distr_l_L difference_diag_L union_empty_l_L.
      rewrite -difference_not_in_singletion_L //.
  }

  rewrite /toks -token2_union_1; last first.
  { rewrite disjoint_singleton_r elem_of_difference. intros [_ i_not_in_gid].
    apply i_not_in_gid. rewrite elem_of_gset_to_coPset //.
  }
  iDestruct "toks" as "[toks toks_i]".
  iMod (exchange_stok_give with "Ex toks_i") as "[zc cinv]"; [solve_ndisj|].

  iModIntro. iSplitL; [|iSplit].
    - repeat iExists _. iFrame (Hγe) "∗#".
      repeat iExists _. iFrame. repeat (iSplitR; [done|]).
      subst G_new. iSplit; [iPureIntro|].
    + rewrite range_insert // disjoint_union_l. set_solver.
    + rewrite big_sepM_insert //. iFrame. repeat iExists _. iFrame "∗#%".
      repeat iExists _. iFrame "∗#".
  - iFrame "p". repeat iExists _. iFrame "∗%#".
    repeat iExists _. iFrame "∗#".
  - iPureIntro. by inversion 1.
Qed.

Lemma rcu_auth_guard_subset :
  rcu_auth_guard_subset' mgmtN ptrsN IsEBRDomain EBRAuth BaseGuard.
Proof.
  intros ??????????.
  iIntros "#IED EBRAuth G".
  iDestruct "IED" as (??????????) "#(%&%& %Hγe & d.l↦ & d.r↦ & IED)".
  iDestruct "G" as (??????????) "(%&%&%&%& % & g.slot↦ & g.dom↦ & †g & S & Act_st)".
  iDestruct "Act_st" as (e ehist_fin ->) "(◯γe_nums & γV_true & γV_false & ◯ehist & I & [-> %Hehist_fin] & ◯ehist_fin & toks & %Disj & Prot)".
  encode_agree Hγe.

  iInv "IED" as (info ptrs sbvmap slist rL ehist)
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".
  iDestruct "EBRAuth" as (??????????) "(%&%&%& info_au & ret_au & %Hinfo_au)".
  encode_agree Hγe.
  iDestruct (ghost_map_auth_agree with "info_au info") as %->.
  iDestruct (ghost_var_agree with "ret_au ret") as %->.
  rewrite Hinfo_au.
  iDestruct (epoch_history_prefix with "ehist ◯ehist_fin") as %HPF.
  apply fold_hist_prefix in HPF.
  iModIntro. iSplitL "info ptrs ret ehist SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
  { repeat iExists _. by iFrame "∗#%". }
  iModIntro. iSplitL "info_au ret_au".
  { repeat iExists _. by iFrame "∗#%". }
  iSplitL; [|done].
  repeat iExists _. iFrame (Hγe) "∗#%".
  repeat iExists _. iFrame "∗#%". done.
Qed.

Lemma guard_acc :
  guard_acc' ptrsN BaseGuard BaseGuardedNodeInfo.
Proof.
  intros ???????????.
  iIntros "[Info #p] G".
  iDestruct "Info" as (??????????) "(% & %Hγe & % & #i↪ & #Ex & #RCI)".
  iDestruct "G" as (??????????) "(%&%&%&%&% & g.slot↦ & g.dom↦ & †g & S & Act_st)".
  iDestruct "Act_st" as (e ehist_fin ->) "(◯γe_nums & γV_true & γV_false & ◯ehist & I & [-> %Hehist_fin] & ◯ehist_fin & toks & %Disj & Prot)".
  encode_agree Hγe.

  iDestruct (ghost_map_lookup with "I p") as %HGp.

  iDestruct (big_sepM_lookup_acc with "Prot") as "[[_ Prot_p] Prot]"; [exact HGp|].
  iDestruct "Prot_p" as (??) "(#◯info_i & γp_i & γc_i & _)".

  iDestruct (ghost_map_elem_agree with "i↪ ◯info_i") as %[= <- <-].

  iInv "RCI" as "[R γc_i]" "Close1".

  iDestruct ("Prot" with "[γp_i γc_i $p]") as "Prot".
  { repeat iExists _. iFrame "∗#". }

  iDestruct "R" as (?) "(><- & R & >p↦)".
  iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Close2".
  iExists vl. iFrame "p↦ R". iSplit; [done|].
  iSplitR "Close1 Close2".
  { repeat iExists _. iFrame "∗#%". repeat iExists _. iFrame "∗#%". done. }

  iIntros (vl') "(%Hvl' & p↦ & R)".
  iMod "Close2".
  iMod ("Close1" with "[p↦ R]"). { repeat iExists _. iFrame "∗#%". iPureIntro. lia. }
  done.
Qed.

Lemma managed_acc :
  managed_acc' mgmtN ptrsN BaseManaged.
Proof.
  intros ???????.
  iIntros "G_p".
    iDestruct "G_p" as (??????????) "(% & % & %Hγ & G_p)".
    iDestruct "G_p" as "(Gcinv & #i□ & pc & #Ex & #RCI & GU)".
  iInv "RCI" as "[R cinv]" "Close1".
  iDestruct "R" as (?) "(>%Hsize_i & R & >p↦)".
  iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Close2".

  iExists vl. iFrame "p↦ R %".
  iSplitR "Close1 Close2". { do 2 (repeat iExists _; iFrame "∗#%"). }

  iIntros (vl') "(%Hvl' & p↦ & R)".
  iMod "Close2".
  iMod ("Close1" with "[p↦ R]"). { repeat iExists _. iFrame "∗#%". iPureIntro. lia. }
  done.
Qed.

Lemma managed_exclusive :
  managed_exclusive' mgmtN ptrsN BaseManaged.
Proof.
  intros ????????.
  iIntros "M M'".
  iDestruct "M" as (??????????) "(% & %Hγe & M)".
  iDestruct "M'" as (??????????) "(% & % & M')".
  encode_agree Hγe.
  iDestruct "M" as (γc_i) "(cinv & i↪ & pc & Ex & CInv & U & γR)".
  iDestruct "M'" as (γc_i') "(cinv' & i'↪ & pc' & Ex' & CInv' & U' & γR')".
  iDestruct (coP_ghost_map_elem_agree with "pc' pc") as %->.
  iDestruct (ghost_map_elem_agree with "i'↪ i↪") as %[= -> ->].
  iDestruct (coP_cinv_own_valid with "cinv' cinv") as %DISJ.
  iPureIntro. rewrite coPneset_disj_iff /= in DISJ.
  set_solver.
Qed.

Lemma managed_get_node_info :
  managed_get_node_info' mgmtN ptrsN BaseManaged BaseNodeInfo.
Proof.
  intros ?????.
  iDestruct 1 as (??????????) "(% & %Hγe & M)".
  iDestruct "M" as (γc_i) "(cinv & #i↪ & pc & #Ex & #CInv & U & γR)".
  repeat iExists _. iFrame (Hγe). iExists γc_i. iFrame "#".
Qed.

Lemma guard_deactivate_spec :
  guard_deactivate_spec' mgmtN ptrsN ebr_guard_deactivate IsEBRDomain BaseInactive BaseGuard.
Proof.
  intros ????????.
  iIntros "#IED" (Φ) "!> G HΦ".
    iDestruct "IED" as (??????????) "#(%&%& %Hγe & d.l↦ & d.r↦ & IED)".
    iDestruct "G" as (??????????) "(%&%&%&%&% & g.slot↦ & g.dom↦ & †g & S & Act_st)".
    iDestruct "Act_st" as (e ehistF ->)
      "(●M & ●VeI & ●VTxI & F & I & [-> %HlenF] & Fin & T & %Disj & Prot)".
    encode_agree Hγe.
  iMod (do_unprotect with "Prot") as "T'"; [solve_ndisj|].

  wp_lam. wp_pures. wp_load. wp_pures.
  iInv "IED" as (info ptrs sbvmap slist rL ehist)
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".
  wp_apply (sbs.(slot_unset_spec) with "[$S $SB]") as "([%Hi %Hsl] & SB & S)".

  iAssert (
    toks γtok (⊤ ∖ gset_to_coPset (fold_hist ehistF)) {[sid idx]}
  ) with "[T T']" as "T".
  { remember (gset_to_coPset (fold_hist ehistF)) as A.
    remember (gset_to_coPset (range G)) as SB.
    iCombine "T T'" as "T". rewrite toks_union_1; last set_solver.
    replace ((⊤ ∖ A ∖ SB) ∪ SB) with (⊤ ∖ A).
    - done.
    - rewrite difference_union_L. assert (SB ⊆ ⊤ ∖ A) as SUBSET.
      { rewrite -disjoint_complement. subst. rewrite -gset_to_coPset_disjoint.
        done. }
      rewrite subseteq_union_L in SUBSET. set_solver.
  }

  iDestruct (SlotBag_NoDup with "SB") as %ND.
  iDestruct (epoch_history_prefix with "ehist Fin") as %PFehistF.
  iDestruct (epoch_history_le_strong with "ehist Fin") as %Hlenle; first lia.
  iMod (ghost_epoch_informations_slot_infos_deactivate with
    "EInfo SInfo ●VTxI ●VeI F ●M T Fin"
  ) as "(EInfo & SInfo & ●VTI)"; eauto; first lia.
  iDestruct (ghost_epoch_informations_set with "EInfo ●VTI")
    as "[EInfo ●VTI]"; eauto.
  iDestruct (slot_infos_set with "SInfo ●VTI")
    as "[SInfo ●VTI]"; eauto.

  iModIntro.
  iSplitL "info ptrs ret ehist SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
  { iNext. repeat iExists _. iFrame "EInfo ∗#%". }
  iApply "HΦ".
  repeat iExists _. by iFrame.
Qed.

Lemma slot_guard_drop γsb γtok γinfo γptrs γeh γrs γU γV γR γe_nums idx (d lBag rList slot g : loc) E :
  ↑to_baseN mgmtN ⊆ E →
  {{{ inv ebrInvN (EBRDomain γsb γtok γinfo γptrs γeh γrs γU γV γR γe_nums d lBag rList) ∗
      sbs.(Slot) γsb slot idx None ∗
      (⊤,{[sid idx]}) ↦P2[γV]{ 1/2/2 } false ∗
      (g +ₗ guardSlot) ↦ #slot ∗
      (g +ₗ guardDom) ↦ #d ∗
      † g … guardSize
  }}}
    slot_drop #slot;; Free #guardSize #g @ E
  {{{ RET #(); True }}}.
Proof.
  iIntros (? Φ) "(#IED & S & ●Sh & g.slot↦ & g.dom↦ & †g) HΦ".
  awp_apply (sbs.(slot_drop_spec) with "S") without "HΦ".
  iInv "IED" as (info ptrs sbvmap slist rL ehist)
    "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".
  iAaccIntro with "SB".
  { iFrame. iIntros "SB". iModIntro. iNext. repeat iExists _. iFrame "∗#%". }
  iIntros "(%Hslot & SB)". destruct Hslot. iModIntro.
  iDestruct (SlotBag_NoDup with "SB") as %NoDup.
  iDestruct (ghost_epoch_informations_set with "EInfo ●Sh") as "[EInfo ●Sh]"; eauto.
  iDestruct (slot_infos_unset with "SInfo ●Sh") as "SInfo"; eauto.
  iSplitR "g.slot↦ g.dom↦ †g".
  { iNext. repeat iExists _. iFrame "∗#%". }
  iIntros "_ HΦ". wp_seq. iCombine "g.slot↦ g.dom↦" as "g↦".
  iEval (rewrite loc_add_0 -!array_singleton -array_app /=) in "g↦".
  wp_free; [done|]. by iApply "HΦ".
Qed.

Lemma guard_drop_spec :
  guard_drop_spec' mgmtN ptrsN ebr_guard_drop IsEBRDomain BaseGuard.
Proof.
  intros ????????.
  iIntros "#IED" (Φ) "!> G HΦ".
    iDestruct "IED" as (??????????) "#(%&%& %Hγe & d.l↦ & d.r↦ & IED)".
    iDestruct "G" as (??????????) "(%&%&%&%&% & g.slot↦ & g.dom↦ & †g & S & Act_st)".
    iDestruct "Act_st" as (e ehistF ->)
    "(●M & ●VeI & ●VTxI & F & I & [-> %HlenF] & Fin & T & %Disj & Prot)".
  encode_agree Hγe.
  iMod (do_unprotect with "Prot") as "T'"; [done|].

  wp_lam. wp_pures. wp_load. wp_pures.

  wp_bind (_ <- _)%E.
  iInv "IED" as (info ptrs sbvmap slist rL ehist)
    "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".
  wp_apply (sbs.(slot_unset_spec) with "[$S $SB]") as "([%Hi %Hsl] & SB & S)".

  iAssert (
    toks γtok (⊤ ∖ gset_to_coPset (fold_hist ehistF)) {[sid idx]}
  ) with "[T T']" as "T".
  { remember (gset_to_coPset (fold_hist ehistF)) as A.
    remember (gset_to_coPset (range G)) as SB.
    iCombine "T T'" as "T". rewrite toks_union_1; last set_solver.
    replace ((⊤ ∖ A ∖ SB) ∪ SB) with (⊤ ∖ A).
    - done.
    - rewrite difference_union_L. assert (SB ⊆ ⊤ ∖ A) as SUBSET.
      { rewrite -disjoint_complement. subst. rewrite -gset_to_coPset_disjoint.
        done. }
      rewrite subseteq_union_L in SUBSET. set_solver.
  }

  iDestruct (SlotBag_NoDup with "SB") as %ND.
  iDestruct (epoch_history_prefix with "ehist Fin") as %PFehistF.
  iDestruct (epoch_history_le_strong with "ehist Fin") as %Hlenle; first lia.
  iMod (ghost_epoch_informations_slot_infos_deactivate with
    "EInfo SInfo ●VTxI ●VeI F ●M T Fin"
  ) as "(EInfo & SInfo & ●VTI)"; eauto; first lia.
  iDestruct (ghost_epoch_informations_set with "EInfo ●VTI")
    as "[EInfo ●VTI]"; eauto.
  iDestruct (slot_infos_set with "SInfo ●VTI")
    as "[SInfo ●VTI]"; eauto.

  iModIntro.
  iSplitL "info ptrs ret ehist SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
  { repeat iExists _. iFrame "EInfo ∗#%". }
  wp_seq. wp_apply (slot_guard_drop with "[$IED $S $●VTI $g.slot↦ $g.dom↦ $†g]"); [solve_ndisj|].
  done.
Qed.

Lemma guard_drop_inactive_spec :
  guard_drop_inactive_spec' mgmtN ptrsN ebr_guard_drop IsEBRDomain BaseInactive.
Proof.
  intros ?????.
  iIntros "#IED" (Φ) "!> G HΦ".
    iDestruct "IED" as (??????????) "#(%&%& %Hγe & d.l↦ & d.r↦ & IED)".
    iDestruct "G" as (??????????) "(%&%&%&%&% & g.slot↦ & g.dom↦ & †g & S & Act_st)".
    encode_agree Hγe.

  wp_lam. wp_pures. wp_load. wp_pures.

  (* deactiavted *)
  wp_bind (_ <- _)%E.
  iInv "IED" as (info ptrs sbvmap slist rL ehist)
    "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".
  wp_apply (sbs.(slot_unset_spec) with "[$S $SB]") as "([%Hi %Hsl] & SB & S)".

  iDestruct (SlotBag_NoDup with "SB") as %ND.
  iDestruct (ghost_epoch_informations_set with "EInfo Act_st")
    as "[EInfo Act_st]"; eauto.
  iDestruct (slot_infos_set with "SInfo Act_st")
    as "[SInfo Act_st]"; eauto.

  iModIntro.
  iSplitL "info ptrs ret ehist SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
  { repeat iExists _. iFrame "EInfo ∗#%". }
  wp_seq. wp_apply (slot_guard_drop with "[$IED $S $Act_st $g.slot↦ $g.dom↦ $†g]"); [solve_ndisj|].
  done.
Qed.

Lemma rcu_domain_retire_spec :
  rcu_domain_retire_spec' mgmtN ptrsN ebr_domain_retire IsEBRDomain EBRAuth BaseManaged.
Proof.
  intros ????????.
  iIntros "#IED M" (Φ) "AU".
  wp_lam. wp_pures.
  wp_apply (guard_new_spec with "IED [//]") as (g) "G"; [solve_ndisj|].
  wp_pures.
  wp_apply (guard_activate_spec with "IED G") as (γg Syn) "G"; [solve_ndisj|].
  iDestruct "IED" as (??????????) "#(%&%& %Hγe & d.l↦ & d.r↦ & IED)".
    iDestruct "G" as (??????????) "(%&%&%&%&% & g.slot↦ & g.dom↦ & †g & S & Act_st)".
    iDestruct "Act_st" as (e ehistF ->)
      "(●M & ●VeI & ●VTxI & F & I & [-> %HlenF] & Fin & T & %Disj & Prot)".
  encode_agree Hγe.
  wp_pures. wp_load. wp_pures. wp_load. wp_pures.
  wp_bind (!_)%E.
  iInv "IED" as (info ptrs sbvmap slist rL ehist)
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".
  iDestruct (sbs.(SlotBag_lookup) with "SB S") as %[Hslist Hsvbmap].
  wp_apply (sbs.(slot_read_value_spec) with "[] [$SB]") as (b v') "[%Hsvbmap' SB]"; [by simplify_list_eq|].
  rewrite Hsvbmap in Hsvbmap'. injection Hsvbmap' as [= <- <-].
  iModIntro. iSplitL "info ptrs ret ehist SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
  { repeat iExists _. by iFrame "∗#%". }
  clear dependent info ptrs sbvmap slist rL ehist.
  wp_let.
  wp_apply (rls.(retired_node_new_spec) with "[//]") as (rNode) "RNode".
  wp_let.
  iDestruct (mono_nats_lb_get with "●M") as "#◯M".
  awp_apply (rls.(retired_list_push_spec) with "RNode").
  iInv "IED" as (info ptrs sbvmap slist rL ehist)
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".
  iAaccIntro with "RL"; iIntros "RL".
  { iModIntro. iSplitL "info ptrs ret ehist SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
    { repeat iExists _. iFrame "∗#%". }
    iFrame "∗#%".
  }
  iDestruct (epoch_history_frag_lookup with "ehist F") as %He.
  apply lookup_lt_is_Some_2 in He as [unlinked_G He].
  iDestruct "M" as (??????????) "(% & % & % & Gcinv & #◯info_i & γp_i & #Ex & #Cinv & γU_i & γR_i)".
  encode_agree Hγe.
  iDestruct (ghost_map_lookup with "info ◯info_i") as %Hinfo_i.
  apply (elem_of_dom_2 (D:= gset positive)) in Hinfo_i as Hinfo_i'.
  iDestruct (UnlinkFlags_lookup_false with "γU_i γU") as %NotIn; [done|].
  iDestruct (epoch_history_le_strong with "ehist Fin") as %ehist_LE; [done|].
  iDestruct (slot_infos_mono_nats_auth_lb with "SInfo ●M") as %LE.
  iMod (epoch_history_retire with "ehist F") as "[ehist ◯ehist]"; [try lia; done..|].
  iMod (epoch_history_snapshot_get e with "ehist") as "[ehist #◯e_snap]".
  { rewrite list_lookup_alter. rewrite He fmap_Some. eauto. }
  assert (length ehist = length (alter (union {[i_p]}) e ehist)) as ->.
  { by rewrite alter_length. }
  (* Update [γU]. In particular, change [γU_i] to true. *)
  (* First lookup [infos] *)
  iAssert(|={E ∖ ∅ ∖ ↑ebrInvN}=> UnlinkFlags γU info (alter (union {[i_p]}) e ehist) ∗ i_p ↦p[γU]{1/2} true)%I with "[γU γU_i]" as ">[γU γU_i]".
  { iDestruct "γU" as "[$ γU]".
    iEval (rewrite big_sepM_delete; [|exact Hinfo_i]) in "γU".
    iDestruct "γU" as "[γU_i' γU]".
    iDestruct "γU_i'" as (U) "[γU_i' %]".
    iDestruct (ghost_vars_agree with "γU_i' γU_i") as %->; [set_solver|].
    iMod (ghost_vars_update_halves' true with "γU_i' γU_i") as "[γU_i $]".
    iEval (rewrite big_sepM_delete; [|done]).
    rewrite bi.sep_exist_r. iExists true. iFrame. iModIntro.
    iSplit.
    { iPureIntro. split; [intros _|done]. rewrite elem_of_fold_hist.
      exists e, ({[i_p]} ∪ unlinked_G). split; [|set_solver].
      rewrite list_lookup_alter He fmap_Some.
      exists unlinked_G. auto.
    }
    iApply (big_sepM_mono with "γU"). iIntros (i' info_i' Hi') "γU_i'".
    iDestruct "γU_i'" as (U) "γU_i'".
    iExists U. iDestruct "γU_i'" as "[$ %U_i']".
    iPureIntro. rewrite not_elem_of_fold_hist in NotIn. destruct U_i' as [U_imp In_imp].
    rewrite lookup_delete_Some in Hi'. destruct Hi' as [NEi Hi'].
    split.
    - intro U'. specialize (U_imp U'). rewrite elem_of_fold_hist in U_imp.
      destruct U_imp as (e' & unlinked_e & He' & ElemOf).
      rewrite elem_of_fold_hist. exists e'.
      destruct (decide (e' = e)) as [->|NE].
      + exists ({[i_p]} ∪ unlinked_e). split; [|apply elem_of_union_r; done].
        rewrite list_lookup_alter fmap_Some. eauto.
      + exists unlinked_e.  rewrite list_lookup_alter_ne; done.
    - intro ElemOf. apply In_imp. rewrite elem_of_fold_hist in ElemOf.
      destruct ElemOf as (e' & unlinked_e & He' & ElemOf).
      rewrite elem_of_fold_hist. exists e'.
      destruct (decide (e' = e)) as [->|NE].
      + rewrite list_lookup_alter fmap_Some in He'.
        destruct He' as (unlinked_e' & Hehist2e & He_union).
        subst.
        exists unlinked_e'. split; [done|].
        specialize (NotIn e unlinked_e' Hehist2e).
        rewrite elem_of_union in ElemOf. destruct ElemOf as [ElemOf|ElemOf]; set_solver.
      + exists unlinked_e. rewrite list_lookup_alter_ne in He'; done.
  }
  (* Update [SInfo] *)
  iDestruct (slot_infos_retire with "SInfo") as "SInfo"; [done|].
  iMod "AU" as (??) "[EBRAuth [_ Commit]]".
  iDestruct "EBRAuth" as (??????????) "(%&%& % & info_au & ret_au & %Hinfo_au)".
  encode_agree Hγe.
  iDestruct (ghost_map_auth_agree with "info_au info") as %->.
  iDestruct (ghost_var_agree with "ret_au ret") as %->.
  rewrite Hinfo_au.
  iMod (ghost_var_update_halves (fold_hist (alter (union {[i_p]}) e ehist)) with "ret_au ret") as "[ret_au ret]".
  iMod ("Commit" with "[info_au ret_au]") as "HΦ".
  { repeat iExists _. iFrame (Hγe) "∗#%". iSplit; [|done].
    assert (fold_hist (alter (union {[i_p]}) e ehist) = {[i_p]} ∪ fold_hist ehist) as ->; [|done].
    rewrite (list_alter_insert _ _ _ unlinked_G); [|done].
    rewrite insert_take_drop; [|lia].
    rewrite -{3}(list_insert_id ehist e unlinked_G); [|done].
    rewrite insert_take_drop; [|lia]. rewrite !fold_hist_app /=.
    rewrite -(list_insert_id ehist e unlinked_G) in NotIn; [|done].
    rewrite insert_take_drop in NotIn; [|lia]. rewrite !fold_hist_app /= in NotIn.
    set_solver.
  }

  iModIntro.
  iSplitL "info ptrs ehist ret SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret Gcinv γp_i γU_i γR_i"; last first.
  { iIntros "_". wp_pures.
    iAssert (BaseGuard _ _ _ _ ∅) with "[g.slot↦ g.dom↦ †g S ●M ●VeI ●VTxI Fin I T ◯ehist Prot]" as "G".
    { repeat iExists _. iFrame (Hγe) "∗#%".
      repeat iExists _. iFrame "∗#%". done.
    }
    wp_apply (guard_drop_spec with "[] G"); [solve_ndisj|..].
    { repeat iExists _. iFrame (Hγe) "#%". }
    iApply "HΦ".
  }
  (* Update [Rec] *)
  iDestruct (recl_infos_retire with "Recl") as "Recl"; [done|].
  iNext.
  iExists _,_,_,_,((p,_,e)::rL),_.
  iFrame "ehist ∗#%".
  iSplit.
  { iPureIntro. rewrite elem_of_subseteq. rewrite elem_of_subseteq in Hdom_i.
    intros i' ElemOf. destruct (decide (i' = i_p)) as [->|NE].
    { rewrite elem_of_dom. eauto. }
    apply (Hdom_i i').
    rewrite elem_of_fold_hist in ElemOf.
    rewrite elem_of_fold_hist.
    destruct ElemOf as (e' & unlinked_e & Hehist2 &ElemOf).
    destruct (decide (e' = e)) as [->|NE_e]; last first.
    { rewrite list_lookup_alter_ne in Hehist2; last done. eauto. }
    rewrite list_lookup_alter He fmap_Some in Hehist2.
    destruct Hehist2 as (unlinked_e' & Hu_G & Hunion ).
    injection Hu_G as [= <-]. subst. set_solver.
  }
  iSplit.
  { iPureIntro. rewrite alter_length. lia. }
  iSplit.
  { iExists i_p, _, _. iFrame "◯e_snap". iSplit.
    { repeat iExists _. iFrame "∗#". }
    iPureIntro. set_solver.
  }
  iPureIntro.
  by rewrite alter_length take_alter; [|lia].
Qed.

Lemma may_advance_spec γsb γtok γinfo γptrs γeh γrs γU γV γR γe_nums (d lBag rList : loc) unlinked_e (e : nat) E :
  ↑(to_baseN mgmtN) ⊆ E →
  {{{ inv ebrInvN (EBRDomain γsb γtok γinfo γptrs γeh γrs γU γV γR γe_nums d lBag rList) ∗
      epoch_history_snap γeh e unlinked_e
      }}}
    may_advance #lBag #e @ E
  {{{ (ret : bool), RET #ret;
      mono_nats_lb γe_nums ⊤ (if ret then e else e-1)
      }}}.
Proof.
  intros ?. iIntros (Φ) "#(IED & ◯ehist_e) HΦ".
  wp_lam. wp_pures.
  wp_bind (!_)%E.
  iInv "IED" as (info ptrs sbvmap slist rL ehist)
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist_len & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".
  wp_apply (sbs.(slot_bag_read_head_spec) with "SB") as "(SB & #SL)".
  set ge := length ehist - 1.
  iDestruct (slot_infos_get_lbs with "SInfo") as "#[◯γe_nums_from ◯γe_nums]".
  iDestruct (epoch_history_snapshot with "ehist ◯ehist_e") as %Hehist.
  destruct Hehist as (unlinked_auth & Hehist & _).
  apply lookup_lt_Some in Hehist.
  assert (e ≤ ge) as HLEe_ge by lia.
  iDestruct ((mono_nats_lb_le e) with "◯γe_nums_from") as "◯γe_nums_from_e"; [done|].
  iDestruct ((mono_nats_lb_le (e-1)) with "◯γe_nums") as "◯γe_nums_e"; [lia|].
  iClear "◯γe_nums_from ◯γe_nums".
  iModIntro. iSplitL "info ptrs ret ehist SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
  { repeat iExists _. iFrame "∗#%". }
  clear dependent info ptrs sbvmap rL ehist unlinked_auth.
  wp_let.

  iAssert (∀ rem (Hrem : rem ≤ (length slist)),
    {{{ mono_nats_lb γe_nums (sids_range rem (length slist)) e }}}
      may_advance_loop #(oloc_to_lit (last (take rem (slist)))) #e @ E
    {{{ (ret : bool), RET #ret; mono_nats_lb γe_nums ⊤ (if ret then e else (e-1)) }}}
  )%I as "may_advance_loop"; last first.
  { iSpecialize ("may_advance_loop" $! (length (slist))).
    rewrite sids_range_empty take_ge; last lia.
    wp_apply ("may_advance_loop" with "[◯γe_nums_from_e]"); [iPureIntro; lia| |iApply "HΦ"].
    iEval (rewrite -(union_empty_l_L (sids_from (length slist)))) in "◯γe_nums_from_e".
    rewrite mono_nats_lb_union; [|set_solver].
    iDestruct "◯γe_nums_from_e" as "[$ _]".
  }

  clear Φ.
  iIntros (rem Hrem Φ) "!> #◯γe_nums_from_rem HΦ".
  iInduction rem as [|rem'] "IH".
  { simpl. wp_lam. wp_pures. rewrite sids_range_0_sids_to.
    iCombine "◯γe_nums_from_rem ◯γe_nums_from_e" as "◯γe_nums".
    rewrite -mono_nats_lb_union; [|apply sids_to_sids_from_disjoint].
    rewrite sids_to_sids_from_union.
    iApply "HΦ". by iFrame "◯γe_nums". }

  (* [rem'] is the index of the current slot. *)
  have [slot Hrem'] : is_Some (slist !! rem').
  { apply lookup_lt_is_Some_2. lia. }
  rewrite take_last; last done. rewrite Hrem' /=.

  (* continue spec *)
  iAssert (∀ge (LE : e ≤ ge),
    mono_nats_lb γe_nums {[sid rem']} ge -∗
    (∀ ret : bool,
         mono_nats_lb γe_nums ⊤ (if ret then e else e - 1) -∗ Φ #ret) -∗
    WP let: "next" := !#(slot +ₗ 0) in may_advance_loop "next" #e @ E {{ v, Φ v }}
  )%I as "continue".
  { iIntros (ge LE) "#◯γe_nums_slot HΦ".
    (* Get proper lb. *)
    iDestruct ((mono_nats_lb_le e) with "◯γe_nums_slot") as "◯γe_nums_slot_e"; [done|].
    iCombine "◯γe_nums_slot_e ◯γe_nums_from_rem" as "◯γe_nums".
    iEval (rewrite -Nat.add_1_r) in "◯γe_nums".
    rewrite -mono_nats_lb_union; last apply sid_sids_range_disjoint_cons.
    rewrite -sids_range_cons; [|lia].

    (* Get next slot. *)
    wp_bind (! _)%E.
    iInv "IED" as (info ptrs sbvmap slist2 rL ehist)
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist_len & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".
    set ge' := length ehist - 1.
    iDestruct (sbs.(SlotBag_prefix) with "SB SL") as %PF2.
    have [slist2' Hslist2] := PF2.
    have {}Hrem'2 : slist2 !! rem' = Some slot.
    { eapply prefix_lookup_Some; [apply Hrem'|done]. }
    wp_apply (sbs.(slot_read_next_spec) $! _ _ _ _ _ _ _ Hrem'2 with "SB") as "SB".
    iModIntro. iSplitL "info ptrs ret ehist SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
    { repeat iExists _. iFrame "∗#%". }

    (* Finish induction *)
    wp_let.
    rewrite Hslist2. rewrite take_app_le; last lia.
    iSpecialize ("IH" with "[%]"); first lia.
    wp_apply ("IH" with "◯γe_nums HΦ").
  }

  wp_lam. wp_pures.

  (*  Check if the slot is active. *)
  wp_bind (! _)%E.
  iInv "IED" as (info ptrs sbvmap slist2 rL ehist)
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist_len & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".
  set ge1 := length ehist - 1.
  iDestruct (sbs.(SlotBag_prefix) with "SB SL") as %PF1.
  have {}Hrem'1 : slist2 !! rem' = Some slot.
  { by eapply prefix_lookup_Some. }
  wp_apply (sbs.(slot_read_active_spec) $! _ _ _ _ _ _ _ Hrem'1 with "SB") as (act e_slot) "[% SB]".

  destruct act; last first.
  { (* Slot is not active, get lb of ge from slot list. *)
    iDestruct (epoch_history_snapshot with "ehist ◯ehist_e") as "%Hehist".
    destruct Hehist as (unlinked_auth & Hehist & _).
    apply lookup_lt_Some in Hehist.
    assert (e ≤ ge1) as HLEe_ge1 by lia.
    iDestruct ((slot_infos_get_inactive_lb slot) with "SInfo") as "#◯γe_nums_slot"; [done..|].
    iModIntro. iSplitL "info ptrs ret ehist SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
    { repeat iExists _. iFrame "∗#%". }
    wp_pures.
    iApply ("continue" $! ge1 HLEe_ge1 with "◯γe_nums_slot HΦ").
  }
  (* Slot is active, close invariant. *)
  iModIntro. iSplitL "info ptrs ret ehist SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
  { repeat iExists _. iFrame "∗#%". }
  wp_pures.
  clear dependent info ptrs sbvmap slist2 rL ehist.

  (* Read slot value *)
  wp_bind (! _)%E.
  iInv "IED" as (info ptrs sbvmap slist2 rL ehist)
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist_len & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".
  set ge := length ehist - 1.
  iDestruct (sbs.(SlotBag_prefix) with "SB SL") as %PF2.
  have [slist2' Hslist2] := PF2.
  have {}Hrem'2 : slist2 !! rem' = Some slot.
  { eapply prefix_lookup_Some; [apply Hrem'|done]. }
  wp_apply (sbs.(slot_read_value_spec) $! _ _ _ _ _ _ _ Hrem'2 with "SB") as (b oe) "[% SB]".
  iDestruct (epoch_history_snapshot with "ehist ◯ehist_e") as "%Hehist".
  destruct Hehist as (unlinked_auth & Hehist & _).
  apply lookup_lt_Some in Hehist.
  assert (e ≤ ge) as HLEe_ge2 by lia.

  destruct oe as [e'|]; last first.
  { (* Not validated slot, get lb of ge from slot list *)
    iDestruct ((slot_infos_get_not_validated_lb slot) with "SInfo") as "#◯γe_nums_slot"; [done..|].

    iModIntro. iSplitL "info ptrs ret ehist SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
    { repeat iExists _. iFrame "∗#%". }
    wp_pures.
    iApply ("continue" $! ge HLEe_ge2 with "◯γe_nums_slot HΦ").
  }

  (* Possibly validated slot, case analysis on value. *)
  destruct (decide (e' = e)) as [->|NE]; last first.
  { (* Slot is not equal, return false. *)
    iModIntro. iSplitL "info ptrs ret ehist SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
    { repeat iExists _. iFrame "∗#%". }
    wp_pures.
    case_bool_decide; last lia.
    wp_pures.
    rewrite bool_decide_eq_false_2; [|injection as ?;lia].
    wp_pures. iModIntro. iApply "HΦ". iFrame "#".
  }
  (* Slot value is equal. Get LB on slot value. *)
  iDestruct ((slot_infos_get_possibly_validated_lb slot) with "SInfo") as "#◯γe_nums_slot"; [done..|].
  iModIntro. iSplitL "info ptrs ret ehist SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
  { repeat iExists _. iFrame "∗#%". }
  wp_pures.
  case_bool_decide; last lia.
  wp_pures.
  rewrite bool_decide_eq_true_2; last done.
  wp_pures.
  by iApply ("continue" with "[] [$◯γe_nums_slot] [$HΦ]").
Qed.

Lemma try_advance_spec γsb γtok γinfo γptrs γeh γrs γU γV γR γe_nums (d lBag rList : loc) E  :
  ↑(to_baseN mgmtN) ⊆ E →
  {{{ (d +ₗ domLBag) ↦□ #lBag ∗ (d +ₗ domRSet) ↦□ #rList ∗
    inv ebrInvN (EBRDomain γsb γtok γinfo γptrs γeh γrs γU γV γR γe_nums d lBag
     rList) }}}
    try_advance #d @ E
  {{{ (ge : nat) unlinked, RET #ge; epoch_history_snap γeh ge unlinked }}}.
Proof.
  intros ?. iIntros (Φ) "#(d.lBag↦ & d.rSet↦ & IED) HΦ".
  wp_lam. wp_pures.
  wp_bind (!_)%E.
  iInv "IED" as (info ptrs sbvmap slist rL ehist)
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist_len & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".
  set ge := length ehist - 1.
  have [unlinked Hge] : (is_Some (ehist !! ge)).
  { apply lookup_lt_is_Some_2. lia. }
  iMod (epoch_history_snapshot_get ge with "ehist") as "[ehist #◯ehist]"; [done|].
  wp_load.
  iModIntro. iSplitL "info ptrs ret ehist SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
  { repeat iExists _. iFrame "∗#%". }
  clear dependent info ptrs sbvmap slist rL.
  wp_pures. wp_load. wp_let.
  wp_apply (may_advance_spec with "[$IED $◯ehist]") as (b) "#◯γe_nums_ge"; [done..|].
  destruct b; last first.
  { wp_pures. iApply ("HΦ" with "◯ehist"). }
  wp_pures. wp_bind (CmpXchg _ _ _)%E.
  (* Open invariant and see If [ge] is still the same. *)
  iInv "IED" as (info ptrs sbvmap slist rL ehist')
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist_len' & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".
  set ge' := length ehist' - 1.
  destruct (decide (ge' = ge)) as [EQ|NE].
  - (* Same, so I am the one updating the global epoch. *)
    (* EQ is intentionally as we may need ge' := length ehist' *)
    iClear "◯ehist". rewrite EQ.
    assert (length ehist' = length ehist) as LenEQ by lia.
    wp_cmpxchg_suc.
    (** Update resources. *)

    (* Get the unlinked history *)
    have [u_ge Hu_ge] : is_Some (ehist' !! (ge - 2)).
    { apply lookup_lt_is_Some_2. lia. }
    set ehistF := take (ge - 2) ehist'.
    set finalized := fold_hist ehistF.

    (* Common facts relating history *)
    assert (take (ge + 1 - 2) ehist' = take (ge - 2) ehist' ++ [u_ge]) as HistDiff.
    { apply list_eq. intros i. destruct (decide (i < ge - 2)) as [LT|GE].
      - rewrite lookup_app_l; [|rewrite take_length; lia].
        rewrite !lookup_take; [done|lia..].
      - rewrite lookup_app_r; [|rewrite take_length; lia].
        destruct (decide (i = ge - 2)) as [->|NE].
        + rewrite take_length_le; [|lia]. rewrite lookup_take; [|lia].
          assert (ge - 2 - (ge - 2) = 0) as -> by lia. by simplify_option_eq.
        + rewrite lookup_take_ge; [|lia]. rewrite lookup_ge_None_2; [done|].
          rewrite take_length /=. lia.
    }
    assert (length (ehist' ++ [∅]) - 1 - 1 = ge) as Len_ge2.
    { rewrite app_length /=. lia. }
    assert (length (ehist' ++ [∅]) - 1 = ge + 1) as Len_ge2_1.
    { rewrite app_length /=. lia. }

    (* Update epoch history and SlotInfos, getting new finalized tokens *)
    iAssert (|={E ∖ ↑ebrInvN}=>
      epoch_history_auth γeh ehist' ∗
      SlotInfos γV γtok γeh γe_nums slist sbvmap (ehist' ++ [∅]) ∗
      toks γtok (gset_to_coPset (u_ge ∖ finalized)) ⊤
    )%I with "[SInfo ehist]" as ">(ehist & SInfo & toks)".
    { (* Update [SInfo], from [ge] to [ge + 1] *)
      (* Non-Validated: Update [●γe_nums] *)
      (* Validated: Nothing to do. *)
      (* BaseManaged lb: we already have it. *)
      unfold SlotInfos.
      rewrite Len_ge2 Len_ge2_1. iFrame "#".
      iDestruct "SInfo" as "(_ & ●γe_nums_from & toks & SInfo)".
      iMod (mono_nats_auth_update_plus 1 with "●γe_nums_from") as "[●γe_nums_from _]".
      rewrite LenEQ. iFrame "●γe_nums_from".
      rewrite !take_app_le; [|lia..].
      rewrite HistDiff fold_hist_snoc.
      fold ehistF. unfold toks.

      (* get [⊤ ∖ gset_to_coPset ((fold_hist ehistF) ∪ u_ge)] from [toks] *)
      assert (⊤ ∖ gset_to_coPset (fold_hist ehistF ∪ u_ge)
              ⊆ ⊤ ∖ gset_to_coPset (fold_hist ehistF)) as Sub_ehsitF.
      { rewrite -disjoint_complement. symmetry.
        rewrite disjoint_subset -gset_to_coPset_subset. set_solver.
      }

      (* Simplifying difference of tokens. *)
      assert (⊤ ∖ gset_to_coPset (fold_hist ehistF)
        ∖ (⊤ ∖ gset_to_coPset (fold_hist ehistF ∪ u_ge))
        = gset_to_coPset (u_ge ∖ finalized))
      as TopDiffDiag.
      { rewrite top_difference_diag -gset_to_coPset_difference. f_equal. set_solver. }

      rewrite token2_get_subset_1; [iDestruct "toks" as "[$ toks]"|done].
      rewrite TopDiffDiag.

      iEval (rewrite -{7}(sids_to_sids_from_union (length slist))).
      rewrite -token2_union_2; [|apply sids_to_sids_from_disjoint].
      iFrame "toks".

      iInduction slist as [|slot slist] "IH" using rev_ind.
      { simpl. rewrite sids_to_0. iFrame. iApply token2_get_empty_2. }
      rewrite !big_sepL_snoc.
      iDestruct "SInfo" as "[SInfo slot]".
      iMod ("IH" with "SInfo ehist") as "{IH} (ehist & $ & toks)".
      rewrite app_length !Nat.add_1_r sids_to_S.
      rewrite -token2_union_2; [|apply sids_to_sid_disjoint; lia].
      iFrame "toks".
      destruct (sbvmap !! slot) as [[b oe]|]; last done.
      destruct b; last first.
      { iDestruct "slot" as "(toks & $ & ●γe_nums)".
        iMod (mono_nats_auth_update_plus 1 with "●γe_nums") as "[●γe_nums _]".
        rewrite Nat.add_1_r. iFrame.
        rewrite token2_get_subset_1; [iDestruct "toks" as "[$ toks]"|done].
        rewrite TopDiffDiag. done.
      }
      destruct oe as [e|]; last first.
      { iDestruct "slot" as "(toks & $ & ●γe_nums)".
        iMod (mono_nats_auth_update_plus 1 with "●γe_nums") as "[●γe_nums _]".
        rewrite Nat.add_1_r. iFrame.
        rewrite token2_get_subset_1; [iDestruct "toks" as "[$ toks]"|done].
        rewrite TopDiffDiag. done.
      }
      iDestruct "slot" as (V) "($ & γV & slot)".
      rewrite  bi.sep_exist_r bi.sep_exist_l. iExists V. iFrame "γV".
      destruct V; last first.
      { iDestruct "slot" as "[toks ●γe_nums]".
        iMod (mono_nats_auth_update_plus 1 with "●γe_nums") as "[●γe_nums _]".
        rewrite Nat.add_1_r. iFrame.
        rewrite token2_get_subset_1; [iDestruct "toks" as "[$ toks]"|done].
        rewrite TopDiffDiag. done.
      }
      iModIntro. iDestruct "slot" as (ehistF') "(%HehsitF' & #◯ehistF' & toks & ●γe_nums)".
      rewrite bi.sep_exist_r bi.sep_exist_l. iExists ehistF'.
      iFrame "#%".
      iDestruct (mono_nats_auth_lb_valid with "●γe_nums ◯γe_nums_ge") as %ge2_LE_e; [set_solver|].
      iDestruct (epoch_history_prefix_strong with "ehist ◯ehistF'") as %PF; [lia|].
      iDestruct (epoch_history_le_strong with "ehist ◯ehistF'") as %LE_ehistF'; [lia|].
      iFrame.
      assert (e = ge) as -> by lia.
      assert (ehistF' = take (length ehist' - 2) ehist') as ->.
      { apply prefix_length_eq; [|done]. rewrite take_length_le; lia. }

      rewrite token2_get_subset_1.
      { iDestruct "toks" as "[$ toks]". rewrite -!gset_to_coPset_difference.
        rewrite difference_diag.
        - rewrite union_comm_L. fold ge ehistF finalized.
          rewrite difference_union_distr_l_L difference_diag_L union_empty_r_L. iFrame.
        - apply fold_hist_prefix, take_prefix_le. lia.
        - apply union_least.
          + apply fold_hist_prefix, take_prefix_le. lia.
          + apply (ehist_elem_in_fold_hist _ (ge -2)).
            rewrite lookup_take; [done|lia].
      }
      rewrite -!gset_to_coPset_difference -gset_to_coPset_subset.
      apply difference_mono_l. set_solver.
    }
    (* Update [ehist], by appending [∅]. *)
    iMod ((epoch_history_advance ehist' ∅) with "ehist") as "[ehist ◯ehist]"; [lia|].
    assert (length ehist' = ge + 1) as -> by lia.
    iAssert (|={E ∖ ↑ebrInvN}=>
      GhostEpochInformations γV γeh γe_nums (ge + 1) slist sbvmap
    )%I with "[EInfo ◯ehist]" as ">EInfo".
    { (* Update [EInfos], from [ge] to [ge + 1] *)
      iDestruct "EInfo" as "(GE_2_et_al & GE_1 & GE_0 & #sbvmap & γV_to_ge & γV_from_ge)".
      unfold GhostEpochInformations. iFrame "#".
      (* [GE_minus_1] -> [GE_minus_2_et_al] *)
      iSplitL "GE_2_et_al GE_1".
      { unfold GE_minus_2_et_al, GE_minus.
        assert (ge + 1 - 1 = ge - 1 + 1) as -> by lia.
        rewrite seq_app big_sepL_snoc.
        iFrame.
        rewrite !Nat.add_1_r !sids_to_S.
        rewrite -!ghost_vars2_union_1; [|apply sids_to_sid_disjoint; lia..].
        iDestruct "GE_1" as "($ & ◯γeh & Slots)".
        iDestruct "GE_2_et_al" as "($ & $ & $)".
        iInduction slist as [|slot slist] "IH" using rev_ind.
        { simpl. rewrite !sids_to_0 sids_from'_0. iFrame. iApply ghost_vars2_get_empty_2. }
        rewrite !big_sepL_snoc. iDestruct "Slots" as "[Slots slot]".
        rewrite app_length Nat.add_1_r sids_to_S.
        rewrite -!ghost_vars2_union_2; [|by apply sids_to_sid_disjoint..].
        iDestruct "slot" as (b v V) "(%Hslot & γV & %HV & slot)".
        (* Preform case analysis on [V] and show that it must be false. *)
        destruct V.
        { iDestruct (mono_nats_auth_lb_valid with "slot ◯γe_nums_ge") as %?; [set_solver|lia]. }
        iFrame.
        iCombine "◯γeh slot" as "◯γeh".
        rewrite epoch_history_frag_union; [|apply sids_from'_sid_disjoint; lia].
        rewrite -sids_from'_S.
        iDestruct "sbvmap" as "[sbvmap _]".
        iApply ("IH" with "sbvmap ◯γeh Slots").
      }
      (* [GE_minus_0] -> [GE_minus_1] *)
      iSplitL "GE_0". { by rewrite Nat.add_sub. }
      unfold GE_minus.
      rewrite !Nat.add_1_r sids_from_S.
      rewrite -!ghost_vars2_union_1; [|apply sids_from_sid_disjoint; lia..].
      iDestruct "γV_to_ge" as "[$ γV_to]".
      iDestruct "γV_from_ge" as "[$ $]".
      iInduction slist as [|slot slist] "IH" using rev_ind.
      { rewrite sids_from'_0. by iFrame. }
      rewrite app_length Nat.add_1_r sids_to_S.
      rewrite -!ghost_vars2_union_2; [|apply sids_to_sid_disjoint; lia..].
      rewrite !big_sepL_snoc.
      iDestruct "sbvmap" as "[sbvmap %sbvmap_slot]".
      destruct sbvmap_slot as (b & v & svbmap_slot).
      iDestruct "γV_to" as "[γV γV_sid]".
      iSpecialize ("IH" with "sbvmap γV ◯ehist").
      iMod "IH" as "(◯γeh & $)".
      iEval (rewrite comm).
      do 3 (iEval (rewrite bi.sep_exist_r); iExists _).
      iFrame. iModIntro.
      rewrite (sids_from'_S (length slist)).
      rewrite -epoch_history_frag_union; [|apply sids_from'_sid_disjoint; lia].
      iDestruct "◯γeh" as "[$ $]".
      iPureIntro. split; [done|inversion 1].
    }

    iAssert (UnlinkFlags γU info (ehist' ++ [∅]))%I with "[γU]" as "γU".
    { unfold UnlinkFlags. by rewrite fold_hist_app /= !union_empty_r_L. }
    (* Get new snapshot *)
    iMod ((epoch_history_snapshot_get (ge + 1)) with "ehist") as "[ehist #◯ehist1]".
    { unfold ge. rewrite Nat.sub_add; [|lia]. rewrite -LenEQ snoc_lookup. done. }
    (* Updated [Recl] *)
    iAssert(ReclaimInfo γR γtok (ehist' ++ [∅]) info)%I
      with "[Recl toks]" as "Recl".
    { unfold ReclaimInfo.
      iDestruct "Recl" as (reclaimed) "(γR_recl & γR_alive & γR_not_created & toksR)".
      iExists reclaimed. iFrame.
      rewrite Len_ge2_1 !take_app_le; [|lia..].
      rewrite HistDiff fold_hist_snoc.
      fold ehistF. unfold toks, finalized.
      iDestruct (token2_valid_1 with "toksR toks") as %Disj; [done|].
      iCombine "toksR toks" as "toks".
      rewrite token2_union_1; [|done].
      rewrite token2_get_subset_1; [iDestruct "toks" as "[$ _]"|].
      rewrite -!gset_to_coPset_difference -gset_to_coPset_union
          -gset_to_coPset_subset.
      rewrite LenEQ.
      apply union_differnce_subst_difference_union.
    }
    iModIntro.
    rewrite !Z.add_1_r !Nat.add_1_r -!Nat2Z.inj_succ.
    iSplitL "info ptrs ehist ret SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
    { repeat iExists _. iFrame "∗#%".
      rewrite fold_hist_snoc /= !union_empty_r_L. iFrame.
      rewrite Len_ge2_1 Nat.add_1_r /=.
      iNext. iFrame "∗". iPureIntro. split_and!; auto.
      subst ge. rewrite -LenEQ take_app_le; [|lia].
      intros i p Hi Hinfo_i.
      apply HPtrs; [|exact Hinfo_i].
      specialize (fold_hist_prefix (take (length ehist' - 1 - 2) ehist') (take (length ehist' - 1 - 1) ehist')
                                    ltac:(apply take_prefix_le; lia)) as SubTake.
      set_solver.
    }
    wp_pures. iApply ("HΦ" with "◯ehist1").
  - (* Different, so another thread has updated the global epoch.*)
    (* Return the updated value value and a snapshot of it *)
    wp_cmpxchg_fail.
    have [unlinked_ge' ?] : is_Some (ehist' !! ge').
    { apply lookup_lt_is_Some. lia. }
    iMod (epoch_history_snapshot_get ge' with "ehist") as "[ehist #◯ehist']"; [done|].
    iSplitL "info ptrs ret ehist SB RL EInfo SInfo γU d.ge↦ Reg Recl Ret".
    { repeat iExists _. by iFrame "∗#%". }
    iModIntro. wp_pures. iApply ("HΦ" with "◯ehist'").
Qed.

Lemma rcu_domain_do_reclamation_spec :
  rcu_domain_do_reclamation_spec' mgmtN ptrsN ebr_domain_do_reclamation IsEBRDomain.
Proof.
  intros ????.
  iIntros "#IED" (Φ) "!> _ HΦ".
  iDestruct "IED" as (??????????) "(%&%& %Hγe & d.l↦ & d.r↦ & IED)".
  wp_lam.
  wp_apply (try_advance_spec with "[$d.l↦ $d.r↦ $IED]") as (ge_b unlinked_ge) "#◯γeh_ge"; [solve_ndisj|done..|].
  wp_pures. wp_load. wp_let.
  awp_apply rls.(retired_list_pop_all_spec) without "HΦ".
  iInv "IED" as (info ptrs sbvmap slist rL1 ehist)
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist_len & >d.ge↦ & >Reg & >Recl & Ret & >%HInfo & >%HPtrs)".
  iAaccIntro with "RL".
  { iIntros "RL !>". iSplit; [|done]. repeat iExists _. iFrame "∗#%". }
  iIntros (rNode1) "[RL RNs]".
  iModIntro. iSplitL "info ptrs ret ehist SB RL EInfo SInfo γU d.ge↦ Reg Recl".
  { repeat iExists _. iFrame "RL". iFrame "∗#%". rewrite big_sepL_nil. done. }
  clear dependent info ptrs sbvmap slist ehist.
  iIntros "_ HΦ". wp_let.
  (* loop *)
  iLöb as "IH" forall (rNode1 rL1).
  wp_lam. wp_pures.
  destruct rNode1 as [rNode1|]; simpl; last first.
  { wp_pures. iApply "HΦ". done. }
  wp_if.
  iDestruct (rls.(retired_nodes_cons) with "RNs") as
    (r1 rs1' next1 size1 epoch1) "[-> [RN RNs]]".
  simpl. iDestruct "Ret" as "[Ret_r Ret]".
  wp_apply (rls.(retired_node_ptr_spec) with "RN") as "RN".
  wp_let.
  wp_apply (rls.(retired_node_epoch_spec) with "RN") as "RN".
  wp_let.
  wp_apply (rls.(retired_node_next_spec) with "RN") as "RN".
  wp_pures.

  case_bool_decide as Hepoch1.
  - (* Not ready to be retired *)
    wp_if. awp_apply (retired_list_push_spec with "RN") without "HΦ RNs".
    iInv "IED" as (info ptrs sbvmap slist rL2 ehist)
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist_len & >d.ge↦ & >Reg & >Recl & Ret' & >%HInfo & >%HPtrs)".
    iAaccIntro with "RL".
    { iIntros "? !>". iFrame "Ret Ret_r". repeat iExists _. iFrame "∗#%". }
    iIntros "RL". iModIntro.
    iSplitL "info ptrs ehist ret SB EInfo SInfo γU d.ge↦ Reg Recl RL Ret_r Ret'".
    { repeat iExists _. iFrame "RL". iFrame "∗#%". }
    iIntros "_ (HΦ & RN)". wp_seq.
    iApply ("IH" with "Ret RN HΦ").
  - (* Retire the Node *)
    wp_if. wp_apply (rls.(retired_node_size_spec) with "RN") as "RN".
    wp_let.
    iDestruct "Ret_r" as (i R unlinked_e) "(Recl & #◯ehist & %i_in_unlinked_e)".
    iDestruct "Recl" as (?) "(Gcinv & #i↪γinfo & r1↪γptrs & #Ex & #CInv_i & γU_i & γR)".
    wp_bind (Free _ _)%E.
    iInv "IED" as (info ptrs sbvmap slist rL2 ehist)
      "(>info & >ptrs & >ehist & >ret & >SB & >RL & >EInfo & >SInfo & >γU & >%Hdom_i & >%Hehist_len & >d.ge↦ & >Reg & >Recl & Ret' & >%HInfo & >%HPtrs)".
    set ge := length ehist -1.
    iDestruct (coP_ghost_map_lookup with "ptrs r1↪γptrs") as %Hr1.
    iDestruct (big_sepM_delete with "Reg") as "[Regr1 Reg]"; eauto.
    iDestruct ("Regr1") as (?) "[%Hi †r1]".

    iAssert (⌜epoch1 + 3 ≤ ge⌝)%I with "[ehist]" as %Hepoch1_ge.
    { iDestruct (epoch_history_snapshot with "ehist ◯γeh_ge") as %Hge.
      destruct Hge as [? [Hge _]].
      apply lookup_lt_Some in Hge. iPureIntro. unfold ge. lia.
    }

    iDestruct "Recl" as (reclaimed) "(●R1 & ●R2 & ●R3 & T)".

    (* cancel CInv in order to free *)
    iDestruct (epoch_history_snapshot with "ehist ◯ehist") as (uae) "[%Huae %Huesub]".
    assert (
      i ∈ gset_to_coPset (fold_hist (take (length ehist - 1 - 2) ehist))
    ) as i_in_ftl.
    { rewrite elem_of_gset_to_coPset elem_of_fold_hist.
      exists epoch1, uae. split; last set_solver.
      rewrite lookup_take; auto. lia.
    }
    destruct (decide (i ∈ gset_to_coPset reclaimed)).
    { iDestruct (ghost_vars2_agree with "γR ●R1") as %V; [set_solver..|done]. }
    rewrite (toks_delete_1 _ _ _ {[i]}); last set_solver.
    iDestruct "T" as "[T Ti]".
    iMod (exchange_toks_give_all with "Ex Ti") as "[rei cinv]"; [solve_ndisj|].
    iCombine "Gcinv cinv" as "cinv".
    rewrite -coP_cinv_own_fractional; last set_solver.
    rewrite -top_complement_singleton.
    iMod (coP_cinv_cancel with "CInv_i cinv") as "P"; [solve_ndisj|].
      iDestruct "P" as (?) "(><- & R & >r1↦)".
    iDestruct (ghost_map_lookup with "info i↪γinfo") as %Hi'.
      rewrite Hi in Hi'. injection Hi' as [= ->]. simpl.

    (* update γR *)
    iDestruct (coP_ghost_map_elem_combine with "r1↪γptrs rei") as "[ri _]".
    rewrite -top_complement_singleton.
    iDestruct (ghost_vars2_delete_1 _ i with "●R2") as "[γR' ●R2]".
    { rewrite gset_to_coPset_difference elem_of_difference. split; auto.
      by rewrite elem_of_gset_to_coPset elem_of_dom.
    }
    iMod (ghost_vars2_update_halves' true with "γR γR'") as "[γR γR']".

    wp_free.

    iMod (coP_ghost_map_delete with "ptrs ri") as "ptrs".

    (* close *)
    iModIntro. iSplitL "info ptrs ehist ret SB RL EInfo SInfo γU d.ge↦ Reg Ret'
      ●R1 ●R2 ●R3 γR' T".
    { repeat iExists _. iFrame. iNext. repeat iSplit; auto.
      - iExists (reclaimed ∪ {[i]}).
        rewrite elem_of_gset_to_coPset in n.
        rewrite gset_to_coPset_union.
        rewrite -ghost_vars2_union_1; last first.
        { apply gset_to_coPset_disjoint. set_solver. }
        rewrite !gset_to_coPset_difference gset_to_coPset_union -!gset_to_coPset_singleton .
        rewrite !difference_union_difference.
        iFrame.
      - iPureIntro. intros p' i' Hp'. apply lookup_delete_Some in Hp' as [Hr1p Hp'].
        by apply HInfo in Hp'.
      - iPureIntro. intros i' p' Hi' [[[? size_i'] γc_i'] [Hp' [= ->]]].
        specialize (HPtrs i' p' Hi'
                    ltac:(exists ({| addr := p'; len := size_i'|},γc_i'); naive_solver)).
        destruct (decide (r1 = p')) as [->|NE]; last first.
        { rewrite lookup_delete_Some. done. }
        assert (i = i') as ->; last first.
        { apply elem_of_gset_to_coPset in i_in_ftl. set_solver. }
        naive_solver.
    }
    wp_seq.
    wp_apply (rls.(retired_node_drop_spec) with "RN") as "_".
    wp_seq. iApply ("IH" with "Ret RNs HΦ").
  Qed.

End ebr.

#[export] Typeclasses Opaque EBRAuth BaseManaged BaseInactive BaseGuard BaseNodeInfo.
