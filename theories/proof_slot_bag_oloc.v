From iris.base_logic Require Export lib.invariants lib.ghost_map.
From smr.program_logic Require Import atomic.
From smr Require Import helpers.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.
From smr.base_logic Require Export lib.mono_list.

From smr Require Import spec_slot_bag_oloc code_slot_bag_oloc.

Set Printing Projections.

Class slot_bag_olocG Σ := SlotBagoLocG {
  slot_bag_oloc_ghost_mapG :> ghost_mapG Σ loc (bool * (option blk));
  slot_bag_oloc_mono_listG :> mono_listG loc Σ;
}.

Definition slot_bag_olocΣ : gFunctors := #[ ghost_mapΣ loc (bool * (option blk)); mono_listΣ loc].

Global Instance subG_slot_bag_olocΣ {Σ} :
  subG slot_bag_olocΣ Σ → slot_bag_olocG Σ.
Proof. solve_inG. Qed.

Section slot_bag.
Context `{!heapGS Σ, !slot_bag_olocG Σ}.
Notation iProp := (iProp Σ).

Implicit Types
  (γsb γm γxs : gname)
  (xs : list loc)
  (sbvmap : gmap loc (bool * (option blk))).

(* domain relation *)

Definition domain_of xs sbvmap :=
  ∀ slot, slot ∈ xs ↔ is_Some (sbvmap !! slot).

(* physical contents *)

Definition slot_phys slot (b : bool) (v : option blk) : iProp :=
  (slot +ₗ slotActive) ↦{# if b then (1/2)%Qp else 1%Qp } #b ∗
  (slot +ₗ slotValue) ↦{# if b then (1/2)%Qp else 1%Qp } #(oblk_to_lit v) ∗
  ⌜if (negb b) then v = None else True⌝.

Fixpoint phys_list_rec xs : iProp :=
  match xs with
  | [] => True
  | slot :: xs =>
     (slot +ₗ slotNext) ↦□ #(oloc_to_lit (head xs)) ∗
     phys_list_rec xs
  end.

Definition phys_list xs : iProp := phys_list_rec (reverse xs).

Definition phys_map xs sbvmap : iProp :=
  phys_list xs ∗
  ([∗ map] slot ↦ bv ∈ sbvmap, slot_phys slot (bv.1) (bv.2)) ∗
  ⌜domain_of xs sbvmap⌝.

Definition ghost_slot_bag γm sbvmap : iProp :=
  ghost_map_auth γm 1 sbvmap ∗
  ([∗ map] slot ↦ bv ∈ sbvmap,
    if decide (sbvmap !! slot = Some (false, None))
    then slot ↪[γm] (false, None) else True).

(* slot and bag definitions *)

Definition Slot γsb (slot : loc) (idx : nat) (v : option blk) : iProp :=
  ∃ γm γxs,
    ⌜γsb = encode (γm, γxs)⌝ ∗
    (slot +ₗ slotActive) ↦{# 1/2} #true ∗
    (slot +ₗ slotValue) ↦{# 1/2} #(oblk_to_lit v) ∗
    slot ↪[γm] (true, v) ∗
    mono_list_idx_own γxs idx slot.

Definition SlotBag γsb (slotBag : loc) sbvmap xs : iProp :=
  ∃ γm γxs,
    ⌜γsb = encode (γm, γxs)⌝ ∗
    (slotBag +ₗ slotBagHead) ↦ #(oloc_to_lit (last xs)) ∗
    phys_map xs sbvmap ∗
    ghost_slot_bag γm sbvmap ∗
    mono_list_auth_own γxs 1 xs.

Definition SlotList γsb xs : iProp :=
  ∃ γm γxs,
    ⌜γsb = encode (γm, γxs)⌝ ∗
    mono_list_lb_own γxs xs.

Fixpoint seq_bag_list (hd : base_lit) (vs : list (option blk)) : iProp :=
  match vs with
  | [] => ⌜hd = NULL⌝
  | v :: vs =>
     ∃ (l : loc) (hd' : base_lit), ⌜hd = LitLoc l⌝ ∗
     (l +ₗ seqNodeValue) ↦ #(oblk_to_lit v) ∗
     (l +ₗ seqNodeNext) ↦ #hd' ∗
     seq_bag_list hd' vs
  end.

Definition SeqBag (seqBag : loc) (vs : list (option blk)) : iProp :=
  ∃ (hd : base_lit),
  (seqBag +ₗ seqHead) ↦ #hd ∗
  seq_bag_list hd vs.

(* Typeclass Instances *)
Global Instance Slot_TimeLess γsb slot idx v : Timeless (Slot γsb slot idx v).
Proof. apply _. Qed.

Global Instance ghost_slot_bag_timeless γm sbvmap : Timeless (ghost_slot_bag γm sbvmap).
Proof.
  apply bi.sep_timeless; first apply _.
  apply big_sepM_timeless. intros.
  case_decide; apply _.
Qed.

Global Instance phys_list_rec_timeless xs : Timeless (phys_list_rec xs).
Proof. induction xs; apply _. Qed.
Global Instance phys_list_rec_persistent xs : Persistent (phys_list_rec xs).
Proof. induction xs; apply _. Qed.
Global Instance phys_list_persistent xs : Persistent (phys_list xs).
Proof. apply _. Qed.
Global Instance phys_list_timeless xs : Timeless (phys_list xs).
Proof. apply _. Qed.

Global Instance SlotBag_TimeLess γsb slotbag sbvmap slist : Timeless (SlotBag γsb slotbag sbvmap slist).
Proof. apply _. Qed.

Global Instance SlotList_Persistent γsb slist : Persistent (SlotList γsb slist).
Proof. apply _. Qed.


(* domain lemmas *)

Lemma elem_of_domain_neg xs sbvmap slot :
  (slot ∈ xs ↔ is_Some (sbvmap !! slot)) ↔
  (slot ∉ xs ↔ sbvmap !! slot = None).
Proof.
  split; split; unfold not; intros.
  - destruct (sbvmap !! slot); naive_solver.
  - rewrite H H0 in H1. by destruct H1.
  - destruct (sbvmap !! slot); naive_solver.
  - destruct (decide (slot ∈ xs)); auto.
    apply H in n. rewrite n in H0. by destruct H0.
Qed.

Lemma domain_of_snoc xs sbvmap slot :
  domain_of (xs ++ [slot]) sbvmap → slot ∉ xs →
  domain_of xs (delete slot sbvmap).
Proof.
  intros. intros slot'.
  destruct (decide (slot = slot')).
  - subst. apply elem_of_domain_neg. by simpl_map.
  - specialize (H slot'). simpl_map.
    rewrite <- H, elem_of_snoc. naive_solver.
Qed.

Lemma domain_of_insert xs sbvmap slot st :
  domain_of xs sbvmap →
  domain_of (xs ++ [slot]) (<[slot:=st]> sbvmap).
Proof.
  intros. intros slot'.
  destruct (decide (slot = slot')).
  - subst. simpl_map. rewrite elem_of_snoc. naive_solver.
  - specialize (H slot'). simpl_map.
    rewrite <- H, elem_of_snoc. naive_solver.
Qed.

Lemma domain_of_undelete xs sbvmap slot :
  domain_of xs (delete slot sbvmap) →
  is_Some (sbvmap !! slot) →
  domain_of (xs ++ [slot]) sbvmap.
Proof.
  intros. intros slot'.
  destruct (decide (slot = slot')).
  - subst. rewrite elem_of_snoc. naive_solver.
  - specialize (H slot'). simpl_map.
    rewrite <- H, elem_of_snoc. naive_solver.
Qed.

Lemma domain_of_update xs sbvmap slot st :
  domain_of xs sbvmap →
  is_Some (sbvmap !! slot) →
  domain_of xs (<[slot:=st]> sbvmap).
Proof.
  intros. intros slot'.
  apply H in H0. destruct (decide (slot = slot')).
  - subst. simpl_map. naive_solver.
  - by simpl_map.
Qed.

(* phys list/map lemmas *)

Lemma phys_list_snoc xs slot :
  phys_list (xs ++ [slot]) ⊣⊢
    (slot +ₗ slotNext) ↦□ #(oloc_to_lit (last xs)) ∗
    phys_list xs.
Proof.
  unfold phys_list. rewrite reverse_snoc. simpl.
  by rewrite head_reverse.
Qed.

Lemma phys_list_prefix xs xs' :
  xs' `prefix_of` xs → phys_list xs -∗ phys_list xs'.
Proof.
  assert (∀ xs xs',
    xs' `suffix_of` xs → phys_list_rec xs -∗ phys_list_rec xs');
    last first.
  { rewrite prefix_suffix_reverse. apply H. }
  clear xs xs'.
  intros. induction xs; iIntros "Lphys".
  { apply suffix_nil_inv in H. by subst. }
  destruct xs'; auto.
  apply suffix_cons_inv in H as [H|H].
  - by rewrite H.
  - iDestruct "Lphys" as "[Lhd Lphys]".
    iApply (IHxs with "[Lphys]"); auto.
Qed.

Lemma phys_list_agree xs xs' :
  last xs = last xs' → phys_list xs -∗ phys_list xs' -∗ ⌜xs = xs'⌝.
Proof.
  revert xs'.
  induction xs using rev_ind; iIntros (xs' Lhd) "#Lphys #Lphys'";
    destruct (rev_des xs') as [|[x' [l' H']]]; subst; auto.
  { by rewrite last_snoc in Lhd. }
  { by rewrite last_snoc in Lhd. }
  do 2 rewrite last_snoc in Lhd. injection Lhd as ->.
  iDestruct (phys_list_snoc with "Lphys") as "[Lhdx Lphysx]".
  iDestruct (phys_list_snoc with "Lphys'") as "[Lhdx' Lphysx']".
  iDestruct (mapsto_agree with "Lhdx Lhdx'") as %[= ?].
  iDestruct (IHxs with "Lphysx Lphysx'") as %->; auto.
Qed.

Lemma phys_list_NoDup xs :
  phys_list xs -∗ ⌜NoDup xs⌝.
Proof.
  induction xs using rev_ind; iIntros "#Lphys".
  { iPureIntro. by apply NoDup_nil. }
  iDestruct (phys_list_snoc with "Lphys") as "[_ Lphys']".
  iDestruct (IHxs with "Lphys'") as %LND.
  destruct (decide (x ∈ xs)); last first.
  { iPureIntro. by apply NoDup_snoc. }

  (* if a ∉ xs, derive contradiction due to cycle *)
  apply elem_of_list_lookup in e as [i Hia].
  iDestruct (phys_list_prefix xs (take (S i) xs) with "Lphys'") as
    "#Lphysd". { apply take_prefix. }
  iDestruct (phys_list_agree (xs++[x]) (take (S i) xs) with "[] []") as "%"; auto.
    { rewrite take_last; auto. rewrite Hia. apply last_snoc. }
  assert (length (xs ++ [x]) > length (take (S i) xs)).
  { rewrite take_length snoc_length. lia. }
  rewrite H in H0; lia.
Qed.

Lemma phys_map_snoc slot xs sbvmap :
  phys_map (xs ++ [slot]) sbvmap -∗
  phys_list (xs ++ [slot]) ∗
  phys_map xs (delete slot sbvmap) ∗
  ∃ act v, slot_phys slot act v ∗ ⌜sbvmap !! slot = Some (act, v)⌝.
Proof.
  iIntros "Mphys";
    iDestruct "Mphys" as "(#Lphys & Ms & %Mdom)".
  iDestruct (phys_list_NoDup with "Lphys") as %LND.
  iDestruct (phys_list_snoc with "Lphys") as "[_ Lphys']".
  assert (is_Some (sbvmap !! slot)) as [[b v] H].
  { apply Mdom. apply elem_of_snoc; by left. }
  iDestruct (big_sepM_delete _ sbvmap slot (b, v) with "Ms")
    as "[Sphys Ms]"; auto.
  iFrame. repeat iSplit; auto.
  iPureIntro. apply domain_of_snoc; auto.
  by apply NoDup_snoc in LND as [_ LND].
Qed.

Lemma phys_map_undelete slot xs act v sbvmap :
  sbvmap !! slot = Some (act, v) →
  domain_of xs sbvmap →
  phys_list xs -∗
  slot_phys slot act v -∗
  ([∗ map] k↦y ∈ delete slot sbvmap, slot_phys k y.1 y.2) -∗
  phys_map xs sbvmap.
Proof.
  iIntros "%Ml %Mdom Lphys Sphys Ms". iFrame. iSplit; auto.
  iApply big_sepM_delete; first apply Ml. iFrame.
Qed.

Lemma phys_map_insert slot xs act v sbvmap :
  sbvmap !! slot = None →
  phys_map xs sbvmap -∗
  slot_phys slot act v -∗
  (slot +ₗ slotNext) ↦□ #(oloc_to_lit (last xs)) -∗
  phys_map (xs ++ [slot]) (<[slot:=(act, v)]> sbvmap).
Proof.
  iIntros "% Mphys Snxt Sphys";
    iDestruct "Mphys" as "(Lphys & Ms & %Mdom)".
  unfold phys_map. simpl.

  repeat iSplit; auto.
  - iApply phys_list_snoc. iFrame.
  - iApply (big_sepM_delete _ _ slot).
    { apply lookup_insert. }
    rewrite delete_insert_delete delete_notin; auto. iFrame.
  - iPureIntro. by apply domain_of_insert.
Qed.

(* slot lemmas *)

Lemma slot_lookup γsb γm γxs xs l idx v :
  γsb = prod_countable.(encode) (γm, γxs) →
  mono_list_auth_own γxs 1 xs -∗
  Slot γsb l idx v -∗
  ⌜xs !! idx = Some l⌝.
Proof.
  iIntros (H) "●L S".
  iDestruct "S" as (??) "(%&_&_&_&◯i)".
  encode_agree H0.
  iApply (mono_list_auth_idx_lookup with "●L ◯i").
Qed.

(* ghost slot bag lemmas *)

Lemma ghost_slot_bag_lookup γm sbvmap slot v :
  ghost_slot_bag γm sbvmap -∗
  slot ↪[γm] v -∗
  ⌜sbvmap !! slot = Some v⌝.
Proof.
  iIntros "[●Mm _] ●Ms".
  iApply (ghost_map_lookup with "●Mm ●Ms").
Qed.

Lemma ghost_slot_bag_insert v γm sbvmap slot :
  sbvmap !! slot = None →
  ghost_slot_bag γm sbvmap ==∗
  ghost_slot_bag γm (<[slot:=v]> sbvmap) ∗
  if decide (v = (false, None)) then True else slot ↪[γm] v.
Proof.
  iIntros "% [●Mm ●S]".
  iMod (ghost_map_insert slot v with "●Mm") as "[●Mm ●Ms]"; auto.
  iModIntro. iFrame.
  destruct (decide (v = (false, None))).
  - iSplit; auto. iApply big_sepM_insert; auto.
    rewrite lookup_insert; subst; simpl. simplify_option_eq. iFrame.
    iApply big_sepM_mono; last auto; simpl.
    iIntros (k x Hkx) "Dec".
    destruct (decide (k = slot)); subst. { by rewrite H in Hkx. }
    by rewrite lookup_insert_ne.
  - iFrame. iApply big_sepM_insert; auto.
    rewrite lookup_insert decide_False; last naive_solver.
    iSplit; auto. iApply big_sepM_mono; last auto; simpl.
    iIntros (k x Hkx) "Dec".
    destruct (decide (k = slot)); subst. { by rewrite H in Hkx. }
    by rewrite lookup_insert_ne.
Qed.

Lemma ghost_slot_bag_update v' γm sbvmap slot v :
  sbvmap !! slot = Some v →
  (if decide (v = (false, None)) then True else slot ↪[γm] v) -∗
  ghost_slot_bag γm sbvmap ==∗
  ghost_slot_bag γm (<[slot:=v']> sbvmap) ∗
  if decide (v' = (false, None)) then True else slot ↪[γm] v'.
Proof.
  iIntros "%H Decv [●Mm ●S]".
  destruct (decide (v = (false, None))).
  - (* ghost slot is inside the bag *)
    subst.
    iPoseProof (big_sepM_delete _ _ slot with "●S") as "[●Ms ●S]".
    { apply H. }
    rewrite decide_True; auto.
    iMod (ghost_map_update v' with "●Mm ●Ms") as "[●Mm ●Ms]"; auto.
    iModIntro. iFrame.
    destruct (decide (v' = (false, None))).
    + (* put ghost slot back into the bag *)
      subst.
      iPoseProof (big_sepM_insert _ (delete slot sbvmap) slot
        with "[●Ms ●S]") as "●S".
      { by rewrite lookup_delete. }
      { iFrame. by rewrite decide_True. }
      simpl. rewrite insert_delete_insert. iFrame.
      rewrite insert_id; last apply H.
      rewrite insert_id; last apply H. auto.
    + (* leave ghost slot outside the bag *)
      iFrame. rewrite <- insert_delete_insert.
      iApply big_sepM_insert.
      { by rewrite lookup_delete. }
      rewrite lookup_insert.
      rewrite decide_False; last naive_solver. iFrame.
      iApply big_sepM_mono; last auto; simpl.
      iIntros (k x Hkx) "Dec".
      destruct (decide (k = slot)); subst. { by rewrite lookup_delete in Hkx. }
      rewrite lookup_insert_ne; auto.
      by rewrite lookup_delete_ne.
  - (* ghost slot is outside the bag *)
    iMod (ghost_map_update with "●Mm Decv") as "[●Mm ●Ms]"; auto.
    iModIntro. iFrame.
    rewrite <- insert_delete_insert.
    destruct (decide (v' = (false, None))).
    + (* put ghost slot into the bag *)
      subst. iSplit; auto.
      iApply big_sepM_insert. { by rewrite lookup_delete. }
      rewrite decide_True; last by rewrite lookup_insert. iFrame.
      iPoseProof (big_sepM_delete with "●S") as "[_ ●S]";
        first apply H.
      iApply big_sepM_mono; last auto; simpl.
      iIntros (k x Hkx) "Dec".
      destruct (decide (k = slot)); subst. { by rewrite lookup_delete in Hkx. }
      rewrite lookup_insert_ne; auto.
      by rewrite lookup_delete_ne.
    + (* leave ghost slot outside the bag *)
      iFrame. iApply big_sepM_insert. { by rewrite lookup_delete. }
      rewrite decide_False; last first.
      { rewrite lookup_insert. naive_solver. }
      iSplit; auto.
      iPoseProof (big_sepM_delete with "●S") as "[_ ●S]";
        first apply H.
      iApply big_sepM_mono; last auto; simpl.
      iIntros (k x Hkx) "Dec".
      destruct (decide (k = slot)); subst. { by rewrite lookup_delete in Hkx. }
      rewrite lookup_insert_ne; auto.
      by rewrite lookup_delete_ne.
Qed.

(* lookup spec *)

Lemma SlotBag_lookup :
  SlotBag_lookup' Slot SlotBag.
Proof.
  iIntros (???????) "B S".
    iDestruct "B" as (??) "(%Hγ & Bhd & Mphys & ●Mm & ●L)".
    iDestruct "S" as (???) "(Sact & Sv & ●Ms & ◯i)";
    encode_agree Hγ.
  iSplit.
  - iApply (mono_list_auth_idx_lookup with "●L ◯i").
  - iApply (ghost_slot_bag_lookup with "●Mm ●Ms").
Qed.

Lemma SlotBag_prefix :
  SlotBag_prefix' SlotBag SlotList.
Proof.
  iIntros (?????) "B S".
    iDestruct "B" as (??) "(%Hγ & Bhd & Mphys & ●Mm & ●L)".
    iDestruct "S" as (???) "◯L";
    encode_agree Hγ.
  by iDestruct (mono_list_auth_lb_valid with "●L ◯L") as %[_ ?].
Qed.

Lemma SlotBag_NoDup :
  SlotBag_NoDup' SlotBag.
Proof.
  iIntros (????) "B";
    iDestruct "B" as (??) "(%Hγ & Bhd & Mphys & ●Mm & ●L)".
    iDestruct "Mphys" as "(Lphys & _ & _)".
  by iApply phys_list_NoDup.
Qed.

(* slot acquire specs *)

Lemma phys_map_no_slot_xs xs sbvmap slot v :
  phys_map xs sbvmap -∗
  (slot +ₗ 2%nat) ↦ #v -∗
  ⌜slot ∉ xs⌝.
Proof.
  iIntros "Mphys Sv";
    iDestruct "Mphys" as "(Lphys & Ms & %Mdom)".
  destruct (decide (slot ∈ xs)); auto.
  apply Mdom in e as [bv e].
  iDestruct (big_sepM_lookup with "Ms") as "Sphys"; [apply e|].
  iDestruct "Sphys" as "(_ & Sv' & _)".
  iDestruct (mapsto_valid_2 with "Sv Sv'") as %[H ->].
  destruct bv. by destruct b.
Qed.

Lemma phys_map_no_slot_sbvmap xs sbvmap slot v :
  phys_map xs sbvmap -∗
  (slot +ₗ 2%nat) ↦ #v -∗
  ⌜sbvmap !! slot = None⌝.
Proof.
  iIntros "Mphys Sv";
    iDestruct "Mphys" as "(Lphys & Ms & %Mdom)".
  destruct (sbvmap !! slot) eqn:e; auto.
  iDestruct (big_sepM_lookup with "Ms") as "Sphys"; [apply e|].
  iDestruct "Sphys" as "(_ & Sv' & _)".
  iDestruct (mapsto_valid_2 with "Sv Sv'") as %[H ->].
  destruct p. by destruct b.
Qed.

Lemma slot_bag_new_spec :
  slot_bag_new_spec' SlotBag.
Proof.
  iIntros (E Φ). iModIntro.
  iIntros "_ HΦ".
  wp_lam. wp_alloc slotbag as "sb↦" "†sb".
  wp_pures. rewrite loc_add_0 array_singleton. wp_store.
  iMod (ghost_map_alloc_empty) as (γm) "●m".
  iMod (mono_list_own_alloc []) as (γxs) "[●xs _]".
  remember (encode (γm, γxs)) as γsb eqn:Hγsb.
  iAssert (SlotBag γsb slotbag ∅ []) with "[●m ●xs sb↦]" as "SlotBag".
  { repeat iExists _. rewrite loc_add_0. iFrame "∗%".
    unfold phys_map, phys_list, phys_list_rec. rewrite !big_sepM_empty. iSplit; [|done].
    simpl. iPureIntro. split_and!; [done..|]. unfold domain_of.
    intro s. split; intro Empty.
    - inversion Empty.
    - rewrite lookup_empty in Empty. destruct Empty as [? EQ]. inversion EQ. }
  iApply "HΦ". by iFrame.
Qed.

Lemma slot_bag_push_slot_loop_spec :
  ⊢ ∀ γsb (slotBag slot : loc) E,
  (∃ p, (slot +ₗ slotNext) ↦ p) -∗
  (slot +ₗ slotActive) ↦ #true -∗
  (slot +ₗ slotValue) ↦ #NULL -∗
  <<< ∀∀ sbvmap xs, ▷ SlotBag γsb slotBag sbvmap xs >>>
    slot_bag_push_slot_loop #slotBag #slot @ E,∅,∅
  <<< let idx := length xs in
      let sbvmap' := <[slot := (true, None)]> sbvmap in
      SlotBag γsb slotBag sbvmap' (xs ++ [slot]) ∗
      Slot γsb slot idx None ∗
      ⌜sbvmap !! slot = None⌝,
      RET #() >>>.
Proof.
  iLöb as "IH".
  iIntros (γsb slotBag slot E) "[%sp Snxt] Sact Sv % AU".
  wp_rec. wp_pures. wp_bind (! _)%E.
  iMod "AU" as (sbvmap xs) "[>B [Abort _]]";
    iDestruct "B" as (γm γxs) "(%Enc & Bhd & Mphys & ●Mm & ●L)";
    iDestruct "Mphys" as "(#Lphys & Ms & %Mdom)".
  wp_load. iMod ("Abort" with "[Bhd ●Mm ●L Ms]") as "AU".
  { iNext; iFrame. iExists γm, γxs. iFrame; auto. }
  clear -γsb. iModIntro. wp_pures. wp_store.

  wp_pures. wp_bind (CmpXchg _ _ _)%E.
  iMod "AU" as (sbvmap' xs') "[>B AU]";
    iDestruct "B" as (γm γxs) "(%Enc & Bhd' & Mphys' & ●Mm & ●L)".
  destruct (decide (last xs = last xs')) as [EQ|NE]; subst.
  - (* success *)
    rewrite -EQ.
    iDestruct "AU" as "[_ Commit]".
    wp_cmpxchg_suc.

    (* make resources to commit *)
    iDestruct (phys_map_no_slot_sbvmap with "[-Sv] Sv") as %Nosbv; auto.
    iDestruct "Mphys'" as "(#Lphys' & Ms' & %Mdom')".
    iDestruct (phys_list_agree with "Lphys Lphys'") as "%"; subst; auto.
    iMod (mapsto_persist with "Snxt") as "#Snxt".
    iMod (ghost_slot_bag_insert (true, None) with "●Mm")
      as "[●Mm ●Ms]"; first apply Nosbv; simpl.
    iMod (mono_list_auth_own_update (xs' ++ [slot]) with "●L")
      as "[●L ◯L]". { apply prefix_app_cut. }
    iDestruct "Sact" as "[Sact1 Sact2]".
    iDestruct "Sv" as "[Sv1 Sv2]".

    (* commit *)
    iMod ("Commit" with "[-]") as "HΦ";
      last (iModIntro; wp_pures; by iApply "HΦ").
    iFrame. iSplitR "●Ms ◯L".
    + iExists γm, γxs. iFrame. iSplit; auto.
      rewrite last_snoc. iFrame.
      iApply (phys_map_insert with "[Ms'] [Sact1 Sv1]"); auto.
      * iFrame. iSplit; auto.
      * iFrame.
    + iSplit; auto. iExists γm, γxs. iSplit; auto. iFrame.
      iApply (mono_list_idx_own_get with "◯L").
      apply snoc_lookup.
  - (* fail, loop *)
    iDestruct "AU" as "[Abort _]".
    wp_cmpxchg_fail.
    iMod ("Abort" with "[Bhd' Mphys' ●Mm ●L]") as "AU".
    { iNext; iFrame. iExists γm, γxs. iFrame; auto. }
    iModIntro. wp_pures.
    iApply ("IH" with "[Snxt] [Sact] [Sv] [AU]"); auto.
Qed.

Lemma slot_bag_try_acquire_inactive_slot_spec (slotBag : loc) γsb E :
  ⊢ <<< ∀∀ γm γxs xs (sbvmap : gmap loc (bool * option blk)),
      ⌜γsb = encode (γm, γxs)⌝ ∗
      (slotBag +ₗ slotBagHead) ↦ #(oloc_to_lit (last xs)) ∗
      phys_map xs sbvmap ∗
      ghost_slot_bag γm sbvmap ∗
      mono_list_auth_own γxs 1 xs >>>
    slot_bag_try_acquire_inactive_slot #slotBag @ E,∅,∅
  <<< ∃∃ (q : option loc),
      (slotBag +ₗ slotBagHead) ↦ #(oloc_to_lit (last xs)) ∗
      mono_list_auth_own γxs 1 xs ∗
      match q with
      | None =>
         phys_map xs sbvmap ∗
         ghost_slot_bag γm sbvmap
      | Some slot =>
         ⌜sbvmap !! slot = Some (false, (None))⌝ ∗
         let sbvmap' := <[slot := (true, (None))]> sbvmap in
         phys_map xs sbvmap' ∗
         ghost_slot_bag γm sbvmap' ∗
         (∃ idx, Slot γsb slot idx (None))
      end,
    RET #(oloc_to_lit q) >>>.
Proof.
  iIntros "% AU".
  wp_rec. wp_pures. wp_bind (! _)%E.
  iMod "AU" as (γm γxs xs sbvmap) "[(%Hγ & Bhd & Mphys & ●Mm & ●L) [Abort _]]";
    iDestruct "Mphys" as "(#Lphys & Ms & %Mdom)".
  iDestruct (mono_list_lb_own_get with "●L") as "#◯L".
  wp_load. iMod ("Abort" with "[-]") as "AU"; iFrame; auto.
  clear -Hγ. iModIntro. wp_pures.

  iLöb as "IH" forall (xs) "Lphys ◯L".

  (* fail loop if head is null *)
  destruct (rev_des xs).
  { rewrite H. clear H xs.
    wp_pures. wp_rec. wp_pures. iMod "AU" as (?? xs sbvmap) "[[%Hγ' P] [_ Commit]]".
    iMod ("Commit" $! None with "[P]") as "HΦ"; last by iApply "HΦ".
    iDestruct "P" as "(P1&P2&P3&P4)"; iFrame. }
  destruct H as [x [xs' H]]. rewrite H. clear H xs. rename xs' into xs.
  rewrite last_snoc. wp_pures.

  (* load head *)
  iDestruct (phys_list_snoc with "Lphys") as "[Lhd Lphysx]".
  wp_rec. wp_load. wp_pures.

  (* cas *)
  wp_bind (CmpXchg _ _ _)%E.
  iMod "AU" as (?? xs' sbvmap') "[(%Hγ' & Bhd' & Mphys' & ●Mm & ●L) AU]";
    iDestruct "Mphys'" as "(#Lphys' & Ms' & %Mdom')";
    encode_agree Hγ'.
  iDestruct (mono_list_auth_lb_valid with "●L ◯L") as
    %[_ Lpf].
  iAssert ⌜is_Some (sbvmap' !! x)⌝%I as ((act, v)) "%Ml".
  { iPureIntro. apply Mdom'.
    eapply elem_of_prefix; last apply Lpf.
    apply elem_of_snoc; by left. }
  iDestruct (big_sepM_delete _ sbvmap' x with "Ms'") as "[Sphys Ms']";
    first apply Ml.
  iDestruct "Sphys" as "(Sact & Sv & %Sav)".

  destruct act; simpl in *.
  - (* slot active, cas fail *)
    iDestruct "AU" as "[Abort _]".
    wp_cmpxchg_fail.
    iMod ("Abort" with "[-]") as "AU".
    { iFrame. iSplit; auto.
      iApply (phys_map_undelete with "[] [Sact Sv]"); auto.
      1: apply Ml. iFrame. }
    iModIntro. wp_pures.
    iApply ("IH" with "[AU]"); auto.
    iApply (mono_list_lb_own_le with "◯L").
    apply prefix_app_cut.
  - (* slot inactive, cas success *)
    iDestruct "AU" as "[_ Commit]". subst.
    wp_cmpxchg_suc.
    iMod (ghost_slot_bag_update (true, None)
      with "[] ●Mm") as "[●Mm ●Ms]"; eauto.
    iDestruct "Sact" as "[Sact1 Sact2]".
    iDestruct "Sv" as "[Sv1 Sv2]".

    iMod ("Commit" $! (Some x) with "[-]") as "HΦ";
      last (iModIntro; wp_pures; by iApply "HΦ").
    simpl. iFrame. iSplit; auto.
    iSplitL "Sact1 Sv1 Ms'".
    + iApply (phys_map_undelete x xs' true (None) _
        with "[] [Sact1 Sv1]"); auto.
      * apply lookup_insert.
      * by apply domain_of_update.
      * iFrame.
      * by rewrite delete_insert_delete.
    + iExists (length xs), γm, γxs.
      iFrame. iSplit; auto.
      iApply mono_list_idx_own_get; auto.
      apply snoc_lookup.
Qed.

(* slot specs *)

Lemma slot_bag_acquire_slot_spec :
  slot_bag_acquire_slot_spec' Slot SlotBag.
Proof.
  iIntros (γsb slotBag E) "% AU".
  wp_rec. wp_bind (slot_bag_try_acquire_inactive_slot _)%E.
  iApply (slot_bag_try_acquire_inactive_slot_spec slotBag γsb).
  iAuIntro. unfold atomic_acc.
  iMod "AU" as (sbvmap xs) "[>B AU]";
    iDestruct "B" as (γm γxs) "(%Enc & Bhd & Mphys & ●Mm & ●L)".
  iModIntro. iExists γm, γxs, xs, sbvmap. iFrame.
  iSplit; auto.

  iSplit.
  { (* prove abort *)
    iDestruct "AU" as "[Abort _]".
    iIntros "(Bhd & Mphys & ●Mm & ●L)".
    iMod ("Abort" with "[-]"); auto.
    iFrame. iExists γm, γxs; auto.
  }

  iIntros (q) "(Bhd & ●L & Scase)".
  destruct q.
  { (* acquire success *)
    iDestruct "AU" as "[_ Commit]".
    iDestruct "Scase" as "(%Ml & Mphys & ●Mm & [%idx S])".
    iDestruct (slot_lookup with "●L S") as "%"; eauto.

    iMod ("Commit" with "[-]") as "HΦ";
      last (iModIntro; iIntros "_"; wp_pures; by iApply "HΦ").
    iFrame. iSplit; eauto.
    iExists γm, γxs. iFrame "∗%".
  }

  (* acquire fail *)
  iDestruct "AU" as "[Abort _]".
  iDestruct "Scase" as "[Mphys ●Mm]".
  iMod ("Abort" with "[-]") as "AU".
  { iFrame. iNext. iExists γm, γxs; iFrame; auto. }
  iModIntro. iIntros "_". simpl. wp_pures. clear.

  (* new slot *)
  unfold slot_new. wp_pures. wp_alloc slot as "S" "?".
  rewrite 3!array_cons 2!loc_add_assoc.
  iDestruct "S" as "(Snxt & Sact & Sv & _)".
  wp_pures. rewrite loc_add_0.
  wp_store. wp_pures. wp_store. wp_pures. wp_store. wp_let.

  (* push the new slot *)
  wp_bind (slot_bag_push_slot_loop _ _)%E.
  iApply (slot_bag_push_slot_loop_spec $! γsb with
    "[Snxt] [Sact] [Sv]"); auto; auto.
  iAuIntro. unfold atomic_acc.
  iMod "AU" as (sbvmap xs) "[B AU]". iModIntro.
  iExists sbvmap, xs. iFrame.
  iSplit.
  - (* abort *)
    iDestruct "AU" as "[Abort _]".
    iIntros "B". iMod ("Abort" with "B") as "AU".
    iModIntro. iFrame.
  - (* commit *)
    iDestruct "AU" as "[_ Commit]".
    iIntros "[B [S %]]".
    iMod ("Commit" with "[B S]") as "HΦ"; iFrame; auto.
    iModIntro. iIntros "_". wp_pures. by iApply "HΦ".
Qed.

Lemma slot_set_spec :
  slot_set_spec' Slot SlotBag.
Proof.
  iIntros (γsb slotBag slot idx oldv v E) ">S %Φ AU".
  wp_rec. wp_pures.
  iMod "AU" as (sbvmap xs) "[>B [_ Commit]]".
  iDestruct (SlotBag_lookup with "B S") as "%".
    iDestruct "S" as (γm γxs) "(%Hγ & Sact & Sv & ●Ms & ◯i)".
    iDestruct "B" as (??) "(%Hγ' & Bhd & Mphys & ●Mm & ●L)";
    iDestruct "Mphys" as "(#Lphys & Ms & %Mdom)";
    encode_agree Hγ.
  iDestruct (ghost_slot_bag_lookup with "●Mm ●Ms") as "%Hmap".

  iMod (ghost_slot_bag_update (true, v) with "[●Ms] [●Mm]") as "[●Mm ●Ms]"; eauto with iFrame.
  iDestruct (big_sepM_delete with "Ms") as "[Sphys Ms]"; first apply Hmap; simpl.
  iDestruct "Sphys" as "[Sact2 [Sv2 %]]".
  iCombine "Sv" "Sv2" as "Sv". wp_store.

  (* make resources to commit *)
  iDestruct "Sv" as "[Sv Sv2]".
  iDestruct (big_sepM_insert
    _ (delete slot sbvmap) slot (true, v) with "[Ms Sact2 Sv2]") as
    "Ms".
  { by rewrite lookup_delete. }
  { iFrame. iFrame. }
  rewrite insert_delete_insert.

  (* commit *)
  iMod ("Commit" with "[-]") as "HΦ"; last (iModIntro; auto; by iApply "HΦ").
  iFrame. iSplit; auto. iSplitL "●L ●Mm"; iExists γm, γxs; iFrame; auto.
  repeat iSplit; auto; iPureIntro.
  by apply domain_of_update.
Qed.

Lemma slot_unset_spec :
  slot_unset_spec' Slot SlotBag.
Proof.
  iIntros (γsb slotBag slot idx v E) ">S %Φ AU".
  wp_rec. wp_pures.
  iMod "AU" as (sbvmap xs) "[>B [_ Commit]]".
  iDestruct (SlotBag_lookup with "B S") as "%".
    iDestruct "S" as (γm γxs) "(%Hγ & Sact & Sv & ●Ms & ◯i)".
    iDestruct "B" as (??) "(%Hγ' & Bhd & Mphys & ●Mm & ●L)";
    iDestruct "Mphys" as "(#Lphys & Ms & %Mdom)";
    encode_agree Hγ.
  iDestruct (ghost_slot_bag_lookup with "●Mm ●Ms") as "%Hmap".

  iMod (ghost_slot_bag_update (true, None) with "[●Ms] [●Mm]") as "[●Mm ●Ms]"; eauto with iFrame.
  iDestruct (big_sepM_delete with "Ms") as "[Sphys Ms]"; first apply Hmap; simpl.
  iDestruct "Sphys" as "[Sact2 [Sv2 %]]".
  iCombine "Sv" "Sv2" as "Sv". wp_store.

  (* make resources to commit *)
  iDestruct "Sv" as "[Sv Sv2]".
  iDestruct (big_sepM_insert
    _ (delete slot sbvmap) slot (true, None) with "[Ms Sact2 Sv2]") as
    "Ms".
  { by rewrite lookup_delete. }
  { iFrame. iFrame. }
  rewrite insert_delete_insert.

  (* commit *)
  iMod ("Commit" with "[-]") as "HΦ"; last (iModIntro; auto; by iApply "HΦ").
  iFrame. iSplit; auto.
  iSplitL "●L ●Mm"; iExists γm, γxs; iFrame; auto.
  repeat iSplit; auto; iPureIntro. by apply domain_of_update.
Qed.

Lemma slot_drop_spec :
  slot_drop_spec' Slot SlotBag.
Proof.
  iIntros (γsb slotBag slot idx E) "Slot %Φ AU".
  wp_lam. wp_op.
  iMod "AU" as (sbvmap slist) "[>SlotBag [_ Commit]]".
  iDestruct (SlotBag_lookup with "SlotBag Slot") as "%Hsb".
  iDestruct "Slot" as (γm γxs) "(%Hγ & Sact & Sv & ●Ms & ◯i)".
  iDestruct "SlotBag" as (??) "(%Hγ' & Bhd & Mphys & ●Mm & ●L)".
  iDestruct "Mphys" as "(#Lphys & Ms & %Mdom)".
  encode_agree Hγ.

  destruct Hsb as [Hslist Hslot].

  iMod (ghost_slot_bag_update (false, None) with "[●Ms] [●Mm]") as "[●Mm ●Ms]"; eauto with iFrame; simpl.
  iDestruct (big_sepM_delete with "Ms") as "[Sphys Ms]"; first apply Hslot; simpl.
  iDestruct "Sphys" as "[Sact2 [Sv2 %]]".
  iCombine "Sact" "Sact2" as "Sact". wp_store.

  (* make resources to commit *)
  iDestruct (big_sepM_insert
    _ (delete slot sbvmap) slot (false, None) with "[Ms Sact Sv Sv2]") as
    "Ms".
  { by rewrite lookup_delete. }
  { by do 2 iFrame. }
  rewrite insert_delete_insert.

  (* commit *)
  iMod ("Commit" with "[-]") as "HΦ"; last (iModIntro; auto; by iApply "HΦ").
  iFrame. iSplit; first by done.
  iExists γm, γxs; iFrame; auto.
  repeat iSplit; auto; iPureIntro. by apply domain_of_update.
Qed.

(* snapshot specs *)

Lemma seq_bag_new_spec :
  seq_bag_new_spec'  SeqBag.
Proof.
  iIntros (E Φ _) "HΦ".
  wp_rec. wp_alloc seqBag as "SBhd" "?". wp_pures.
  rewrite array_singleton loc_add_0.
  wp_store.
  iModIntro. iApply "HΦ". iExists _.
  rewrite loc_add_0. by iFrame.
Qed.

Lemma seq_bag_add_spec :
  seq_bag_add_spec' SeqBag.
Proof.
  iIntros (E seqBag vs v Φ) "SB HΦ";
    iDestruct "SB" as (hd) "(SBhd & SBphys)".
  wp_rec. wp_pures. wp_load. wp_pures.
  wp_alloc seqNode as "N" "?". wp_pures.
  rewrite 2!array_cons. iDestruct "N" as "[Nnxt [Nv _]]".
  rewrite 2!loc_add_0.
  wp_store. wp_pures. wp_store. wp_pures. rewrite loc_add_0. wp_store.
  iModIntro. iApply "HΦ". iExists seqNode; iFrame.
  rewrite loc_add_0. iFrame.
  iExists seqNode, hd. by iFrame.
Qed.

Lemma slot_bag_read_head_spec :
  slot_bag_read_head_spec' SlotBag SlotList.
Proof.
  iIntros (????? Φ) "B HΦ".
  iDestruct "B" as (γm γxs) "(%Hγ & Bhd & Mphys & ●Mm & ●L)";
  iDestruct "Mphys" as "(#Lphys & Ms & %Mdom)".
  iDestruct (mono_list_lb_own_get with "●L") as "#◯L".
  wp_load.
  iApply "HΦ". iModIntro. iSplit; (iExists _,_; iFrame "∗#%").
Qed.

Lemma slot_read_active_spec :
  slot_read_active_spec' SlotBag.
Proof.
  iIntros (??????? Hidx Φ) "!> B HΦ".
  iDestruct "B" as (γm γxs) "(%Hγ & Bhd & Mphys & ●Mm & ●L)";
  iDestruct "Mphys" as "(#Lphys & Ms & %Mdom)".
  have [[act v] Ml] : is_Some (sbvmap !! slot).
  { apply Mdom. by eapply elem_of_list_lookup_2. }
  iDestruct (big_sepM_lookup_acc _ _ _ _ Ml with "Ms") as "[Sphys Ms]".
  iDestruct "Sphys" as "(Sact & Sv & %Sav)".
  wp_load.
  iSpecialize ("Ms" with "[$Sact $Sv //]").
  iApply "HΦ".
  iModIntro. iSplit; [done|].
  iExists γm, γxs. iFrame. repeat iSplit; auto.
Qed.

Lemma slot_read_value_spec :
  slot_read_value_spec' SlotBag.
Proof.
  iIntros (??????? Hidx Φ) "!> B HΦ".
  iDestruct "B" as (γm γxs) "(%Hγ & Bhd & Mphys & ●Mm & ●L)";
  iDestruct "Mphys" as "(#Lphys & Ms & %Mdom)".
  have [[act v] Ml] : is_Some (sbvmap !! slot).
  { apply Mdom. by eapply elem_of_list_lookup_2. }
  iDestruct (big_sepM_lookup_acc _ _ _ _ Ml with "Ms") as "[Sphys Ms]".
  iDestruct "Sphys" as "(Sact & Sv & %Sav)".
  wp_load.
  iSpecialize ("Ms" with "[$Sact $Sv //]").
  iApply "HΦ".
  iModIntro. iSplit; [done|].
  iExists γm, γxs. iFrame. repeat iSplit; auto.
Qed.

Lemma phys_list_lookup slist idx slot :
  slist !! idx = Some slot →
  phys_list slist -∗
  (slot +ₗ slotNext) ↦□ #(oloc_to_lit (last (take idx slist))).
Proof.
  unfold phys_list.
  iIntros (Hidx) "#LPhys".
  iInduction slist as [|slot' slist'] "IH" using rev_ind forall (idx slot Hidx); first done.
  rewrite reverse_app /=. iDestruct "LPhys" as "[slot↦ Lphys']". fold (phys_list slist').
  rewrite head_reverse.
  case (decide (idx = length slist')) as [->|NE].
  { rewrite snoc_lookup in Hidx. injection Hidx as ->.
    rewrite take_app. done. }
  have {}Hidx : slist' !! idx = Some slot.
  { apply lookup_lt_Some in Hidx as Hlen. rewrite app_length /= in Hlen.
    by rewrite lookup_app_l in Hidx; last lia. }
  apply lookup_lt_Some in Hidx as Hlen.
  rewrite take_app_le; last lia.
  by iApply "IH".
Qed.

Lemma slot_read_next_spec :
  slot_read_next_spec' SlotBag.
Proof.
  iIntros (??????? Hidx Φ) "!> B HΦ".
  iDestruct "B" as (γm γxs) "(%Hγ & Bhd & Mphys & ●Mm & ●L)";
  iDestruct "Mphys" as "(#Lphys & Ms & %Mdom)".
  have [[act v] Ml] : is_Some (sbvmap !! slot).
  { apply Mdom. by eapply elem_of_list_lookup_2. }
  iDestruct (big_sepM_lookup_acc _ _ _ _ Ml with "Ms") as "[Sphys Ms]".
  iDestruct "Sphys" as "(Sact & Sv & %Sav)". simpl.
  iDestruct (phys_list_lookup _ _ _ Hidx with "Lphys") as "?".
  wp_load.
  iModIntro. iApply "HΦ".
  iSpecialize ("Ms" with "[$Sact $Sv //]").
  iExists γm, γxs. iFrame. repeat iSplit; auto.
Qed.

Lemma seq_bag_contains_loop_spec :
  ∀ hd vs (v : option blk) E,
  {{{ seq_bag_list hd vs }}}
    seq_bag_contains_loop #hd #(oblk_to_lit v) @ E
  {{{ RET #(bool_decide (v ∈ vs));
      seq_bag_list hd vs }}}.
Proof.
  iIntros (hd vs v E Φ) "SBphys HΦ".
  iLöb as "IH" forall (hd vs).
  wp_rec. wp_pures.
  destruct vs as [|b vs].
  { (* search fail *)
    simpl. iDestruct "SBphys" as %->. wp_pures.
    by iApply "HΦ". }
  simpl. iDestruct "SBphys" as (l hd') "(% & SBv & SBnxt & SBphys')".
  subst. wp_pures. wp_load.

  wp_pures.

  destruct (decide (b = v)); subst.
  { (* search success *)
    rewrite bool_decide_eq_true_2; last first.
    { apply elem_of_cons; by left. }
    wp_pures. destruct v as [v|].
    - wp_pures. rewrite bool_decide_eq_true_2; auto; wp_pures.
      iModIntro. iApply "HΦ". by repeat (iExists _; iFrame).
    - wp_pures. iApply "HΦ". by repeat (iExists _; iFrame).
  }
  replace (bool_decide (b = v)) with false; last first.
  { rewrite bool_decide_eq_false_2; done. }
  wp_pures. wp_load.

  iApply ("IH" $! hd' vs with "[SBphys']"); auto.
  iNext. iIntros "SBphys".
  replace (bool_decide (v ∈ vs)) with (bool_decide (v ∈ b::vs)).
  - iApply "HΦ". iExists l, hd'; by iFrame.
  - destruct (decide (v ∈ vs)).
    + rewrite bool_decide_eq_true_2. 2: apply elem_of_cons; by right.
      rewrite bool_decide_eq_true_2; auto.
    + rewrite bool_decide_eq_false_2. 2: apply not_elem_of_cons; auto.
      rewrite bool_decide_eq_false_2; auto.
Qed.

Lemma seq_bag_contains_spec :
  seq_bag_contains_spec' SeqBag.
Proof.
  iIntros (seqBag vs v E Φ) "SB HΦ";
    iDestruct "SB" as (hd) "(SBhd & SBphys)".
  wp_rec. wp_pures. wp_load. wp_let.
  iApply (seq_bag_contains_loop_spec hd vs v with "SBphys"); auto.
  iNext. iIntros "SBphys". iApply "HΦ". iExists hd; by iFrame.
Qed.

Lemma seq_bag_contains_other_loop_spec :
  ∀ hd vs v E,
  {{{ seq_bag_list hd vs }}}
    seq_bag_contains_other_loop #hd #(oblk_to_lit v) @ E
  {{{ v', RET #(bool_decide (v' ∈ vs ∧ v' ≠ v));
      seq_bag_list hd vs }}}.
Proof.
  iIntros (hd vs v E Φ) "SBphys HΦ".
  iLöb as "IH" forall (hd vs).
  wp_rec. wp_pures.
  destruct vs as [|b vs].
  { (* search fail *)
    simpl. iDestruct "SBphys" as %->. wp_pures.
    iSpecialize ("HΦ" $! v).
    by iApply "HΦ". }
  simpl. iDestruct "SBphys" as (l hd') "(% & SBv & SBnxt & SBphys')".
  subst. wp_pures. wp_load.

  wp_pures.
  destruct (decide (b = v)); subst; last first.
  { (* search success *)
    rewrite bool_decide_eq_false_2; last by congruence.
    iSpecialize ("HΦ" $! b).
    rewrite bool_decide_eq_true_2; last first.
    { split; [apply elem_of_cons; by left|done]. }
    wp_pures. iModIntro.
    iApply "HΦ". by repeat (iExists _; iFrame). }
  replace (bool_decide (v = v)) with true; last first.
  { rewrite bool_decide_eq_true_2; congruence. }
  wp_pures. wp_load.

  iApply ("IH" $! hd' vs with "[SBphys']"); auto.
  iNext. iIntros (v') "SBphys".
  iSpecialize ("HΦ" $! v').
  replace (bool_decide (v' ∈ vs ∧ v' ≠ v)) with (bool_decide (v' ∈ v::vs ∧ v' ≠ v)); last first.
  { destruct (decide (v' = v)).
    - rewrite bool_decide_eq_false_2. 2: intros [_ ?]; congruence.
      rewrite bool_decide_eq_false_2; auto. intros [_ ?]; congruence.
    - destruct (decide (v' ∈ vs)).
      + rewrite bool_decide_eq_true_2; last first.
        { split; [apply elem_of_cons; by right|done]. }
        rewrite bool_decide_eq_true_2; done.
      + rewrite bool_decide_eq_false_2; last first.
        { intros [In _]. apply elem_of_cons in In. destruct In; congruence. }
        rewrite bool_decide_eq_false_2; auto. intros [? _]; congruence.
  }
  iApply "HΦ". iExists l, hd'; by iFrame.
Qed.

Lemma seq_bag_contains_other_spec :
  seq_bag_contains_other_spec' SeqBag.
Proof.
  iIntros (seqBag vs v E Φ) "SB HΦ";
    iDestruct "SB" as (hd) "(SBhd & SBphys)".
  wp_rec. wp_pures. wp_load. wp_let.
  iApply (seq_bag_contains_other_loop_spec hd vs v with "SBphys"); auto.
  iNext. iIntros (v') "SBphys". iApply "HΦ". iExists hd; by iFrame.
Qed.

End slot_bag.

Definition slot_bag_impl Σ `{!heapGS Σ, !slot_bag_olocG Σ}
    : spec_slot_bag_oloc.slot_bag_spec Σ := {|
  spec_slot_bag_oloc.Slot := Slot;
  spec_slot_bag_oloc.SlotList := SlotList;
  spec_slot_bag_oloc.SeqBag := SeqBag;

  spec_slot_bag_oloc.Slot_Timeless := Slot_TimeLess;
  spec_slot_bag_oloc.SlotBag_Timeless := SlotBag_TimeLess;
  spec_slot_bag_oloc.SlotList_Persistent := SlotList_Persistent;

  spec_slot_bag_oloc.slot_bag_new_spec := slot_bag_new_spec;
  spec_slot_bag_oloc.slot_bag_acquire_slot_spec := slot_bag_acquire_slot_spec;
  spec_slot_bag_oloc.slot_bag_read_head_spec := slot_bag_read_head_spec;
  spec_slot_bag_oloc.slot_set_spec := slot_set_spec;
  spec_slot_bag_oloc.slot_unset_spec := slot_unset_spec;
  spec_slot_bag_oloc.slot_drop_spec := slot_drop_spec;
  spec_slot_bag_oloc.slot_read_active_spec := slot_read_active_spec;
  spec_slot_bag_oloc.slot_read_value_spec := slot_read_value_spec;
  spec_slot_bag_oloc.slot_read_next_spec := slot_read_next_spec;

  spec_slot_bag_oloc.SlotBag_lookup := SlotBag_lookup;
  spec_slot_bag_oloc.SlotBag_prefix := SlotBag_prefix;
  spec_slot_bag_oloc.SlotBag_NoDup := SlotBag_NoDup;

  spec_slot_bag_oloc.seq_bag_new_spec := seq_bag_new_spec;
  spec_slot_bag_oloc.seq_bag_add_spec := seq_bag_add_spec;

  spec_slot_bag_oloc.seq_bag_contains_spec := seq_bag_contains_spec;
  spec_slot_bag_oloc.seq_bag_contains_other_spec := seq_bag_contains_other_spec;
|}.
