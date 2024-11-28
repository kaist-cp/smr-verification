From smr.program_logic Require Import atomic.
From iris.base_logic.lib Require Import invariants.
From smr.lang Require Import proofmode notation.
From smr Require Import code_slot_bag_onat.
From iris.prelude Require Import options.

(* NOTE: Sync with spec_slot_bag_oloc *)

Definition SlotT Σ : Type :=
  ∀ (γsb : gname) (slot : loc) (idx : nat) (v : option nat), iProp Σ.

Definition SlotBagT Σ : Type :=
  ∀ (γsb : gname) (slotBag : loc)
    (sbvmap : gmap loc (bool * option nat)) (slist : list loc), iProp Σ.

Definition SlotListT Σ : Type :=
  ∀ (γsb : gname) (slist : list loc), iProp Σ.

Section spec.
Context {Σ} `{!heapGS Σ}.
Context
  (Slot : SlotT Σ)
  (SlotBag : SlotBagT Σ)
  (SlotList : SlotListT Σ).

Definition slot_bag_acquire_slot_spec' : Prop :=
  ⊢ ∀ γsb (slotBag : loc) E,
  <<{ ∀∀ sbvmap slist, ▷ SlotBag γsb slotBag sbvmap slist }>>
    slot_bag_acquire_slot #slotBag @ E,∅,∅
  <<{ ∃∃ slist' (slot : loc) (idx : nat),
        let sbvmap' := <[slot := (true, None)]> sbvmap in
        SlotBag γsb slotBag sbvmap' slist' ∗
        Slot γsb slot idx None ∗
        ⌜ (slist' = slist ++ [slot] ∧
            sbvmap !! slot = None ∧
            idx = length slist) ∨
          (slist' = slist ∧
            sbvmap !! slot = Some (false, None) ∧
            slist !! idx = Some slot) ⌝ |
      RET #slot }>>.

Definition slot_bag_read_head_spec' : Prop :=
  ∀ γsb slotBag sbvmap slist E,
  {{{ SlotBag γsb slotBag sbvmap slist }}}
    ! #(slotBag +ₗ 0) @ E
  {{{ RET #(oloc_to_lit (last slist));
      SlotBag γsb slotBag sbvmap slist ∗
      SlotList γsb slist }}}.

Definition slot_set_spec' : Prop :=
  ⊢ ∀ γsb (slotBag slot : loc) (idx : nat) (v' v : option nat) E,
  ▷ Slot γsb slot idx v' -∗
  <<{ ∀∀ sbvmap slist, ▷ SlotBag γsb slotBag sbvmap slist }>>
    slot_set #slot #(onat_to_lit v) @ E,∅,∅
  <<{ ⌜slist !! idx = Some slot ∧ sbvmap !! slot = Some (true, v')⌝ ∗
      SlotBag γsb slotBag (<[slot := (true, v)]> sbvmap) slist ∗
      Slot γsb slot idx v |
      RET #() }>>.

Definition slot_unset_spec' : Prop :=
  ⊢ ∀ γsb (slotBag slot : loc) (idx : nat) (v : option nat) E sbvmap slist,
  {{{ Slot γsb slot idx v ∗ SlotBag γsb slotBag sbvmap slist }}}
    #(slot +ₗ slotValue) <- #(-1) @ E
  {{{ RET #();
      ⌜slist !! idx = Some slot ∧ sbvmap !! slot = Some (true, v)⌝ ∗
      SlotBag γsb slotBag (<[slot := (true, None)]> sbvmap) slist ∗
      Slot γsb slot idx None
       }}}.

Definition slot_bag_new_spec' : Prop :=
  ⊢ ∀ E,
  {{{ True }}}
    slot_bag_new #() @ E
  {{{ γsb (slotbag : loc), RET #slotbag; SlotBag γsb slotbag ∅ [] }}}.

Definition slot_drop_spec' : Prop :=
  ⊢ ∀ γsb (slotBag slot : loc) (idx : nat) E,
  ▷ Slot γsb slot idx None -∗
  <<{ ∀∀ sbvmap slist, ▷ SlotBag γsb slotBag sbvmap slist }>>
    slot_drop #slot @ E,∅,∅
  <<{ ⌜slist !! idx = Some slot ∧ sbvmap !! slot = Some (true, None)⌝ ∗
      let sbvmap' := <[slot := (false, None)]> sbvmap in
      SlotBag γsb slotBag sbvmap' slist | RET #() }>>.

Definition slot_read_active_spec' : Prop :=
  ⊢ ∀ γsb sbvmap (slist : list loc) slotBag (slot : loc) idx E
      (_ : slist !! idx = Some slot),
  {{{ SlotBag γsb slotBag sbvmap slist }}}
    ! #(slot +ₗ slotActive) @ E
  {{{ (b : bool) v, RET #b;
      ⌜sbvmap !! slot = Some (b, v)⌝ ∗
      SlotBag γsb slotBag sbvmap slist }}}.

Definition slot_read_value_spec' : Prop :=
  ⊢ ∀ γsb sbvmap (slist : list loc) slotBag (slot : loc) idx E
      (_ : slist !! idx = Some slot),
  {{{ SlotBag γsb slotBag sbvmap slist }}}
    ! #(slot +ₗ slotValue) @ E
  {{{ b (v : option nat), RET #(onat_to_lit v);
      ⌜sbvmap !! slot = Some (b, v)⌝ ∗
      SlotBag γsb slotBag sbvmap slist }}}.

Definition slot_read_next_spec' : Prop :=
  ⊢ ∀ γsb sbvmap (slist : list loc) slotBag (slot : loc) idx E
      (_ : slist !! idx = Some slot),
  {{{ SlotBag γsb slotBag sbvmap slist }}}
    ! #(slot +ₗ slotNext) @ E
  {{{ RET #(oloc_to_lit (last (take idx slist)));
      SlotBag γsb slotBag sbvmap slist }}}.

Definition SlotBag_lookup' : Prop :=
  ⊢ ∀ slotBag γsb slot sbvmap slist idx v,
  SlotBag γsb slotBag sbvmap slist -∗ Slot γsb slot idx v -∗
    ⌜slist !! idx = Some slot ∧ sbvmap !! slot = Some (true, v)⌝.

Definition SlotBag_prefix' : Prop :=
  ⊢ ∀ slotBag γsb sbvmap slist1 slist2,
  SlotBag γsb slotBag sbvmap slist1 -∗ SlotList γsb slist2 -∗
    ⌜slist2 `prefix_of` slist1⌝.

Definition SlotBag_NoDup' : Prop :=
  ⊢ ∀ slotBag γsb sbvmap slist,
  SlotBag γsb slotBag sbvmap slist -∗ ⌜NoDup slist⌝.

End spec.

Record slot_bag_spec {Σ} `{!heapGS Σ} : Type := SlotBagSpec {
  Slot : SlotT Σ;
  SlotBag : SlotBagT Σ;
  SlotList : SlotListT Σ;

  Slot_Timeless : ∀ γsb slot idx v, Timeless (Slot γsb slot idx v);
  SlotBag_Timeless : ∀ γsb slotBag sbvmap slist, Timeless (SlotBag γsb slotBag sbvmap slist);
  SlotList_Persistent : ∀ γsb slist, Persistent (SlotList γsb slist);

  slot_bag_new_spec : slot_bag_new_spec' SlotBag;
  slot_bag_acquire_slot_spec : slot_bag_acquire_slot_spec' Slot SlotBag;
  slot_bag_read_head_spec : slot_bag_read_head_spec' SlotBag SlotList;
  slot_set_spec : slot_set_spec' Slot SlotBag;
  slot_unset_spec : slot_unset_spec' Slot SlotBag;
  slot_drop_spec : slot_drop_spec' Slot SlotBag;
  slot_read_active_spec : slot_read_active_spec' SlotBag;
  slot_read_value_spec : slot_read_value_spec' SlotBag;
  slot_read_next_spec : slot_read_next_spec' SlotBag;

  SlotBag_lookup : SlotBag_lookup' Slot SlotBag;
  SlotBag_prefix : SlotBag_prefix' SlotBag SlotList;
  SlotBag_NoDup : SlotBag_NoDup' SlotBag;
}.

Global Arguments slot_bag_spec _ {_}.
Global Existing Instances Slot_Timeless SlotBag_Timeless SlotList_Persistent.
