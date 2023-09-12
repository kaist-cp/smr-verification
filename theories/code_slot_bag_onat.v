From smr.lang Require Import tactics notation.
From iris.prelude Require Import options.

(** Slot *)
Notation slotSize := 3%nat (only parsing).
Notation slotNext := 0 (only parsing).
Notation slotActive := 1 (only parsing).
Notation slotValue := 2 (only parsing).

Definition slot_new : val :=
  λ: <>,
    let: "slot" := AllocN #slotSize #0 in
    "slot" +ₗ #slotNext <- #NULL;;
    "slot" +ₗ #slotActive <- #true;;
    "slot" +ₗ #slotValue <- #(-1);;
    "slot".

Definition slot_set : val :=
  λ: "slot" "epoch",
    "slot" +ₗ #slotValue <- "epoch".

Definition slot_unset : val :=
  λ: "slot",
    "slot" +ₗ #slotValue <- #(-1).

Definition slot_drop : val :=
  λ: "slot",
    "slot" +ₗ #slotActive <- #false.

(** SlotBag *)
Notation slotBagSize := 1%nat (only parsing).
Notation slotBagHead := 0 (only parsing).

Definition slot_bag_new : val :=
  λ: <>,
    let: "slotBag" := AllocN #slotBagSize #0 in
    "slotBag" +ₗ #slotBagHead <- #NULL;;
    "slotBag".

Definition slot_try_acquire_inactive_slot_loop : val :=
  rec: "loop" "slot" :=
    if: "slot" = #NULL
    then #NULL
    else
      let: "next" := !("slot" +ₗ #slotNext) in
      if: CAS ("slot" +ₗ #slotActive) #false #true
      then "slot"
      else "loop" "next".

Definition slot_bag_try_acquire_inactive_slot : val :=
  λ: "slotBag",
    let: "head" := !("slotBag" +ₗ #slotBagHead) in
    slot_try_acquire_inactive_slot_loop "head".

Definition slot_bag_push_slot_loop : val :=
  rec: "loop" "slotBag" "new" :=
    let: "head" := !("slotBag" +ₗ #slotBagHead) in
    "new" +ₗ #slotNext <- "head";;
    if: CAS ("slotBag" +ₗ #slotBagHead) "head" "new" then
      #()
    else
      "loop" "slotBag" "new".

Definition slot_bag_acquire_slot : val :=
  λ: "slotBag",
    let: "slot" := slot_bag_try_acquire_inactive_slot "slotBag" in
    if: "slot" ≠ #NULL
    then "slot"
    else
      let: "new" := slot_new #() in
      slot_bag_push_slot_loop "slotBag" "new";;
      "new".
