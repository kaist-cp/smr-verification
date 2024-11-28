From smr.lang Require Import tactics notation.
From iris.prelude Require Import options.

(** Sequential bag using linked list *)
Notation seqNodeSize := 2%nat (only parsing).
Notation seqNodeNext := 0 (only parsing).
Notation seqNodeValue := 1 (only parsing).
Notation seqSize := 1%nat (only parsing).
Notation seqHead := 0 (only parsing).

Definition seq_bag_new : val :=
  λ: <>,
    let: "seq" := AllocN #seqSize #0 in
    "seq" +ₗ #seqHead <- #NULL;;
    "seq".

Definition seq_bag_add : val :=
  λ: "seq" "ptr",
    let: "head" := !("seq" +ₗ #seqHead) in
    let: "seqNode" := AllocN #seqNodeSize #0 in
    "seqNode" +ₗ #seqNodeNext <- "head";;
    "seqNode" +ₗ #seqNodeValue <- "ptr";;
    "seq" +ₗ #seqHead <- "seqNode".

Definition seq_bag_contains_loop : val :=
  rec: "loop" "head" "ptr" :=
    if: "head" = #NULL
    then #false
    else
      if: !("head" +ₗ #seqNodeValue) = "ptr"
      then #true
      else "loop" !("head" +ₗ #seqNodeNext) "ptr".

Definition seq_bag_contains : val :=
  λ: "seq" "ptr",
    let: "head" := !("seq" +ₗ #seqHead) in
    seq_bag_contains_loop "head" "ptr".

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
    "slot" +ₗ #slotValue <- #NULL;;
    "slot".

Definition slot_set : val :=
  λ: "slot" "ptr",
    "slot" +ₗ #slotValue <- "ptr".

Definition slot_unset : val :=
  λ: "slot",
    "slot" +ₗ #slotValue <- #NULL.

Definition slot_drop : val :=
  λ: "slot",
    "slot" +ₗ #slotActive <- #false.

(** SlotBag *)
Notation slotBagSize := 1 (only parsing).
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

Definition slot_bag_snapshot_loop : val :=
  rec: "loop" "snapshot" "slot" :=
    if: "slot" = #NULL then
      #()
    else
      let: "active" := !("slot" +ₗ #slotActive) in
      ( if: "active" then
          let: "value" := !("slot" +ₗ #slotValue) in
          seq_bag_add "snapshot" "value"
        else #() ) ;;
      let: "next" :=  !("slot" +ₗ #slotNext) in
      "loop" "snapshot" "next".

Definition slot_bag_snapshot : val :=
  λ: "slotBag",
    let: "snapshot" := seq_bag_new #() in
    let: "head" := !("slotBag" +ₗ #slotBagHead) in
    slot_bag_snapshot_loop "snapshot" "head";;
    "snapshot".
