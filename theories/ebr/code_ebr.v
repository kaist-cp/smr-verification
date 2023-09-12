From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import code_slot_bag_onat code_retired_list.

(** RCUDomain *)
Notation domSize := 3 (only parsing).
Notation domLBag := 0 (only parsing).
Notation domRSet := 1 (only parsing).
Notation domGEpoch := 2 (only parsing).

(** Guard *)
Notation guardSize := 2%nat (only parsing).
Notation guardSlot := 0 (only parsing).
Notation guardDom := 1 (only parsing).

(** RCUDomain *)
Definition ebr_domain_new : val := λ: <>,
  let: "dom" := AllocN #domSize #0 in
  "dom" +ₗ #domLBag <- slot_bag_new #();;
  "dom" +ₗ #domRSet <- retired_list_new #();;
  "dom" +ₗ #domGEpoch <- #3%nat;;
  "dom".

Definition may_advance_loop : val :=
  rec: "loop" "slot" "g_epoch" :=
    if: "slot" = #NULL then
      #true
    else
      let: "continue" := (λ: <>,
        let: "next" :=  !("slot" +ₗ #slotNext) in
        "loop" "next" "g_epoch"
      ) in
      let: "active" := !("slot" +ₗ #slotActive) in
      if: "active" then
        let: "value" := !("slot" +ₗ #slotValue) in
        if: #0%nat ≤ "value" then (* activated ("pinned") epoch *)
          if: "value" ≠ "g_epoch" then
            #false
          else
            "continue" #()
        else
          "continue" #()
      else
        "continue" #().

(* If there exists a slot with active epoch not equal to [g_epoch], return [false]. *)
Definition may_advance : val :=
  λ: "LBag" "g_epoch",
    let: "head" := !("LBag" +ₗ #slotBagHead) in
    may_advance_loop "head" "g_epoch".

Definition try_advance : val :=
  λ: "dom",
    let: "g_epoch" := !("dom" +ₗ #domGEpoch) in
    (* SC fence *)
    let: "LBag" := !("dom" +ₗ #domLBag) in
    if: may_advance "LBag" "g_epoch" then
      let: "new_epoch" := "g_epoch" + #1%nat in
      let: "res" := CmpXchg ("dom" +ₗ #domGEpoch) "g_epoch" "new_epoch" in
      if: Snd "res" then
        "new_epoch"
      else
        Fst "res"
    else
      "g_epoch".

Definition ebr_domain_do_reclamation_loop : val :=
  rec: "loop" "rSet" "rNode" "g_epoch" :=
    if: "rNode" = #NULL then
      #()
    else
      let: "ptr" := retired_node_ptr "rNode" in
      let: "epoch" := retired_node_epoch "rNode" in
      let: "next" := retired_node_next "rNode" in
      ( if: "g_epoch" < "epoch" + #3%nat then
          retired_list_push "rSet" "rNode"
        else
          let: "size" := retired_node_size "rNode" in
          Free "size" "ptr";;
          retired_node_drop "rNode");;
      "loop" "rSet" "next" "g_epoch".

Definition ebr_domain_do_reclamation : val :=
  λ: "dom",
    let: "g_epoch" := try_advance "dom" in
    let: "rSet" := !("dom" +ₗ #domRSet) in
    let: "rNode" := retired_list_pop_all "rSet" in
    ebr_domain_do_reclamation_loop "rSet" "rNode" "g_epoch".

(** guard *)
Definition ebr_guard_new : val :=
  λ: "dom",
    let: "bag" := !("dom" +ₗ #domLBag) in
    let: "slot" := slot_bag_acquire_slot "bag" in
    let: "guard" := AllocN #guardSize #0 in
    "guard" +ₗ #guardSlot <- "slot";;
    "guard" +ₗ #guardDom <- "dom";;
    "guard".

Definition activate_loop : val :=
  rec: "loop" "slot" "dom" "epoch" :=
    slot_set "slot" "epoch";;
    (* SC fence before validating *)
    let: "val_epoch" := !("dom" +ₗ #domGEpoch) in
    if: "val_epoch" = "epoch" then
      #()
    else
      "loop" "slot" "dom" "val_epoch".

Definition ebr_guard_activate : val :=
  λ: "guard",
    let: "slot" := !("guard" +ₗ #guardSlot) in
    let: "dom" := !("guard" +ₗ #guardDom) in
    let: "epoch" := !("dom" +ₗ #domGEpoch) in
    activate_loop "slot" "dom" "epoch".

Definition ebr_guard_deactivate : val :=
  λ: "guard",
    let: "slot" := !("guard" +ₗ #guardSlot) in
    "slot" +ₗ #slotValue <- #(-1).

Definition ebr_guard_drop : val :=
  λ: "guard",
    let: "slot" := !("guard" +ₗ #guardSlot) in
    "slot" +ₗ #slotValue <- #(-1);;
    slot_drop "slot";;
    Free #guardSize "guard".

Definition ebr_domain_retire : val :=
  λ: "dom" "ptr" "size",
    let: "guard" := ebr_guard_new "dom" in
    ebr_guard_activate "guard";;
    let: "rSet" := !("dom" +ₗ #domRSet) in
    let: "slot" := !("guard" +ₗ #guardSlot) in
    let: "epoch" := !("slot" +ₗ #slotValue) in
    let: "rNode" := retired_node_new "ptr" "size" "epoch" in
    retired_list_push "rSet" "rNode";;
    ebr_guard_drop "guard".
