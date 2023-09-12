From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import code_slot_bag_oloc code_retired_list.

(** Implements a minimized version of Folly Hazptr.h.
Folly's optimizations:
- Efficient node reuse
- Folly collects the unreclaimable ptrs and pushes them with single CAS
- many more ..
*)

(** HazardDomain *)
Notation domSize := 2%nat (only parsing).
Notation domHBag := 0 (only parsing).
Notation domRSet := 1 (only parsing).

(** Shield *)
Notation shieldSize := 1%nat (only parsing).
Notation shieldSlot := 0 (only parsing).

(** HazardDomain *)
Definition hazard_domain_new : val := λ: <>,
  let: "dom" := AllocN #domSize #0 in
  "dom" +ₗ #domHBag <- slot_bag_new #();;
  "dom" +ₗ #domRSet <- retired_list_new #();;
  "dom".

Definition hazard_domain_do_reclamation_loop : val :=
  rec: "loop" "rSet" "rNode" "hazards" :=
    if: "rNode" = #NULL then
      #()
    else
      let: "ptr" := retired_node_ptr "rNode" in
      let: "next" := retired_node_next "rNode" in
      ( if: seq_bag_contains "hazards" "ptr" then
          retired_list_push "rSet" "rNode"
        else
          let: "size" := retired_node_size "rNode" in
          Free "size" "ptr";;
          retired_node_drop "rNode");;
      "loop" "rSet" "next" "hazards".

Definition hazard_domain_do_reclamation : val :=
  λ: "dom",
    let: "rSet" := !("dom" +ₗ #domRSet) in
    let: "rNode" := retired_list_pop_all "rSet" in
    (* SC fence *)
    let: "hBag" := !("dom" +ₗ #domHBag) in
    let: "hazards" := slot_bag_snapshot "hBag" in
    hazard_domain_do_reclamation_loop "rSet" "rNode" "hazards".

Definition hazard_domain_retire : val :=
  λ: "dom" "ptr" "size",
    let: "rSet" := !("dom" +ₗ #domRSet) in
    (* We give [#()] for epoch of retired node in hazard pointers *)
    let: "rNode" := retired_node_new "ptr" "size" #0%nat in
    retired_list_push "rSet" "rNode".

(** Shield *)
Definition shield_new : val :=
  λ: "dom",
    let: "bag" := !("dom" +ₗ #domHBag) in
    let: "slot" := slot_bag_acquire_slot "bag" in
    let: "shield" := AllocN #shieldSize #0 in
    "shield" +ₗ #shieldSlot <- "slot";;
    "shield".

Definition shield_set : val :=
  λ: "shield" "ptr",
    let: "slot" := !("shield" +ₗ #shieldSlot) in
    slot_set "slot" "ptr".
    (* SC fence before validating *)

Definition shield_protect_loop : val :=
  rec: "loop" "shield" "atomic" "ptr" :=
    shield_set "shield" "ptr";;
    (* SC fence *)
    let: "ptr'" := !"atomic" in
    if: "ptr" = "ptr'" then
      "ptr'"
    else
      "loop" "shield" "atomic" "ptr'".

Definition shield_protect : val :=
  λ: "shield" "atomic",
    let: "ptr" := !"atomic" in
    shield_protect_loop "shield" "atomic" "ptr".

Definition shield_unset : val :=
  λ: "shield",
    let: "slot" := !("shield" +ₗ #shieldSlot) in
    slot_unset "slot".

Definition shield_drop : val :=
  λ: "shield",
    let: "slot" := !("shield" +ₗ #shieldSlot) in
    slot_unset "slot";;
    slot_drop "slot";;
    Free #shieldSize "shield".
