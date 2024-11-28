From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import hazptr.spec_hazptr.

Notation nodeSize := 2 (only parsing).
Notation data := 0 (only parsing).
Notation next := 1 (only parsing).
Notation queueSize := 3 (only parsing).
Notation head := 0 (only parsing).
Notation tail := 1 (only parsing).
Notation domain := 2 (only parsing).

Section ms.
Variable (hazptr : hazard_pointer_code).

Definition queue_new : val :=
  λ: "dom",
    let: "sentinel":= AllocN #nodeSize #0 in
    "sentinel" +ₗ #next <- #NULL;;
    let: "queue" := AllocN #queueSize #0 in
    "queue" +ₗ #head <- "sentinel";;
    "queue" +ₗ #tail <- "sentinel";;
    "queue" +ₗ #domain <- "dom";;
    "queue".

Definition find_tail : val :=
  rec: "find_tail" "queue" "shield" :=
    let: "tail" := hazptr.(shield_protect) "shield" ("queue" +ₗ #tail) in
    let: "next" := !("tail" +ₗ #next) in
    if: "next" = #NULL then
      "tail"
    else
      CAS ("queue" +ₗ #tail) "tail" "next";;
      "find_tail" "queue" "shield".

Definition queue_push_loop : val :=
  rec: "loop" "queue" "new" "shield" :=
    let: "tail" := find_tail "queue" "shield" in
    if: CAS ("tail" +ₗ #next) #NULL "new" then
      (* The tail pointer lags behind the actual tail by at most one node. *)
      CAS ("queue" +ₗ #tail) "tail" "new"
    else
      "loop" "queue" "new" "shield".

Definition queue_push : val :=
  λ: "queue" "data",
    let: "new" := AllocN #nodeSize #0 in
    "new" +ₗ #data <- "data";;
    "new" +ₗ #next <- #NULL;;
    let: "shield" := hazptr.(shield_new) !("queue" +ₗ #domain) in
    queue_push_loop "queue" "new" "shield";;
    hazptr.(shield_drop) "shield".

Definition queue_pop_loop : val :=
  rec: "loop" "queue" "head_shield" "next_shield" :=
    let: "head" := hazptr.(shield_protect) "head_shield" ("queue" +ₗ #head) in (* #1 *)
    let: "next" := !("head" +ₗ #next) in (* #2 *)
    if: "next" = #NULL then
      NONE
    else
      hazptr.(shield_set) "next_shield" "next";;
      (* Update tail pointer to ensure that the node to be retired will be
      unreachable after undating the head pointer. NOTE: This can be done
      after successfully updating the head pointer, right before retiring. In
      that case, the tail pointer may temporarily lag behind the head
      pointer. *)
      let: "tail" := !("queue" +ₗ #tail) in (* #4 *)
      (if: "head" = "tail" then
        CAS ("queue" +ₗ #tail) "tail" "next" else #());; (* #5 *)
      (* Update head pointer to the next node. *)
      if: CAS ("queue" +ₗ #head) "head" "next" then (* #6 *)
        let: "data" := !("next" +ₗ #data) in
        hazptr.(hazard_domain_retire) !("queue" +ₗ #domain) "head" #nodeSize;;
        SOME "data"
      else
        "loop" "queue" "head_shield" "next_shield".

Definition queue_pop : val :=
  λ: "queue",
    let: "domain" := !("queue" +ₗ #domain) in
    let: "head_shield" := hazptr.(shield_new) "domain" in
    let: "next_shield" := hazptr.(shield_new) "domain" in
    let: "ov" := queue_pop_loop "queue" "head_shield" "next_shield" in
    hazptr.(shield_drop) "head_shield";;
    hazptr.(shield_drop) "next_shield";;
    "ov".

End ms.
