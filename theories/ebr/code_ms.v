From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import ebr.spec_rcu_simple.

Notation nodeSize := 2 (only parsing).
Notation data := 0 (only parsing).
Notation next := 1 (only parsing).
Notation queueSize := 3 (only parsing).
Notation head := 0 (only parsing).
Notation tail := 1 (only parsing).
Notation domain := 2 (only parsing).

Section ms.
Variable (rcu : rcu_code).

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
  rec: "find_tail" "queue" :=
    let: "tail" := !("queue" +ₗ #tail) in
    let: "next" := !("tail" +ₗ #next) in
    if: "next" = #NULL then
      "tail"
    else
      CAS ("queue" +ₗ #tail) "tail" "next";;
      "find_tail" "queue".

Definition queue_push_loop : val :=
  rec: "loop" "queue" "new" :=
    let: "tail" := find_tail "queue" in
    if: CAS ("tail" +ₗ #next) #NULL "new" then
      (* The tail pointer lags behind the actual tail by at most one node. *)
      CAS ("queue" +ₗ #tail) "tail" "new"
    else
      "loop" "queue" "new".

Definition queue_push : val :=
  λ: "queue" "data" "guard",
    let: "new" := AllocN #nodeSize #0 in
    "new" +ₗ #next <- #NULL;;
    "new" +ₗ #data <- "data";;
    rcu.(guard_activate) "guard";;
    queue_push_loop "queue" "new";;
    rcu.(guard_deactivate) "guard".

Definition queue_pop_loop : val :=
  rec: "loop" "queue" :=
    let: "head" := !("queue" +ₗ #head) in (* #1 *)
    let: "next" := !("head" +ₗ #next) in (* #2 *)
    if: "next" = #NULL then
      NONE
    else
      (* Update tail pointer to ensure that the node to be retired will be
      unreachable after undating the head pointer. NOTE: This can be done
      after successfully updating the head pointer, right before retiring. In
      that case, the tail pointer may temporarily lag behind the head
      pointer. *)
      let: "tail" := !("queue" +ₗ #tail) in (* #3 *)
      (if: "head" = "tail" then
        CAS ("queue" +ₗ #tail) "tail" "next" else #());; (* #4 *)
      (* Update head pointer to the next node. *)
      if: CAS ("queue" +ₗ #head) "head" "next" then (* #5 *)
        let: "data" := !("next" +ₗ #data) in
        rcu.(rcu_domain_retire) !("queue" +ₗ #domain) "head" #nodeSize;;
        SOME "data"
      else
        "loop" "queue".

Definition queue_pop : val :=
  λ: "queue" "guard",
    rcu.(guard_activate) "guard";;
    let: "ov" := queue_pop_loop "queue" in
    rcu.(guard_deactivate) "guard";;
    "ov".

End ms.
