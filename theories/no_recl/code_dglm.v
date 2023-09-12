From smr.lang Require Import notation.
From iris.prelude Require Import options.

Notation nodeSize := 2 (only parsing).
Notation data := 0 (only parsing).
Notation next := 1 (only parsing).
Notation queueSize := 2 (only parsing).
Notation head := 0 (only parsing).
Notation tail := 1 (only parsing).

Section dglm.

(* Note: new and push are same as MS queue, but are inlined for better line count comparison. *)
Definition queue_new : val :=
  λ: <>,
    let: "sentinel":= AllocN #nodeSize #0 in
    "sentinel" +ₗ #next <- #NULL;;
    let: "queue" := AllocN #queueSize #0 in
    "queue" +ₗ #head <- "sentinel";;
    "queue" +ₗ #tail <- "sentinel";;
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
  λ: "queue" "data",
    let: "new" := AllocN #nodeSize #0 in
    "new" +ₗ #data <- "data";;
    "new" +ₗ #next <- #NULL;;
    queue_push_loop "queue" "new";;
    #().

Definition queue_pop : val :=
  rec: "loop" "queue" :=
    let: "head" := !("queue" +ₗ #head) in (* #1 *)
    let: "next" := !("head" +ₗ #next) in (* #2 *)
    if: "next" = #NULL then
      NONE
    else
      (* Update head pointer to the next node. *)
      if: CAS ("queue" +ₗ #head) "head" "next" then (* #4 *)
        let: "tail" := !("queue" +ₗ #tail) in  (* #3 *)
        (if: "head" = "tail" then
          CAS ("queue" +ₗ #tail) "tail" "next" else #());;
        SOME !("next" +ₗ #data)
      else
        "loop" "queue".

End dglm.
