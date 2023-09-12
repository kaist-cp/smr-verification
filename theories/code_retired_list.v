From smr.lang Require Import tactics notation.
From iris.prelude Require Import options.

(** RetiredNode *)
Notation rNodeSize := 4%nat (only parsing).
Notation rNodeNext := 0 (only parsing).
Notation rNodePtr := 1 (only parsing).
Notation rNodePtrSize := 2 (only parsing).
Notation rNodeEpoch := 3 (only parsing).

Definition retired_node_new : val :=
  λ: "ptr" "size" "epoch",
    let: "rNode" := AllocN #rNodeSize #0 in
    "rNode" +ₗ #rNodeNext <- #NULL;;
    "rNode" +ₗ #rNodePtr <- "ptr";;
    "rNode" +ₗ #rNodePtrSize <- "size";;
    "rNode" +ₗ #rNodeEpoch <- "epoch";;
    "rNode".

Definition retired_node_next : val :=
  λ: "rNode",
    ! ("rNode" +ₗ #rNodeNext).

Definition retired_node_ptr : val :=
  λ: "rNode",
    ! ("rNode" +ₗ #rNodePtr).

Definition retired_node_size : val :=
  λ: "rNode",
    ! ("rNode" +ₗ #rNodePtrSize).

Definition retired_node_epoch : val :=
  λ: "rNode",
    ! ("rNode" +ₗ #rNodeEpoch).

Definition retired_node_drop : val :=
  λ: "rNode",
    Free #rNodeSize "rNode".

(** RetiredSet *)
Notation rSetSize := 1%nat (only parsing).
Notation rSetHead := 0 (only parsing).

Definition retired_list_new : val :=
  λ: <>,
    let: "rSet" := AllocN #rSetSize #0 in
    "rSet" +ₗ #rSetHead <- #NULL;;
    "rSet".

Definition retired_list_push : val :=
  rec: "loop" "rSet" "rNode" :=
    let: "head" := !("rSet" +ₗ #rSetHead) in
    "rNode" +ₗ #rNodeNext <- "head";;
    if: CAS ("rSet" +ₗ #rSetHead) "head" "rNode" then
      #()
    else
      "loop" "rSet" "rNode".

Definition retired_list_pop_all : val :=
  λ: "rSet", Xchg ("rSet" +ₗ #rSetHead) #NULL.
