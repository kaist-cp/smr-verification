From smr.lang Require Import notation.
From iris.prelude Require Import options.

Notation stackSize := 1 (only parsing).
Notation head := 0 (only parsing).
Notation nodeSize := 2 (only parsing).
Notation data := 0 (only parsing).
Notation next := 1 (only parsing).

Section treiber.

Definition tstack_new : val :=
  λ: <>,
    let: "stack" := AllocN #stackSize #0 in
    "stack" +ₗ #head <- #NULL;;
    "stack".

Definition tstack_push_loop : val :=
  rec: "loop" "stack" "new" :=
    let: "head" := !("stack" +ₗ #head) in
    "new" +ₗ #next <- "head";;
    if: CAS ("stack" +ₗ #head) "head" "new" then
      #()
    else
      "loop" "stack" "new".

Definition tstack_push : val :=
  λ: "stack" "x",
    let: "new" := AllocN #nodeSize #0 in
    "new" +ₗ #data <- "x";;
    tstack_push_loop "stack" "new".

Definition tstack_pop : val :=
  rec: "loop" "stack" :=
    let: "head" := !("stack" +ₗ #head) in
    if: "head" = #NULL then
      NONE
    else
      let: "next" := !("head" +ₗ #next) in
      if: CAS ("stack" +ₗ #head) "head" "next" then
        SOME !("head" +ₗ #data)
      else
        "loop" "stack".

End treiber.
