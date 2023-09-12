From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import ebr.spec_rcu_simple.

Notation stackSize := 2 (only parsing).
Notation head := 0 (only parsing).
Notation domain := 1 (only parsing).
Notation nodeSize := 2 (only parsing).
Notation data := 0 (only parsing).
Notation next := 1 (only parsing).

Section treiber.
Variable (rcu : rcu_code).

Definition tstack_new : val :=
  λ: "dom",
    let: "stack" := AllocN #stackSize #0 in
    "stack" +ₗ #head <- #NULL;;
    "stack" +ₗ #domain <- "dom";;
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
  λ: "stack" "x" "guard",
    let: "new" := AllocN #nodeSize #0 in
    "new" +ₗ #data <- "x";;
    tstack_push_loop "stack" "new".

Definition tstack_pop_loop : val :=
  rec: "loop" "stack" :=
    let: "head" := !("stack" +ₗ #head) in
    if: "head" = #NULL then
      NONE
    else
      let: "next" := !("head" +ₗ #next) in
      if: CAS ("stack" +ₗ #head) "head" "next" then
        let: "data" := !("head" +ₗ #data) in
        let: "domain" := !("stack" +ₗ #domain) in
        rcu.(rcu_domain_retire) "domain" "head" #nodeSize;;
        SOME "data"
      else
        "loop" "stack".

Definition tstack_pop : val :=
  λ: "stack" "guard",
    rcu.(guard_activate) "guard";;
    let: "ov" := tstack_pop_loop "stack" in
    rcu.(guard_deactivate) "guard";;
    "ov".

End treiber.
