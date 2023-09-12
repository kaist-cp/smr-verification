From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import hazptr.spec_hazptr.

Notation stackSize := 2 (only parsing).
Notation head := 0 (only parsing).
Notation domain := 1 (only parsing).
Notation nodeSize := 2 (only parsing).
Notation data := 0 (only parsing).
Notation next := 1 (only parsing).

Section treiber.
Variable (hazptr : hazard_pointer_code).

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
  λ: "stack" "x",
    let: "new" := AllocN #nodeSize #0 in
    "new" +ₗ #data <- "x";;
    tstack_push_loop "stack" "new".

Definition tstack_pop_loop : val :=
  rec: "loop" "stack" "shield" :=
    let: "head" := hazptr.(shield_protect) "shield" ("stack" +ₗ #head) in
    if: "head" = #NULL then
      NONE
    else
      let: "next" := !("head" +ₗ #next) in
      if: CAS ("stack" +ₗ #head) "head" "next" then
        let: "data" := !("head" +ₗ #data) in
        let: "domain" := !("stack" +ₗ #domain) in
        hazptr.(hazard_domain_retire) "domain" "head" #nodeSize;;
        SOME "data"
      else
        "loop" "stack" "shield".

Definition tstack_pop : val :=
  λ: "stack",
    let: "domain" := !("stack" +ₗ #domain) in
    let: "shield" := hazptr.(shield_new) "domain" in
    let: "ov" := tstack_pop_loop "stack" "shield" in
    hazptr.(shield_drop) "shield";;
    "ov".

End treiber.
