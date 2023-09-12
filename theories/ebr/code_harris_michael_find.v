From smr.lang Require Import notation.
From smr.ebr Require Import spec_rcu_common code_harris_operations.

From iris.prelude Require Import options.

Section harris_michael_find.

Variable (rcu : rcu_code).

Definition hm_find_inner : val :=
  rec: "loop" "p" "domain" "key" "prev" "curr" :=
    let: "p'" := NewProph in
    let: "next" := !("curr" +ₗ #next) in
    let: "tagged" := (tag "next") ≠ #0 in
    resolve_proph: "p" to: "tagged" ;;
    if: "tagged" then
      (if: CAS ("prev" +ₗ #next) "curr" (untag "next") then
        rcu.(rcu_domain_retire) "domain" (untag "curr") #nodeSize;;
        "loop" "p'" "domain" "key" "prev" (untag "next")
       else
        NONE)
    else
      let: "curr_key" := !("curr" +ₗ #key) in
      if: "curr_key" < "key" then
        "loop" "p'" "domain" "key" "curr" "next"
      else
        SOME ("curr_key" = "key", "prev", "curr")
.

Definition hm_find : val :=
  rec: "loop" "list" "domain" "key" :=
  let: "p" := NewProph in
  let: "prev" := !("list" +ₗ #head) in
  let: "curr" := !("prev" +ₗ #next) in
  match: hm_find_inner "p" "domain" "key" "prev" "curr" with
    NONE => "loop" "list" "domain" "key"
  | SOME "res" => "res"
  end
.

End harris_michael_find.
