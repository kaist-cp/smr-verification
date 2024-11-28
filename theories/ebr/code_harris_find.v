From smr.lang Require Import notation.
From smr.ebr Require Import spec_rcu_common code_harris_operations.

From iris.prelude Require Import options.

Section harris_find.

Variable (rcu : rcu_code).

Definition get_anchor : val :=
  λ: "anchor" "curr",
    if: ("anchor" = #NULL) then
      "curr"
    else
      "anchor".

Definition chain_retire : val :=
  rec: "loop" "domain" "anchor" "curr" :=
    if: "anchor" = "curr" then
      #()
    else
      let: "next" := !("anchor" +ₗ #next) in
      rcu.(rcu_domain_retire) "domain" "anchor" #nodeSize;;
      "loop" "domain" (untag "next") "curr".

Definition harris_find_inner : val :=
  rec: "loop" "pr" "domain" "key" "prev" "curr" "anchor" :=
    let: "next" := Resolve !("curr" +ₗ #next) "pr" #() in
    if: (tag "next") ≠ #0 then
      let: "new_anchor" := get_anchor "anchor" "curr" in
      "loop" "pr" "domain" "key" "prev" (untag "next") "new_anchor"
    else
      let: "curr_key" := !("curr" +ₗ #key) in
      if: "curr_key" < "key" then
        "loop" "pr" "domain" "key" "curr" "next" #NULL
      else
        if: ("anchor" = #NULL) then
          SOME ("curr_key" = "key", "prev", "curr")
        else
          if: CAS ("prev" +ₗ #next) "anchor" "curr" then
            let: "next" := Resolve !("curr" +ₗ #next) "pr" #() in
            chain_retire "domain" "anchor" "curr";;
            if: (tag "next") ≠ #0 then
              NONE
            else
              SOME ("curr_key" = "key", "prev", "curr")
          else
            NONE
.

Definition harris_find : val :=
  rec: "loop" "list" "domain" "key" :=
  let: "pr" := NewProph in
  let: "prev" := !("list" +ₗ #head) in
  let: "curr" := !("prev" +ₗ #next) in
  match: harris_find_inner "pr" "domain" "key" "prev" "curr" #NULL with
    NONE => "loop" "list" "domain" "key"
  | SOME "res" => "res"
  end
.

End harris_find.
