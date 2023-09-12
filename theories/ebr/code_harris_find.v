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
  rec: "loop" "pr_tag" "domain" "key" "prev" "curr" "anchor" :=
    let: "pr_tag'" := NewProph in
    let: "next" := !("curr" +ₗ #next) in
    let: "tagged" := (tag "next") ≠ #0 in
    resolve_proph: "pr_tag" to: "tagged" ;;
    if: "tagged" then
      let: "new_anchor" := get_anchor "anchor" "curr" in
      "loop" "pr_tag'" "domain" "key" "prev" (untag "next") "new_anchor"
    else
      let: "curr_key" := !("curr" +ₗ #key) in
      if: "curr_key" < "key" then
        "loop" "pr_tag'" "domain" "key" "curr" "next" #NULL
      else
        if: ("anchor" = #NULL) then
          SOME ("curr_key" = "key", "prev", "curr")
        else
          let: "pr_tag_cas" := NewProph in
          if: CAS ("prev" +ₗ #next) "anchor" "curr" then
            let: "next" := !("curr" +ₗ #next) in
            let: "tagged" := (tag "next") ≠ #0 in
            resolve_proph: "pr_tag_cas" to: "tagged" ;;
            chain_retire "domain" "anchor" "curr";;
            if: "tagged" then
              NONE
            else
              SOME ("curr_key" = "key", "prev", "curr")
          else
            NONE
.

Definition harris_find : val :=
  rec: "loop" "list" "domain" "key" :=
  let: "pr_tag" := NewProph in
  let: "prev" := !("list" +ₗ #head) in
  let: "curr" := !("prev" +ₗ #next) in
  match: harris_find_inner "pr_tag" "domain" "key" "prev" "curr" #NULL with
    NONE => "loop" "list" "domain" "key"
  | SOME "res" => "res"
  end
.

End harris_find.
