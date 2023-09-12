From smr.lang Require Import notation.

From smr.no_recl Require Import code_harris_operations.
From iris.prelude Require Import options.

Section harris_find.

Definition get_anchor : val :=
  λ: "anchor" "curr",
    if: ("anchor" = #NULL) then
      "curr"
    else
      "anchor".

Definition harris_find_inner : val :=
  rec: "loop" "pr_tag" "key" "prev" "curr" "anchor" :=
    let: "pr_tag'" := NewProph in
    let: "next" := !("curr" +ₗ #next) in
    let: "tagged" := (tag "next") ≠ #0 in
    resolve_proph: "pr_tag" to: "tagged" ;;
    if: "tagged" then
      let: "new_anchor" := get_anchor "anchor" "curr" in
      "loop" "pr_tag'" "key" "prev" ("next" `tag` #0) "new_anchor"
    else
      let: "curr_key" := !("curr" +ₗ #key) in
      if: "curr_key" < "key" then
        "loop" "pr_tag'" "key" "curr" "next" #NULL
      else
        if: ("anchor" = #NULL) then
          SOME ("curr_key" = "key", "prev", "curr")
        else
          let: "pr_tag_cas" := NewProph in
          if: CAS ("prev" +ₗ #next) "anchor" "curr" then
            let: "next" := !("curr" +ₗ #next) in
            let: "tagged" := (tag "next") ≠ #0 in
            resolve_proph: "pr_tag_cas" to: "tagged" ;;
            if: "tagged" then
              NONE
            else
              SOME ("curr_key" = "key", "prev", "curr")
          else
            NONE
.

Definition harris_find : val :=
  rec: "loop" "list" "key" :=
  let: "pr_tag" := NewProph in
  let: "prev" := !("list" +ₗ #head) in
  let: "curr" := !("prev" +ₗ #next) in
  match: harris_find_inner "pr_tag" "key" "prev" "curr" #NULL with
    NONE => "loop" "list" "key"
  | SOME "res" => "res"
  end
.

End harris_find.
