From smr.lang Require Import notation.

From smr.no_recl Require Import code_harris_operations.
From iris.prelude Require Import options.

Section harris_michael_find.

Definition hm_find_inner : val :=
  rec: "loop" "p" "key" "prev" "curr" :=
    let: "next" := Resolve !("curr" +ₗ #next) "p" #() in
    if: (tag "next") ≠ #0 then
      (if: CAS ("prev" +ₗ #next) "curr" ("next" `tag` #0) then
        "loop" "p" "key" "prev" ("next" `tag` #0)
       else
        NONE)
    else
      let: "curr_key" := !("curr" +ₗ #key) in
      if: "curr_key" < "key" then
        "loop" "p" "key" "curr" "next"
      else
        SOME ("curr_key" = "key", "prev", "curr")
.

Definition hm_find : val :=
  rec: "loop" "list" "key" :=
  let: "p" := NewProph in
  let: "prev" := !("list" +ₗ #head) in
  let: "curr" := !("prev" +ₗ #next) in
  match: hm_find_inner "p" "key" "prev" "curr" with
    NONE => "loop" "list" "key"
  | SOME "res" => "res"
  end
.

End harris_michael_find.
