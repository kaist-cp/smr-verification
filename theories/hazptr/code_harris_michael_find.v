From smr.lang Require Import notation.
From smr.hazptr Require Import spec_hazptr code_harris_operations.

From iris.prelude Require Import options.

Section harris_michael_find.

Variable (hazptr : hazard_pointer_code).

Definition hm_find_inner : val :=
  rec: "loop" "domain" "key" "prev" "curr" "prev_sh" "curr_sh" :=
    hazptr.(shield_set) "curr_sh" "curr";;
    let: "p" := NewProph in
    let: "curr_new" :=  !("prev" +ₗ #next) in
    if: (tag "curr_new") ≠ #0 then
      ("prev_sh", "curr_sh", NONE)
    else if: "curr_new" ≠ ("curr") then
      "loop" "domain" "key" "prev" "curr_new" "prev_sh" "curr_sh"
    else
      let: "next" := !("curr" +ₗ #next) in
      let: "tagged" := (tag "next") ≠ #0 in
      resolve_proph: "p" to: "tagged" ;;
      if: "tagged" then
        (if: CAS ("prev" +ₗ #next) "curr" (untag "next") then
          hazptr.(hazard_domain_retire) "domain" "curr" #nodeSize;;
          "loop" "domain" "key" "prev" (untag "next") "prev_sh" "curr_sh"
        else
          ("prev_sh", "curr_sh", NONE))
      else
        let: "curr_key" := !("curr" +ₗ #key) in
        if: "curr_key" < "key" then
          "loop" "domain" "key" "curr" "next" "curr_sh" "prev_sh"
        else
          ("prev_sh", "curr_sh", SOME ("curr_key" = "key", "prev", "curr"))
.

Definition hm_find : val :=
  rec: "loop" "list" "domain" "key" "prev_sh" "curr_sh" :=
  let: "prev" := !("list" +ₗ #head) in
  let: "curr" := !("prev" +ₗ #next) in
  hazptr.(shield_set) "prev_sh" "prev";;
  let: "sh_res" := hm_find_inner "domain" "key" "prev" "curr" "prev_sh" "curr_sh" in
  let: "o_res" := Snd "sh_res" in
  let: "sh" := Fst "sh_res" in
  match: "o_res" with
    NONE => "loop" "list" "domain" "key" (Fst "sh") (Snd "sh")
  | SOME "res" => ((Fst "sh"), (Snd "sh"), "res")
  end
.

End harris_michael_find.
