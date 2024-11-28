From smr.lang Require Import notation.
From smr.hazptr Require Import spec_hazptr code_harris_operations.

From iris.prelude Require Import options.

Section harris_find.

Variable (hazptr : hazard_pointer_code).

(* Return ((a_p_sh, a_sh, p_sh), (a_p, an)) *)
Definition get_anchor : val :=
  λ: "a_p" "a" "prev" "curr" "a_p_sh" "a_sh" "prev_sh",
    if: ("a_p" = #NULL) then
      (("prev_sh", "a_sh", "a_p_sh"), ("prev", "curr"))
    else if: "a" = "prev" then
      (("a_p_sh", "prev_sh", "a_sh"), ("a_p", "a"))
    else
      (("a_p_sh", "a_sh", "prev_sh"), ("a_p", "a")).

Definition chain_retire : val :=
  rec: "loop" "domain" "anchor" "curr" :=
    if: "anchor" = "curr" then
      #()
    else
      let: "next" := !("anchor" +ₗ #next) in
      hazptr.(hazard_domain_retire) "domain" "anchor" #nodeSize;;
      "loop" "domain" (untag "next") "curr".

Definition harris_find_inner : val :=
  rec: "loop" "domain" "key" "a_p" "a" "prev" "curr" "a_p_sh" "a_sh" "prev_sh" "curr_sh" :=
    let: "c_t" := tag "curr" in
    let: "curr" := untag "curr" in
    hazptr.(shield_set) "curr_sh" "curr";;
    let: "pr" := NewProph in
    (* continue assuming validation of curr succeeded. *)
    let: "continue" := (λ: <>,
      let: "next" := Resolve !("curr" +ₗ #next) "pr" #() in
      if: (tag "next") ≠ #0 then
        let: "shs_as" := get_anchor "a_p" "a" "prev" "curr" "a_p_sh" "a_sh" "prev_sh" in
        let: "shs" := Fst "shs_as" in
        let: "as" := Snd "shs_as" in
        let: "a_shs" := Fst "shs" in
        let: "prev_sh" := Snd "shs" in
        "loop" "domain" "key"
          (Fst "as") (Snd "as") "curr" "next"
          (Fst "a_shs") (Snd "a_shs") "curr_sh" "prev_sh"
      else
        let: "curr_key" := !("curr" +ₗ #key) in
        if: "curr_key" < "key" then
          (* Only curr_sh is important. *)
          "loop" "domain" "key" #NULL #NULL "curr" "next" "a_p_sh" "a_sh" "curr_sh" "prev_sh"
        else
          if: ("a" = #NULL) then
            hazptr.(shield_drop) "a_p_sh";;
            hazptr.(shield_drop) "a_sh";;
            ("prev_sh", "curr_sh", SOME ("curr_key" = "key", "prev", "curr"))
          else
            let: "res" := CmpXchg ("a_p" +ₗ #next) "a" "curr" in
            if: Snd "res" then
              let: "next" := Resolve !("curr" +ₗ #next) "pr" #() in
              chain_retire "domain" "a" "curr";;
              if: (tag "next") ≠ #0 then
                (* Only a_p_sh is important. *)
                "loop" "domain" "key" #NULL #NULL "a_p" "curr" "a_sh" "curr_sh" "a_p_sh" "prev_sh"
              else
                hazptr.(shield_drop) "prev_sh";;
                hazptr.(shield_drop) "a_sh";;
                ("a_p_sh", "curr_sh", SOME ("curr_key" = "key", "a_p", "curr"))
            else
              if: tag (Fst "res") ≠ #0 then
                hazptr.(shield_drop) "a_p_sh";;
                hazptr.(shield_drop) "a_sh";;
                ("prev_sh", "curr_sh", NONE)
              else
                (* Only a_p_sh is important. *)
                "loop" "domain" "key" #NULL #NULL "a_p" (Fst "res") "a_sh" "curr_sh" "a_p_sh" "prev_sh"
    ) in
    if: "c_t" ≠ #0 then
      (* Validate on anchor. *)
      (* a_p and a should both not be null here. *)
      let: "a_new" := !("a_p" +ₗ #next) in
      if: tag "a_new" = #0 then
        if: untag "a_new" = "a" then
          "continue" #()
        else
          (* Only a_p_sh is important. *)
          "loop" "domain" "key" #NULL #NULL "a_p" "a_new"  "curr_sh" "prev_sh" "a_p_sh" "a_sh"
      else
        hazptr.(shield_drop) "a_p_sh";;
        hazptr.(shield_drop) "a_sh";;
        ("prev_sh", "curr_sh", NONE)
    else
      (* Validate on curr. *)
      (* Prophecy analysis here *)
      let: "c_new" := !("prev" +ₗ #next) in
      if: tag "c_new" = #0 then
        if: untag "c_new" = untag "curr" then
          "continue" #()
        else
          (* Only prev_sh is important. *)
          "loop" "domain" "key" #NULL #NULL "prev" "c_new" "a_p_sh" "a_sh" "prev_sh" "curr_sh"
      else
        hazptr.(shield_drop) "a_p_sh";;
        hazptr.(shield_drop) "a_sh";;
        ("prev_sh", "curr_sh", NONE)
  .

Definition harris_find : val :=
  rec: "loop" "list" "domain" "key" "prev_sh" "curr_sh" :=
  let: "prev" := !("list" +ₗ #head) in
  let: "curr" := !("prev" +ₗ #next) in
  hazptr.(shield_set) "prev_sh" "prev";;
  let: "a_p_sh" := (hazptr.(shield_new) "domain") in
  let: "a_sh" := (hazptr.(shield_new) "domain") in
  let: "sh_res" := harris_find_inner "domain" "key" #NULL #NULL "prev" "curr" "a_p_sh" "a_sh" "prev_sh" "curr_sh" in
  let: "o_res" := Snd "sh_res" in
  let: "sh" := Fst "sh_res" in
  match: "o_res" with
    NONE => "loop" "list" "domain" "key" (Fst "sh") (Snd "sh")
  | SOME "res" => (Fst "sh", Snd "sh", "res")
  end
.

End harris_find.
