From smr.lang Require Import notation.
From smr.hazptr Require Import spec_hazptr.

From iris.prelude Require Import options.


Notation listSize := 2 (only parsing).
Notation head := 0 (only parsing).
Notation domain := 1 (only parsing).

(* Node info *)
Notation nodeSize := 2 (only parsing).
Notation next := 0 (only parsing). (* tagged pointer to the next node *)
Notation key := 1 (only parsing). (* real data *)

Record harris_find_code : Type := HarrisFindCode {
  harris_find : val;
}.

Section harris_operations.

Variable (harris : harris_find_code) (hazptr : hazard_pointer_code).

Definition harris_new : val :=
  λ: "dom",
    let: "posinf" := AllocN #nodeSize #0 in
    let: "neginf" := AllocN #nodeSize #0 in
    "neginf" +ₗ #key <- #-∞ᵢ;;
    "neginf" +ₗ #next <- "posinf";;
    "posinf" +ₗ #key <- #∞ᵢ;;
    "posinf" +ₗ #next <- #NULL;;
    let: "list" := AllocN #listSize #0 in
    "list" +ₗ #head <- "neginf";;
    "list" +ₗ #domain <- "dom";;
    "list".

Definition harris_lookup : val :=
  λ: "list" "key",
    let: "domain" := !("list" +ₗ #domain) in
    let: "prev_sh" := hazptr.(shield_new) "domain" in
    let: "curr_sh" := hazptr.(shield_new) "domain" in
    let: "sh_res" := harris.(harris_find) "list" "domain" "key" "prev_sh" "curr_sh" in
    let: "res" := Snd "sh_res" in
    let: "sh" := Fst "sh_res" in
    hazptr.(shield_drop) (Fst "sh") ;;
    hazptr.(shield_drop) (Snd "sh") ;;
    (Fst (Fst "res")).

Definition harris_insert_loop : val :=
  rec: "loop" "list" "domain" "key" "new" "prev_sh" "curr_sh" :=
    let: "sh_res" := harris.(harris_find) "list" "domain" "key" "prev_sh" "curr_sh" in
    let: "res" := Snd "sh_res" in
    let: "sh" := Fst "sh_res" in
    if: Fst (Fst "res") then
      Free #nodeSize "new";;
      (Fst "sh", Snd "sh", #false)
    else
      let: "prev" := Snd (Fst "res") in
      let: "curr" := Snd "res" in
      "new" +ₗ #next <- "curr";;
      if: CAS ("prev" +ₗ #next) "curr" "new" then
        (Fst "sh", Snd "sh", #true)
      else
        "loop" "list" "domain" "key" "new" (Fst "sh") (Snd "sh").

Definition harris_insert : val :=
  λ: "list" "key",
    let: "domain" := !("list" +ₗ #domain) in
    let: "prev_sh" := hazptr.(shield_new) "domain" in
    let: "curr_sh" := hazptr.(shield_new) "domain" in
    let: "new" := AllocN #nodeSize #0 in
    "new" +ₗ #key <- "key";;
    let: "sh_res" := harris_insert_loop "list" "domain" "key" "new" "prev_sh" "curr_sh" in
    let: "res" := Snd "sh_res" in
    let: "sh" := Fst "sh_res" in
    hazptr.(shield_drop) (Fst "sh") ;;
    hazptr.(shield_drop) (Snd "sh") ;;
    "res".

Definition harris_delete_loop : val :=
  rec: "loop" "list" "domain" "key" "prev_sh" "curr_sh" :=
  let: "sh_res" := harris.(harris_find) "list" "domain" "key" "prev_sh" "curr_sh" in
  let: "res" := Snd "sh_res" in
  let: "sh" := Fst "sh_res" in
  if: ~ (Fst (Fst "res")) then
    (Fst "sh", Snd "sh", #false)
  else
    let: "curr" := Snd "res" in
    let: "next" := !("curr" +ₗ #next) in
    let: "tagged" := (tag "next") ≠ #0 in
    if: "tagged" then
      "loop" "list" "domain" "key" (Fst "sh") (Snd "sh")
    else if: CAS ("curr" +ₗ #next) "next" ("next" `tag` #1) then
      let: "prev" := Snd (Fst "res") in
      (if: CAS ("prev" +ₗ #next) "curr" "next" then
        hazptr.(hazard_domain_retire) "domain" "curr" #nodeSize
      else
        #()
      );;
      (Fst "sh", Snd "sh", #true)
    else
      "loop" "list" "domain" "key" (Fst "sh") (Snd "sh").

Definition harris_delete : val :=
  λ: "list" "key",
    let: "domain" := !("list" +ₗ #domain) in
    let: "prev_sh" := hazptr.(shield_new) "domain" in
    let: "curr_sh" := hazptr.(shield_new) "domain" in
    let: "sh_res" := harris_delete_loop "list" "domain" "key" "prev_sh" "curr_sh" in
    let: "res" := Snd "sh_res" in
    let: "sh" := Fst "sh_res" in
    hazptr.(shield_drop) (Fst "sh") ;;
    hazptr.(shield_drop) (Snd "sh") ;;
    "res".

End harris_operations.
