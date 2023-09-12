From smr.lang Require Import notation.
From iris.prelude Require Import options.

Notation listSize := 1 (only parsing).
Notation head := 0 (only parsing).

(* Node info *)
Notation nodeSize := 2 (only parsing).
Notation next := 0 (only parsing). (* tagged pointer to the next node *)
Notation key := 1 (only parsing). (* real data *)

Record harris_find_code : Type := HarrisFindCode {
  harris_find : val;
}.

Section harris_operations.

Variable (harris : harris_find_code).

Definition harris_new : val :=
  λ: <>,
    let: "posinf" := AllocN #nodeSize #0 in
    let: "neginf" := AllocN #nodeSize #0 in
    "neginf" +ₗ #key <- #-∞ᵢ;;
    "neginf" +ₗ #next <- "posinf";;
    "posinf" +ₗ #key <- #∞ᵢ;;
    "posinf" +ₗ #next <- #NULL;;
    let: "list" := AllocN #listSize #0 in
    "list" +ₗ #head <- "neginf";;
    "list".

Definition harris_lookup : val :=
  λ: "list" "key",
    Fst (Fst (harris.(harris_find) "list" "key")).

Definition harris_insert_loop : val :=
  rec: "loop" "list" "key" "new" :=
    let: "res" := harris.(harris_find) "list" "key" in
    if: Fst (Fst "res") then
      Free #nodeSize "new";;
      #false
    else
      let: "prev" := Snd (Fst "res") in
      let: "curr" := Snd "res" in
      "new" +ₗ #next <- "curr";;
      if: CAS ("prev" +ₗ #next) "curr" "new" then
        #true
      else
        "loop" "list" "key" "new".

Definition harris_insert : val :=
  λ: "list" "key",
    let: "new" := AllocN #nodeSize #0 in
    "new" +ₗ #key <- "key";;
    harris_insert_loop "list" "key" "new".

Definition harris_delete : val :=
  rec: "loop" "list" "key" :=
  let: "res" := harris.(harris_find) "list" "key" in
  if: ~ (Fst (Fst "res")) then
    #false
  else
    let: "curr" := Snd "res" in
    let: "next" := !("curr" +ₗ #next) in
    let: "tagged" := (tag "next") ≠ #0 in
    if: "tagged" then
      "loop" "list" "key"
    else if: CAS ("curr" +ₗ #next) "next" ("next" `tag` #1) then
      let: "prev" := Snd (Fst "res") in
      CAS ("prev" +ₗ #next) "curr" "next";;
      #true
    else
      "loop" "list" "key".

End harris_operations.
