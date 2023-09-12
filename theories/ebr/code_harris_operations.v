From smr.lang Require Import notation.
From smr Require Import ebr.spec_rcu_common.

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

Variable (harris : harris_find_code) (rcu : rcu_code).

Definition harris_new : val :=
  λ: "domain",
    let: "posinf" := AllocN #nodeSize #0 in
    let: "neginf" := AllocN #nodeSize #0 in
    "neginf" +ₗ #key <- #-∞ᵢ;;
    "neginf" +ₗ #next <- "posinf";;
    "posinf" +ₗ #key <- #∞ᵢ;;
    "posinf" +ₗ #next <- #NULL;;
    let: "list" := AllocN #listSize #0 in
    "list" +ₗ #head <- "neginf";;
    "list" +ₗ #domain <- "domain";;
    "list".

Definition harris_lookup : val :=
  λ: "list" "guard" "key",
    let: "domain" := !("list" +ₗ #domain) in
    rcu.(guard_activate) "guard";;
    let: "res" := Fst (Fst (harris.(harris_find) "list" "domain" "key")) in
    rcu.(guard_deactivate) "guard";;
    "res".

Definition harris_insert_loop : val :=
  rec: "loop" "list" "domain" "key" "new" :=
    let: "res" := harris.(harris_find) "list" "domain" "key" in
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
        "loop" "list" "domain" "key" "new".

Definition harris_insert : val :=
  λ: "list" "guard" "key",
    let: "domain" := !("list" +ₗ #domain) in
    rcu.(guard_activate) "guard";;
    let: "new" := AllocN #nodeSize #0 in
    "new" +ₗ #key <- "key";;
    let: "res" := harris_insert_loop "list" "domain" "key" "new" in
    rcu.(guard_deactivate) "guard";;
    "res".

Definition harris_delete_loop : val :=
  rec: "loop" "list" "domain" "key" :=
  let: "res" := harris.(harris_find) "list" "domain" "key" in
  if: ~ (Fst (Fst "res")) then
    #false
  else
    let: "curr" := Snd "res" in
    let: "next" := !("curr" +ₗ #next) in
    let: "tagged" := (tag "next") ≠ #0 in
    if: "tagged" then
      "loop" "list" "domain" "key"
    else if: CAS ("curr" +ₗ #next) "next" ("next" `tag` #1) then
      let: "prev" := Snd (Fst "res") in
      (if: CAS ("prev" +ₗ #next) "curr" "next" then
        rcu.(rcu_domain_retire) "domain" "curr" #nodeSize
      else
        #());;
      #true
    else
      "loop" "list" "domain" "key".

Definition harris_delete : val :=
  λ: "list" "guard" "key",
    let: "domain" := !("list" +ₗ #domain) in
    rcu.(guard_activate) "guard";;
    let: "res" := harris_delete_loop "list" "domain" "key" in
    rcu.(guard_deactivate) "guard";;
    "res".

End harris_operations.
