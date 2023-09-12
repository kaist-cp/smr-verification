From smr.lang Require Import notation.
From iris.prelude Require Import options.
From smr Require Import ebr.spec_rcu_simple.

Notation dequeSize := 4 (only parsing).
Notation circle := 0 (only parsing).
Notation qtop := 1 (only parsing).
Notation qbot := 2 (only parsing).
Notation qdom := 3 (only parsing).
Notation csz := 0 (only parsing).
Notation carr := 1 (only parsing).

Section cldeque.

Variable (rcu : rcu_code).
Definition circ_access : val :=
  λ: "arr" "i" "n",
    "arr" +ₗ ("i" `rem` "n").

Definition circle_new : val :=
  λ: "sz",
    let: "circle" := AllocN (#1 + "sz") #0 in
    ("circle" +ₗ #csz) <- "sz" ;;
    "circle".

Definition circle_grow_rec : val :=
  rec: "grow_rec" "arr" "sz" "narr" "nsz" "t" "b" :=
    if: "t" < "b"
    then (
      let: "b'" := "b" - #1 in
      let: "v" := !(circ_access "arr" "b'" "sz") in
      (circ_access "narr" "b'" "nsz") <- "v" ;;
      "grow_rec" "arr" "sz" "narr" "nsz" "t" "b'"
    )
    else #().

Definition circle_grow : val :=
  λ: "circle" "t" "b" "sz",
    let: "nsz" := #2 * "sz" in
    let: "ncirc" := circle_new "nsz" in
    circle_grow_rec ("circle" +ₗ #carr) "sz" ("ncirc" +ₗ #1) "nsz" "t" "b" ;;
    "ncirc".

Definition deque_new : val :=
  λ: "dom" "sz",
    let: "deque" := AllocN #dequeSize #0 in
    "deque" +ₗ #circle <- circle_new "sz" ;;
    "deque" +ₗ #qtop <- #1 ;;
    "deque" +ₗ #qbot <- #1 ;;
    "deque" +ₗ #qdom <- "dom" ;;
    "deque".

Definition deque_push : val :=
  λ: "deque" "v" "guard",
    let: "b" := !("deque" +ₗ #qbot) in
    let: "t" := !("deque" +ₗ #qtop) in
    let: "circle" := !("deque" +ₗ #circle) in
    let: "sz" := !("circle" +ₗ #csz) in
    (if: "t" + "sz" ≤ "b" + #1
      then "deque" +ₗ #circle <- circle_grow "circle" "t" "b" "sz"
      else #()
    ) ;;
    let: "circle'" := !("deque" +ₗ #circle) in
    let: "sz'" := !("circle'" +ₗ #csz) in
    (circ_access ("circle'" +ₗ #carr) "b" "sz'") <- "v" ;;
    "deque" +ₗ #qbot <- "b" + #1.

Definition deque_pop : val :=
  λ: "deque" "guard",
    let: "b" := !("deque" +ₗ #qbot) - #1 in
    let: "circle" := !("deque" +ₗ #circle) in
    let: "sz" := !("circle" +ₗ #csz) in
    "deque" +ₗ #qbot <- "b" ;;
    let: "t" := !("deque" +ₗ #qtop) in
    if: "b" < "t" then (* empty pop *)
      "deque" +ₗ #qbot <- "t" ;; NONE
    else let: "v" := !(circ_access ("circle" +ₗ #carr) "b" "sz") in
    if: "t" < "b" then SOME "v" (* normal case *)
    else let: "ok" := CAS ("deque" +ₗ #qtop) "t" ("t" + #1) in
    "deque" +ₗ #qbot <- "t" + #1 ;;
    if: "ok" then SOME "v" (* popped *)
    else NONE. (* stolen *)

(* NOTE: b ≤ t doesn't necessarily mean the deque was empty!
  It can also be the case that there was one element and
  the owner thread decremented b trying to pop. *)
Definition deque_steal : val :=
  λ: "deque" "guard",
    let: "t" := !("deque" +ₗ #qtop) in
    let: "b" := !("deque" +ₗ #qbot) in
    rcu.(guard_activate) "guard" ;;
    let: "circle" := !("deque" +ₗ #circle) in
    let: "sz" := !("circle" +ₗ #csz) in
    if: "b" ≤ "t" then
      rcu.(guard_deactivate) "guard" ;;
      NONE (* no chance *)
    else let: "v" := !(circ_access ("circle" +ₗ #carr) "t" "sz") in
    rcu.(guard_deactivate) "guard" ;; 
    if: CAS ("deque" +ₗ #qtop) "t" ("t" + #1)
    then SOME "v" (* success *)
    else NONE. (* fail *)

End cldeque.

