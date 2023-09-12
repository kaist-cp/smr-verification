From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import ebr.spec_rcu_simple.

Section counter.
Variable (rcu : rcu_code).

(* [c +ₗ #0]: AtomicPtr<usize>, [c +ₗ #1]: HazardDomain *)
Definition counter_new : val := λ: "dom",
  let: "counter" := AllocN #2 #0 in
  let: "p" := AllocN #1 #0 in
  "p" <- #0;;
  "counter" +ₗ #0 <- "p";;
  "counter" +ₗ #1 <- "dom";;
  "counter".

Definition counter_inc_loop : val :=
  rec: "loop" "atomic" "new" :=
    let: "old" :=  !"atomic" in
    "new" <- !("old" +ₗ #0) + #1;;
    if: CAS "atomic" "old" "new" then
      "old"
    else
      "loop" "atomic" "new".

Definition counter_inc : val := λ: "counter" "guard",
  let: "domain" := !("counter" +ₗ #1) in
  let: "new" := AllocN #1 #0 in
  rcu.(guard_activate) "guard";;
  let: "old" := counter_inc_loop ("counter" +ₗ #0) "new" in
  let: "ret" := !("old" +ₗ #0) in
  rcu.(rcu_domain_retire) "domain" "old" #1%nat;;
  rcu.(guard_deactivate) "guard";;
  "ret".

End counter.
