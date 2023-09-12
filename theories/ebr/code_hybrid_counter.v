From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import ebr.spec_rcu_simple.

Section counter.
Variable (rcu : rcu_code).

(* [c +ₗ #0]: AtomicPtr<usize>, [c +ₗ #1]: RCUDomain *)
Definition hcounter_new : val := λ: "dom",
  let: "counter" := AllocN #2 #0 in
  let: "p" := AllocN #1 #0 in
  "p" <- #0;;
  "counter" +ₗ #0 <- "p";;
  "counter" +ₗ #1 <- "dom";;
  "counter".

Definition hcounter_inc_loop : val :=
  rec: "loop" "atomic" "domain" :=
    let: "node" := !"atomic" in
    let: "n" := !"node" in
    if: "n" `rem` #2 = #0 then
      if: CAS "node" "n" ("n" + #1%nat) then
        "n"
      else
        "loop" "atomic" "domain"
    else
      let: "new_node" := AllocN #1 #0 in
      "new_node" <- "n" + #1;;
      if: CAS "atomic" "node" "new_node" then
        rcu.(rcu_domain_retire) "domain" "node" #1%nat;;
        "n"
      else
        Free #1 "new_node";;
        "loop" "atomic" "domain".

Definition hcounter_inc : val := λ: "counter" "guard",
  let: "domain" := !("counter" +ₗ #1) in
  rcu.(guard_activate) "guard";;
  let: "n" := hcounter_inc_loop ("counter" +ₗ #0) "domain" in
  rcu.(guard_deactivate) "guard";;
  "n".

End counter.
