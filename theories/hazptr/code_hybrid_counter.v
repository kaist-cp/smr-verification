From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import hazptr.spec_hazptr.

Section counter.
Variable (hazptr : hazard_pointer_code).

(* [c +ₗ #0]: AtomicPtr<usize>, [c +ₗ #1]: HazardDomain *)
Definition hcounter_new : val := λ: "dom",
  let: "counter" := AllocN #2 #0 in
  let: "p" := AllocN #1 #0 in
  "p" <- #0;;
  "counter" +ₗ #0 <- "p";;
  "counter" +ₗ #1 <- "dom";;
  "counter".

Definition hcounter_inc_loop : val :=
  rec: "loop" "atomic" "domain" "shield" :=
    let: "node" := hazptr.(shield_protect) "shield" "atomic" in
    let: "n" := !"node" in
    if: "n" `rem` #2 = #0 then
      if: CAS "node" "n" ("n" + #1%nat) then
        "n"
      else
        "loop" "atomic" "domain" "shield"
    else
      let: "new_node" := Alloc #0 in
      "new_node" <- "n" + #1;;
      if: CAS "atomic" "node" "new_node" then
        hazptr.(hazard_domain_retire) "domain" "node" #1%nat;;
        "n"
      else
        Free #1 "new_node";;
        "loop" "atomic" "domain" "shield".

Definition hcounter_inc : val := λ: "counter",
  let: "domain" := !("counter" +ₗ #1) in
  let: "shield" := hazptr.(shield_new) "domain" in
  let: "n" := hcounter_inc_loop ("counter" +ₗ #0) "domain" "shield" in
  hazptr.(shield_drop) "shield";;
  "n".

End counter.
