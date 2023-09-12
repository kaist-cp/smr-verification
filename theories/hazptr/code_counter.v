From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import hazptr.spec_hazptr.

Section counter.
Variable (hazptr : hazard_pointer_code).

(* [c +ₗ #0]: AtomicPtr<usize>, [c +ₗ #1]: HazardDomain *)
Definition counter_new : val := λ: "dom",
  let: "counter" := AllocN #2 #0 in
  let: "p" := AllocN #1 #0 in
  "p" <- #0;;
  "counter" +ₗ #0 <- "p";;
  "counter" +ₗ #1 <- "dom";;
  "counter".

Definition counter_inc_loop : val :=
  rec: "loop" "atomic" "shield" "new" :=
    let: "old" := hazptr.(shield_protect) "shield" "atomic" in
    "new" <- !("old" +ₗ #0%nat) + #1;;
    if: CAS "atomic" "old" "new" then
      "old"
    else
      "loop" "atomic" "shield" "new".

Definition counter_inc : val := λ: "counter",
  let: "domain" := !("counter" +ₗ #1) in
  let: "shield" := hazptr.(shield_new) "domain" in
  let: "new" := AllocN #1 #0 in
  let: "old" := counter_inc_loop ("counter" +ₗ #0) "shield" "new" in
  let: "ret" := !("old" +ₗ #0%nat) in
  hazptr.(hazard_domain_retire) "domain" "old" #1%nat;;
  hazptr.(shield_drop) "shield";;
  "ret".

End counter.
