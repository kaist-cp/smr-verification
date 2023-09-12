From smr.lang Require Import notation.
From iris.prelude Require Import options.

Section counter.

(* [c +ₗ #0]: AtomicPtr<usize> *)
Definition counter_new : val := λ: <>,
  let: "counter" := AllocN #1 #0 in
  let: "p" := AllocN #1 #0 in
  "p" <- #0;;
  "counter" +ₗ #0 <- "p";;
  "counter".

Definition counter_inc_loop : val :=
  rec: "loop" "atomic" "new" :=
    let: "old" := !"atomic" in
    "new" <- !"old" + #1;;
    if: CAS "atomic" "old" "new" then
      "old"
    else
      "loop" "atomic" "new".

Definition counter_inc : val := λ: "counter",
  let: "new" := AllocN #1 #0 in
  let: "old" := counter_inc_loop ("counter" +ₗ #0) "new" in
  let: "ret" := !"old" in
  "ret".

End counter.
