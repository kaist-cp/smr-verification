From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import ebr.spec_rcu_simple.

Notation rdcssSize := 2 (only parsing).
Notation ptr := 0 (only parsing).
Notation domain := 1 (only parsing).
Notation descSize := 1 (only parsing).
Notation data := 0 (only parsing).

Section rdcss.
Variable (rcu : rcu_code).

Definition new_rdcss : val :=
  λ: "n" "dom",
    let: "rdcss" := AllocN #rdcssSize #0 in
    "rdcss" +ₗ #ptr <- InjL "n";;
    "rdcss" +ₗ #domain <- "dom";;
    "rdcss".

Definition complete : val :=
  λ: "l_descr" "l_n" "domain",
    let: "data" := !("l_descr" +ₗ #data) in (* data = (l_m, m1, n1, n2, p) *)
    let: "l_m"  := Fst (Fst (Fst (Fst ("data")))) in
    let: "m1"   := Snd (Fst (Fst (Fst ("data")))) in
    let: "n1"   := Snd (Fst (Fst ("data"))) in
    let: "n2"   := Snd (Fst ("data")) in
    let: "p"    := Snd ("data") in
    (* Create a thread identifier using NewProph *)
    let: "tid_ghost" := NewProph in
    let: "n_new"     := (if: !"l_m" = "m1" then "n2" else "n1") in
    let: "r"         := Resolve (CmpXchg "l_n" (InjR "l_descr") (InjL "n_new")) "p" "tid_ghost" in
    if: Snd "r" then rcu.(rcu_domain_retire) "domain" "l_descr" #descSize
    else #().

Definition get_inner : val :=
  rec: "get_inner" "l_n" "domain" :=
    match: !"l_n" with
      InjL "n" => "n"
    | InjR "l_descr" =>
        complete "l_descr" "l_n" "domain";;
        "get_inner" "l_n" "domain"
    end.

Definition get : val :=
  λ: "l_n" "guard",
    let: "domain" := !("l_n" +ₗ #1) in
    rcu.(guard_activate) "guard";;
    let: "n" := get_inner "l_n" "domain" in
    rcu.(guard_deactivate) "guard";;
    "n".

Definition rdcss : val :=
  λ: "l_m" "l_n" "m1" "n1" "n2" "guard",
    let: "domain"  := !("l_n" +ₗ #domain) in
    rcu.(guard_activate) "guard";;
    (* Allocate the descriptor for the operation *)
    let: "p"       := NewProph in
    let: "l_descr" := ref ("l_m", "m1", "n1", "n2", "p") in
    let: "result"  := ( rec: "rdcss_inner" "_" :=
      (* Attempt to establish the descriptor to make the opration "active". *)
      let: "r" := CmpXchg "l_n" (InjL "n1") (InjR "l_descr") in
      match: Fst "r" with
        InjL "n" =>
          (* non-descriptor value read, check if CmpXchg was successful *)
          if: Snd "r" then
            (* CmpXchg was successful, finish operation *)
            complete "l_descr" "l_n" "domain";;
            "n1"
          else
            (* CmpXchg failed, hence we could linearize at CmpXchg *)
            Free #1 "l_descr";;
            "n"
      | InjR "l_descr_other" =>
        (** A descriptor from a concurrent operation was read,
            try to help and then restart *)
        complete "l_descr_other" "l_n" "domain";;
        "rdcss_inner" #()
      end
    ) #() in
    rcu.(guard_deactivate) "guard";;
    "result".

End rdcss.
