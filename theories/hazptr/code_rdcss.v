From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import hazptr.spec_hazptr.

Notation rdcssSize := 2 (only parsing).
Notation ptr := 0 (only parsing).
Notation domain := 1 (only parsing).
Notation descSize := 1 (only parsing).
Notation data := 0 (only parsing).

Section rdcss.
Variable (hazptr : hazard_pointer_code).

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
    if: Snd "r" then hazptr.(hazard_domain_retire) "domain" "l_descr" #descSize
    else #().

Definition get : val :=
  rec: "get" "l_n" :=
    let: "domain" := !("l_n" +ₗ #domain) in
    match: !"l_n" with
      InjL "n" => "n"
    | InjR "l_descr" =>
      let: "shield" := hazptr.(shield_new) "domain" in
      hazptr.(shield_set) "shield" "l_descr";;
      (* Validation *)
      (if: !"l_n" = InjR "l_descr" then
        (* Validation success *)
        complete "l_descr" "l_n" "domain"
      else
        (* Validation failed *)
        #());;
      hazptr.(shield_drop) "shield";;
      "get" "l_n"
    end.

Definition rdcss : val :=
  λ: "l_m" "l_n" "m1" "n1" "n2",
    let: "domain"  := !("l_n" +ₗ #domain) in
    let: "shield_descr" := hazptr.(shield_new) "domain" in
    (* Allocate the descriptor for the operation. *)
    let: "p"         := NewProph in
    let: "l_descr"     := ref ("l_m", "m1", "n1", "n2", "p") in
    (* We don't need validation for [shield_set] since there's no concurrent access yet *)
    hazptr.(shield_set) "shield_descr" "l_descr";;
    let: "result" := (rec: "rdcss_inner" "_" :=
      (* Attempt to establish the descriptor to make the operation "active". *)
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
            hazptr.(hazard_domain_retire) "domain" "l_descr" #1%nat;;
            "n"
      | InjR "l_descr_other" =>
        (** A descriptor from a concurrent operation was read,
            try to help and then restart *)
        let: "shield" := hazptr.(shield_new) "domain" in
        hazptr.(shield_set) "shield" "l_descr_other";;
        (* Validate *)
        (if: !"l_n" = InjR "l_descr_other" then
          (* Validation success *)
          complete "l_descr_other" "l_n" "domain"
        else
          (* Validation failed *)
          #());;
        hazptr.(shield_drop) "shield";;
        "rdcss_inner" #()
      end
    ) #() in
    hazptr.(shield_drop) "shield_descr";;
    "result".

End rdcss.
