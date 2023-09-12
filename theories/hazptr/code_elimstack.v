From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import hazptr.spec_hazptr.

Notation stackSize := 3 (only parsing).
Notation head := 0 (only parsing).
Notation offer := 1 (only parsing).
Notation domain := 2 (only parsing).
Notation nodeSize := 2 (only parsing).
Notation data := 0 (only parsing).
Notation next := 1 (only parsing).
Notation state := 1 (only parsing).

Notation offer_pending := 0 (only parsing).
Notation offer_revoked := 2 (only parsing).
Notation offer_accepted := 1 (only parsing).

Section elimstack.
Variable (hazptr : hazard_pointer_code).

Definition estack_new : val :=
  λ: "dom",
    let: "stack" := AllocN #stackSize #0 in
    "stack" +ₗ #head <- #NULL;;
    "stack" +ₗ #offer <- #NULL;;
    "stack" +ₗ #domain <- "dom";;
    "stack".

Definition estack_push : val :=
  rec: "loop" "stack" "val" :=
    let: "head_old" := !("stack" +ₗ #head) in
    let: "new" := AllocN #nodeSize #0 in
    "new" +ₗ #data <- "val";;
    "new" +ₗ #next <- "head_old";;
    if: CAS ("stack" +ₗ #head) "head_old" "new" then #()
    else
      "new" +ₗ #state <- #offer_pending;; (* this now corresponds to the `state` *)
      "stack" +ₗ #offer <- "new";;
      (* wait to see if anyone takes it *)
      (* ... okay, enough waiting *)
      "stack" +ₗ #offer <- #NULL;;
      if: CAS ("new" +ₗ #state) #offer_pending #offer_revoked then
        (* We retracted the offer. Just try the entire thing again *)
        let: "domain" := !("stack" +ₗ #domain) in
        hazptr.(hazard_domain_retire) "domain" "new" #nodeSize;;
        "loop" "stack" "val"
      else
        (* Someone took the offer. We are done. *)
        let: "domain" := !("stack" +ₗ #domain) in
        hazptr.(hazard_domain_retire) "domain" "new" #nodeSize;;
        #().

Definition estack_pop_loop : val :=
  rec: "loop" "stack" "shield" :=
    let: "head" := hazptr.(shield_protect) "shield" ("stack" +ₗ #head) in
    if: "head" = #NULL then
      NONE (* stack empty *)
    else
      let: "next" := !("head" +ₗ #next) in
      (* See if we can change the master head pointer *)
      if: CAS ("stack" +ₗ #head) "head" "next" then
        (* That worked! We are done. Return the value. *)
        let: "data" := !("head" +ₗ #data) in
        let: "domain" := !("stack" +ₗ #domain) in
        hazptr.(hazard_domain_retire) "domain" "head" #nodeSize;;
        SOME "data"
      else
        (* See if there is an offer on the side-channel *)
        let: "offer" := hazptr.(shield_protect) "shield" ("stack" +ₗ #offer) in
        if: "offer" = #NULL then
          (* Nope, no offer. Just try again. *)
          "loop" "stack" "shield"
        else
          (* Try to accept the offer. *)
          if: CAS ("offer" +ₗ #state) #offer_pending #offer_accepted then
            (* Success! We are done. Return the offered value. *)
            SOME !("offer" +ₗ #data)
          else
            (* Someone else was faster. Just try again. *)
            "loop" "stack" "shield".

Definition estack_pop : val :=
  λ: "stack",
    let: "domain" := !("stack" +ₗ #domain) in
    let: "shield" := hazptr.(shield_new) "domain" in
    let: "ov" := estack_pop_loop "stack" "shield" in
    hazptr.(shield_drop) "shield";;
    "ov".

End elimstack.
