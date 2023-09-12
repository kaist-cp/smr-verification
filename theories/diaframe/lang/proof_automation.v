From iris.prelude Require Import options.

From iris.proofmode Require Export proofmode.
From diaframe Require Export proofmode_base.
From smr.diaframe.lang Require Export base_hints specs.
From diaframe Require Export steps.verify_tac.

From iris.bi Require Export bi telescopes derived_laws.
From iris.base_logic Require Export lib.invariants.

From smr.lang Require Export notation derived_laws.
From smr.lang Require Import proofmode.


(* Importing this file should give you access to Diaframe's automation,
   including required hints to automatically verify programs written in
   heap_lang. *)
