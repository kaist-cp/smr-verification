(* Modified version supporting persistent ghost vars. *)

From iris.algebra Require Import dfrac_agree.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own ghost_var.
From iris.prelude Require Import options.

Local Existing Instance ghost_var_inG.

Local Definition persistent_ghost_var_def `{!ghost_varG Σ A}
    (γ : gname) (a : A) : iProp Σ :=
  own γ (to_dfrac_agree (A:=leibnizO A) (DfracDiscarded) a).
Local Definition persistent_ghost_var_aux : seal (@persistent_ghost_var_def). Proof. by eexists. Qed.
Definition persistent_ghost_var := persistent_ghost_var_aux.(unseal).
Local Definition persistent_ghost_var_unseal :
  @persistent_ghost_var = @persistent_ghost_var_def := persistent_ghost_var_aux.(seal_eq).
Global Arguments persistent_ghost_var {Σ A _} γ a.

Local Ltac unseal := rewrite
  ?ghost_var.ghost_var_unseal /ghost_var.ghost_var_def
  ?persistent_ghost_var_unseal /persistent_ghost_var_def.

Section lemmas.
  Context `{!ghost_varG Σ A}.
  Implicit Types (a b : A) (q : Qp).

  Global Instance persistent_ghost_var_timeless γ a : Timeless (persistent_ghost_var γ a).
  Proof. unseal. apply _. Qed.
  Global Instance persistent_ghost_var_persistent γ a : Persistent (persistent_ghost_var γ a).
  Proof. unseal. apply _. Qed.

  (** Persistent ghost var rules *)
  Lemma ghost_var_persist γ q a :
    ghost_var γ q a ==∗ persistent_ghost_var γ a.
  Proof. unseal. iApply own_update. apply dfrac_agree_persist. Qed.

  Lemma persistent_ghost_var_valid_2 γ a1 a2 q2 :
    persistent_ghost_var γ a1 -∗ ghost_var γ q2 a2 -∗ ⌜(q2 < 1)%Qp ∧ a1 = a2⌝.
  Proof.
    unseal. iIntros "Hvar1 Hvar2".
    iCombine "Hvar1 Hvar2" gives %[Hq Ha]%dfrac_agree_op_valid_L.
    done.
  Qed.
  (** Almost all the time, this is all you really need. *)
  Lemma persistent_ghost_var_agree γ a1 a2 q2 :
    persistent_ghost_var γ a1 -∗ ghost_var γ q2 a2 -∗ ⌜a1 = a2⌝.
  Proof.
    iIntros "Hvar1 Hvar2".
    iDestruct (persistent_ghost_var_valid_2 with "Hvar1 Hvar2") as %[_ ?]. done.
  Qed.

  Global Instance persistent_ghost_var_combine_gives_1 γ a1 a2 q2 :
    CombineSepGives (persistent_ghost_var γ a1) (ghost_var γ q2 a2)
      ⌜(q2 < 1)%Qp ∧ a1 = a2⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (persistent_ghost_var_valid_2 with "H1 H2") as %[H1 H2].
    eauto.
  Qed.

  Global Instance persistent_ghost_var_combine_gives_2 γ a1 a2 q2 :
    CombineSepGives (ghost_var γ q2 a2) (persistent_ghost_var γ a1)
      ⌜(q2 < 1)%Qp ∧ a1 = a2⌝.
  Proof.
    rewrite /CombineSepGives comm. apply persistent_ghost_var_combine_gives_1.
  Qed.

End lemmas.
