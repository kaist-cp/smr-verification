(* Edit of the Iris mono_nat to support persistent ownership. *)

From iris.algebra.lib Require Import mono_nat.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own mono_nat.
From iris.prelude Require Import options.

Local Existing Instance mono_natG_inG.

Local Definition mono_nat_persistent_def `{!mono_natG Σ}
    (γ : gname) (n : nat) : iProp Σ :=
  own γ (●MN□ n).
Local Definition mono_nat_persistent_aux : seal (@mono_nat_persistent_def).
Proof. by eexists. Qed.
Definition mono_nat_persistent := mono_nat_persistent_aux.(unseal).
Local Definition mono_nat_persistent_unseal :
  @mono_nat_persistent = @mono_nat_persistent_def := mono_nat_persistent_aux.(seal_eq).
Global Arguments mono_nat_persistent {Σ _} γ n.

Local Ltac unseal := rewrite
  ?mono_nat.mono_nat_auth_own_unseal /mono_nat.mono_nat_auth_own_def
  ?mono_nat.mono_nat_lb_own_unseal /mono_nat.mono_nat_lb_own_def
  ?mono_nat_persistent_unseal /mono_nat_persistent_def.

Section mono_nat.
  Context `{!mono_natG Σ}.
  Implicit Types (n m : nat).

  Global Instance mono_nat_persistent_timeless γ n : Timeless (mono_nat_persistent γ n).
  Proof. unseal. apply _. Qed.
  Global Instance mono_nat_persistent_persistent γ n : Persistent (mono_nat_persistent γ n).
  Proof. unseal. apply _. Qed.

  Lemma mono_nat_persistent_lb_own_valid γ n m :
    mono_nat_persistent γ n -∗ mono_nat_lb_own γ m -∗ ⌜m ≤ n⌝.
  Proof.
    unseal. iIntros "Hpers Hlb".
    by iCombine "Hpers Hlb" gives %[_ ?]%mono_nat_both_dfrac_valid.
  Qed.

  Lemma mono_nat_persistent_agree γ n1 n2 :
    mono_nat_persistent γ n1 -∗
    mono_nat_persistent γ n2 -∗
    ⌜n1 = n2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    by iCombine "H1 H2" gives %[_ ?]%mono_nat_auth_dfrac_op_valid.
  Qed.

  Lemma mono_nat_persistent_lb_own_get γ n :
    mono_nat_persistent γ n -∗ mono_nat_lb_own γ n.
  Proof. unseal. iApply own_mono; apply mono_nat_included. Qed.

  Lemma mono_nat_own_persist γ q n :
    mono_nat_auth_own γ q n ==∗ mono_nat_persistent γ n.
  Proof. unseal. iApply own_update; apply mono_nat_auth_persist. Qed.

End mono_nat.
