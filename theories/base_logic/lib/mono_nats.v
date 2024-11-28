From stdpp Require Import coPset.
From iris.algebra Require Import mono_nat functions.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.
From smr Require Import helpers.

(* TODO: upstream *)
Global Instance discrete_fun_core_id {A} {B : A → ucmra} (f : discrete_fun B) :
  (∀ i, CoreId (f i)) → CoreId f.
Proof. intros ?. constructor => x. by apply core_id_total. Qed.
Global Hint Extern 100 (CoreId (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.

Definition mono_natsR : cmra :=
  positive -d> mono_natUR.

Definition to_mono_nats_auth (E : coPset) (f : Qp) (n : nat) : mono_natsR :=
  λ k, if bool_decide (k ∈ E) then ●MN{#f} n else ◯MN 0.

Definition to_mono_nats_lb (E : coPset) (n : nat) : mono_natsR :=
  λ k, if bool_decide (k ∈ E) then ◯MN n else ◯MN 0.

Section mono_natsR.

  Global Instance to_mono_nats_auth_discrete E f n : Discrete (to_mono_nats_auth E f n).
  Proof. apply _. Qed.

  Global Instance to_mono_nats_lb_core_id E n : CoreId (to_mono_nats_lb E n).
  Proof. rewrite /to_mono_nats_lb. apply _. Qed.

  Global Instance to_mono_nats_lb_discrete E n : Discrete (to_mono_nats_lb E n).
  Proof. apply _. Qed.

  Lemma to_mono_nats_auth_lookup k E q a :
    k ∈ E → to_mono_nats_auth E q a k = ●MN{#q} a.
  Proof. intros. unfold to_mono_nats_auth. by rewrite bool_decide_eq_true_2. Qed.

  Lemma to_mono_nats_auth_lookup_None k E q a :
    k ∉ E → to_mono_nats_auth E q a k = ◯MN 0.
  Proof. intros. unfold to_mono_nats_auth. by rewrite bool_decide_eq_false_2. Qed.

  Lemma to_mono_nats_lb_lookup k E a :
    k ∈ E → to_mono_nats_lb E a k = ◯MN a.
  Proof. intros. unfold to_mono_nats_lb. by rewrite bool_decide_eq_true_2. Qed.

  Lemma to_mono_nats_lb_lookup_None k E a :
    k ∉ E → to_mono_nats_lb E a k = ◯MN 0.
  Proof. intros. unfold to_mono_nats_lb. by rewrite bool_decide_eq_false_2. Qed.

  Lemma to_mono_nats_auth_union E1 E2 q a :
    E1 ## E2 →
    to_mono_nats_auth E1 q a ⋅ to_mono_nats_auth E2 q a
    ≡ to_mono_nats_auth (E1 ∪ E2) q a.
  Proof.
    intros H x. rewrite discrete_fun_lookup_op.
    destruct (decide (x ∈ E1)).
    - rewrite to_mono_nats_auth_lookup; auto.
      rewrite to_mono_nats_auth_lookup_None; last set_solver.
      rewrite to_mono_nats_auth_lookup; last set_solver.
      rewrite mono_nat_auth_lb_op -assoc -mono_nat_lb_op Nat.max_0_r //.
    - rewrite to_mono_nats_auth_lookup_None; auto.
      destruct (decide (x ∈ E2)).
      + rewrite to_mono_nats_auth_lookup; auto.
        rewrite to_mono_nats_auth_lookup; last set_solver. done.
      + rewrite to_mono_nats_auth_lookup_None; auto.
        rewrite to_mono_nats_auth_lookup_None; last set_solver. done.
  Qed.

  Lemma to_mono_nats_lb_union E1 E2 a :
    E1 ## E2 →
    to_mono_nats_lb E1 a ⋅ to_mono_nats_lb E2 a
    ≡ to_mono_nats_lb (E1 ∪ E2) a.
  Proof.
    intros H x. rewrite discrete_fun_lookup_op.
    destruct (decide (x ∈ E1)).
    - rewrite to_mono_nats_lb_lookup; auto.
      rewrite to_mono_nats_lb_lookup_None; last set_solver.
      rewrite to_mono_nats_lb_lookup; last set_solver.
      rewrite -mono_nat_lb_op Nat.max_0_r //.
    - rewrite to_mono_nats_lb_lookup_None; auto.
      destruct (decide (x ∈ E2)).
      + rewrite to_mono_nats_lb_lookup; auto.
        rewrite to_mono_nats_lb_lookup; last set_solver. done.
      + rewrite to_mono_nats_lb_lookup_None; auto.
        rewrite to_mono_nats_lb_lookup_None; last set_solver. done.
  Qed.

  Lemma to_mono_nats_frac E p q a :
    to_mono_nats_auth E p a ⋅ to_mono_nats_auth E q a ≡ to_mono_nats_auth E (p + q) a.
  Proof.
    intros x. rewrite discrete_fun_lookup_op.
    destruct (decide (x ∈ E)).
    - rewrite !to_mono_nats_auth_lookup //.
      rewrite -mono_nat_auth_dfrac_op //.
    - by rewrite !to_mono_nats_auth_lookup_None.
  Qed.

  Lemma to_mono_nats_auth_op E1 E2 a1 q1 a2 q2 :
    to_mono_nats_auth E1 q1 a1 ⋅ to_mono_nats_auth E2 q2 a2
    = λ k', (to_mono_nats_auth E1 q1 a1 k') ⋅ (to_mono_nats_auth E2 q2 a2 k').
  Proof. auto. Qed.

  Lemma to_mono_nats_auth_lb_op E1 E2 a1 q1 a2 :
    to_mono_nats_auth E1 q1 a1 ⋅ to_mono_nats_lb E2 a2
    = λ k', (to_mono_nats_auth E1 q1 a1 k') ⋅ (to_mono_nats_lb E2 a2 k').
  Proof. auto. Qed.

  Lemma to_mono_nats_lb_op E1 E2 a1 a2 :
    to_mono_nats_lb E1 a1 ⋅ to_mono_nats_lb E2 a2
    = λ k', (to_mono_nats_lb E1 a1 k') ⋅ (to_mono_nats_lb E2 a2 k').
  Proof. auto. Qed.

  Lemma mono_nats_included E q n :
    to_mono_nats_lb E n ≼ to_mono_nats_auth E q n.
  Proof.
    exists (to_mono_nats_auth E q n).
    rewrite (comm op) to_mono_nats_auth_lb_op.
    intros k.
    case (decide (k ∈ E)) => Hk.
    - rewrite to_mono_nats_auth_lookup //. rewrite to_mono_nats_lb_lookup //.
      rewrite -mono_nat_auth_lb_op //.
    - rewrite to_mono_nats_auth_lookup_None //. rewrite to_mono_nats_lb_lookup_None //.
  Qed.

  Lemma mono_nats_lb_included E n1 n2 :
    n1 ≤ n2 →
    to_mono_nats_lb E n1 ≼ to_mono_nats_lb E n2.
  Proof.
    exists (to_mono_nats_lb E n2).
    rewrite to_mono_nats_lb_op.
    intros k.
    case (decide (k ∈ E)) => Hk.
    - rewrite !to_mono_nats_lb_lookup //. rewrite -mono_nat_lb_op_le_l //.
    - rewrite !to_mono_nats_lb_lookup_None //.
  Qed.
End mono_natsR.

Class mono_natsG Σ := MonoNatsG {
  mono_nats_inG : inG Σ mono_natsR
}.
Local Existing Instance mono_nats_inG.

Definition mono_natsΣ : gFunctors :=
  #[GFunctor mono_natsR].

Global Instance subG_mono_natsΣ {Σ} :
  subG mono_natsΣ Σ → mono_natsG Σ.
Proof. solve_inG. Qed.

Section mono_nats_def.
  Context `{!mono_natsG Σ}.

  Local Definition mono_nats_auth_def (γ : gname) (E : coPset) (f : Qp) (n : nat) : iProp Σ :=
    own γ (to_mono_nats_auth E f n).
  Local Definition mono_nats_auth_aux : seal (@mono_nats_auth_def). Proof. by eexists. Qed.
  Definition mono_nats_auth := mono_nats_auth_aux.(unseal).
  Local Definition mono_nats_auth_unseal : @mono_nats_auth = @mono_nats_auth_def := mono_nats_auth_aux.(seal_eq).

  Local Definition mono_nats_lb_def (γ : gname) (E : coPset) (n : nat) : iProp Σ :=
    own γ (to_mono_nats_lb E n).
  Local Definition mono_nats_lb_aux : seal (@mono_nats_lb_def). Proof. by eexists. Qed.
  Definition mono_nats_lb := mono_nats_lb_aux.(unseal).
  Local Definition mono_nats_lb_unseal : @mono_nats_lb = @mono_nats_lb_def := mono_nats_lb_aux.(seal_eq).
End mono_nats_def.

Section mono_nats_rules.
  Context `{!mono_natsG Σ}.
  Implicit Types (E : coPset) (q : Qp) (n : nat).

  Local Ltac unseal := rewrite
    ?mono_nats_auth_unseal /mono_nats_auth_def
    ?mono_nats_lb_unseal /mono_nats_lb_def.

  Global Instance mono_nats_auth_timeless γ E q n : Timeless (mono_nats_auth γ E q n).
  Proof. unseal. apply _. Qed.

  Global Instance mono_nats_lb_timeless γ E n : Timeless (mono_nats_lb γ E n).
  Proof. unseal. apply _. Qed.
  Global Instance mono_nats_lb_persistent γ E n : Persistent (mono_nats_lb γ E n).
  Proof. unseal. apply _. Qed.

  Global Instance mono_nats_auth_fractional γ E n :
    Fractional (λ q, mono_nats_auth γ E q n).
  Proof. unseal. intros p q. by rewrite -own_op to_mono_nats_frac. Qed.
  Global Instance mono_nats_auth_as_fractional γ E q n :
    AsFractional (mono_nats_auth γ E q n) (λ q, mono_nats_auth γ E q n) q.
  Proof. split; [auto|apply _]. Qed.

  Lemma mono_nats_own_alloc n :
    ⊢ |==> ∃ γ, mono_nats_auth γ ⊤ 1 n ∗ mono_nats_lb γ ⊤ n.
  Proof.
    unseal. iMod (own_alloc (to_mono_nats_auth ⊤ 1 n ⋅ to_mono_nats_lb ⊤ n)) as (γ) "[??]".
    { intro. rewrite discrete_fun_lookup_op.
      unfold to_mono_nats_auth; simpl. unfold to_mono_nats_lb; simpl.
      by apply mono_nat_both_valid. }
    auto with iFrame.
  Qed.

  Lemma mono_nats_auth_valid γ E1 E2 q1 q2 n1 n2 :
    E1 ∩ E2 ≠ ∅ →
    mono_nats_auth γ E1 q1 n1 -∗
    mono_nats_auth γ E2 q2 n2 -∗
    ⌜(q1 + q2 ≤ 1)%Qp ∧ n1 = n2⌝.
  Proof.
    unseal. iIntros (D) "M1 M2".
    apply coPset_choose in D as [x D].
    iCombine "M1 M2" gives %Q.
    specialize (Q x). rewrite to_mono_nats_auth_op in Q.
    repeat rewrite to_mono_nats_auth_lookup in Q; try set_solver.
    rewrite mono_nat_auth_dfrac_op_valid in Q. done.
  Qed.

  Lemma mono_nats_auth_agree γ E1 E2 q1 q2 n1 n2 :
    E1 ∩ E2 ≠ ∅ →
    mono_nats_auth γ E1 q1 n1 -∗
    mono_nats_auth γ E2 q2 n2 -∗
    ⌜n1 = n2⌝.
  Proof.
    iIntros (D) "M1 M2".
    iDestruct (mono_nats_auth_valid with "M1 M2") as %[_ ?]; auto.
  Qed.

  Lemma mono_nats_auth_singleton_agree γ i q1 q2 n1 n2 :
    mono_nats_auth γ {[i]} q1 n1 -∗
    mono_nats_auth γ {[i]} q2 n2 -∗
    ⌜n1 = n2⌝.
  Proof. apply mono_nats_auth_agree; set_solver. Qed.

  Lemma mono_nats_auth_lb_valid γ E1 E2 q n1 n2 :
    E1 ∩ E2 ≠ ∅ →
    mono_nats_auth γ E1 q n1 -∗
    mono_nats_lb γ E2 n2 -∗
    ⌜n2 ≤ n1⌝.
  Proof.
    unseal. iIntros (D) "A L".
    apply coPset_choose in D as [x D].
    iCombine "A L" gives %Q.
    specialize (Q x). rewrite to_mono_nats_auth_lb_op in Q.
    rewrite to_mono_nats_auth_lookup in Q; try set_solver.
    rewrite to_mono_nats_lb_lookup in Q; try set_solver.
    rewrite mono_nat_both_dfrac_valid in Q. by destruct Q.
  Qed.

  Lemma mono_nats_auth_lb_singleton_valid γ i q n1 n2 :
    mono_nats_auth γ {[i]} q n1 -∗
    mono_nats_lb γ {[i]} n2 -∗
    ⌜n2 ≤ n1⌝.
  Proof. apply mono_nats_auth_lb_valid; set_solver. Qed.

  Lemma mono_nats_lb_get γ E q n :
    mono_nats_auth γ E q n -∗ mono_nats_lb γ E n.
  Proof. unseal. iApply own_mono. apply mono_nats_included. Qed.

  Lemma mono_nats_lb_le m γ E n :
    m ≤ n →
    mono_nats_lb γ E n -∗ mono_nats_lb γ E m.
  Proof. intros. unseal. iApply own_mono. by apply mono_nats_lb_included. Qed.

  Lemma mono_nats_auth_union γ E1 E2 q n :
    E1 ## E2 →
    mono_nats_auth γ (E1 ∪ E2) q n ⊣⊢ mono_nats_auth γ E1 q n ∗ mono_nats_auth γ E2 q n.
  Proof. unseal. intros D. by rewrite -own_op to_mono_nats_auth_union. Qed.

  Lemma mono_nats_lb_union γ E1 E2 n :
    E1 ## E2 →
    mono_nats_lb γ (E1 ∪ E2) n ⊣⊢ mono_nats_lb γ E1 n ∗ mono_nats_lb γ E2 n.
  Proof. unseal. intros D. by rewrite -own_op to_mono_nats_lb_union. Qed.

  Lemma mono_nats_auth_update {γ E n} n' :
    n ≤ n' →
    mono_nats_auth γ E 1 n ==∗ mono_nats_auth γ E 1 n' ∗ mono_nats_lb γ E n'.
  Proof.
    unseal. iIntros (Hn) "A".
    rewrite -own_op. iMod (own_update with "A"); auto.
    apply discrete_fun_update=>x. rewrite discrete_fun_lookup_op.
    destruct (decide (x ∈ E)).
    - repeat rewrite to_mono_nats_auth_lookup; auto.
      rewrite to_mono_nats_lb_lookup; auto.
      rewrite -mono_nat_auth_lb_op. by apply mono_nat_update.
    - repeat rewrite to_mono_nats_auth_lookup_None; auto.
      rewrite to_mono_nats_lb_lookup_None; auto. done.
  Qed.

  Lemma mono_nats_auth_update_plus {γ E n} m :
    mono_nats_auth γ E 1 n ==∗ mono_nats_auth γ E 1 (n + m) ∗ mono_nats_lb γ E (n + m).
  Proof. apply mono_nats_auth_update. lia. Qed.

End mono_nats_rules.
