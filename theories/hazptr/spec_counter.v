From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr.hazptr Require Import spec_hazptr.
From iris.prelude Require Import options.

Definition CounterT Σ : Type :=
  ∀ (γ : gname) (z : Z), iProp Σ.

Definition IsCounterT Σ (N : namespace) : Type :=
  ∀ (γ : gname) (c : loc), iProp Σ.

Local Open Scope Z.

Section spec.
Context `{!heapGS Σ}.
Context (counterN : namespace) (hazptrN : namespace) (DISJN : counterN ## hazptrN).
Variables
  (counter_new : val)
  (counter_inc : val).
Variables
  (hazptr : hazard_pointer_spec Σ hazptrN)
  (Counter : CounterT Σ)
  (IsCounter : IsCounterT Σ counterN).

Definition counter_new_spec' : Prop :=
  ⊢ ∀ γd d,
  {{{ hazptr.(IsHazardDomain) γd d }}}
    counter_new #d
  {{{ γ c, RET #c; IsCounter γ c ∗ Counter γ 0 }}}.

Definition counter_inc_spec' : Prop :=
  ⊢ ∀ γ c,
  IsCounter γ c -∗
  <<< ∀∀ (x : Z), Counter γ x >>>
    counter_inc #c @ ⊤,↑counterN,↑(mgmtN hazptrN)
  <<< Counter γ (x + 1), RET #x >>>.

End spec.

Record counter_code : Type := CounterCode {
  counter_new : val;
  counter_inc : val;
}.

Record counter_spec {Σ} `{!heapGS Σ} {counterN hazptrN : namespace}
    {DISJN : counterN ## hazptrN}
    {hazptr : hazard_pointer_spec Σ hazptrN}
  : Type := CounterSpec {
  counter_spec_code :> counter_code;

  Counter: CounterT Σ;
  IsCounter : IsCounterT Σ counterN;

  Counter_Timeless : ∀ γ c, Timeless (Counter γ c);
  IsCounter_Persistent : ∀ γ l, Persistent (IsCounter γ l);

  counter_new_spec : counter_new_spec' counterN hazptrN counter_spec_code.(counter_new) hazptr Counter IsCounter;
  counter_inc_spec : counter_inc_spec' counterN hazptrN counter_spec_code.(counter_inc) Counter IsCounter;
}.

Global Arguments counter_spec : clear implicits.
Global Arguments counter_spec _ {_} _ _ _ _ : assert.
Global Existing Instances Counter_Timeless IsCounter_Persistent.
