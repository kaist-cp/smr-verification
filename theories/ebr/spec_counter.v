From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr.ebr Require Import spec_rcu_simple.
From iris.prelude Require Import options.

Local Open Scope Z.

Definition CounterT Σ : Type :=
  ∀ (γ : gname) (z : Z), iProp Σ.

Definition IsCounterT Σ (N : namespace) : Type :=
  ∀ (γe γc : gname) (c : loc), iProp Σ.

Section spec.
Context {Σ} `{!heapGS Σ}.
Context (counterN : namespace) (rcuN : namespace) (DISJN : counterN ## rcuN).
Variables
  (counter_new : val)
  (counter_inc : val).
Variables
  (rcu : rcu_simple_spec Σ rcuN)
  (Counter : CounterT Σ)
  (IsCounter : IsCounterT Σ counterN).

Definition counter_new_spec' : Prop :=
  ⊢ ∀ γd d,
  {{{ rcu.(IsRCUDomain) γd d }}}
    counter_new #d
  {{{ γc c, RET #c; IsCounter γd γc c ∗ Counter γc 0 }}}.

Definition counter_inc_spec' : Prop :=
  ⊢ ∀ γe γc c g,
  IsCounter γe γc c -∗ rcu.(Guard) γe g Deactivated -∗
  <<< ∀∀ (x : Z), Counter γc x >>>
    counter_inc #c #g @ ⊤,↑counterN,↑(mgmtN rcuN)
  <<< Counter γc (x + 1), RET #x, rcu.(Guard) γe g Deactivated >>>.

End spec.

Record counter_code : Type := CounterCode {
  counter_new : val;
  counter_inc : val;
}.

Record counter_spec {Σ} `{!heapGS Σ} {counterN rcuN : namespace}
    {DISJN : counterN ## rcuN}
    {rcu : rcu_simple_spec Σ rcuN}
  : Type := CounterSpec {
  counter_spec_code :> counter_code;

  Counter: CounterT Σ;
  IsCounter : IsCounterT Σ counterN;

  Counter_Timeless : ∀ γ c, Timeless (Counter γ c);
  IsCounter_Persistent : ∀ γe γc l, Persistent (IsCounter γe γc l);

  counter_new_spec : counter_new_spec' counterN rcuN counter_spec_code.(counter_new) rcu Counter IsCounter;
  counter_inc_spec : counter_inc_spec' counterN rcuN counter_spec_code.(counter_inc) rcu Counter IsCounter;
}.

Global Arguments counter_spec : clear implicits.
Global Arguments counter_spec _ {_} _ _ _ _: assert.
Global Existing Instances Counter_Timeless IsCounter_Persistent.
