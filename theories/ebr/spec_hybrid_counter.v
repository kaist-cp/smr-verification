From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr.ebr Require Import spec_rcu_simple.
From iris.prelude Require Import options.

Definition HCounterT Σ : Type :=
  ∀ (γc : gname) (x : nat), iProp Σ.

Definition IsHCounterT Σ (N : namespace) : Type :=
  ∀ (γe γc : gname) (c : loc), iProp Σ.

Section spec.
Context {Σ} `{!heapGS Σ} (hcounterN rcuN : namespace) (DISJN : hcounterN ## rcuN).
Variables
  (hcounter_new : val)
  (hcounter_inc : val).
Variables
  (rcu : rcu_simple_spec Σ rcuN)
  (HCounter : HCounterT Σ )
  (IsHCounter : IsHCounterT Σ hcounterN).

Definition hcounter_new_spec' : Prop :=
  ⊢ ∀ γd d,
  {{{ rcu.(IsRCUDomain) γd d }}}
    hcounter_new #d
  {{{ γc c, RET #c; IsHCounter γd γc c ∗ HCounter γc 0%nat }}}.

Definition hcounter_inc_spec' : Prop :=
  ⊢ ∀ γe γc c g,
  IsHCounter γe γc c -∗ rcu.(Guard) γe g Deactivated -∗
  <<< ∀∀ (x : nat), HCounter γc x >>>
    hcounter_inc #c #g @ ⊤,(↑hcounterN ∪ ↑(ptrsN rcuN)),↑(mgmtN rcuN)
  <<< HCounter γc (x + 1)%nat, RET #x, rcu.(Guard) γe g Deactivated >>>.

End spec.

Record hcounter_code : Type := HCounterCode {
  hcounter_new : val;
  hcounter_inc : val;
}.

Record hcounter_spec {Σ} `{!heapGS Σ} {hcounterN rcuN : namespace}
    {DISJN : hcounterN ## rcuN}
    {rcu : rcu_simple_spec Σ rcuN}
  : Type := HCounterSpec {
  hcounter_spec_code :> hcounter_code;

  HCounter: HCounterT Σ;
  IsHCounter : IsHCounterT Σ hcounterN;

  HCounter_Timeless : ∀ γc c, Timeless (HCounter γc c);
  IsHCounter_Persistent : ∀ γe γc l, Persistent (IsHCounter γe γc l);

  hcounter_new_spec : hcounter_new_spec' hcounterN rcuN hcounter_spec_code.(hcounter_new) rcu HCounter IsHCounter;
  hcounter_inc_spec : hcounter_inc_spec' hcounterN rcuN hcounter_spec_code.(hcounter_inc) rcu HCounter IsHCounter;
}.

Global Arguments hcounter_spec : clear implicits.
Global Arguments hcounter_spec _ {_} _ _ _ _ : assert.
Global Existing Instances HCounter_Timeless IsHCounter_Persistent.
