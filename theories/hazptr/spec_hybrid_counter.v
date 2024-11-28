From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr.hazptr Require Import spec_hazptr.
From iris.prelude Require Import options.

Definition HCounterT Σ : Type :=
  ∀ (γ : gname) (x : nat), iProp Σ.

Definition IsHCounterT Σ (N : namespace) : Type :=
  ∀ (γ : gname) (c : loc), iProp Σ.

Section spec.
Context `{!heapGS Σ}.
Context (hcounterN : namespace) (hazptrN : namespace) (DISJN : hcounterN ## hazptrN).
Variables
  (hcounter_new : val)
  (hcounter_inc : val).
Variables
  (hazptr : hazard_pointer_spec Σ hazptrN)
  (HCounter : HCounterT Σ )
  (IsHCounter : IsHCounterT Σ hcounterN).

Definition hcounter_new_spec' : Prop :=
  ⊢ ∀ γd d,
  {{{ hazptr.(IsHazardDomain) γd d }}}
    hcounter_new #d
  {{{ γ c, RET #c; IsHCounter γ c ∗ HCounter γ 0%nat }}}.

Definition hcounter_inc_spec' : Prop :=
  ⊢ ∀ γ c,
  IsHCounter γ c -∗
  <<{ ∀∀ (x : nat), HCounter γ x }>>
    hcounter_inc #c @ ⊤,(↑hcounterN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
  <<{ HCounter γ (x + 1)%nat | RET #x }>>.

End spec.

Record hcounter_code : Type := HCounterCode {
  hcounter_new : val;
  hcounter_inc : val;
}.

Record hcounter_spec {Σ} `{!heapGS Σ} {hcounterN hazptrN : namespace}
    {DISJN : hcounterN ## hazptrN}
    {hazptr : hazard_pointer_spec Σ hazptrN}
  : Type := HCounterSpec {
  hcounter_spec_code :> hcounter_code;

  HCounter: HCounterT Σ;
  IsHCounter : IsHCounterT Σ hcounterN;

  HCounter_Timeless : ∀ γ c, Timeless (HCounter γ c);
  IsHCounter_Persistent : ∀ γ l, Persistent (IsHCounter γ l);

  hcounter_new_spec : hcounter_new_spec' hcounterN hazptrN hcounter_spec_code.(hcounter_new) hazptr HCounter IsHCounter;
  hcounter_inc_spec : hcounter_inc_spec' hcounterN hazptrN hcounter_spec_code.(hcounter_inc) HCounter IsHCounter;
}.

Global Arguments hcounter_spec : clear implicits.
Global Arguments hcounter_spec _ {_} _ _ _ _ : assert.
Global Existing Instances HCounter_Timeless IsHCounter_Persistent.
