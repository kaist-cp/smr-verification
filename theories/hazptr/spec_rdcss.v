From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr.hazptr Require Import spec_hazptr.
From iris.prelude Require Import options.

Definition RdcssT Σ : Type :=
  ∀ (γ : gname) (n : val), iProp Σ.

Definition IsRdcssT Σ (N : namespace) : Type :=
  ∀ (γ : gname) (l_n : loc), iProp Σ.

Section spec.
Context `{!heapGS Σ}.
Context (rdcssN : namespace) (hazptrN : namespace) (DISJN : rdcssN ## hazptrN).
Variables
  (new_rdcss : val)
  (get : val)
  (rdcss : val).
Variables
  (hazptr : hazard_pointer_spec Σ hazptrN)
  (Rdcss : RdcssT Σ)
  (IsRdcss : IsRdcssT Σ rdcssN).

Definition new_rdcss_spec' : Prop :=
  ⊢ ∀ γd d (n : val),
  ⌜rdcssN ## inv_heapN⌝ → inv_heap_inv -∗
  {{{ hazptr.(IsHazardDomain) γd d }}}
    new_rdcss n #d
  {{{ (γ γ_n : gname) l_n, RET #l_n; ⌜γ = encode (γd, γ_n)⌝ ∗ IsRdcss γ l_n ∗ Rdcss γ n }}}.

Definition get_spec' : Prop :=
  ⊢ ∀ γ (l_n : loc),
  IsRdcss γ l_n -∗
  <<< ∀∀ (n : val), Rdcss γ n >>>
    get #l_n @ ⊤,(↑rdcssN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
  <<< Rdcss γ n, RET n >>>.

Definition rdcss_spec' : Prop :=
  ⊢ ∀ γ (l_n l_m : loc) (m1 n1 n2 : val),
  ⌜val_is_unboxed (InjLV n1)⌝ →
  ⌜val_is_unboxed m1⌝ →
  IsRdcss γ l_n -∗
  <<< ∀∀ (m n : val), l_m ↦_(λ _, True) m ∗ Rdcss γ n >>>
    rdcss #l_m #l_n m1 n1 n2 @ ⊤,(↑rdcssN ∪ ↑(ptrsN hazptrN) ∪ ↑inv_heapN),↑(mgmtN hazptrN)
  <<< l_m ↦_(λ _, True) m ∗ Rdcss γ (if decide (m = m1 ∧ n = n1) then n2 else n), RET n >>>.

End spec.

Record rdcss_code : Type := RdcssCode {
  new_rdcss : val;
  get : val;
  rdcss : val;
}.

Record rdcss_spec_record {Σ} `{!heapGS Σ} {rdcssN hazptrN : namespace}
    {DISJN : rdcssN ## hazptrN}
    {hazptr : hazard_pointer_spec Σ hazptrN}
  : Type := RdcssSpec {
  rdcss_spec_code :> rdcss_code;

  Rdcss : RdcssT Σ;
  IsRdcss : IsRdcssT Σ rdcssN;

  Rdcss_Timeless : ∀ γ n, Timeless (Rdcss γ n);
  IsRdcss_Persistent : ∀ γ l_n, Persistent (IsRdcss γ l_n);

  new_rdcss_spec : new_rdcss_spec' rdcssN hazptrN rdcss_spec_code.(new_rdcss) hazptr Rdcss IsRdcss;
  get_spec : get_spec' rdcssN hazptrN rdcss_spec_code.(get) Rdcss IsRdcss;
  rdcss_spec : rdcss_spec' rdcssN hazptrN rdcss_spec_code.(rdcss) Rdcss IsRdcss;
}.

Global Arguments rdcss_spec_record : clear implicits.
Global Arguments rdcss_spec_record _ {_} _ _ _ _ : assert.
Global Existing Instances Rdcss_Timeless IsRdcss_Persistent.
