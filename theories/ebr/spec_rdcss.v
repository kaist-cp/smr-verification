From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr.ebr Require Import spec_rcu_simple.
From iris.prelude Require Import options.

Definition RdcssT Σ : Type :=
  ∀ (γ_n : gname) (n : val), iProp Σ.

Definition IsRdcssT Σ (N : namespace) : Type :=
  ∀ (γ_e γ_n : gname) (l_n : loc), iProp Σ.

Section spec.
Context `{!heapGS Σ}.
Context (rdcssN : namespace) (rcuN : namespace) (DISJN : rdcssN ## rcuN).
Variables
  (new_rdcss : val)
  (get : val)
  (rdcss : val).
Variables
  (rcu : rcu_simple_spec Σ rcuN)
  (Rdcss : RdcssT Σ)
  (IsRdcss : IsRdcssT Σ rdcssN).

Definition new_rdcss_spec' : Prop :=
  ⊢ ∀ γ_e d (n : val),
  ⌜rdcssN ## inv_heapN⌝ → inv_heap_inv -∗
  {{{ rcu.(IsRCUDomain) γ_e d }}}
    new_rdcss n #d
  {{{ (γ_n : gname) l_n, RET #l_n; IsRdcss γ_e γ_n l_n ∗ Rdcss γ_n n }}}.

Definition get_spec' : Prop :=
  ⊢ ∀ γ_e γ_n (l_n : loc) g,
  IsRdcss γ_e γ_n l_n -∗ rcu.(Guard) γ_e g Deactivated -∗
  <<{ ∀∀ (n : val), Rdcss γ_n n }>>
    get #l_n #g @ ⊤,(↑rdcssN ∪ ↑(ptrsN rcuN)),↑(mgmtN rcuN)
  <<{ Rdcss γ_n n | RET n; rcu.(Guard) γ_e g Deactivated }>>.

Definition rdcss_spec' : Prop :=
  ⊢ ∀ γ_e γ_n (l_n l_m g : loc) (m1 n1 n2 : val),
  ⌜val_is_unboxed (InjLV n1)⌝ →
  ⌜val_is_unboxed m1⌝ →
  IsRdcss γ_e γ_n l_n -∗
  rcu.(Guard) γ_e g Deactivated -∗
  <<{ ∀∀ (m n : val), l_m ↦_(λ _, True) m ∗ Rdcss γ_n n }>>
    rdcss #l_m #l_n m1 n1 n2 #g @ ⊤,(↑rdcssN ∪ ↑(ptrsN rcuN) ∪ ↑inv_heapN),↑(mgmtN rcuN)
  <<{ l_m ↦_(λ _, True) m ∗ Rdcss γ_n (if decide (m = m1 ∧ n = n1) then n2 else n) | RET n; rcu.(Guard) γ_e g Deactivated }>>.

End spec.

Record rdcss_code : Type := RdcssCode {
  new_rdcss : val;
  get : val;
  rdcss : val;
}.

Record rdcss_spec_record {Σ} `{!heapGS Σ} {rdcssN rcuN : namespace}
    {DISJN : rdcssN ## rcuN}
    {rcu : rcu_simple_spec Σ rcuN}
  : Type := RdcssSpec {
  rdcss_spec_code :> rdcss_code;

  Rdcss : RdcssT Σ;
  IsRdcss : IsRdcssT Σ rdcssN;

  Rdcss_Timeless : ∀ γ_n n, Timeless (Rdcss γ_n n);
  IsRdcss_Persistent : ∀ γ_e γ_n l_n, Persistent (IsRdcss γ_e γ_n l_n);

  new_rdcss_spec : new_rdcss_spec' rdcssN rcuN rdcss_spec_code.(new_rdcss) rcu Rdcss IsRdcss;
  get_spec : get_spec' rdcssN rcuN rdcss_spec_code.(get) rcu Rdcss IsRdcss;
  rdcss_spec : rdcss_spec' rdcssN rcuN rdcss_spec_code.(rdcss) rcu Rdcss IsRdcss;
}.

Global Arguments rdcss_spec_record : clear implicits.
Global Arguments rdcss_spec_record _ {_} _ _ _ _ : assert.
Global Existing Instances Rdcss_Timeless IsRdcss_Persistent.
