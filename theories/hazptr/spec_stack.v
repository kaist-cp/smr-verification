From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr.hazptr Require Import spec_hazptr.
From iris.prelude Require Import options.

Definition StackT Σ : Type :=
  ∀ (γ : gname) (xs : list val), iProp Σ.

Definition IsStackT Σ (N : namespace) : Type :=
  ∀ (γ : gname) (l : loc), iProp Σ.

Section spec.
Context `{!heapGS Σ}.
Context (stackN : namespace) (hazptrN : namespace) (DISJN : stackN ## hazptrN).
Variables
  (stack_new : val)
  (stack_push : val)
  (stack_pop : val).
Variables
  (hazptr : hazard_pointer_spec Σ hazptrN)
  (Stack : StackT Σ)
  (IsStack : IsStackT Σ stackN).

Definition stack_new_spec' : Prop :=
  ⊢ ∀ γd d,
  {{{ hazptr.(IsHazardDomain) γd d }}}
    stack_new #d
  {{{ γ st, RET #st; IsStack γ st ∗ Stack γ [] }}}.

Definition stack_push_spec' : Prop :=
  ⊢ ∀ γ st (x : val),
  IsStack γ st -∗
  <<< ∀∀ xs, Stack γ xs >>>
    stack_push #st x @ ⊤,(↑stackN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
  <<< Stack γ (x::xs), RET #() >>>.

Definition stack_pop_spec' : Prop :=
  ⊢ ∀ γ st,
  IsStack γ st -∗
  <<< ∀∀ xs, Stack γ xs >>>
    stack_pop #st @ ⊤,(↑stackN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
  <<< Stack γ (match xs with | [] => [] | _::xs => xs end),
      RET (match xs with | [] => NONEV | v::_ => SOMEV v end)
  >>>.

End spec.

Record stack_code : Type := StackCode {
  stack_new : val;
  stack_push : val;
  stack_pop : val;
}.

Record stack_spec {Σ} `{!heapGS Σ} {stackN hazptrN : namespace}
    {DISJN : stackN ## hazptrN}
    {hazptr : hazard_pointer_spec Σ hazptrN}
  : Type := StackSpec {
  stack_spec_code :> stack_code;

  Stack: StackT Σ;
  IsStack : IsStackT Σ stackN;

  Stack_Timeless : ∀ γ xs, Timeless (Stack γ xs);
  IsStack_Persistent : ∀ γ l, Persistent (IsStack γ l);

  stack_new_spec : stack_new_spec' stackN hazptrN stack_spec_code.(stack_new) hazptr Stack IsStack;
  stack_push_spec : stack_push_spec' stackN hazptrN stack_spec_code.(stack_push) Stack IsStack;
  stack_pop_spec : stack_pop_spec' stackN hazptrN stack_spec_code.(stack_pop) Stack IsStack;
}.

Global Arguments stack_spec : clear implicits.
Global Arguments stack_spec _ {_} _ _ _ _ : assert.
Global Existing Instances Stack_Timeless IsStack_Persistent.
