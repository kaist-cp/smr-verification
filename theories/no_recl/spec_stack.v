From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

Definition StackT Σ : Type :=
  ∀ (γ : gname) (xs : list val), iProp Σ.

Definition IsStackT Σ (N : namespace) : Type :=
  ∀ (γ : gname) (l : loc), iProp Σ.

Section spec.
Context `{!heapGS Σ}.
Context (stackN : namespace).
Variables
  (stack_new : val)
  (stack_push : val)
  (stack_pop : val).
Variables
  (Stack : StackT Σ)
  (IsStack : IsStackT Σ stackN).

Definition stack_new_spec' : Prop :=
  ⊢
  {{{ True }}}
    stack_new #()
  {{{ γ st, RET #st; IsStack γ st ∗ Stack γ [] }}}.

Definition stack_push_spec' : Prop :=
  ⊢ ∀ γ st (x : val),
  IsStack γ st -∗
  <<< ∀∀ xs, Stack γ xs >>>
    stack_push #st x @ ⊤,↑stackN,∅
  <<< Stack γ (x::xs), RET #() >>>.

Definition stack_pop_spec' : Prop :=
  ⊢ ∀ γ st,
  IsStack γ st -∗
  <<< ∀∀ xs, Stack γ xs >>>
    stack_pop #st @ ⊤,↑stackN,∅
  <<< Stack γ (match xs with | [] => [] | _::xs' => xs' end),
      RET (match xs with | [] => NONEV | v::_ => SOMEV v end)
  >>>.

End spec.

Record stack_code : Type := StackCode {
  stack_new : val;
  stack_push : val;
  stack_pop : val;
}.

Record stack_spec {Σ} `{!heapGS Σ} {stackN : namespace}
  : Type := StackSpec {
  stack_spec_code :> stack_code;

  Stack: StackT Σ;
  IsStack : IsStackT Σ stackN;

  Stack_Timeless : ∀ γ xs, Timeless (Stack γ xs);
  IsStack_Persistent : ∀ γ l, Persistent (IsStack γ l);

  stack_new_spec : stack_new_spec' stackN stack_spec_code.(stack_new) Stack IsStack;
  stack_push_spec : stack_push_spec' stackN stack_spec_code.(stack_push) Stack IsStack;
  stack_pop_spec : stack_pop_spec' stackN stack_spec_code.(stack_pop) Stack IsStack;
}.

Global Arguments stack_spec : clear implicits.
Global Arguments stack_spec _ {_} _ : assert.
Global Existing Instances Stack_Timeless IsStack_Persistent.
