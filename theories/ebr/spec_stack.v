From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr.ebr Require Import spec_rcu_simple.
From iris.prelude Require Import options.

Definition StackT Σ : Type :=
  ∀ (γs : gname) (xs : list val), iProp Σ.

Definition IsStackT Σ (N : namespace) : Type :=
  ∀ (γe γs : gname) (l : loc), iProp Σ.

Section spec.
Context {Σ} `{!heapGS Σ}.
Context (stackN rcuN : namespace) (DISJN : stackN ## rcuN).
Variables
  (stack_new : val)
  (stack_push : val)
  (stack_pop : val).
Variables
  (rcu : rcu_simple_spec Σ rcuN)
  (Stack : StackT Σ)
  (IsStack : IsStackT Σ stackN).

Definition stack_new_spec' : Prop :=
  ⊢ ∀ γe d,
  {{{ rcu.(IsRCUDomain) γe d }}}
    stack_new #d
  {{{ γs st, RET #st; IsStack γe γs st ∗ Stack γs [] }}}.

Definition stack_push_spec' : Prop :=
  ⊢ ∀ γe γs st g (x : val),
  IsStack γe γs st -∗ rcu.(Guard) γe g Deactivated -∗
  <<{ ∀∀ xs, Stack γs xs }>>
    stack_push #st x #g @ ⊤,(↑stackN ∪ ↑(ptrsN rcuN)),↑(mgmtN rcuN)
  <<{ Stack γs (x::xs) | RET #(); rcu.(Guard) γe g Deactivated }>>.

Definition stack_pop_spec' : Prop :=
  ⊢ ∀ γe γs st g,
  IsStack γe γs st -∗  rcu.(Guard) γe g Deactivated -∗
  <<{ ∀∀ xs, Stack γs xs }>>
    stack_pop #st #g @ ⊤,(↑stackN ∪ ↑(ptrsN rcuN)),↑(mgmtN rcuN)
  <<{ Stack γs (match xs with | [] => [] | _::xs => xs end) |
      RET (match xs with | [] => NONEV | v::_ => SOMEV v end);
      rcu.(Guard) γe g Deactivated
  }>>.

End spec.

Record stack_code : Type := StackCode {
  stack_new : val;
  stack_push : val;
  stack_pop : val;
}.

Record stack_spec {Σ} `{!heapGS Σ} {stackN rcuN : namespace}
    {DISJN : stackN ## rcuN}
    {rcu : rcu_simple_spec Σ rcuN}
  : Type := StackSpec {
  stack_spec_code :> stack_code;

  Stack: StackT Σ;
  IsStack : IsStackT Σ stackN;

  Stack_Timeless : ∀ γs xs, Timeless (Stack γs xs);
  IsStack_Persistent : ∀ γe γs l, Persistent (IsStack γe γs l);

  stack_new_spec : stack_new_spec' stackN rcuN stack_spec_code.(stack_new) rcu Stack IsStack;
  stack_push_spec : stack_push_spec' stackN rcuN stack_spec_code.(stack_push) rcu Stack IsStack;
  stack_pop_spec : stack_pop_spec' stackN rcuN stack_spec_code.(stack_pop) rcu Stack IsStack;
}.

Global Arguments stack_spec : clear implicits.
Global Arguments stack_spec _ {_} _ _ _ _ : assert.
Global Existing Instances Stack_Timeless IsStack_Persistent.
