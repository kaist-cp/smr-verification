From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr.hazptr Require Import spec_hazptr.
From iris.prelude Require Import options.

Definition QueueT Σ : Type :=
  ∀ (γ : gname) (xs : list val), iProp Σ.

Definition IsQueueT Σ (N : namespace) : Type :=
  ∀ (γq : gname) (qu : loc), iProp Σ.

Section spec.
Context `{!heapGS Σ}.
Context (queueN : namespace) (hazptrN : namespace) (DISJN : queueN ## hazptrN).
Variables
  (queue_new : val)
  (queue_push : val)
  (queue_pop : val).
Variables
  (hazptr : hazard_pointer_spec Σ hazptrN)
  (Queue : QueueT Σ )
  (IsQueue : IsQueueT Σ queueN).

Definition queue_new_spec' : Prop :=
  ⊢ ∀ γd d,
  {{{ hazptr.(IsHazardDomain) γd d }}}
    queue_new #d
  {{{ γq qu, RET #qu; IsQueue γq qu ∗ Queue γq [] }}}.

Definition queue_push_spec' : Prop :=
  ⊢ ∀ γq qu (x : val),
  IsQueue γq qu -∗
  <<{ ∀∀ xs, Queue γq xs }>>
    queue_push #qu x @ ⊤,(↑queueN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
  <<{ Queue γq (xs ++ [x]) | RET #() }>>.

Definition queue_pop_spec' : Prop :=
  ⊢ ∀ γq qu,
  IsQueue γq qu -∗
  <<{ ∀∀ xs, Queue γq xs }>>
    queue_pop #qu @ ⊤,(↑queueN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
  <<{ Queue γq (match xs with [] => [] | _::xs => xs end) |
      RET (match xs with [] => NONEV | v::_ => SOMEV v end)
  }>>.
End spec.

Record queue_code : Type := QueueCode {
  queue_new : val;
  queue_push : val;
  queue_pop : val;
}.

Record queue_spec {Σ} `{!heapGS Σ} {queueN hazptrN : namespace}
    {DISJN : queueN ## hazptrN}
    {hazptr : hazard_pointer_spec Σ hazptrN}
  : Type := QueueSpec {
  queue_spec_code :> queue_code;

  Queue: QueueT Σ;
  IsQueue : IsQueueT Σ queueN;

  Queue_Timeless : ∀ γ xs, Timeless (Queue γ xs);
  IsQueue_Persistent : ∀ γ l, Persistent (IsQueue γ l);

  queue_new_spec : queue_new_spec' queueN hazptrN queue_spec_code.(queue_new) hazptr Queue IsQueue;
  queue_push_spec : queue_push_spec' queueN hazptrN queue_spec_code.(queue_push) Queue IsQueue;
  queue_pop_spec : queue_pop_spec' queueN hazptrN queue_spec_code.(queue_pop) Queue IsQueue;
}.

Global Arguments queue_spec : clear implicits.
Global Arguments queue_spec _ {_} _ _ _ _ : assert.
Global Existing Instances Queue_Timeless IsQueue_Persistent.
