From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr.ebr Require Import spec_rcu_simple.
From iris.prelude Require Import options.

Definition QueueT Σ : Type :=
  ∀ (γq : gname) (xs : list val), iProp Σ.

Definition IsQueueT Σ (N : namespace) : Type :=
  ∀ (γe : gname) (γq : gname) (qu : loc), iProp Σ.

Section spec.
Context {Σ} `{!heapGS Σ} (queueN rcuN : namespace) (DISJN : queueN ## rcuN).
Variables
  (queue_new : val)
  (queue_push : val)
  (queue_pop : val).
Variables
  (rcu : rcu_simple_spec Σ rcuN)
  (Queue : QueueT Σ)
  (IsQueue : IsQueueT Σ queueN).

Definition queue_new_spec' : Prop :=
  ⊢ ∀ γd d,
  {{{ rcu.(IsRCUDomain) γd d }}}
    queue_new #d
  {{{ γq qu, RET #qu; IsQueue γd γq qu ∗ Queue γq [] }}}.

Definition queue_push_spec' : Prop :=
  ⊢ ∀ γe γq qu (x : val) g,
  IsQueue γe γq qu -∗ rcu.(Guard) γe g Deactivated -∗
  <<< ∀∀ xs, Queue γq xs >>>
    queue_push #qu x #g @ ⊤,(↑queueN ∪ ↑(ptrsN rcuN)),↑(mgmtN rcuN)
  <<< Queue γq (xs ++ [x]), RET #(), rcu.(Guard) γe g Deactivated >>>.

Definition queue_pop_spec' : Prop :=
  ⊢ ∀ γe γq qu g,
  IsQueue γe γq qu -∗ rcu.(Guard) γe g Deactivated -∗
  <<< ∀∀ xs, Queue γq xs >>>
    queue_pop #qu #g @ ⊤,(↑queueN ∪ ↑(ptrsN rcuN)),↑(mgmtN rcuN)
  <<< Queue γq (match xs with [] => [] | _::xs => xs end),
      RET (match xs with [] => NONEV | v::_ => SOMEV v end),
      rcu.(Guard) γe g Deactivated
  >>>.
End spec.

Record queue_code : Type := QueueCode {
  queue_new : val;
  queue_push : val;
  queue_pop : val;
}.

Record queue_spec {Σ} `{!heapGS Σ} {queueN rcuN : namespace}
    {DISJN: queueN ## rcuN}
    {rcu : rcu_simple_spec Σ rcuN}
  : Type := QueueSpec {
  queue_spec_code :> queue_code;

  Queue: QueueT Σ;
  IsQueue : IsQueueT Σ queueN;

  Queue_Timeless : ∀ γq xs, Timeless (Queue γq xs);
  IsQueue_Persistent : ∀ γe γq l, Persistent (IsQueue γe γq l);

  queue_new_spec : queue_new_spec' queueN rcuN queue_spec_code.(queue_new) rcu Queue IsQueue;
  queue_push_spec : queue_push_spec' queueN rcuN queue_spec_code.(queue_push) rcu Queue IsQueue;
  queue_pop_spec : queue_pop_spec' queueN rcuN queue_spec_code.(queue_pop) rcu Queue IsQueue;
}.

Global Arguments queue_spec : clear implicits.
Global Arguments queue_spec _ {_} _ _ _ _ : assert.
Global Existing Instances Queue_Timeless IsQueue_Persistent.
