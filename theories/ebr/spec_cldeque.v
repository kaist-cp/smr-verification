From smr Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr.ebr Require Import spec_rcu_simple.
From iris.prelude Require Import options.

Definition DequeT Σ : Type :=
  ∀ (γ : gname) (xs : list val), iProp Σ.

Definition IsDequeT Σ (N : namespace) : Type :=
  ∀ (γe γ : gname) (l : blk), iProp Σ.

Definition OwnDequeT Σ (N : namespace) : Type :=
  ∀ (γ : gname) (l : blk), iProp Σ.

Section spec.
Context `{!heapGS Σ}.
Context (dequeN : namespace) (rcuN : namespace) (DISJN : dequeN ## rcuN).
Variables
  (deque_new : val)
  (deque_push : val)
  (deque_pop : val)
  (deque_steal : val).
Variables
  (rcu : rcu_simple_spec Σ rcuN)
  (deque : DequeT Σ)
  (IsDeque : IsDequeT Σ dequeN)
  (OwnDeque : OwnDequeT Σ dequeN).

Definition deque_new_spec' : Prop :=
  ⊢ ∀ γe (d : blk) n,
  ⌜0 < n⌝ -∗
  {{{ rcu.(IsRCUDomain) γe d }}}
    deque_new #d #n
  {{{ γ q, RET #q; IsDeque γe γ q ∗ deque γ [] ∗ OwnDeque γ q }}}.

Definition deque_push_spec' : Prop :=
  ⊢ ∀ γe γ q g (x : val),
  IsDeque γe γ q -∗ OwnDeque γ q -∗ rcu.(Guard) γe g Deactivated -∗
  <<< ∀∀ xs, deque γ xs >>>
    deque_push #q x #g @ ⊤,(↑dequeN ∪ ↑(ptrsN rcuN)),↑(mgmtN rcuN)
  <<< deque γ (xs ++ [x]),
    RET #(), OwnDeque γ q ∗ rcu.(Guard) γe g Deactivated >>>.

Definition deque_pop_spec' : Prop :=
  ⊢ ∀ γe γ q g,
  IsDeque γe γ q -∗ OwnDeque γ q -∗ rcu.(Guard) γe g Deactivated -∗
  <<< ∀∀ xs, deque γ xs >>>
    deque_pop #q #g @ ⊤,(↑dequeN ∪ ↑(ptrsN rcuN)),↑(mgmtN rcuN)
  <<< ∃∃ (xs' : list val) (ov : val),
        deque γ xs' ∗
        match ov with
        | NONEV => ⌜xs = xs'⌝
        | SOMEV v => ⌜xs = xs' ++ [v]⌝
        | _ => False
        end,
      RET ov, OwnDeque γ q ∗ rcu.(Guard) γe g Deactivated >>>.

Definition deque_steal_spec' : Prop :=
  ⊢ ∀ γe γ q g,
  IsDeque γe γ q -∗ rcu.(Guard) γe g Deactivated -∗
  <<< ∀∀ xs, deque γ xs >>>
    deque_pop #q #g @ ⊤,(↑dequeN ∪ ↑(ptrsN rcuN)),↑(mgmtN rcuN)
  <<< ∃∃ (xs' : list val) (ov : val),
        deque γ xs' ∗
        match ov with
        | NONEV => ⌜xs = xs'⌝
        | SOMEV v => ⌜xs = [v] ++ xs'⌝
        | _ => False
        end,
      RET ov, rcu.(Guard) γe g Deactivated >>>.
End spec.

Record deque_code : Type := dequeCode {
  deque_new : val;
  deque_push : val;
  deque_pop : val;
  deque_steal : val;
}.

(** A general logically atomic interface for Chase-Lev deques. *)
Record deque_spec {Σ} `{!heapGS Σ} {dequeN rcuN : namespace}
    {DISJN : dequeN ## rcuN}
    {rcu : rcu_simple_spec Σ rcuN}
  : Type := DequeSpec {
  deque_spec_code :> deque_code;

  Deque: DequeT Σ;
  IsDeque : IsDequeT Σ dequeN;
  OwnDeque : OwnDequeT Σ dequeN;
  (* -- predicate properties -- *)
  IsDeque_Persistent : ∀ γe γ q, Persistent (IsDeque γe γ q);
  Deque_Timeless : ∀ γ ls, Timeless (Deque γ ls);
  (* -- operation specs -- *)
  deque_new_spec : deque_new_spec' dequeN rcuN deque_spec_code.(deque_new) rcu Deque IsDeque OwnDeque;
  deque_push_spec : deque_push_spec' dequeN rcuN deque_spec_code.(deque_push) rcu Deque IsDeque OwnDeque;
  deque_pop_spec : deque_pop_spec' dequeN rcuN deque_spec_code.(deque_pop) rcu Deque IsDeque OwnDeque;
  deque_steal_spec : deque_steal_spec' dequeN rcuN deque_spec_code.(deque_steal) rcu Deque IsDeque;
}.

Global Arguments deque_spec : clear implicits.
Global Arguments deque_spec _ {_} _ _ _ _ : assert.
Global Existing Instances Deque_Timeless IsDeque_Persistent.

