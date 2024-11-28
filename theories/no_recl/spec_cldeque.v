From iris.base_logic.lib Require Import invariants.
From smr Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

Definition DequeT Σ : Type :=
  ∀ (γ : gname) (xs : list val), iProp Σ.

Definition IsDequeT Σ (N : namespace) : Type :=
  ∀ (γ : gname) (q : blk), iProp Σ.

Definition OwnDequeT Σ (N : namespace) : Type :=
  ∀ (γ : gname) (q : blk), iProp Σ.

Section spec.
Context `{!heapGS Σ}.
Context (dequeN : namespace).
Variables
  (deque_new : val)
  (deque_push : val)
  (deque_pop : val)
  (deque_steal : val).
Variables
  (deque : DequeT Σ)
  (IsDeque : IsDequeT Σ dequeN)
  (OwnDeque : OwnDequeT Σ dequeN).

Definition deque_new_spec' : Prop :=
  ⊢ ∀ n,
  ⌜0 < n⌝ -∗
  {{{ True }}}
    deque_new #n
  {{{ γ q, RET #q; IsDeque γ q ∗ deque γ [] ∗ OwnDeque γ q }}}.

Definition deque_push_spec' : Prop :=
  ⊢ ∀ γ q (x : val),
  IsDeque γ q -∗ OwnDeque γ q -∗
  <<{ ∀∀ xs, deque γ xs }>>
    deque_push #q x @ ⊤,↑dequeN,∅
  <<{ deque γ (xs ++ [x]) | RET #(); OwnDeque γ q }>>.

Definition deque_pop_spec' : Prop :=
  ⊢ ∀ γ q,
  IsDeque γ q -∗ OwnDeque γ q -∗
  <<{ ∀∀ xs, deque γ xs }>>
    deque_pop #q @ ⊤,↑dequeN,∅
  <<{ ∃∃ (xs' : list val) (ov : val),
        deque γ xs' ∗
        match ov with
        | NONEV => ⌜xs = xs'⌝
        | SOMEV v => ⌜xs = xs' ++ [v]⌝
        | _ => False
        end |
      RET ov; OwnDeque γ q }>>.

Definition deque_steal_spec' : Prop :=
  ⊢ ∀ γ q,
  IsDeque γ q -∗
  <<{ ∀∀ xs, deque γ xs }>>
    deque_pop #q @ ⊤,↑dequeN,∅
  <<{ ∃∃ (xs' : list val) (ov : val),
        deque γ xs' ∗
        match ov with
        | NONEV => ⌜xs = xs'⌝
        | SOMEV v => ⌜xs = [v] ++ xs'⌝
        | _ => False
        end |
      RET ov }>>.
End spec.

Record deque_code : Type := dequeCode {
  deque_new : val;
  deque_push : val;
  deque_pop : val;
  deque_steal : val;
}.

(** A general logically atomic interface for Chase-Lev deques. *)
Record deque_spec {Σ} `{!heapGS Σ} {dequeN : namespace}
  : Type := DequeSpec {
  deque_spec_code :> deque_code;

  Deque: DequeT Σ;
  IsDeque : IsDequeT Σ dequeN;
  OwnDeque : OwnDequeT Σ dequeN;
  (* -- predicate properties -- *)
  IsDeque_Persistent : ∀ γ q, Persistent (IsDeque γ q);
  Deque_Timeless : ∀ γ ls, Timeless (Deque γ ls);
  (* -- operation specs -- *)
  deque_new_spec : deque_new_spec' dequeN deque_spec_code.(deque_new) Deque IsDeque OwnDeque;
  deque_push_spec : deque_push_spec' dequeN deque_spec_code.(deque_push) Deque IsDeque OwnDeque;
  deque_pop_spec : deque_pop_spec' dequeN deque_spec_code.(deque_pop) Deque IsDeque OwnDeque;
  deque_steal_spec : deque_steal_spec' dequeN deque_spec_code.(deque_steal) Deque IsDeque;
}.

Global Arguments deque_spec : clear implicits.
Global Arguments deque_spec _ {_} _ : assert.
Global Existing Instances Deque_Timeless IsDeque_Persistent.

