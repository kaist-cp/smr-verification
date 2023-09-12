From iris.algebra Require Import gset.
From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

Definition OrderedSetT Σ : Type :=
  ∀ (γo : gname) (xs : gset Z), iProp Σ.

Definition IsOrderedSetT Σ (N : namespace) : Type :=
  ∀ (γo : gname) (oset : loc), iProp Σ.

Section spec.
Context {Σ} `{!heapGS Σ} (ordsetN : namespace).
Variables
  (ordset_new : val)
  (ordset_lookup : val)
  (ordset_insert : val)
  (ordset_delete : val).
Variables
  (OrderedSet : OrderedSetT Σ)
  (IsOrderedSet : IsOrderedSetT Σ ordsetN).

Definition ordset_new_spec' : Prop :=
  ⊢ {{{ True }}}
    ordset_new #()
  {{{ γo oset, RET #oset; IsOrderedSet γo oset ∗ OrderedSet γo ∅ }}}.

Definition ordset_lookup_spec' : Prop :=
  ⊢ ∀ γo oset (x : Z),
  IsOrderedSet γo oset-∗
  <<< ∀∀ xs, OrderedSet γo xs >>>
    ordset_lookup #oset #x @ ⊤,↑ordsetN,∅
  <<< ∃∃ (b : bool), OrderedSet γo xs ∗ ⌜b = bool_decide (x ∈ xs)⌝, RET #b >>>.

Definition ordset_insert_spec' : Prop :=
  ⊢ ∀ γo oset (x : Z),
  IsOrderedSet γo oset -∗
  <<< ∀∀ xs, OrderedSet γo xs >>>
    ordset_insert #oset #x @ ⊤,↑ordsetN,∅
  <<< ∃∃ (b : bool) xs', OrderedSet γo xs' ∗
          ⌜if (b : bool) then
            x ∉ xs ∧ xs' = {[ x ]} ∪ xs
          else
            x ∈ xs ∧ xs' = xs⌝,
          RET #b >>>.

Definition ordset_delete_spec' : Prop :=
  ⊢ ∀ γo oset (x : Z),
  IsOrderedSet γo oset -∗
  <<< ∀∀ xs, OrderedSet γo xs >>>
    ordset_delete #oset #x @ ⊤,↑ordsetN,∅
  <<< ∃∃ (b : bool) xs', OrderedSet γo xs' ∗
          ⌜if (b : bool) then
            x ∈ xs ∧ xs' = xs ∖ {[ x ]}
          else
            x ∉ xs ∧ xs' = xs⌝,
          RET #b >>>.
End spec.

Record ordset_code : Type := OrderedSetCode {
  ordset_new : val;
  ordset_lookup : val;
  ordset_insert : val;
  ordset_delete : val;
}.

Record ordset_spec {Σ} `{!heapGS Σ} {ordsetN : namespace}
  : Type := OrderedSetSpec {
  ordset_spec_code :> ordset_code;

  OrderedSet : OrderedSetT Σ;
  IsOrderedSet : IsOrderedSetT Σ ordsetN;

  OrderedSet_Timeless : ∀ γo xs, Timeless (OrderedSet γo xs);
  IsOrderedSet_Persistent : ∀ γo oset, Persistent (IsOrderedSet γo oset);

  ordset_new_spec : ordset_new_spec' ordsetN ordset_spec_code.(ordset_new) OrderedSet IsOrderedSet;
  ordset_lookup_spec : ordset_lookup_spec' ordsetN ordset_spec_code.(ordset_lookup) OrderedSet IsOrderedSet;
  ordset_insert_spec : ordset_insert_spec' ordsetN ordset_spec_code.(ordset_insert) OrderedSet IsOrderedSet;
  ordset_delete_spec : ordset_delete_spec' ordsetN ordset_spec_code.(ordset_delete) OrderedSet IsOrderedSet;
}.

Global Arguments ordset_spec : clear implicits.
Global Arguments ordset_spec _ {_} _ : assert.
Global Existing Instances OrderedSet_Timeless IsOrderedSet_Persistent.
