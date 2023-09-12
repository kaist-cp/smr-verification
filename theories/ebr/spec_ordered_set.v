From iris.algebra Require Import gset.
From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr.ebr Require Import spec_rcu_traversal.
From iris.prelude Require Import options.

Definition OrderedSetT Σ : Type :=
  ∀ (γo : gname) (xs : gset Z), iProp Σ.

Definition IsOrderedSetT Σ (N : namespace) : Type :=
  ∀ (γr : gname) (γo : gname) (oset : loc), iProp Σ.

Section spec.
Context {Σ} `{!heapGS Σ} (ordsetN rcuN : namespace) (DISJN : ordsetN ## rcuN).
Variables
  (ordset_new : val)
  (ordset_lookup : val)
  (ordset_insert : val)
  (ordset_delete : val).
Variables
  (rcu : rcu_traversal_spec Σ rcuN)
  (OrderedSet : OrderedSetT Σ)
  (IsOrderedSet : IsOrderedSetT Σ ordsetN).

Definition ordset_new_spec' : Prop :=
  ⊢ ∀ γr d,
  {{{ rcu.(IsRCUDomain) γr d }}}
    ordset_new #d
  {{{ γo oset, RET #oset; IsOrderedSet γr γo oset ∗ OrderedSet γo ∅ }}}.

Definition ordset_lookup_spec' : Prop :=
  ⊢ ∀ γr γo oset (x : Z) g,
  IsOrderedSet γr γo oset -∗ rcu.(Inactive) γr g -∗
  <<< ∀∀ xs, OrderedSet γo xs >>>
    ordset_lookup #oset #g #x @ ⊤,(↑ordsetN ∪ ↑(ptrsN rcuN)),↑(mgmtN rcuN)
  <<< ∃∃ (b : bool), OrderedSet γo xs ∗ ⌜b = bool_decide (x ∈ xs)⌝, RET #b, rcu.(Inactive) γr g >>>.

Definition ordset_insert_spec' : Prop :=
  ⊢ ∀ γr γo oset (x : Z) g,
  IsOrderedSet γr γo oset -∗ rcu.(Inactive) γr g -∗
  <<< ∀∀ xs, OrderedSet γo xs >>>
    ordset_insert #oset #g #x @ ⊤,(↑ordsetN ∪ ↑(ptrsN rcuN)),↑(mgmtN rcuN)
  <<< ∃∃ (b : bool) xs', OrderedSet γo xs' ∗
          ⌜if (b : bool) then
            x ∉ xs ∧ xs' = {[ x ]} ∪ xs
          else
            x ∈ xs ∧ xs' = xs⌝,
          RET #b,
          rcu.(Inactive) γr g >>>.

Definition ordset_delete_spec' : Prop :=
  ⊢ ∀ γr γo oset (x : Z) g,
  IsOrderedSet γr γo oset -∗ rcu.(Inactive) γr g -∗
  <<< ∀∀ xs, OrderedSet γo xs >>>
    ordset_delete #oset #g #x @ ⊤,(↑ordsetN ∪ ↑(ptrsN rcuN)),↑(mgmtN rcuN)
  <<< ∃∃ (b : bool) xs', OrderedSet γo xs' ∗
          ⌜if (b : bool) then
            x ∈ xs ∧ xs' = xs ∖ {[ x ]}
          else
            x ∉ xs ∧ xs' = xs⌝,
          RET #b,
          rcu.(Inactive) γr g >>>.
End spec.

Record ordset_code : Type := OrderedSetCode {
  ordset_new : val;
  ordset_lookup : val;
  ordset_insert : val;
  ordset_delete : val;
}.

Record ordset_spec {Σ} `{!heapGS Σ} {ordsetN rcuN : namespace}
    {DISJN: ordsetN ## rcuN}
    {rcu : rcu_traversal_spec Σ rcuN}
  : Type := OrderedSetSpec {
  ordset_spec_code :> ordset_code;

  OrderedSet : OrderedSetT Σ;
  IsOrderedSet : IsOrderedSetT Σ ordsetN;

  OrderedSet_Timeless : ∀ γo xs, Timeless (OrderedSet γo xs);
  IsOrderedSet_Persistent : ∀ γr γo oset, Persistent (IsOrderedSet γr γo oset);

  ordset_new_spec : ordset_new_spec' ordsetN rcuN ordset_spec_code.(ordset_new) rcu OrderedSet IsOrderedSet;
  ordset_lookup_spec : ordset_lookup_spec' ordsetN rcuN ordset_spec_code.(ordset_lookup) rcu OrderedSet IsOrderedSet;
  ordset_insert_spec : ordset_insert_spec' ordsetN rcuN ordset_spec_code.(ordset_insert) rcu OrderedSet IsOrderedSet;
  ordset_delete_spec : ordset_delete_spec' ordsetN rcuN ordset_spec_code.(ordset_delete) rcu OrderedSet IsOrderedSet;
}.

Global Arguments ordset_spec : clear implicits.
Global Arguments ordset_spec _ {_} _ _ _ _ : assert.
Global Existing Instances OrderedSet_Timeless IsOrderedSet_Persistent.
