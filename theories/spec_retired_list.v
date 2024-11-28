From smr.program_logic Require Import atomic.
From smr Require Import helpers.
From smr.lang Require Import proofmode notation.
From smr Require Import code_retired_list.
From iris.prelude Require Import options.

Definition RetiredNodeT Σ : Type :=
  ∀ (rNode : loc) (r : blk) (next : option loc) (size: nat) (epoch: nat), iProp Σ.

Definition RetiredListT Σ : Type :=
  ∀ (rList : loc) (rs : list (blk * nat * nat)), iProp Σ.

Definition RetiredNodesT Σ : Type :=
  ∀ (rNode : option loc) (rs : list (blk * nat * nat)), iProp Σ.

Section spec.
Context {Σ} `{!heapGS Σ}.
Context
  (RetiredNode : RetiredNodeT Σ)
  (RetiredList : RetiredListT Σ)
  (RetiredNodes : RetiredNodesT Σ).

Definition retired_node_new_spec' : Prop :=
  ∀ ptr size epoch E,
  {{{ True }}}
    retired_node_new #ptr #size #epoch @ E
  {{{ rNode, RET #rNode; RetiredNode rNode ptr None size epoch }}}.

Definition retired_node_next_spec' : Prop :=
  ∀ rNode r next size epoch E,
  {{{ RetiredNode rNode r next size epoch }}}
    retired_node_next #rNode @ E
  {{{ RET #(oloc_to_lit next); RetiredNode rNode r next size epoch }}}.

Definition retired_node_ptr_spec' : Prop :=
  ∀ rNode r next size epoch E,
  {{{ RetiredNode rNode r next size epoch }}}
    retired_node_ptr #rNode @ E
  {{{ RET #r; RetiredNode rNode r next size epoch }}}.

Definition retired_node_size_spec' : Prop :=
  ∀ rNode r next size epoch E,
  {{{ RetiredNode rNode r next size epoch }}}
    retired_node_size #rNode @ E
  {{{ RET #size; RetiredNode rNode r next size epoch }}}.

Definition retired_node_epoch_spec' : Prop :=
  ∀ rNode r next size epoch E,
  {{{ RetiredNode rNode r next size epoch }}}
    retired_node_epoch #rNode @ E
  {{{ RET #epoch; RetiredNode rNode r next size epoch }}}.

Definition retired_node_drop_spec' : Prop :=
  ∀ rNode r next size epoch E,
  {{{ RetiredNode rNode r next size epoch }}}
    retired_node_drop #rNode @ E
  {{{ RET #(); True }}}.

Definition retired_list_new_spec' : Prop :=
  ∀ E,
  {{{ True }}}
    retired_list_new #() @ E
  {{{ rList, RET #rList; RetiredList rList [] }}}.

Definition retired_list_push_spec' : Prop :=
  ∀ rNode r next size epoch (rList : loc) E,
  RetiredNode rNode r next size epoch -∗
  <<{ ∀∀ rs, ▷ RetiredList rList rs }>>
    retired_list_push #rList #rNode @ E,∅,∅
  <<{ RetiredList rList ((r,size,epoch)::rs) | RET #() }>>.

Definition retired_list_pop_all_spec' : Prop :=
  ⊢ ∀ (rList : loc) E,
  <<{ ∀∀ rs, ▷ RetiredList rList rs }>>
    retired_list_pop_all #rList @ E,∅,∅
  <<{ ∃∃ (rNode : option loc),
        RetiredList rList [] ∗ RetiredNodes rNode rs |
      RET #(oloc_to_lit rNode) }>>.

Definition retired_nodes_cons' : Prop :=
  ∀ rNode rs,
  RetiredNodes (Some rNode) rs ⊣⊢
  ∃ r rs' next size epoch, ⌜rs = (r,size,epoch)::rs'⌝ ∗
    RetiredNode rNode r next size epoch ∗ RetiredNodes next rs'.

End spec.

Record retired_list_spec {Σ} `{!heapGS Σ} : Type := RetiredSetSpec {
  RetiredNode : RetiredNodeT Σ;
  RetiredList : RetiredListT Σ;
  RetiredNodes : RetiredNodesT Σ;

  RetiredNode_Timeless : ∀ rNode ptr next size epoch, Timeless (RetiredNode rNode ptr next size epoch);
  RetiredList_Timeless : ∀ rList rs, Timeless (RetiredList rList rs);
  RetiredNodes_Timeless : ∀ rNode rs, Timeless (RetiredNodes rNode rs);

  retired_nodes_cons : retired_nodes_cons' RetiredNode RetiredNodes;
  retired_node_new_spec : retired_node_new_spec' RetiredNode;
  retired_node_next_spec : retired_node_next_spec' RetiredNode;
  retired_node_ptr_spec : retired_node_ptr_spec' RetiredNode;
  retired_node_size_spec : retired_node_size_spec' RetiredNode;
  retired_node_epoch_spec : retired_node_epoch_spec' RetiredNode;
  retired_node_drop_spec : retired_node_drop_spec' RetiredNode;
  retired_list_new_spec : retired_list_new_spec' RetiredList;
  retired_list_push_spec : retired_list_push_spec' RetiredNode RetiredList;
  retired_list_pop_all_spec : retired_list_pop_all_spec' RetiredList RetiredNodes;
}.

Global Arguments retired_list_spec _ {_}.
Global Existing Instances RetiredNode_Timeless RetiredList_Timeless RetiredNodes_Timeless.
