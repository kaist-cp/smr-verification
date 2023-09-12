From iris.base_logic Require Import lib.invariants.
From smr.program_logic Require Import atomic.
From smr Require Import helpers.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr Require Import spec_retired_list code_retired_list.

Set Printing Projections.

Section retired_list.
Context `{!heapGS Σ}.
Notation iProp := (iProp Σ).

(* hd is the head of a linked list representing xs *)
Fixpoint phys_list (hd : base_lit) (xs : list (blk * nat * nat)) : iProp :=
  match xs with
  | [] => ⌜hd = LitLoc NULL⌝
  | (x, size, epoch) :: xs =>
     ∃ (p : loc) (nxt : option loc), ⌜hd = LitLoc p⌝ ∗
     (p +ₗ rNodeNext) ↦ #(oloc_to_lit nxt) ∗
     (p +ₗ rNodePtr) ↦ #x ∗
     (p +ₗ rNodePtrSize) ↦ #size ∗
     (p +ₗ rNodeEpoch) ↦ #epoch ∗
     †p…rNodeSize ∗
     phys_list (oloc_to_lit nxt) xs
  end.

Definition RetiredNode (rNode ptr : loc) (next : option loc) (size : nat) (epoch : nat) : iProp :=
  (rNode +ₗ rNodeNext) ↦ #(oloc_to_lit next) ∗
  (rNode +ₗ rNodePtr) ↦ #ptr ∗
  (rNode +ₗ rNodePtrSize) ↦ #size ∗
  (rNode +ₗ rNodeEpoch) ↦ #epoch ∗
  †rNode…rNodeSize.

Definition RetiredList (rList : loc) (rs : list (blk * nat * nat)) : iProp :=
  ∃ (hd : option loc),
    (rList +ₗ rSetHead) ↦ #(oloc_to_lit hd) ∗
    phys_list (oloc_to_lit hd) rs.

Definition RetiredNodes (rNode : option loc) (rs : list (blk * nat * nat)) : iProp :=
  phys_list (oloc_to_lit rNode) rs.

Global Instance phys_list_timeless hd xs: Timeless (phys_list hd xs).
Proof.
  revert hd. induction xs; simpl; [apply _|].
  intros. repeat case_match. subst. apply _.
Qed.
Global Instance RetiredNode_Timeless rNode ptr next size epoch:
  Timeless (RetiredNode rNode ptr next size epoch).
Proof. apply _. Qed.
Global Instance RetiredList_Timeless rList rs: Timeless (RetiredList rList rs).
Proof. apply _. Qed.
Global Instance RetiredNodes_Timeless rNode rs: Timeless (RetiredNodes rNode rs).
Proof. apply _. Qed.

Lemma retired_node_new_spec :
  retired_node_new_spec' RetiredNode.
Proof.
  iIntros (?????) "_ HΦ".
  wp_rec. wp_pures. wp_alloc r as "r↦" "†r".
  wp_pures.
  repeat (wp_apply (wp_store_offset with "r↦") as "r↦"; [by simplify_list_eq|]; wp_pures).
  iApply "HΦ". simpl. iFrame. rewrite !array_cons 3!loc_add_assoc loc_add_0.
  by iDestruct "r↦" as "($ & $ & $ & $ & _)".
Qed.

Lemma retired_node_next_spec :
  retired_node_next_spec' RetiredNode.
Proof.
  iIntros (???????) "[r.next↦ ?] HΦ".
  wp_rec. wp_pures. wp_load. iModIntro.
  iApply "HΦ"; iFrame.
Qed.

Lemma retired_node_ptr_spec :
  retired_node_ptr_spec' RetiredNode.
Proof.
  iIntros (???????) "(? & r.ptr↦ & ?) HΦ".
  wp_rec. wp_pures. wp_load. iModIntro.
  iApply "HΦ"; iFrame.
Qed.

Lemma retired_node_size_spec :
  retired_node_size_spec' RetiredNode.
Proof.
  iIntros (???????) "(? & ? & r.size↦ & ?) HΦ".
  wp_rec. wp_pures. wp_load. iModIntro.
  iApply "HΦ"; iFrame.
Qed.

Lemma retired_node_epoch_spec :
  retired_node_epoch_spec' RetiredNode.
Proof.
  iIntros (???????) "(? & ? & ? & r.epoch↦ & ?) HΦ".
  wp_rec. wp_pures. wp_load. iModIntro.
  iApply "HΦ"; iFrame.
Qed.

Lemma retired_node_drop_spec :
  retired_node_drop_spec' RetiredNode.
Proof.
  iIntros (???????) "(r.next↦ & r.ptr↦ & r.size↦ & r.epoch↦ & †r) HΦ".
  rewrite -!array_singleton loc_add_0.
  iCombine "r.next↦ r.ptr↦" as "r↦".
  rewrite -array_app.
  (* rewrite -heap_mapsto_vec_app /=. *)
  iCombine "r↦ r.size↦" as "r↦".
  rewrite -array_app.
  iCombine "r↦ r.epoch↦" as "r↦".
  rewrite -array_app /=.
  wp_rec. wp_free; [done|by iApply "HΦ"].
Qed.

Lemma retired_list_new_spec :
  retired_list_new_spec' RetiredList.
Proof.
  iIntros (??) "_ HΦ". wp_rec. wp_alloc r as "r↦" "†r".
  wp_pures. rewrite loc_add_0 array_singleton. wp_store.
  iModIntro. iApply "HΦ".
  iExists None. rewrite loc_add_0. by iFrame.
Qed.

Lemma retired_list_push_spec :
  retired_list_push_spec' RetiredNode RetiredList.
Proof.
  iIntros (???????) "r↦ % AU". iDestruct "r↦" as "(r.next↦ & r.ptr↦ & r.size↦ & r.epoch↦ & †r)".
  iLöb as "IH" forall (next).
  wp_rec. wp_pures.

  wp_bind (! _)%E.
  iMod "AU" as (xs1) "[[%hd1 [>Hrs Hphys]] [Abort _]]".
  wp_load.
  iMod ("Abort" with "[Hrs Hphys]") as "AU".
  { iNext. iExists hd1; iFrame. }
  iModIntro. clear.

  wp_pures. wp_store. wp_pures.

  wp_bind (CmpXchg _ _ _)%E.
  iMod "AU" as (xs2) "[[%hd2 [>Hrs Hphys]] AU]".
  destruct (decide (hd1 = hd2)) as [?|NE]; subst.
  - (* success *)
    iDestruct "AU" as "[_ Commit]".
    wp_cmpxchg_suc.
    iMod ("Commit" with "[-]") as "HΦ".
    { iExists (Some rNode); iFrame.
      iExists rNode, hd2. iSplit; auto. iFrame. }
    iModIntro. wp_pures. by iApply "HΦ".
  - (* fail *)
    iDestruct "AU" as "[Abort _]".
    wp_cmpxchg_fail.
    iMod ("Abort" with "[Hrs Hphys]") as "AU".
    { iNext. iExists hd2; iFrame. }
    iModIntro. wp_pures.
    iApply ("IH" with "r.next↦ r.ptr↦ r.size↦ r.epoch↦ †r AU").
Qed.

Lemma retired_list_pop_all_spec :
  retired_list_pop_all_spec' RetiredList RetiredNodes.
Proof.
  iIntros (???) "AU".
  wp_rec. wp_pures.
  iMod "AU" as (?) "[Hrl [_ Commit]]".
  iDestruct "Hrl" as (?) "[>Hrl Hphys]".
  iApply (wp_xchg with "Hrl").
  iNext. iIntros "Hrl".
  iMod ("Commit" with "[-]") as "HΦ"; last by iApply "HΦ".
  iSplitL "Hrl"; auto. iExists None; auto.
Qed.

Lemma retired_nodes_cons :
  retired_nodes_cons' RetiredNode RetiredNodes.
Proof.
  iIntros (rNode rs). iSplit.
  - iIntros "RNodes". rewrite /RetiredNodes /=.
    destruct rs as [|[[r e] p] rs]; simpl.
    + iDestruct "RNodes" as %[= ?].
    + iDestruct "RNodes" as (? nxt [= <-]) "(?&?&?&?&?&?)".
      repeat iExists _. by iFrame.
  - iDestruct 1 as (r rs' next size epoch ->) "(RNode & RNodes)".
    rewrite /RetiredNodes /RetiredNode /=. repeat iExists _. by iFrame.
Qed.
End retired_list.

Definition retired_list_impl Σ `{!heapGS Σ} : spec_retired_list.retired_list_spec Σ := {|
  spec_retired_list.RetiredNode := RetiredNode;
  spec_retired_list.RetiredList := RetiredList;
  spec_retired_list.RetiredNodes := RetiredNodes;

  spec_retired_list.RetiredNode_Timeless := RetiredNode_Timeless;
  spec_retired_list.RetiredList_Timeless := RetiredList_Timeless;
  spec_retired_list.RetiredNodes_Timeless := RetiredNodes_Timeless;

  spec_retired_list.retired_node_new_spec := retired_node_new_spec;
  spec_retired_list.retired_node_next_spec := retired_node_next_spec;
  spec_retired_list.retired_node_ptr_spec := retired_node_ptr_spec;
  spec_retired_list.retired_node_size_spec := retired_node_size_spec;
  spec_retired_list.retired_node_epoch_spec := retired_node_epoch_spec;
  spec_retired_list.retired_node_drop_spec := retired_node_drop_spec;
  spec_retired_list.retired_list_new_spec := retired_list_new_spec;
  spec_retired_list.retired_list_push_spec := retired_list_push_spec;
  spec_retired_list.retired_list_pop_all_spec := retired_list_pop_all_spec;

  spec_retired_list.retired_nodes_cons := retired_nodes_cons;
|}.
