(* Importing required RAs and namespace*)
From smr.lang Require Import proofmode.
From smr Require Import logic.reclamation.

(* Proof of hazard pointer and inner DS *)
From smr Require Import proof_retired_list proof_slot_bag_oloc.
From smr.hazptr Require Import spec_hazptr code_hazptr proof_hazptr.

(* Proof of hazard pointer clients. *)
From smr.hazptr Require Export spec_counter code_counter proof_counter.
From smr.hazptr Require Export spec_hybrid_counter code_hybrid_counter proof_hybrid_counter.
From smr.hazptr Require Export spec_stack.
From smr.hazptr Require Export code_treiber proof_treiber.
From smr.hazptr Require Export code_elimstack proof_elimstack.
From smr.hazptr Require Export spec_queue.
From smr.hazptr Require Export code_ms proof_ms.
From smr.hazptr Require Export code_dglm proof_dglm.
From smr.hazptr Require Export spec_rdcss code_rdcss proof_rdcss.
From smr.hazptr Require Export spec_cldeque code_cldeque proof_cldeque.
From smr.hazptr Require Export spec_ordered_set code_harris_operations proof_harris_michael_find.

From iris.prelude Require Import options.

Definition hazptrN := nroot .@ "hazptr".
Definition counterN := nroot .@ "counter".
Definition hcounterN := nroot .@ "hcounter".
Definition treiberN := nroot .@ "treiber".
Definition elimN := nroot .@ "elim".
Definition msqueueN := nroot .@ "msqueue".
Definition dglmN := nroot .@ "dglm".
Definition rdcssN := nroot .@ "rdcss".
Definition cldequeN := nroot .@ "cldeque".
Definition hmsN := nroot .@ "hms".

Class hazptrG Σ := HazPtrG {
  hazptr_reclamationG :> reclamationG Σ;
  hazptr_slot_bag :> slot_bag_olocG Σ;
}.

Definition hazptrΣ : gFunctors := #[reclamationΣ; slot_bag_olocΣ].

Global Instance subG_hazptrΣ {Σ} :
  subG hazptrΣ Σ → hazptrG Σ.
Proof. solve_inG. Qed.

Definition hazard_pointer_code_impl : hazard_pointer_code := {|
  spec_hazptr.hazard_domain_new := hazard_domain_new;
  spec_hazptr.hazard_domain_retire := hazard_domain_retire;
  spec_hazptr.hazard_domain_do_reclamation := hazard_domain_do_reclamation;
  spec_hazptr.shield_new := shield_new;
  spec_hazptr.shield_set := shield_set;
  spec_hazptr.shield_protect := shield_protect;
  spec_hazptr.shield_unset := shield_unset;
  spec_hazptr.shield_drop := shield_drop;
|}.

Definition hazard_pointer_impl Σ `{!heapGS Σ, !hazptrG Σ}
    : spec_hazptr.hazard_pointer_spec Σ hazptrN := {|
  spec_hazptr.hazard_pointer_spec_code := hazard_pointer_code_impl;

  spec_hazptr.IsHazardDomain := IsHazardDomain hazptrN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_hazptr.Managed := Managed hazptrN;
  spec_hazptr.Shield := Shield hazptrN (slot_bag_impl Σ);

  spec_hazptr.IsHazardDomain_Persistent := IsHazardDomain_Persistent hazptrN (slot_bag_impl Σ) (retired_list_impl Σ);

  spec_hazptr.hazard_domain_new_spec := hazard_domain_new_spec hazptrN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_hazptr.hazard_domain_register := hazard_domain_register hazptrN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_hazptr.shield_new_spec := shield_new_spec hazptrN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_hazptr.shield_set_spec := shield_set_spec hazptrN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_hazptr.shield_validate := shield_validate hazptrN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_hazptr.shield_protect_spec := shield_protect_spec hazptrN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_hazptr.shield_unset_spec := shield_unset_spec hazptrN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_hazptr.shield_drop_spec := shield_drop_spec hazptrN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_hazptr.shield_acc := shield_acc hazptrN (slot_bag_impl Σ);
  spec_hazptr.managed_acc := managed_acc hazptrN;
  spec_hazptr.managed_exclusive := managed_exclusive hazptrN;
  spec_hazptr.shield_managed_agree := shield_managed_agree hazptrN (slot_bag_impl Σ);
  spec_hazptr.hazard_domain_retire_spec := hazard_domain_retire_spec hazptrN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_hazptr.hazard_domain_do_reclamation_spec := hazard_domain_do_reclamation_spec hazptrN (slot_bag_impl Σ) (retired_list_impl Σ);
|}.

Definition counter_code_impl : counter_code := {|
  spec_counter.counter_new := counter_new;
  spec_counter.counter_inc := (counter_inc hazard_pointer_code_impl);
|}.

Definition counter_impl Σ `{!heapGS Σ, !counterG Σ, !hazptrG Σ}
    : counter_spec Σ counterN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ) := {|
  spec_counter.counter_spec_code := counter_code_impl;

  spec_counter.Counter := Counter;
  spec_counter.IsCounter := IsCounter counterN hazptrN (hazard_pointer_impl Σ);

  spec_counter.Counter_Timeless := Counter_Timeless;
  spec_counter.IsCounter_Persistent := IsCounter_Persistent counterN hazptrN (hazard_pointer_impl Σ);

  spec_counter.counter_new_spec := counter_new_spec counterN hazptrN (hazard_pointer_impl Σ);
  spec_counter.counter_inc_spec := counter_inc_spec counterN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ);
|}.

Definition hcounter_code_impl : hcounter_code := {|
  spec_hybrid_counter.hcounter_new := hcounter_new;
  spec_hybrid_counter.hcounter_inc := (hcounter_inc hazard_pointer_code_impl);
|}.

Definition hcounter_impl Σ `{!heapGS Σ, !hazptrG Σ, !hcounterG Σ}
    : hcounter_spec Σ hcounterN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ) := {|
  spec_hybrid_counter.hcounter_spec_code := hcounter_code_impl;

  spec_hybrid_counter.HCounter := HCounter;
  spec_hybrid_counter.IsHCounter := IsHCounter hcounterN hazptrN (hazard_pointer_impl Σ);

  spec_hybrid_counter.HCounter_Timeless := HCounter_Timeless;
  spec_hybrid_counter.IsHCounter_Persistent := IsHCounter_Persistent hcounterN hazptrN (hazard_pointer_impl Σ);

  spec_hybrid_counter.hcounter_new_spec := hcounter_new_spec hcounterN hazptrN (hazard_pointer_impl Σ);
  spec_hybrid_counter.hcounter_inc_spec := hcounter_inc_spec hcounterN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ);
|}.

Definition treiber_code_impl : stack_code := {|
  stack_new := tstack_new;
  stack_push := tstack_push;
  stack_pop := (tstack_pop hazard_pointer_code_impl);
|}.

Definition treiber_impl Σ `{!heapGS Σ, !hazptrG Σ, !treiberG Σ}
    : stack_spec Σ treiberN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ) := {|
  stack_spec_code := treiber_code_impl;

  Stack := TStack;
  IsStack := IsTStack treiberN hazptrN (hazard_pointer_impl Σ);

  Stack_Timeless := TStack_Timeless;
  IsStack_Persistent := IsTStack_Persistent treiberN hazptrN (hazard_pointer_impl Σ);

  stack_new_spec := tstack_new_spec treiberN hazptrN (hazard_pointer_impl Σ);
  stack_push_spec := tstack_push_spec treiberN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ);
  stack_pop_spec := tstack_pop_spec treiberN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ);
|}.

Definition elimstack_code_impl : stack_code := {|
  stack_new := estack_new;
  stack_push := (estack_push hazard_pointer_code_impl);
  stack_pop := (estack_pop hazard_pointer_code_impl);
|}.

Definition elimstack_impl Σ `{!heapGS Σ, !hazptrG Σ, !elimstackG Σ}
    : stack_spec Σ elimN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ) := {|
  stack_spec_code := elimstack_code_impl;

  Stack := EStack;
  IsStack := IsEStack elimN hazptrN (hazard_pointer_impl Σ);

  Stack_Timeless := EStack_Timeless;
  IsStack_Persistent := IsEStack_Persistent elimN hazptrN (hazard_pointer_impl Σ);

  stack_new_spec := estack_new_spec elimN hazptrN (hazard_pointer_impl Σ);
  stack_push_spec := estack_push_spec elimN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ);
  stack_pop_spec := estack_pop_spec elimN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ);
|}.

Definition ms_code_impl : queue_code := {|
  spec_queue.queue_new := code_ms.queue_new;
  spec_queue.queue_push := (code_ms.queue_push hazard_pointer_code_impl);
  spec_queue.queue_pop := (code_ms.queue_pop hazard_pointer_code_impl);
|}.

Definition ms_impl Σ `{!heapGS Σ, !hazptrG Σ, !msG Σ}
    : queue_spec Σ msqueueN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ) := {|
  spec_queue.queue_spec_code := ms_code_impl;

  spec_queue.Queue := proof_ms.Queue;
  spec_queue.IsQueue := proof_ms.IsQueue msqueueN hazptrN (hazard_pointer_impl Σ);

  spec_queue.Queue_Timeless := proof_ms.Queue_Timeless;
  spec_queue.IsQueue_Persistent := proof_ms.IsQueue_Persistent msqueueN hazptrN (hazard_pointer_impl Σ);

  spec_queue.queue_new_spec := proof_ms.queue_new_spec msqueueN hazptrN (hazard_pointer_impl Σ);
  spec_queue.queue_push_spec := proof_ms.queue_push_spec msqueueN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ);
  spec_queue.queue_pop_spec := proof_ms.queue_pop_spec msqueueN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ);
|}.

Definition dglm_code_impl : queue_code := {|
  spec_queue.queue_new := code_dglm.queue_new;
  spec_queue.queue_push := (code_dglm.queue_push hazard_pointer_code_impl);
  spec_queue.queue_pop := (code_dglm.queue_pop hazard_pointer_code_impl);
|}.

Definition dglm_impl Σ `{!heapGS Σ, !hazptrG Σ, !dglmG Σ}
    : queue_spec Σ dglmN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ) := {|
  spec_queue.queue_spec_code := dglm_code_impl;

  spec_queue.Queue := proof_dglm.Queue;
  spec_queue.IsQueue := proof_dglm.IsQueue dglmN hazptrN (hazard_pointer_impl Σ);

  spec_queue.Queue_Timeless := proof_dglm.Queue_Timeless;
  spec_queue.IsQueue_Persistent := proof_dglm.IsQueue_Persistent dglmN hazptrN (hazard_pointer_impl Σ);

  spec_queue.queue_new_spec := proof_dglm.queue_new_spec dglmN hazptrN (hazard_pointer_impl Σ);
  spec_queue.queue_push_spec := proof_dglm.queue_push_spec dglmN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ);
  spec_queue.queue_pop_spec := proof_dglm.queue_pop_spec dglmN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ);
|}.

Definition rdcss_code_impl : rdcss_code := {|
  spec_rdcss.new_rdcss := new_rdcss;
  spec_rdcss.get := (get hazard_pointer_code_impl);
  spec_rdcss.rdcss := (rdcss hazard_pointer_code_impl);
|}.

Definition rdcss_impl Σ `{!heapGS Σ, !hazptrG Σ, !rdcssG Σ}
    : rdcss_spec_record Σ rdcssN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ) := {|
  spec_rdcss.rdcss_spec_code := rdcss_code_impl;

  spec_rdcss.Rdcss := Rdcss;
  spec_rdcss.IsRdcss := IsRdcss rdcssN hazptrN (hazard_pointer_impl Σ);

  spec_rdcss.Rdcss_Timeless := Rdcss_Timeless;
  spec_rdcss.IsRdcss_Persistent := IsRdcss_Persistent rdcssN hazptrN (hazard_pointer_impl Σ);

  spec_rdcss.new_rdcss_spec := new_rdcss_spec rdcssN hazptrN (hazard_pointer_impl Σ);
  spec_rdcss.get_spec := get_spec rdcssN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ);
  spec_rdcss.rdcss_spec := rdcss_spec rdcssN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ);
|}.

Definition cldeque_code_impl : deque_code := {|
  spec_cldeque.deque_new := deque_new;
  spec_cldeque.deque_push := (deque_push hazard_pointer_code_impl);
  spec_cldeque.deque_pop := deque_pop;
  spec_cldeque.deque_steal := (deque_steal hazard_pointer_code_impl);
|}.

Definition cldeque_impl Σ `{!heapGS Σ, !hazptrG Σ, !cldequeG Σ}
    : deque_spec Σ cldequeN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ) := {|
  spec_cldeque.deque_spec_code := cldeque_code_impl;

  spec_cldeque.Deque := Deque;
  spec_cldeque.IsDeque := IsDeque cldequeN hazptrN (hazard_pointer_impl Σ);

  spec_cldeque.OwnDeque := OwnDeque;

  spec_cldeque.IsDeque_Persistent := IsDeque_persistent cldequeN hazptrN (hazard_pointer_impl Σ);
  spec_cldeque.Deque_Timeless := Deque_timeless;

  spec_cldeque.deque_new_spec := deque_new_spec cldequeN hazptrN (hazard_pointer_impl Σ);
  spec_cldeque.deque_push_spec := deque_push_spec cldequeN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ);
  spec_cldeque.deque_pop_spec := deque_pop_spec cldequeN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ);
  spec_cldeque.deque_steal_spec := deque_steal_spec cldequeN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ);
|}.

Definition harris_op_code_impl (h : harris_find_code) : ordset_code := {|
  spec_ordered_set.ordset_new := harris_new;
  spec_ordered_set.ordset_lookup := (harris_lookup h hazard_pointer_code_impl);
  spec_ordered_set.ordset_insert := (harris_insert h hazard_pointer_code_impl);
  spec_ordered_set.ordset_delete := (harris_delete h hazard_pointer_code_impl);
|}.

Definition harris_op_impl Σ N (DISJN : N ## hazptrN) `{!heapGS Σ, !hazptrG Σ, !hlG Σ}
    (h : hfind_spec Σ N hazptrN DISJN (hazard_pointer_impl Σ))
    : ordset_spec Σ N hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ) := {|
  spec_ordered_set.ordset_spec_code := harris_op_code_impl h.(harris_find_spec_code);

  spec_ordered_set.OrderedSet := HSet;
  spec_ordered_set.IsOrderedSet := IsHSet N hazptrN (hazard_pointer_impl Σ);

  spec_ordered_set.IsOrderedSet_Persistent := IsHSet_persistent N hazptrN (hazard_pointer_impl Σ);
  spec_ordered_set.OrderedSet_Timeless := HSet_timeless;

  spec_ordered_set.ordset_new_spec := hset_new_spec N hazptrN (hazard_pointer_impl Σ);
  spec_ordered_set.ordset_lookup_spec := hset_lookup_spec N hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ) h;
  spec_ordered_set.ordset_insert_spec := hset_insert_spec N hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ) h;
  spec_ordered_set.ordset_delete_spec := hset_delete_spec N hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ) h;
|}.

Program Definition hm_impl Σ `{!heapGS Σ, !hazptrG Σ, !hlG Σ}
    : ordset_spec Σ hmsN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ) :=
  harris_op_impl Σ hmsN ltac:(solve_ndisj) (hm_impl Σ hmsN hazptrN ltac:(solve_ndisj) (hazard_pointer_impl Σ)).
