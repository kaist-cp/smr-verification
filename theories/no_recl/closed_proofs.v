(* Importing required RAs and namespace*)
From smr.lang Require Import proofmode.
From smr Require Import logic.reclamation.

(* Proof of hazard pointer and inner DS *)
From smr Require Import proof_retired_list proof_slot_bag_oloc.

(* Proof of hazard pointer clients. *)
From smr.no_recl Require Export spec_counter code_counter proof_counter.
From smr.no_recl Require Export spec_stack.
From smr.no_recl Require Export code_treiber proof_treiber.
From smr.no_recl Require Export code_elimstack proof_elimstack.
From smr.no_recl Require Export spec_queue.
From smr.no_recl Require Export code_ms proof_ms.
From smr.no_recl Require Export code_dglm proof_dglm.
From smr.no_recl Require Export spec_rdcss code_rdcss proof_rdcss.
From smr.no_recl Require Export spec_cldeque code_cldeque proof_cldeque.
From smr.no_recl Require Export spec_ordered_set code_harris_operations proof_harris_find proof_harris_michael_find.

From iris.prelude Require Import options.

Definition counterN := nroot .@ "counter".
Definition treiberN := nroot .@ "treiber".
Definition elimN := nroot .@ "elim".
Definition msqueueN := nroot .@ "msqueue".
Definition dglmN := nroot .@ "dglm".
Definition rdcssN := nroot .@ "rdcss".
Definition cldequeN := nroot .@ "cldeque".
Definition hsN := nroot .@ "hsN".
Definition hmsN := nroot .@ "hmsN".

Definition counter_code_impl : counter_code := {|
  spec_counter.counter_new := counter_new;
  spec_counter.counter_inc := counter_inc;
|}.

Definition counter_impl Σ `{!heapGS Σ, !counterG Σ}
    : counter_spec Σ counterN := {|
  spec_counter.counter_spec_code := counter_code_impl;

  spec_counter.Counter := Counter;
  spec_counter.IsCounter := IsCounter counterN;

  spec_counter.Counter_Timeless := Counter_Timeless;
  spec_counter.IsCounter_Persistent := IsCounter_Persistent counterN;

  spec_counter.counter_new_spec := counter_new_spec counterN;
  spec_counter.counter_inc_spec := counter_inc_spec counterN;
|}.

Definition treiber_code_impl : stack_code := {|
  stack_new := tstack_new;
  stack_push := tstack_push;
  stack_pop := tstack_pop;
|}.

Definition treiber_impl Σ `{!heapGS Σ, !treiberG Σ}
    : stack_spec Σ treiberN := {|
  stack_spec_code := treiber_code_impl;

  Stack := TStack;
  IsStack := IsTStack treiberN;

  Stack_Timeless := TStack_Timeless;
  IsStack_Persistent := IsTStack_Persistent treiberN;

  stack_new_spec := tstack_new_spec treiberN;
  stack_push_spec := tstack_push_spec treiberN;
  stack_pop_spec := tstack_pop_spec treiberN;
|}.

Definition elimstack_code_impl : stack_code := {|
  stack_new := estack_new;
  stack_push := estack_push;
  stack_pop := estack_pop;
|}.

Definition elimstack_impl Σ `{!heapGS Σ, !elimstackG Σ}
    : stack_spec Σ elimN := {|
  stack_spec_code := elimstack_code_impl;

  Stack := EStack;
  IsStack := IsEStack elimN;

  Stack_Timeless := EStack_Timeless;
  IsStack_Persistent := IsEStack_Persistent elimN;

  stack_new_spec := estack_new_spec elimN;
  stack_push_spec := estack_push_spec elimN;
  stack_pop_spec := estack_pop_spec elimN;
|}.

Definition ms_code_impl : queue_code := {|
  spec_queue.queue_new := code_ms.queue_new;
  spec_queue.queue_push := code_ms.queue_push;
  spec_queue.queue_pop := code_ms.queue_pop;
|}.

Definition ms_impl Σ `{!heapGS Σ, !msG Σ}
    : queue_spec Σ msqueueN := {|
  spec_queue.queue_spec_code := ms_code_impl;

  spec_queue.Queue := proof_ms.Queue;
  spec_queue.IsQueue := proof_ms.IsQueue msqueueN;

  spec_queue.Queue_Timeless := proof_ms.Queue_Timeless;
  spec_queue.IsQueue_Persistent := proof_ms.IsQueue_Persistent msqueueN;

  spec_queue.queue_new_spec := proof_ms.queue_new_spec msqueueN;
  spec_queue.queue_push_spec := proof_ms.queue_push_spec msqueueN;
  spec_queue.queue_pop_spec := proof_ms.queue_pop_spec msqueueN;
|}.

Definition dglm_code_impl : queue_code := {|
  spec_queue.queue_new := code_dglm.queue_new;
  spec_queue.queue_push := code_dglm.queue_push;
  spec_queue.queue_pop := code_dglm.queue_pop;
|}.

Definition dglm_impl Σ `{!heapGS Σ, !dglmG Σ}
    : queue_spec Σ dglmN := {|
  spec_queue.queue_spec_code := dglm_code_impl;

  spec_queue.Queue := proof_dglm.Queue;
  spec_queue.IsQueue := proof_dglm.IsQueue dglmN;

  spec_queue.Queue_Timeless := proof_dglm.Queue_Timeless;
  spec_queue.IsQueue_Persistent := proof_dglm.IsQueue_Persistent dglmN;

  spec_queue.queue_new_spec := proof_dglm.queue_new_spec dglmN;
  spec_queue.queue_push_spec := proof_dglm.queue_push_spec dglmN;
  spec_queue.queue_pop_spec := proof_dglm.queue_pop_spec dglmN;
|}.

Definition rdcss_code_impl : rdcss_code := {|
  spec_rdcss.new_rdcss := new_rdcss;
  spec_rdcss.get := get;
  spec_rdcss.rdcss := rdcss;
|}.

Definition rdcss_impl Σ `{!heapGS Σ, !rdcssG Σ}
    : rdcss_spec_record Σ rdcssN := {|
  spec_rdcss.rdcss_spec_code := rdcss_code_impl;

  spec_rdcss.Rdcss := Rdcss;
  spec_rdcss.IsRdcss := IsRdcss rdcssN;

  spec_rdcss.Rdcss_Timeless := Rdcss_Timeless;
  spec_rdcss.IsRdcss_Persistent := IsRdcss_Persistent rdcssN;

  spec_rdcss.new_rdcss_spec := new_rdcss_spec rdcssN;
  spec_rdcss.get_spec := get_spec rdcssN;
  spec_rdcss.rdcss_spec := rdcss_spec rdcssN;
|}.

Definition cldeque_code_impl : deque_code := {|
  spec_cldeque.deque_new := deque_new;
  spec_cldeque.deque_push := deque_push;
  spec_cldeque.deque_pop := deque_pop;
  spec_cldeque.deque_steal := deque_steal;
|}.

Definition cldeque_impl Σ `{!heapGS Σ, !cldequeG Σ}
    : deque_spec Σ cldequeN := {|
  spec_cldeque.deque_spec_code := cldeque_code_impl;

  spec_cldeque.Deque := Deque;
  spec_cldeque.IsDeque := IsDeque cldequeN;

  spec_cldeque.OwnDeque := OwnDeque;

  spec_cldeque.IsDeque_Persistent := IsDeque_persistent cldequeN;
  spec_cldeque.Deque_Timeless := Deque_timeless;

  spec_cldeque.deque_new_spec := deque_new_spec cldequeN;
  spec_cldeque.deque_push_spec := deque_push_spec cldequeN;
  spec_cldeque.deque_pop_spec := deque_pop_spec cldequeN;
  spec_cldeque.deque_steal_spec := deque_steal_spec cldequeN;
|}.

Definition harris_op_code_impl (h : harris_find_code) : ordset_code := {|
  spec_ordered_set.ordset_new := harris_new;
  spec_ordered_set.ordset_lookup := (harris_lookup h);
  spec_ordered_set.ordset_insert := (harris_insert h);
  spec_ordered_set.ordset_delete := (harris_delete h);
|}.

Definition harris_op_impl Σ N `{!heapGS Σ, !hlG Σ} (h : hfind_spec Σ N)
    : ordset_spec Σ N := {|
  spec_ordered_set.ordset_spec_code := (harris_op_code_impl h.(harris_find_spec_code));

  spec_ordered_set.OrderedSet := HSet;
  spec_ordered_set.IsOrderedSet := IsHSet N;

  spec_ordered_set.IsOrderedSet_Persistent := IsHSet_persistent N;
  spec_ordered_set.OrderedSet_Timeless := HSet_timeless;

  spec_ordered_set.ordset_new_spec := hset_new_spec N;
  spec_ordered_set.ordset_lookup_spec := hset_lookup_spec N h;
  spec_ordered_set.ordset_insert_spec := hset_insert_spec N h;
  spec_ordered_set.ordset_delete_spec := hset_delete_spec N h;
|}.

Definition hm_impl Σ `{!heapGS Σ, !hlG Σ} : ordset_spec Σ hmsN := harris_op_impl Σ hmsN (hm_impl Σ hmsN).

Definition harris_impl Σ `{!heapGS Σ, !hlG Σ} : ordset_spec Σ hsN := harris_op_impl Σ hsN (harris_impl Σ hsN).
