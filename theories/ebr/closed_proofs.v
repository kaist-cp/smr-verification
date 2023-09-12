(* Importing required RAs and namespace *)
From smr.lang Require Import proofmode.
From smr Require Import base_logic.lib.mono_nats logic.reclamation logic.epoch_history logic.node_link_history.

(* Proof of rcu and inner DS *)
From smr Require Import proof_retired_list proof_slot_bag_onat.
From smr.ebr Require Import code_ebr spec_rcu_base spec_rcu_simple spec_rcu_traversal proof_ebr_rcu_base proof_rcu_simple proof_rcu_traversal.

(* Proof of rcu clients. *)
From smr.ebr Require Export spec_counter code_counter proof_counter.
From smr.ebr Require Export spec_hybrid_counter code_hybrid_counter proof_hybrid_counter.
From smr.ebr Require Export spec_stack.
From smr.ebr Require Export code_treiber proof_treiber.
From smr.ebr Require Export code_elimstack proof_elimstack.
From smr.ebr Require Export spec_queue.
From smr.ebr Require Export code_ms proof_ms.
From smr.ebr Require Export code_dglm proof_dglm.
From smr.ebr Require Export spec_rdcss code_rdcss proof_rdcss.
From smr.ebr Require Export spec_cldeque code_cldeque proof_cldeque.
From smr.ebr Require Export spec_ordered_set code_harris_operations proof_harris_find proof_harris_michael_find.

From iris.prelude Require Import options.

Definition rcuN := nroot .@ "rcu".
Definition rcu_mgmtN := rcuN .@ "mgmt".
Definition rcu_ptrsN := rcuN .@ "ptr".
Definition counterN := nroot .@ "counter".
Definition hcounterN := nroot .@ "hcounter".
Definition treiberN := nroot .@ "treiber".
Definition elimN := nroot .@ "elim".
Definition msqueueN := nroot .@ "msqueue".
Definition dglmN := nroot .@ "dglm".
Definition rdcssN := nroot .@ "rdcss".
Definition cldequeN := nroot .@ "cldeque".
Definition hsN := nroot .@ "hsN".
Definition hmsN := nroot .@ "hmsN".

Lemma DISJN : rcu_mgmtN ## rcu_ptrsN. Proof. solve_ndisj. Qed.

Class rcu_base_implG Σ := RCUBaseImplG {
  rcu_base_impl_ebrG :> ebrG Σ;
  rcu_base_impl_slot_bag :> slot_bag_onatG Σ;
}.

Definition rcu_base_implΣ : gFunctors := #[ebrΣ; slot_bag_onatΣ].

Global Instance subG_rcu_base_implΣ {Σ} :
  subG rcu_base_implΣ Σ → rcu_base_implG Σ.
Proof. solve_inG. Qed.

Class rcu_simple_implG Σ := RCUSimpleImplG {
  rcu_simple_impl_baseG :> rcu_base_implG Σ;
}.

Definition rcu_simple_implΣ : gFunctors := #[rcu_base_implΣ].

Global Instance subG_simple_implΣ {Σ} :
  subG rcu_simple_implΣ Σ → rcu_simple_implG Σ.
Proof. solve_inG. Qed.

Class rcu_traversal_implG Σ := RCUTraversalImplG {
  rcu_tarversal_impl_baseG :> rcu_base_implG Σ;
  rcu_tarversal_implG :> rcu_traversalG Σ;
}.

Definition rcu_traversal_implΣ : gFunctors := #[rcu_base_implΣ; rcu_traversalΣ].

Global Instance subG_traversal_implΣ {Σ} :
  subG rcu_traversal_implΣ Σ → rcu_traversal_implG Σ.
Proof. solve_inG. Qed.

Definition ebr_rcu_code_impl : rcu_code := {|
  spec_rcu_common.rcu_domain_new := ebr_domain_new;
  spec_rcu_common.rcu_domain_retire := ebr_domain_retire;
  spec_rcu_common.rcu_domain_do_reclamation := ebr_domain_do_reclamation;
  spec_rcu_common.guard_new := ebr_guard_new;
  spec_rcu_common.guard_activate := ebr_guard_activate;
  spec_rcu_common.guard_deactivate := ebr_guard_deactivate;
  spec_rcu_common.guard_drop := ebr_guard_drop;
|}.

Definition rcu_base_impl Σ `{!heapGS Σ, !rcu_base_implG Σ}
    : rcu_base_spec Σ rcu_mgmtN rcu_ptrsN := {|
  spec_rcu_base.rcu_spec_code := ebr_rcu_code_impl;

  spec_rcu_base.RCUAuth := proof_ebr_rcu_base.EBRAuth;
  spec_rcu_base.IsRCUDomain := proof_ebr_rcu_base.IsEBRDomain rcu_mgmtN rcu_ptrsN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_rcu_base.BaseManaged := proof_ebr_rcu_base.BaseManaged rcu_mgmtN rcu_ptrsN;
  spec_rcu_base.BaseInactive := proof_ebr_rcu_base.BaseInactive (slot_bag_impl Σ);
  spec_rcu_base.BaseGuard := proof_ebr_rcu_base.BaseGuard rcu_mgmtN (slot_bag_impl Σ);
  spec_rcu_base.BaseNodeInfo := proof_ebr_rcu_base.BaseNodeInfo rcu_mgmtN rcu_ptrsN;
  spec_rcu_base.BaseGuardedNodeInfo := proof_ebr_rcu_base.BaseGuardedNodeInfo rcu_mgmtN rcu_ptrsN;

  spec_rcu_base.RCUAuth_timeless := proof_ebr_rcu_base.EBRAuth_timeless rcu_mgmtN rcu_ptrsN DISJN;
  spec_rcu_base.IsRCUDomain_persistent := proof_ebr_rcu_base.IsEBRDomain_Persistent rcu_mgmtN rcu_ptrsN DISJN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_rcu_base.BaseNodeInfo_persistent := proof_ebr_rcu_base.BaseNodeInfo_persistent rcu_mgmtN rcu_ptrsN DISJN;
  spec_rcu_base.BaseNodeInfo_contractive := proof_ebr_rcu_base.BaseNodeInfo_contractive rcu_mgmtN rcu_ptrsN DISJN;
  spec_rcu_base.BaseGuardedNodeInfo_persistent := proof_ebr_rcu_base.BaseGuardedNodeInfo_persistent rcu_mgmtN rcu_ptrsN DISJN;

  spec_rcu_base.rcu_domain_new_spec := proof_ebr_rcu_base.rcu_domain_new_spec rcu_mgmtN rcu_ptrsN DISJN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_rcu_base.rcu_domain_register := proof_ebr_rcu_base.rcu_domain_register rcu_mgmtN rcu_ptrsN DISJN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_rcu_base.guard_new_spec := proof_ebr_rcu_base.guard_new_spec rcu_mgmtN rcu_ptrsN DISJN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_rcu_base.guard_protect := proof_ebr_rcu_base.guard_protect rcu_mgmtN rcu_ptrsN DISJN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_rcu_base.guard_protect_node_info := proof_ebr_rcu_base.guard_protect_node_info rcu_mgmtN rcu_ptrsN DISJN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_rcu_base.rcu_auth_guard_subset := proof_ebr_rcu_base.rcu_auth_guard_subset rcu_mgmtN rcu_ptrsN DISJN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_rcu_base.guard_activate_spec := proof_ebr_rcu_base.guard_activate_spec rcu_mgmtN rcu_ptrsN DISJN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_rcu_base.guard_deactivate_spec := proof_ebr_rcu_base.guard_deactivate_spec rcu_mgmtN rcu_ptrsN DISJN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_rcu_base.guard_drop_spec := proof_ebr_rcu_base.guard_drop_spec rcu_mgmtN rcu_ptrsN DISJN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_rcu_base.guard_drop_inactive_spec := proof_ebr_rcu_base.guard_drop_inactive_spec rcu_mgmtN rcu_ptrsN DISJN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_rcu_base.guard_acc := proof_ebr_rcu_base.guard_acc rcu_mgmtN rcu_ptrsN DISJN (slot_bag_impl Σ);
  spec_rcu_base.managed_acc := proof_ebr_rcu_base.managed_acc rcu_mgmtN rcu_ptrsN DISJN;
  spec_rcu_base.managed_exclusive := proof_ebr_rcu_base.managed_exclusive rcu_mgmtN rcu_ptrsN DISJN;
  spec_rcu_base.managed_get_node_info := proof_ebr_rcu_base.managed_get_node_info rcu_mgmtN rcu_ptrsN DISJN;
  spec_rcu_base.guard_managed_agree := proof_ebr_rcu_base.guard_managed_agree rcu_mgmtN rcu_ptrsN DISJN (slot_bag_impl Σ);
  spec_rcu_base.rcu_domain_retire_spec := proof_ebr_rcu_base.rcu_domain_retire_spec rcu_mgmtN rcu_ptrsN DISJN (slot_bag_impl Σ) (retired_list_impl Σ);
  spec_rcu_base.rcu_domain_do_reclamation_spec := proof_ebr_rcu_base.rcu_domain_do_reclamation_spec rcu_mgmtN rcu_ptrsN DISJN (slot_bag_impl Σ) (retired_list_impl Σ);
|}.

Definition rcu_simple_impl Σ `{!heapGS Σ, !rcu_simple_implG Σ}
    : rcu_simple_spec Σ rcuN := {|
  spec_rcu_simple.rcu_spec_code := ebr_rcu_code_impl;

  spec_rcu_simple.IsRCUDomain := proof_rcu_simple.IsRCUDomain rcuN (rcu_base_impl Σ);
  spec_rcu_simple.Managed := proof_rcu_simple.Managed rcuN (rcu_base_impl Σ);
  spec_rcu_simple.Guard := proof_rcu_simple.Guard rcuN (rcu_base_impl Σ);
  spec_rcu_simple.NodeInfo := proof_rcu_simple.NodeInfo rcuN (rcu_base_impl Σ);

  spec_rcu_simple.IsRCUDomain_Persistent := proof_rcu_simple.IsRCUDomain_Persistent rcuN (rcu_base_impl Σ);

  spec_rcu_simple.rcu_domain_new_spec := proof_rcu_simple.rcu_domain_new_spec rcuN (rcu_base_impl Σ);
  spec_rcu_simple.rcu_domain_register := proof_rcu_simple.rcu_domain_register rcuN (rcu_base_impl Σ);
  spec_rcu_simple.guard_new_spec := proof_rcu_simple.guard_new_spec rcuN (rcu_base_impl Σ);
  spec_rcu_simple.guard_protect := proof_rcu_simple.guard_protect rcuN (rcu_base_impl Σ);
  spec_rcu_simple.guard_activate_spec := proof_rcu_simple.guard_activate_spec rcuN (rcu_base_impl Σ);
  spec_rcu_simple.guard_deactivate_spec := proof_rcu_simple.guard_deactivate_spec rcuN (rcu_base_impl Σ);
  spec_rcu_simple.guard_drop_spec := proof_rcu_simple.guard_drop_spec rcuN (rcu_base_impl Σ);
  spec_rcu_simple.guard_acc := proof_rcu_simple.guard_acc rcuN (rcu_base_impl Σ);
  spec_rcu_simple.managed_acc := proof_rcu_simple.managed_acc rcuN (rcu_base_impl Σ);
  spec_rcu_simple.managed_exclusive := proof_rcu_simple.managed_exclusive rcuN (rcu_base_impl Σ);
  spec_rcu_simple.guard_managed_agree := proof_rcu_simple.guard_managed_agree rcuN (rcu_base_impl Σ);
  spec_rcu_simple.rcu_domain_retire_spec := proof_rcu_simple.rcu_domain_retire_spec rcuN (rcu_base_impl Σ);
  spec_rcu_simple.rcu_domain_do_reclamation_spec := proof_rcu_simple.rcu_domain_do_reclamation_spec rcuN (rcu_base_impl Σ);
|}.

Definition rcu_traversal_impl Σ `{!heapGS Σ, !rcu_traversal_implG Σ}
    : rcu_traversal_spec Σ rcuN := {|
  spec_rcu_traversal.rcu_spec_code := ebr_rcu_code_impl;

  spec_rcu_traversal.IsRCUDomain := proof_rcu_traversal.IsRCUDomain rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.Inactive := proof_rcu_traversal.Inactive rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.Guard := proof_rcu_traversal.Guard rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.Managed := proof_rcu_traversal.Managed rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.Deleted := proof_rcu_traversal.Deleted rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.RCUPointsTo := proof_rcu_traversal.RCUPointsTo rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.RCUNodeInfo := proof_rcu_traversal.RCUNodeInfo rcuN (rcu_base_impl Σ);

  spec_rcu_traversal.IsRCUDomain_Persistent := proof_rcu_traversal.IsRCUDomain_Persistent rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.RCUPointsTo_Some_Contractive := proof_rcu_traversal.RCUPointsTo_Some_Contractive rcuN (rcu_base_impl Σ);

  spec_rcu_traversal.rcu_domain_new_spec := proof_rcu_traversal.rcu_domain_new_spec rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.rcu_domain_register := proof_rcu_traversal.rcu_domain_register rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.guard_new_spec := proof_rcu_traversal.guard_new_spec rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.guard_activate_spec := proof_rcu_traversal.guard_activate_spec rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.guard_deactivate_spec := proof_rcu_traversal.guard_deactivate_spec rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.guard_drop_spec := proof_rcu_traversal.guard_drop_spec rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.guard_drop_inactive_spec := proof_rcu_traversal.guard_drop_inactive_spec rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.guard_protect_managed := proof_rcu_traversal.guard_protect_managed rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.guard_protect_rcu_points_to := proof_rcu_traversal.guard_protect_rcu_points_to rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.guard_acc := proof_rcu_traversal.guard_acc rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.managed_acc := proof_rcu_traversal.managed_acc rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.deleted_acc := proof_rcu_traversal.deleted_acc rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.managed_exclusive := proof_rcu_traversal.managed_exclusive rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.guard_managed_agree := proof_rcu_traversal.guard_managed_agree rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.rcu_points_to_link := proof_rcu_traversal.rcu_points_to_link rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.rcu_points_to_unlink := proof_rcu_traversal.rcu_points_to_unlink rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.rcu_points_to_update := proof_rcu_traversal.rcu_points_to_update rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.managed_delete := proof_rcu_traversal.managed_delete rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.deleted_clean := proof_rcu_traversal.deleted_clean rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.rcu_domain_retire_spec := proof_rcu_traversal.rcu_domain_retire_spec rcuN (rcu_base_impl Σ);
  spec_rcu_traversal.rcu_domain_do_reclamation_spec := proof_rcu_traversal.rcu_domain_do_reclamation_spec rcuN (rcu_base_impl Σ);
|}.

Definition counter_code_impl : counter_code := {|
  spec_counter.counter_new := counter_new;
  spec_counter.counter_inc := (counter_inc ebr_rcu_code_impl);
|}.

Definition counter_impl Σ `{!heapGS Σ, !counterG Σ, !rcu_simple_implG Σ}
    : counter_spec Σ counterN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ) := {|
  spec_counter.counter_spec_code := counter_code_impl;

  spec_counter.Counter := Counter;
  spec_counter.IsCounter := IsCounter counterN rcuN (rcu_simple_impl Σ);

  spec_counter.Counter_Timeless := Counter_Timeless;
  spec_counter.IsCounter_Persistent := IsCounter_Persistent counterN rcuN (rcu_simple_impl Σ);

  spec_counter.counter_new_spec := counter_new_spec counterN rcuN (rcu_simple_impl Σ);
  spec_counter.counter_inc_spec := counter_inc_spec counterN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ);
|}.

Definition hcounter_code_impl : hcounter_code := {|
  spec_hybrid_counter.hcounter_new := hcounter_new;
  spec_hybrid_counter.hcounter_inc := (hcounter_inc ebr_rcu_code_impl);
|}.

Definition hcounter_impl Σ `{!heapGS Σ, !hcounterG Σ, !rcu_simple_implG Σ}
    : hcounter_spec Σ hcounterN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ) := {|
  spec_hybrid_counter.hcounter_spec_code := hcounter_code_impl;

  spec_hybrid_counter.HCounter := HCounter;
  spec_hybrid_counter.IsHCounter := IsHCounter hcounterN rcuN (rcu_simple_impl Σ);

  spec_hybrid_counter.HCounter_Timeless := HCounter_Timeless;
  spec_hybrid_counter.IsHCounter_Persistent := IsHCounter_Persistent hcounterN rcuN (rcu_simple_impl Σ);

  spec_hybrid_counter.hcounter_new_spec := hcounter_new_spec hcounterN rcuN (rcu_simple_impl Σ);
  spec_hybrid_counter.hcounter_inc_spec := hcounter_inc_spec hcounterN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ);
|}.

Definition treiber_code_impl : stack_code := {|
  stack_new := tstack_new;
  stack_push := tstack_push;
  stack_pop := (tstack_pop ebr_rcu_code_impl);
|}.

Definition treiber_impl Σ `{!heapGS Σ, !treiberG Σ, !rcu_simple_implG Σ}
    : stack_spec Σ treiberN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ) := {|
  stack_spec_code := treiber_code_impl;

  Stack := TStack;
  IsStack := IsTStack treiberN rcuN (rcu_simple_impl Σ);

  Stack_Timeless := TStack_Timeless;
  IsStack_Persistent := IsTStack_Persistent treiberN rcuN (rcu_simple_impl Σ);

  stack_new_spec := tstack_new_spec treiberN rcuN (rcu_simple_impl Σ);
  stack_push_spec := tstack_push_spec treiberN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ);
  stack_pop_spec := tstack_pop_spec treiberN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ);
|}.

Definition elimstack_code_impl : stack_code := {|
  stack_new := estack_new;
  stack_push := (estack_push ebr_rcu_code_impl);
  stack_pop := (estack_pop ebr_rcu_code_impl);
|}.

Definition elimstack_impl Σ `{!heapGS Σ, !elimstackG Σ, !rcu_simple_implG Σ}
    : stack_spec Σ elimN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ) := {|
  stack_spec_code := elimstack_code_impl;

  Stack := EStack;
  IsStack := IsEStack elimN rcuN (rcu_simple_impl Σ);

  Stack_Timeless := EStack_Timeless;
  IsStack_Persistent := IsEStack_Persistent elimN rcuN (rcu_simple_impl Σ);

  stack_new_spec := estack_new_spec elimN rcuN (rcu_simple_impl Σ);
  stack_push_spec := estack_push_spec elimN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ);
  stack_pop_spec := estack_pop_spec elimN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ);
|}.

Definition ms_code_impl : queue_code := {|
  spec_queue.queue_new := code_ms.queue_new;
  spec_queue.queue_push := (code_ms.queue_push ebr_rcu_code_impl);
  spec_queue.queue_pop := (code_ms.queue_pop ebr_rcu_code_impl);
|}.

Definition ms_impl Σ `{!heapGS Σ, !msG Σ, !rcu_simple_implG Σ}
    : queue_spec Σ msqueueN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ) := {|
  spec_queue.queue_spec_code := ms_code_impl;

  spec_queue.Queue := proof_ms.Queue;
  spec_queue.IsQueue := proof_ms.IsQueue msqueueN rcuN (rcu_simple_impl Σ);

  spec_queue.Queue_Timeless := proof_ms.Queue_Timeless;
  spec_queue.IsQueue_Persistent := proof_ms.IsQueue_Persistent msqueueN rcuN (rcu_simple_impl Σ);

  spec_queue.queue_new_spec := proof_ms.queue_new_spec msqueueN rcuN (rcu_simple_impl Σ);
  spec_queue.queue_push_spec := proof_ms.queue_push_spec msqueueN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ);
  spec_queue.queue_pop_spec := proof_ms.queue_pop_spec msqueueN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ);
|}.

Definition dglm_code_impl : queue_code := {|
  spec_queue.queue_new := code_dglm.queue_new;
  spec_queue.queue_push := (code_dglm.queue_push ebr_rcu_code_impl);
  spec_queue.queue_pop := (code_dglm.queue_pop ebr_rcu_code_impl);
|}.

Definition dglm_impl Σ `{!heapGS Σ, !dglmG Σ, !rcu_simple_implG Σ}
    : queue_spec Σ dglmN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ) := {|
  spec_queue.queue_spec_code := dglm_code_impl;

  spec_queue.Queue := proof_dglm.Queue;
  spec_queue.IsQueue := proof_dglm.IsQueue dglmN rcuN (rcu_simple_impl Σ);

  spec_queue.Queue_Timeless := proof_dglm.Queue_Timeless;
  spec_queue.IsQueue_Persistent := proof_dglm.IsQueue_Persistent dglmN rcuN (rcu_simple_impl Σ);

  spec_queue.queue_new_spec := proof_dglm.queue_new_spec dglmN rcuN (rcu_simple_impl Σ);
  spec_queue.queue_push_spec := proof_dglm.queue_push_spec dglmN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ);
  spec_queue.queue_pop_spec := proof_dglm.queue_pop_spec dglmN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ);
|}.

Definition rdcss_code_impl : rdcss_code := {|
  spec_rdcss.new_rdcss := new_rdcss;
  spec_rdcss.get := (get ebr_rcu_code_impl);
  spec_rdcss.rdcss := (rdcss ebr_rcu_code_impl);
|}.

Definition rdcss_impl Σ `{!heapGS Σ, !rdcssG Σ, !rcu_simple_implG Σ}
    : rdcss_spec_record Σ rdcssN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ) := {|
  spec_rdcss.rdcss_spec_code := rdcss_code_impl;

  spec_rdcss.Rdcss := Rdcss;
  spec_rdcss.IsRdcss := IsRdcss rdcssN rcuN (rcu_simple_impl Σ);

  spec_rdcss.Rdcss_Timeless := Rdcss_Timeless;
  spec_rdcss.IsRdcss_Persistent := IsRdcss_Persistent rdcssN rcuN (rcu_simple_impl Σ);

  spec_rdcss.new_rdcss_spec := new_rdcss_spec rdcssN rcuN (rcu_simple_impl Σ);
  spec_rdcss.get_spec := get_spec rdcssN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ);
  spec_rdcss.rdcss_spec := rdcss_spec rdcssN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ);
|}.

Definition cldeque_code_impl : deque_code := {|
  spec_cldeque.deque_new := deque_new;
  spec_cldeque.deque_push := deque_push;
  spec_cldeque.deque_pop := deque_pop;
  spec_cldeque.deque_steal := (deque_steal ebr_rcu_code_impl);
|}.

Definition cldeque_impl Σ `{!heapGS Σ, !cldequeG Σ, !rcu_simple_implG Σ}
    : deque_spec Σ cldequeN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ) := {|
  spec_cldeque.deque_spec_code := cldeque_code_impl;

  spec_cldeque.Deque := Deque;
  spec_cldeque.IsDeque := IsDeque cldequeN rcuN (rcu_simple_impl Σ);

  spec_cldeque.OwnDeque := OwnDeque;

  spec_cldeque.IsDeque_Persistent := IsDeque_persistent cldequeN rcuN (rcu_simple_impl Σ);
  spec_cldeque.Deque_Timeless := Deque_timeless;

  spec_cldeque.deque_new_spec := deque_new_spec cldequeN rcuN (rcu_simple_impl Σ);
  spec_cldeque.deque_push_spec := deque_push_spec cldequeN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ);
  spec_cldeque.deque_pop_spec := deque_pop_spec cldequeN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ);
  spec_cldeque.deque_steal_spec := deque_steal_spec cldequeN rcuN ltac:(solve_ndisj) (rcu_simple_impl Σ);
|}.

Definition harris_op_code_impl (h : harris_find_code) : ordset_code := {|
  spec_ordered_set.ordset_new := harris_new;
  spec_ordered_set.ordset_lookup := (harris_lookup h ebr_rcu_code_impl);
  spec_ordered_set.ordset_insert := (harris_insert h ebr_rcu_code_impl);
  spec_ordered_set.ordset_delete := (harris_delete h ebr_rcu_code_impl);
|}.

Definition harris_op_impl Σ N (DISJN : N ## rcuN) `{!heapGS Σ, !hlG Σ, !rcu_traversal_implG Σ}
    (h : hfind_spec Σ N rcuN DISJN (rcu_traversal_impl Σ))
    : ordset_spec Σ N rcuN DISJN (rcu_traversal_impl Σ) := {|
  spec_ordered_set.ordset_spec_code := harris_op_code_impl h.(harris_find_spec_code);

  spec_ordered_set.OrderedSet := HSet;
  spec_ordered_set.IsOrderedSet := IsHSet N rcuN (rcu_traversal_impl Σ);

  spec_ordered_set.IsOrderedSet_Persistent := IsHSet_persistent N rcuN (rcu_traversal_impl Σ);
  spec_ordered_set.OrderedSet_Timeless := HSet_timeless;

  spec_ordered_set.ordset_new_spec := hset_new_spec N rcuN (rcu_traversal_impl Σ);
  spec_ordered_set.ordset_lookup_spec := hset_lookup_spec N rcuN DISJN (rcu_traversal_impl Σ) h;
  spec_ordered_set.ordset_insert_spec := hset_insert_spec N rcuN DISJN (rcu_traversal_impl Σ) h;
  spec_ordered_set.ordset_delete_spec := hset_delete_spec N rcuN DISJN (rcu_traversal_impl Σ) h;
|}.

Definition hm_impl Σ `{!heapGS Σ, !hlG Σ, !rcu_traversal_implG Σ}
    : ordset_spec Σ hmsN rcuN ltac:(solve_ndisj) (rcu_traversal_impl Σ) :=
  harris_op_impl Σ hmsN ltac:(solve_ndisj) (hm_impl Σ hmsN rcuN ltac:(solve_ndisj) (rcu_traversal_impl Σ)).

Definition harris_impl Σ `{!heapGS Σ, !hlG Σ, !rcu_traversal_implG Σ}
    : ordset_spec Σ hsN rcuN ltac:(solve_ndisj) (rcu_traversal_impl Σ) :=
  harris_op_impl Σ hsN ltac:(solve_ndisj) (harris_impl Σ hsN rcuN ltac:(solve_ndisj) (rcu_traversal_impl Σ)).
