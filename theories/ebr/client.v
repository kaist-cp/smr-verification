From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import adequacy notation proofmode.
From smr.ebr Require Import spec_rcu_common spec_rcu_simple closed_proofs.

From iris.prelude Require Import options.

Section code.
Definition rcu_code := ebr_rcu_code_impl.
Definition counter_code := counter_code_impl.
Definition hcounter_code := hcounter_code_impl.
Definition treiber_code := treiber_code_impl.
Definition elimstack_code := elimstack_code_impl.
Definition ms_code := ms_code_impl.
Definition dglm_code := dglm_code_impl.
Definition rdcss_code := rdcss_code_impl.
Definition cldeque_code := cldeque_code_impl.

Definition client1 : val := λ: <>,
  let: "dom" := rcu_code.(rcu_domain_new) #() in
  let: "guard" := rcu_code.(guard_new) "dom" in
  let: "c" := counter_code.(spec_counter.counter_new) "dom" in
  let: "h" := hcounter_code.(spec_hybrid_counter.hcounter_new) "dom" in
  counter_code.(spec_counter.counter_inc) "c" "guard";;
  hcounter_code.(spec_hybrid_counter.hcounter_inc) "h" "guard";;

  let: "s" := treiber_code.(spec_stack.stack_new) "dom" in
  let: "q" := ms_code.(spec_queue.queue_new) "dom" in
  treiber_code.(spec_stack.stack_push) "s" #1%Z "guard";;
  ms_code.(spec_queue.queue_push) "q" #2%Z "guard";;
  let: "oa" := treiber_code.(spec_stack.stack_pop) "s" "guard" in
  let: "ob" := ms_code.(spec_queue.queue_pop) "q" "guard" in

  rcu_code.(guard_drop) "guard";;
  rcu_code.(rcu_domain_do_reclamation) "dom";;
  let: "a" :=
    match: "oa" with
     NONE => #()
    | SOME "a" => "a"
    end
  in
  let: "b" :=
    match: "ob" with
     NONE => #()
    | SOME "b" => "b"
    end
  in
  "a" + "b".

Definition reclaim_forever : val :=
  rec: "loop" "dom" :=
    rcu_code.(rcu_domain_do_reclamation) "dom";;
    "loop" "dom".

Definition client2 : val := λ: <>,
  let: "dom" := rcu_code.(rcu_domain_new) #() in
  Fork (reclaim_forever "dom");;
  let: "guard" := rcu_code.(guard_new) "dom" in
  let: "guard'" := rcu_code.(guard_new) "dom" in
  let: "s" := treiber_code.(spec_stack.stack_new) "dom" in
  Fork(
    treiber_code.(spec_stack.stack_push) "s" #10%Z "guard";;
    treiber_code.(spec_stack.stack_pop) "s" "guard";;
    rcu_code.(guard_drop) "guard"
  );;
  treiber_code.(spec_stack.stack_push) "s" #10%Z "guard'";;
  treiber_code.(spec_stack.stack_pop) "s" "guard'";;
  rcu_code.(guard_drop) "guard'".

Definition client3 : val := λ: <>,
  let: "dom" := rcu_code.(rcu_domain_new) #() in
  let: "guard" := rcu_code.(guard_new) "dom" in
  let: "s1" := elimstack_code.(spec_stack.stack_new) "dom" in
  let: "s2" := elimstack_code.(spec_stack.stack_new) "dom" in
  elimstack_code.(spec_stack.stack_push) "s1" #10%Z "guard";;
  let: "oa" := elimstack_code.(spec_stack.stack_pop) "s1" "guard" in
  let: "a" :=
    match: "oa" with
     NONE => #()
    | SOME "a" => "a"
    end
  in
  elimstack_code.(spec_stack.stack_push) "s2" "a" "guard";;
  let: "ob" := elimstack_code.(spec_stack.stack_pop) "s2" "guard" in
  match: "ob" with
    NONE => #()
  | SOME "b" => "b"
  end
  .

End code.

Section proof.
Context `{!heapGS Σ, !rcu_simple_implG Σ, !counterG Σ, !hcounterG Σ, !treiberG Σ, !elimstackG Σ, !msG Σ}.

Definition rcu := rcu_simple_impl Σ.
Definition counter := counter_impl Σ.
Definition hcounter := hcounter_impl Σ.
Definition treiber := treiber_impl Σ.
Definition elimstack := elimstack_impl Σ.
Definition ms := ms_impl Σ.

Definition clientN := nroot .@ "client".

Lemma client1_spec :
  {{{ True }}}
    client1 #()
  {{{ RET #3; True }}}.
Proof using All.
  iIntros (Φ) "_ HΦ".
  wp_lam. wp_apply (rcu.(spec_rcu_simple.rcu_domain_new_spec) with "[//]") as (??) "#E".
  wp_let.
  wp_apply (rcu.(spec_rcu_simple.guard_new_spec) with "[//]") as (?) "G"; [auto|auto|].
  wp_let.

  (* counters *)
  wp_apply (counter.(spec_counter.counter_new_spec) with "[//]") as (??) "[#IC C]".
  wp_let.
  wp_apply (hcounter.(spec_hybrid_counter.hcounter_new_spec) with "[//]") as (??) "[#IH H]".
  wp_let.
  awp_apply (counter.(spec_counter.counter_inc_spec) with "IC G") without "HΦ".
  iAaccIntro with "C"; first by eauto with iFrame.
  iIntros "C !> G HΦ". wp_seq.
  awp_apply (hcounter.(spec_hybrid_counter.hcounter_inc_spec) with "IH G") without "HΦ".
  iAaccIntro with "H"; first by eauto with iFrame.
  iIntros "H !> G HΦ". wp_seq.

  (* stack, queue *)
  wp_apply (treiber.(spec_stack.stack_new_spec) with "[//]") as (??) "[#IS S]".
  wp_let.
  wp_apply (ms.(spec_queue.queue_new_spec) with "[//]") as (??) "[#IQ Q]".
  wp_let.

  (* NOTE: we need to explictly give the values for push
    because Coq will otherwise not be able to do unification.
    Suspected reason is simplification due to [of_val]  *)
  awp_apply (treiber.(spec_stack.stack_push_spec) $! _ _ _ _ #1 with "IS G") without "HΦ".
  iAaccIntro with "S"; first by eauto with iFrame.
  iIntros "S !> G HΦ". wp_seq.
  awp_apply (ms.(spec_queue.queue_push_spec) $! _ _ _ #2 with "IQ G") without "HΦ".
  iAaccIntro with "Q"; first by eauto with iFrame.
  iIntros "Q !> G HΦ". wp_seq.
  awp_apply (treiber.(spec_stack.stack_pop_spec) with "IS G") without "HΦ".
  iAaccIntro with "S"; first by eauto with iFrame.
  iIntros "S !> G HΦ". wp_pures.
  awp_apply (ms.(spec_queue.queue_pop_spec) with "IQ G") without "HΦ".
  iAaccIntro with "Q"; first by eauto with iFrame.
  iIntros "Q !> G HΦ". wp_pures.

  wp_apply (rcu.(spec_rcu_simple.guard_drop_spec) with "E G") as "_"; [auto|].
  wp_seq.
  wp_apply (rcu.(spec_rcu_simple.rcu_domain_do_reclamation_spec) with "E [//]") as "_"; [auto|].
  wp_pures. by iApply "HΦ".
Qed.

Lemma reclaim_forever_spec γd d :
  rcu.(spec_rcu_simple.IsRCUDomain) γd d -∗
  {{{ True }}} reclaim_forever #d {{{ RET #(); True }}}.
Proof.
  iIntros "#D".
  iIntros (Φ) "!> _ HΦ". iLöb as "IH".
  wp_lam. wp_apply (rcu.(spec_rcu_simple.rcu_domain_do_reclamation_spec) with "D [//]") as "_"; [auto|].
  wp_seq. by iApply "IH".
Qed.

Lemma client2_spec :
  {{{ True }}}
    client2 #()
  {{{ RET #(); True }}}.
Proof using All.
  iIntros (Φ) "_ HΦ".
  wp_lam.
  wp_apply (rcu.(spec_rcu_simple.rcu_domain_new_spec) with "[//]") as (??) "#D".
  wp_let.
  wp_apply wp_fork. { wp_apply reclaim_forever_spec; auto. }
  wp_seq.
  wp_apply (rcu.(spec_rcu_simple.guard_new_spec) with "[//]") as (?) "G"; [auto|auto|].
  wp_let.
  wp_apply (rcu.(spec_rcu_simple.guard_new_spec) with "[//]") as (?) "G'"; [auto|auto|].
  wp_let.
  wp_apply (treiber.(spec_stack.stack_new_spec) with "[//]") as (??) "[#IS S]".
  wp_let.
  iMod (inv_alloc clientN _ (∃ xs, TStack γs xs) with "[S]") as "#SInv". { eauto. }

  wp_apply (wp_fork with "[G]").
  { iNext.
    awp_apply (treiber.(spec_stack.stack_push_spec) $! _ _ _ _ #10 with "IS G").
    iInv "SInv" as (xs) ">S". iAaccIntro with "S".
    { iIntros "S !>". iFrame. eauto. }
    iIntros "S !>". iSplitL "S"; [eauto|].
    iIntros "G". wp_seq.
    awp_apply (treiber.(spec_stack.stack_pop_spec) with "IS G").
    iInv "SInv" as (xs') ">S". iAaccIntro with "S".
    { iIntros "S". eauto with iFrame. }
    iIntros "S !>". iSplitL "S"; [eauto|].
    iIntros "G". wp_seq.
    wp_apply (rcu.(spec_rcu_simple.guard_drop_spec) with "D G"); auto.
  }

  wp_seq.
  awp_apply (treiber.(spec_stack.stack_push_spec) $! _ _ _ _ #10 with "IS G'").
  iInv "SInv" as (xs) ">S". iAaccIntro with "S".
  { iIntros "S !>". iFrame. eauto. }
  iIntros "S !>". iSplitL "S"; [eauto|].
  iIntros "G'". wp_seq.
  awp_apply (treiber.(spec_stack.stack_pop_spec) with "IS G'").
  iInv "SInv" as (xs') ">S". iAaccIntro with "S".
  { iIntros "S". eauto with iFrame. }
  iIntros "S !>". iSplitL "S"; [eauto|].
  iIntros "G'". wp_seq.
  wp_apply (rcu.(spec_rcu_simple.guard_drop_spec) with "D G'"); auto.
Qed.

Lemma client3_spec :
  {{{ True }}}
    client3 #()
  {{{ RET #10; True }}}.
Proof using All.
  iIntros (Φ) "_ HΦ".
  wp_lam.
  wp_apply (rcu.(spec_rcu_simple.rcu_domain_new_spec) with "[//]") as (??) "#D".
  wp_let.
  wp_apply (rcu.(spec_rcu_simple.guard_new_spec) with "[//]") as (?) "G"; [auto|auto|].
  wp_let.
  wp_apply (elimstack.(spec_stack.stack_new_spec) with "[//]") as (γ1 ?) "[#IS1 S1]".
  wp_let.
  wp_apply (elimstack.(spec_stack.stack_new_spec) with "[//]") as (γ2 ?) "[#IS2 S2]".
  wp_let.

  awp_apply (elimstack.(spec_stack.stack_push_spec) $! _ _ _ _ #10 with "IS1 G") without "HΦ".
  iAaccIntro with "S1"; first by eauto with iFrame.
  iIntros "S1 !> G HΦ". wp_seq.
  awp_apply (elimstack.(spec_stack.stack_pop_spec) with "IS1 G") without "HΦ".
  iAaccIntro with "S1"; first by eauto with iFrame.
  iIntros "S1 !> G HΦ". wp_pures.

  awp_apply (elimstack.(spec_stack.stack_push_spec) $! _ _ _ _ #10 with "IS2 G") without "HΦ".
  iAaccIntro with "S2"; first by eauto with iFrame.
  iIntros "S2 !> G HΦ". wp_seq.
  awp_apply (elimstack.(spec_stack.stack_pop_spec) with "IS2 G") without "HΦ".
  iAaccIntro with "S2"; first by eauto with iFrame.
  iIntros "S2 !> G HΦ". wp_pures.
  by iApply "HΦ".
Qed.

End proof.

Definition clientΣ : gFunctors := #[heapΣ; rcu_simple_implΣ; counterΣ; hcounterΣ; treiberΣ; elimstackΣ; msΣ].

Lemma client1_adequate σ : adequate NotStuck (client1 #()) σ (λ v _, v = #3).
Proof.
  apply (heap_adequacy clientΣ)=> ?.
  iIntros "_". iApply client1_spec; done.
Qed.

Lemma client2_adequate σ : adequate NotStuck (client2 #()) σ (λ v _, v = #()).
Proof.
  apply (heap_adequacy clientΣ)=> ?.
  iIntros "_". iApply client2_spec; done.
Qed.

Lemma client3_adequate σ : adequate NotStuck (client3 #()) σ (λ v _, v = #10).
Proof.
  apply (heap_adequacy clientΣ)=> ?.
  iIntros "_". iApply client3_spec; done.
Qed.
