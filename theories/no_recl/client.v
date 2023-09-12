From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import adequacy notation proofmode.
From smr.no_recl Require Import closed_proofs.

From iris.prelude Require Import options.

Section code.
Definition counter_code := counter_code_impl.
Definition treiber_code := treiber_code_impl.
Definition elimstack_code := elimstack_code_impl.
Definition ms_code := ms_code_impl.
Definition dglm_code := dglm_code_impl.
Definition rdcss_code := rdcss_code_impl.
Definition cldeque_code := cldeque_code_impl.

Definition client1 : val := λ: <>,
  let: "c" := counter_code.(spec_counter.counter_new) #() in
  counter_code.(spec_counter.counter_inc) "c";;

  let: "s" := treiber_code.(spec_stack.stack_new) #() in
  let: "q" := ms_code.(spec_queue.queue_new) #() in
  treiber_code.(spec_stack.stack_push) "s" #1%Z;;
  ms_code.(spec_queue.queue_push) "q" #2%Z;;
  let: "oa" := treiber_code.(spec_stack.stack_pop) "s" in
  let: "ob" := ms_code.(spec_queue.queue_pop) "q" in
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

Definition client2 : val := λ: <>,
  let: "s" := treiber_code.(spec_stack.stack_new) #() in
  Fork(
    treiber_code.(spec_stack.stack_push) "s" #10%Z;;
    treiber_code.(spec_stack.stack_pop) "s"
  );;
  treiber_code.(spec_stack.stack_push) "s" #10%Z;;
  treiber_code.(spec_stack.stack_pop) "s";;
  #().

Definition client3 : val := λ: <>,
  let: "s1" := elimstack_code.(spec_stack.stack_new) #() in
  let: "s2" := elimstack_code.(spec_stack.stack_new) #() in
  elimstack_code.(spec_stack.stack_push) "s1" #10%Z;;
  let: "oa" := elimstack_code.(spec_stack.stack_pop) "s1" in
  let: "a" :=
    match: "oa" with
     NONE => #()
    | SOME "a" => "a"
    end
  in
  elimstack_code.(spec_stack.stack_push) "s2" "a";;
  let: "ob" := elimstack_code.(spec_stack.stack_pop) "s2" in
  match: "ob" with
    NONE => #()
  | SOME "b" => "b"
  end
  .

End code.

Section proof.
Context `{!heapGS Σ, !counterG Σ, !treiberG Σ, !elimstackG Σ, msG Σ}.

Definition counter := counter_impl Σ.
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
  wp_lam.

  (* counters *)
  wp_apply (counter.(spec_counter.counter_new_spec) with "[//]") as (??) "[#IC C]".
  wp_let.
  awp_apply (counter.(spec_counter.counter_inc_spec) with "IC") without "HΦ".
  iAaccIntro with "C"; first by eauto with iFrame.
  iIntros "C !> _ HΦ". wp_seq.

  (* stack, queue *)
  wp_apply (treiber.(spec_stack.stack_new_spec) with "[//]") as (??) "[#IS S]".
  wp_let.
  wp_apply (ms.(spec_queue.queue_new_spec) with "[//]") as (??) "[#IQ Q]".
  wp_let.
  (* NOTE: we need to explictly give the values for push
    because Coq will otherwise not be able to do unification.
    Suspected reason is simplification due to [of_val]  *)
  awp_apply (treiber.(spec_stack.stack_push_spec) $! _ _ #1 with "IS") without "HΦ".
  iAaccIntro with "S"; first by eauto with iFrame.
  iIntros "S !> _ HΦ". wp_seq.
  awp_apply (ms.(spec_queue.queue_push_spec) $! _ _ #2 with "IQ") without "HΦ".
  iAaccIntro with "Q"; first by eauto with iFrame.
  iIntros "Q !> _ HΦ". wp_seq.
  awp_apply (treiber.(spec_stack.stack_pop_spec) with "IS") without "HΦ"; eauto.
  iAaccIntro with "S"; first by eauto with iFrame.
  iIntros "S !> _ HΦ". wp_pures.
  awp_apply (ms.(spec_queue.queue_pop_spec) with "IQ") without "HΦ"; eauto.
  iAaccIntro with "Q"; first by eauto with iFrame.
  iIntros "Q !> _ HΦ". wp_pures.
  by iApply "HΦ".
Qed.

Lemma client2_spec :
  {{{ True }}}
    client2 #()
  {{{ RET #(); True }}}.
Proof using All.
  iIntros (Φ) "_ HΦ".
  wp_lam.
  wp_apply (treiber.(spec_stack.stack_new_spec) with "[//]") as (??) "[#IS S]".
  wp_let.
  iMod (inv_alloc clientN _ (∃ xs, TStack γ xs) with "[S]") as "#SInv". { eauto. }

  wp_apply wp_fork.
  { awp_apply (treiber.(spec_stack.stack_push_spec) $! _ _ #10 with "IS").
    iInv "SInv" as (xs) ">S". iAaccIntro with "S".
    { iIntros "S !>". iFrame. eauto. }
    iIntros "S !>". iSplitL "S"; eauto.
    iIntros "_". wp_seq.
    awp_apply (treiber.(spec_stack.stack_pop_spec) with "IS"); auto.
    iInv "SInv" as (xs') ">S". iAaccIntro with "S".
    { iIntros "S". eauto with iFrame. }
    iIntros "S !>". iSplitL "S"; eauto with iFrame.
  }

  iIntros. wp_seq.
  awp_apply (treiber.(spec_stack.stack_push_spec) $! _ _ #10 with "IS").
  iInv "SInv" as (xs) ">S". iAaccIntro with "S".
  { iIntros "S !>". iFrame. eauto. }
  iIntros "S !>". iSplitL "S"; eauto.
  iIntros "_". wp_seq.
  awp_apply (treiber.(spec_stack.stack_pop_spec) with "IS") without "HΦ"; auto.
  iInv "SInv" as (xs') ">S". iAaccIntro with "S".
  { iIntros "S". eauto with iFrame. }
  iIntros "S !>". iSplitL "S"; eauto with iFrame.
  iIntros "_ HΦ". wp_pures. by iApply "HΦ".
Qed.

Lemma client3_spec :
  {{{ True }}}
    client3 #()
  {{{ RET #10; True }}}.
Proof using All.
  iIntros (Φ) "_ HΦ".
  wp_lam. wp_apply (elimstack.(spec_stack.stack_new_spec) with "[//]") as (γ1 ?) "[#IS1 S1]".
  wp_let.
  wp_apply (elimstack.(spec_stack.stack_new_spec) with "[//]") as (γ2 ?) "[#IS2 S2]".
  wp_let.

  awp_apply (elimstack.(spec_stack.stack_push_spec) $! _ _ #10 with "IS1") without "HΦ".
  iAaccIntro with "S1"; first by eauto with iFrame.
  iIntros "S1 !> _ HΦ". wp_seq.
  awp_apply (elimstack.(spec_stack.stack_pop_spec) with "IS1") without "HΦ"; eauto.
  iAaccIntro with "S1"; first by eauto with iFrame.
  iIntros "S1 !> _ HΦ". wp_pures.

  awp_apply (elimstack.(spec_stack.stack_push_spec) $! _ _ #10 with "IS2") without "HΦ".
  iAaccIntro with "S2"; first by eauto with iFrame.
  iIntros "S2 !> _ HΦ". wp_pures.
  awp_apply (elimstack.(spec_stack.stack_pop_spec) with "IS2") without "HΦ"; eauto.
  iAaccIntro with "S2"; first by eauto with iFrame.
  iIntros "S2 !> _ HΦ". wp_pures. by iApply "HΦ".
Qed.

End proof.

Definition clientΣ : gFunctors := #[heapΣ; counterΣ; treiberΣ; elimstackΣ; msΣ].

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
