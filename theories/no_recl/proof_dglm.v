From iris.base_logic Require Import lib.mono_nat lib.invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr.base_logic Require Import lib.mono_list.
From smr Require Import helpers no_recl.spec_queue no_recl.code_dglm.

Set Printing Projections.

Local Open Scope nat_scope.

Class dglmG Σ := DGLMG {
  #[local] ms_mono_listG :: mono_listG (loc * val) Σ;
  #[local] ms_mono_natG :: mono_natG Σ;
}.

Definition dglmΣ : gFunctors := #[mono_listΣ (loc * val); mono_natΣ].

Global Instance subG_dglmΣ {Σ} :
  subG dglmΣ Σ → dglmG Σ.
Proof. solve_inG. Qed.

Section dglm_queue.
Context `{!heapGS Σ, !dglmG Σ}.
Notation iProp := (iProp Σ).
Context (queueN : namespace).


(* iExists + iFrame *)
Ltac exfr := repeat (repeat iExists _; iFrame "∗#%").

Implicit Types
  (γcl γh : gname)
  (CL : list (loc * val))
  (ih it : nat).

(* Note: invariant, new and push are same as MS queue, but are inlined for better line count comparison. *)

(* Abstract state of the queue *)
Definition Queue (γq : gname) (xs : list val) : iProp :=
  ∃ γcl γh CL ih,
    ⌜γq = encode (γcl, γh)⌝ ∗
    mono_list_auth_own γcl (1/2/2) CL ∗
    mono_nat_auth_own γh (1/2) ih ∗
    ⌜xs = (drop (ih + 1) CL).*2⌝
    .

Global Instance Queue_Timeless γq xs : Timeless (Queue γq xs).
Proof. apply _. Qed.

Definition node_info γcl p i_p x_p : iProp :=
  mono_list_idx_own γcl i_p (p, x_p).

Definition node_status p γcl i_p : iProp :=
  (* pending *)
  ( ∃ CL, ⌜i_p = length CL - 1⌝ ∗ (p +ₗ next) ↦ #NULL ∗ mono_list_auth_own γcl (1/2) CL ) ∨
  (* shot *)
  ( ∃ (n_p : loc) x_n_p, (p +ₗ next) ↦□ #n_p ∗ node_info γcl n_p (i_p + 1) x_n_p )
  .

Definition node γcl p i_p x_p : iProp :=
  (p +ₗ data) ↦□ x_p ∗
  node_info γcl p i_p x_p ∗
  node_status p γcl i_p
  .

Definition Nodes γcl CL : iProp :=
  [∗ list] i ↦ info ∈ CL, let '(p, x_p) := info in
    node γcl p i x_p.

Definition QueueInternalInv qu γcl γh : iProp :=
  ∃ CL
    (h : loc) ih (* current head (sentinel) node *)
    (t : loc) it (* node pointed to by the tail pointer *),
    (* nodes *)
    Nodes γcl CL ∗
    mono_list_auth_own γcl (1/2/2) CL ∗
    (* head pointer *)
    (qu +ₗ head) ↦ #h ∗
    mono_nat_auth_own γh (1/2) ih ∗
    (* tail pointer *)
    (qu +ₗ tail) ↦ #t ∗
    ⌜ fst <$> CL !! ih = Some h ∧
      fst <$> CL !! it = Some t ⌝.

Lemma get_node_info {γcl} i_p CL p x_p :
  CL !! i_p = Some (p,x_p) →
  Nodes γcl CL -∗
  ((p +ₗ data) ↦□ x_p ∗ node_info γcl p i_p x_p).
Proof.
  iIntros (Hi_p) "Nodes".
  unfold Nodes.
  iDestruct (big_sepL_lookup_acc with "Nodes") as "[node Nodes]"; [apply Hi_p|]. simpl.
  iDestruct "node" as "($&$&node)".
Qed.

(* Persistent assertions about the queue *)
Definition IsQueue (γq : gname) (qu : loc) : iProp :=
  ∃ γcl γh,
    ⌜γq = encode (γcl, γh)⌝ ∗
    inv queueN (QueueInternalInv qu γcl γh).

Global Instance nodes_timeless γcl p i_p x_p : Timeless (node γcl p i_p x_p).
Proof. apply _. Qed.

Global Instance Nodes_Timeless γcl CL : Timeless (Nodes γcl CL).
Proof. unfold Nodes. apply big_sepL_timeless. intros? []. apply _. Qed.

Global Instance IsQueue_Persistent γq qu : Persistent (IsQueue γq qu).
Proof. apply _. Qed.

Lemma Nodes_access {γcl} i_p CL p x_p :
  CL !! i_p = Some (p,x_p) →
  Nodes γcl CL -∗
  node γcl p i_p x_p ∗ (node γcl p i_p x_p -∗ Nodes γcl CL).
Proof.
  iIntros (Hi_p) "Nodes". unfold Nodes.
  iDestruct (big_sepL_lookup_acc with "Nodes") as "[node Nodes]"; [apply Hi_p|]. simpl.
  iFrame "∗#%".
Qed.

Lemma Nodes_insert {γcl} CL i_p p x_p :
  i_p = length CL →
  Nodes γcl CL -∗
  node γcl p i_p x_p -∗
  Nodes γcl (CL ++ [(p,x_p)]).
Proof.
  iIntros (->) "??". unfold Nodes. iApply big_sepL_snoc. by iFrame.
Qed.

Lemma node_case {γcl} p i_p x_p :
  node γcl p i_p x_p -∗
  (* pending *)
  ( ∃ CL, ⌜i_p = length CL - 1⌝ ∗
      (p +ₗ next) ↦ #NULL ∗
      mono_list_auth_own γcl (1/2) CL ∗
      ( (* read *)
        mono_list_auth_own γcl (1/2) CL -∗ (p +ₗ next) ↦ #NULL -∗
        node γcl p i_p x_p ) ∧
      ( (* shot *)
        ∀ (n_p : loc) x_n_p,
        (p +ₗ next) ↦□ #n_p -∗
        node_info γcl n_p (i_p + 1) x_n_p -∗
        node γcl p i_p x_p ) ) ∨
  (* shot *)
  ( ∃ (n_p : loc) x_n_p,
      (p +ₗ next) ↦□ #n_p ∗
      node_info γcl n_p (i_p + 1) x_n_p ∗
      node γcl p i_p x_p)
  .
Proof.
  iDestruct 1 as "(#p.d↦ & #Info_p & St_p)".
  iDestruct "St_p" as "[St_p|St_p]".
  - iDestruct "St_p" as (? ->) "(p.n↦ & ●CL_T)". iLeft.
    iExists CL. iSplit; [done|]. iFrame "●CL_T p.n↦". iSplit.
    + iIntros. iFrame "∗#%". iLeft. iExists CL. iFrame. done.
    + iIntros. iFrame "∗#%".
  - iDestruct "St_p" as (n_p x_n_p) "#[p.n↦ Info_n_p]".
    do 2 (iRight; iExists _,_; iFrame "#").
Qed.

Lemma queue_new_spec :
  queue_new_spec' queueN queue_new Queue IsQueue.
Proof.
  iIntros (Φ _) "HΦ".
  wp_lam. wp_alloc s as "s↦" "†s". wp_pures.
  iEval (rewrite array_cons array_singleton) in "s↦". iDestruct "s↦" as "[s.x↦ s.n↦]".
  iMod (pointsto_persist with "s.x↦") as "#s.x↦".
  wp_store. wp_alloc qu as "qu↦" "†qu"; wp_pures.
  repeat (wp_apply (wp_store_offset with "qu↦") as "qu↦"; [by simplify_list_eq|]; wp_pures).
  iEval (rewrite !array_cons !Loc.add_assoc //) in "qu↦".
  iDestruct "qu↦" as "(qu.h↦ & qu.t↦ & _)".
  iMod (mono_list_own_alloc [(Loc.blk_to_loc s,#0)]) as (γcl) "[[●CL_T ●CL] #◯CL]".
  iDestruct (mono_list_idx_own_get 0 with "◯CL") as "Info_s"; [done|].
  iAssert (node_status _ _ _) with "[●CL_T s.n↦]" as "Gt_s".
  { iLeft. iExists _. iFrame. done. }
  iDestruct "●CL" as "[●CL_I ●CL_Q]".
  iMod (mono_nat_own_alloc 0) as (γh) "[[●ih_I ●ih_Q] _]".
  remember (encode (γcl, γh)) as γq eqn:Hγq.
  iAssert (Queue γq []) with "[●CL_Q ●ih_Q]" as "Q".
  { repeat iExists _. iFrame "∗%". done. }
  iMod (inv_alloc queueN _ (QueueInternalInv qu _ _) with "[-HΦ Q]") as "#Inv".
  { iNext. iFrame. iExists 0. iFrame "∗#%". by iSplit. }
  iAssert (IsQueue _ _) as "IQ".
  { iFrame "#%". }
  iApply ("HΦ" with "[$IQ $Q]").
Qed.

Lemma try_advance_tail_spec qu γcl γh (t n : loc) i_t (x_n : val) :
  {{{ inv queueN (QueueInternalInv qu γcl γh) ∗
      mono_list_idx_own γcl (i_t + 1) (n, x_n) }}}
    CAS #(qu +ₗ tail) #t #n
  {{{ b, RET b; True }}}.
Proof.
  iIntros (Φ) "[#Inv #Info_n] HΦ".
  wp_bind (CmpXchg _ _ _).
  iInv "Inv" as (CL1 h1 ih1 t1 it1)
              ">(Nodes & ●CL_I & qu.h↦ & ●ih_I & qu.t↦ & %F)".

  case (decide (t = t1)) as [->|NE_t1]; last first.
  {  wp_cmpxchg_fail.
    (* close internal inv *) iModIntro.
    iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ Nodes".
    { repeat iExists _. iFrame "∗#%". }
    wp_pure. by iApply "HΦ". }
  iDestruct (mono_list_auth_idx_lookup with "●CL_I Info_n") as %?%(f_equal (fmap fst)).
  wp_cmpxchg_suc.
  (* close internal inv *) iModIntro.
  iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ Nodes".
  { repeat iExists _. iFrame "∗#%". iPureIntro. naive_solver. }
  wp_pure. by iApply "HΦ".
Qed.

Lemma find_tail_spec qu γcl γh :
  {{{ inv queueN (QueueInternalInv qu γcl γh) }}}
    find_tail #qu
  {{{ x_t i_t (t : loc), RET #t; mono_list_idx_own γcl i_t (t,x_t) }}}.
Proof using All.
  iIntros (Φ) "#Inv HΦ". iLöb as "IH".
  wp_lam. wp_pures.

  (* get protected pointer from tail pointer *)
  wp_bind (! _)%E.
  iInv "Inv" as (CL1 h1 ih1 t1 it1)
              ">(Nodes & ●CL_I & qu.h↦ & ●ih_I & qu.t↦ & %F1)".
  (* Access the node pointed by the tail pointer *)
  specialize F1 as F.
  destruct F as [_ F]. rewrite -list_lookup_fmap in F. apply list_lookup_fmap_inv in F as [[??][[= <-] ?]].

  iDestruct (get_node_info it1 with "Nodes") as "[#t1.d↦ #Info_t1]"; [done|].
  wp_load.
  (* close internal inv *) iModIntro.
  iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ Nodes".
  { repeat iExists _. iFrame "∗#%". }

  wp_pures.

  wp_bind (! _)%E.
  iInv "Inv" as (CL2 h2 ih2 t2 it2)
              ">(Nodes & ●CL_I & qu.h↦ & ●ih_I & qu.t↦ & %F2)".
  iDestruct (mono_list_auth_idx_lookup with "●CL_I Info_t1") as %HCL2it1.
  iDestruct (Nodes_access it1 with "Nodes") as "[N_t1 Nodes]"; [done|].
  (* It this node actual tail? *)
  iDestruct (node_case with "N_t1") as "[CASE|CASE]".
  { (* actual tail *)
    iDestruct "CASE" as (? ->) "(t1.n↦ & ●CL_T & N_t1 & _)".
    wp_load.
    iSpecialize ("N_t1" with "●CL_T t1.n↦").
    iSpecialize ("Nodes" with "N_t1").
    iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ Nodes".
    { repeat iExists _. iFrame "∗#%". }
    wp_pures. by iApply ("HΦ" with "[$Info_t1]"). }

  (* Not tail *)
  iDestruct "CASE" as (n_t1 x_n_t1) "(#t1.n↦ & #Info_n_t1 & N_t1)".
  wp_load.
  iSpecialize ("Nodes" with "N_t1").
  iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ Nodes". { repeat iExists _. iFrame "∗#%". }
  wp_pures.

  (* Try advancing the tail *)
  wp_apply (try_advance_tail_spec) as (?) "_"; [iFrame "∗#%"|].
  wp_seq. iApply ("IH" with "HΦ").
Qed.

Lemma queue_push_spec :
  queue_push_spec' queueN queue_push Queue IsQueue.
Proof using All.
  iIntros (γq qu x).
  iDestruct 1 as (?? Hγq) "#Inv".
  iIntros (Φ) "AU".

  wp_lam. wp_alloc n as "n↦" "†n". iClear "†n". wp_pures.
  repeat (wp_apply (wp_store_offset with "n↦") as "n↦"; [by simplify_list_eq|]; wp_pures).

  (* start push loop *)
  iLöb as "IH".
  wp_rec. wp_pures.

  wp_apply (find_tail_spec with "Inv") as (x_t i_t t) "#Idx_t".
  wp_let. wp_op.

  (* Try [next] field CAS. Is this node the actual tail? *)
  wp_bind (CmpXchg _ _ _).
  iInv "Inv" as (CL1 h1 ih1 t1 it1)
              ">(Nodes & ●CL_I & qu.h↦ & ●ih_I & qu.t↦ & %F1)".
  iDestruct (mono_list_auth_idx_lookup with "●CL_I Idx_t") as %Hit.
  iDestruct (Nodes_access i_t with "[$Nodes]") as "[N_h1 Nodes]"; [apply Hit|].

  iDestruct (node_case with "N_h1") as "[CASE|CASE]"; last first.
  { (* not tail; CAS failure *)
    iDestruct "CASE" as (n_t x_n_t) "(#t.n↦ & #Info_n_t & N_t)". simpl.
    wp_cmpxchg_fail.
    iModIntro. iSplitR "AU n↦". { repeat iExists _. iFrame "∗#%". iApply ("Nodes" with "N_t"). }
    wp_pure. wp_if. iApply ("IH" with "AU n↦"). }

  (* [t] is the actual tail. *)
  iDestruct "CASE" as (? Hi_t) "[t.n↦ [●CL_T N_t]]". simpl.
  iMod "AU" as (xs) "[Q [_ Commit]]".
  iDestruct "Q" as (????) "(% & ●CL_Q & ●ih_Q & %)".
  encode_agree Hγq.
  (* agree *)
  iDestruct (mono_list_auth_own_agree with "●CL_I ●CL_Q") as %[_ <-].
  iDestruct (mono_list_auth_own_agree with "●CL_I ●CL_T") as %[_ <-].
  iDestruct (mono_nat_auth_own_agree with "●ih_I ●ih_Q") as %[_ <-].
  (* snapshots *)
  iDestruct (mono_list_lb_own_get with "●CL_I") as "#◯CL1".
  (* updates *)
  iCombine "●CL_T ●CL_I ●CL_Q" as "●CL".

  iMod (mono_list_auth_own_update_app [(Loc.blk_to_loc n,x)] with "●CL") as "[[●CL_T ●CL] #◯CL1']".
  set (CL1' := CL1 ++ [(Loc.blk_to_loc n, x)]) in *.
  have Hit1' : CL1' !! (i_t + 1) = Some (Loc.blk_to_loc n, x).
  { subst CL1' i_t. destruct F1 as (_ & ?%lookup_fmap_lt_Some). (* [length CL > 0] *)
    rewrite lookup_app_r; [|lia].
    by replace (length CL1 - 1 + 1 - length CL1) with 0 by lia. }
  (* required for advancing the tail pointer *)
  iDestruct (mono_list_idx_own_get _ _ Hit1' with "◯CL1'") as "Info_n".
  iEval (rewrite array_cons array_singleton) in "n↦". iDestruct "n↦" as "[n.x↦ n.n↦]".
  iMod (pointsto_persist with "n.x↦") as "#n.x↦".
  (* register the enqueued node *)
  iAssert (node γcl n _ _) with "[●CL_T n.n↦]" as "N_n".
  { unfold node. rewrite !Loc.add_0. iFrame "∗#%". iLeft.
    iExists _. iFrame "●CL_T n.n↦". iPureIntro.
    rewrite length_app /=.
    apply lookup_lt_Some in Hit. (* [length CL1 > 0] *) lia. }
  iDestruct "●CL" as "[●CL_I ●CL_Q]".

  wp_cmpxchg_suc. iMod (pointsto_persist with "t.n↦") as "#t.n↦".
  (* commit *)
  iMod ("Commit" with "[●CL_Q ●ih_Q]") as "HΦ".
  { repeat iExists _. iFrame "∗#%". iPureIntro.
    subst xs CL1'. rewrite !fmap_drop fmap_app /=.
    rewrite drop_app_le //. rewrite length_fmap.
    destruct F1 as [?%lookup_fmap_lt_Some _]. lia. }
  iModIntro. iModIntro.
  iSpecialize ("N_t" with "t.n↦ Info_n"). iSpecialize ("Nodes" with "N_t").
  iDestruct (Nodes_insert _ (i_t+1) with "Nodes N_n") as "Nodes".
  { apply lookup_lt_Some in Hit. (* [length CL1 > 0] *) lia. }
  (* close internal inv *)
  iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ Nodes".
  { repeat iExists _. iFrame "∗#%". iPureIntro.
    destruct F1 as (Hih1 & Hit1). split_and!.
    - eapply prefix_lookup_fmap; [done|by eexists].
    - eapply prefix_lookup_fmap; [done|by eexists].
  }

  wp_pures.

  (* Try advancing the tail *)
  wp_apply (try_advance_tail_spec with "[$Inv $Info_n]") as (?) "_".

  wp_pures. by iApply "HΦ".
Qed.

Lemma queue_pop_spec :
  queue_pop_spec' queueN queue_pop Queue IsQueue.
Proof using All.
  iIntros (γq qu).
  iDestruct 1 as (?? Hγq) "#Inv".
  iIntros (Φ) "AU".

  iLöb as "IH".
  wp_rec. wp_pures.

  wp_bind (! _)%E.
  iInv "Inv" as (CL1 h1 ih1 t1 it1)
                ">(Nodes & ●CL_I & qu.h↦ & ●ih_I & qu.t↦ & %F1)".
  specialize F1 as F.
  destruct F as [F _]. rewrite -list_lookup_fmap in F. apply list_lookup_fmap_inv in F as [[??][[= <-] ?]].
  iDestruct (get_node_info ih1 with "Nodes") as "#(_ & Idx_h1)"; [done|].
  iDestruct (mono_nat_lb_own_get with "●ih_I") as "#◯ih1".

  wp_load.
  iModIntro.
  iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ Nodes"; first by exfr.

  wp_pures.

  (* Read the head's next field. If it's null, commit empty pop. *)
  wp_bind (! _)%E.
  iInv "Inv" as (CL2 h2 ih2 t2 it2)
              ">(Nodes & ●CL_I & qu.h↦ & ●ih_I & qu.t↦ & %F2)".

  (* agree *)
  iDestruct (mono_nat_lb_own_valid with "●ih_I ◯ih1") as %[_ LE_ih12].

  iDestruct (mono_list_auth_idx_lookup with "●CL_I Idx_h1") as %CL2_ih1.
  iDestruct (Nodes_access ih1 with "Nodes") as "[N_h1 Nodes]"; [done|].
  (* Case analysis on the status of node [ih1]. *)
  iDestruct (node_case with "N_h1") as "[CASE|CASE]".
  { (* [head.next] is null (tail). Commit empty pop *)
    iDestruct "CASE" as (? Hi_t) "[t.n↦ [●CL_T N_t]]". simpl.
    iMod "AU" as (xs2) "[Q [_ Commit]]".
    iDestruct "Q" as (????) "(% & ●CL_Q & ●ih_Q & %)".
    encode_agree Hγq.
    (* agree *)
    iDestruct (mono_list_auth_own_agree with "●CL_I ●CL_Q") as %[_ <-].
    iDestruct (mono_list_auth_own_agree with "●CL_I ●CL_T") as %[_ <-].
    iDestruct (mono_nat_auth_own_agree with "●ih_I ●ih_Q") as %[_ <-].
    assert (ih1 = ih2) as ->; last clear LE_ih12.
    { destruct F2 as (?%lookup_fmap_lt_Some & _). lia. }
    assert (xs2 = []) as ->.
    { subst ih2 xs2.
      destruct F2 as (_ & ?%lookup_fmap_lt_Some).
      rewrite fmap_drop drop_ge //. rewrite length_fmap. lia. }
    (* Commit empty pop *)
    wp_load.
    iMod ("Commit" with "[●CL_Q ●ih_Q]") as "HΦ".
    { repeat iExists _. iFrame "∗#%". }
    iModIntro.
    iSpecialize ("N_t" with "●CL_T t.n↦").
    (* close internal inv *) iModIntro.
    iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ Nodes N_t"; first by exfr; iApply "Nodes".

    wp_pures.
    iApply "HΦ". }

  (* [head.next] is not null. *)
  iDestruct "CASE" as (n_h1 x_n_h1) "(#h1.n↦ & #Info_n_h1 & N_h1)".
  wp_load.
  iModIntro.
  iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ Nodes N_h1"; first by exfr; iApply "Nodes".

  wp_pures.

  (* Pop CAS *)
  wp_bind (CmpXchg _ _ _)%E.
  iInv "Inv" as (CL4 h4 ih4 t4 it4)
              ">(Nodes & ●CL_I & qu.h↦ & ●ih_I & qu.t↦ & %F4)".

  (* Has the head pointer changed? *)
  case (decide (h1 = h4)) as [->|NE_h14]; last first.
  { wp_cmpxchg_fail.
    (* close internal inv *) iModIntro.
    iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ Nodes".
    { repeat iExists _. iFrame "∗#%". }
    wp_pure. wp_if.
    wp_apply ("IH" with "AU"). }

  (* agree *)
  specialize F4 as F.
  destruct F as [F _]. rewrite -list_lookup_fmap in F. apply list_lookup_fmap_inv in F as [[??][[= <-] ?]].
  iDestruct (Nodes_access ih4 with "Nodes") as "[N_h4 Nodes]"; [done|].
  iDestruct (node_case with "N_h4") as "[CASE|CASE]".
  { iDestruct "CASE" as (? Hi_t) "[t.n↦ [●CL_T N_t]]". simpl.
    iDestruct (pointsto_agree with "h1.n↦ t.n↦") as %[= ?].
  }
  iDestruct "CASE" as (??) "(#h4.n↦ & #Info_n_h4 & N_h4)".
  iDestruct (pointsto_agree with "h1.n↦ h4.n↦") as %[= <-].

  (* lookup *)
  iDestruct (mono_list_auth_idx_lookup with "●CL_I Info_n_h4") as %Hih4'.

  wp_cmpxchg_suc.

  (* clean up *)
  iSpecialize ("Nodes" with "N_h4").

  (* access AU *)
  iMod "AU" as (xs4) "[Q [_ Commit]]".
  iDestruct "Q" as (????) "(% & ●CL_Q & ●ih_Q & %Hxs4)".
  encode_agree Hγq.
  (* agree *)
  iDestruct (mono_list_auth_own_agree with "●CL_I ●CL_Q") as %[_ <-].
  iDestruct (mono_nat_auth_own_agree with "●ih_I ●ih_Q") as %[_ <-].
  iDestruct (get_node_info (ih4 + 1) with "Nodes") as "#(n_h1.d↦ & _)"; [done|].

  (* abstract state *)
  rewrite (drop_S _ _ _ Hih4') -Nat.add_1_r fmap_cons /= in Hxs4.
  (* update *)
  iCombine ("●ih_I ●ih_Q") as "●ih".
  iMod (mono_nat_own_update (ih4+1) with "●ih") as "[[●ih_I ●ih_Q] _]"; [lia|].

  (* commit *)
  iMod ("Commit" with "[●CL_Q ●ih_Q]") as "HΦ".
  { subst xs4. repeat iExists _. by iFrame "∗#%". }
  (* close internal inv *) iModIntro.
  iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ Nodes".
  { repeat iExists _.
    iFrame "∗#%". iPureIntro. destruct_and! F4. split_and!.
    - by apply (f_equal (fmap fst)) in Hih4'.
    - done.
  }

  wp_pures.

  (* read tail pointer *)
  wp_bind (! _)%E.
  iInv "Inv" as (CL3 h3 ih3 t3 it3)
              ">(Nodes & ●CL_I & qu.h↦ & ●ih_I & qu.t↦ & %F3)".
  wp_load.
  iModIntro.
  iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ Nodes"; first by exfr.

  wp_pures.

  (* Try advancing the tail. *)
  wp_bind (if: _ then _ else _)%E.
  set (fix_tail := (if: #(bool_decide _) then _ else _)%E) in *.
  iAssert (
    {{{ True }}}
      fix_tail
    {{{ v, RET v; True }}}
  )%I as "HT_fix_tail".
  { subst fix_tail.
    iIntros (Φ') "!> _ HΦ'".
    case (decide (h4 = t3)) as [->|NE_ht].
    - rewrite bool_decide_eq_true_2; last done.
      wp_pures.
      wp_apply (try_advance_tail_spec with "[$Inv $Info_n_h1]") as (?) "_".
      by iApply "HΦ'".
    - rewrite bool_decide_eq_false_2; last congruence.
      wp_pures. by iApply "HΦ'".
  }

  wp_apply ("HT_fix_tail" with "[$]") as (v_clear) "_".
  wp_seq.
  iClear (fix_tail v_clear) "HT_fix_tail".

  wp_pures.

  (* Read data *)
  wp_load.

  wp_pures.

  subst xs4. iApply "HΦ".
Qed.

#[export] Typeclasses Opaque Queue IsQueue.

End dglm_queue.
