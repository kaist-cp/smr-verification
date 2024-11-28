From iris.algebra Require Import agree.
From iris.base_logic Require Import lib.mono_nat lib.invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr.base_logic Require Import lib.mono_list.
From smr Require Import helpers ebr.spec_rcu_simple ebr.spec_queue ebr.code_ms.

Set Printing Projections.

Local Open Scope nat_scope.

Class msG Σ := MSG {
  #[local] ms_inG :: inG Σ (agreeR natO);
  #[local] ms_mono_listG :: mono_listG (gname * blk * val) Σ;
  #[local] ms_mono_natG :: mono_natG Σ;
}.

Definition msΣ : gFunctors := #[GFunctor (agreeR natO); mono_listΣ (gname * blk *val); mono_natΣ].

Global Instance subG_msΣ {Σ} :
  subG msΣ Σ → msG Σ.
Proof. solve_inG. Qed.

Section ms_queue.
Context `{!heapGS Σ, !msG Σ}.
Notation iProp := (iProp Σ).
Context (queueN rcuN : namespace) (DISJN : rcuN ## queueN).

(* iExists + iFrame *)
Ltac exfr := repeat (repeat iExists _; iFrame "∗#%").

Variable (rcu : rcu_simple_spec Σ rcuN).

Implicit Types
  (γe γcl γh γt : gname)
  (CL : list (gname * blk * val))
  (ih it : nat).

(* Abstract state of the queue *)
Definition Queue (γq : gname) (xs : list val) : iProp :=
  ∃ γcl γh γt CL ih,
    ⌜γq = encode (γcl, γh, γt)⌝ ∗
    mono_list_auth_own γcl (1/2/2) CL ∗
    mono_nat_auth_own γh (1/2) ih ∗
    ⌜xs = (drop (ih + 1) CL).*2⌝
    .

Global Instance Queue_Timeless γq xs : Timeless (Queue γq xs).
Proof. apply _. Qed.

Notation node_idx γ_p i_p := (own γ_p (to_agree (i_p : nat))).

Definition node_info γcl p γ_p i_p x_p : iProp :=
  mono_list_idx_own γcl i_p (γ_p, p, x_p).

Definition node_status γcl i_p (on_p : option blk) : iProp :=
  (* pending *)
  ( ∃ CL, ⌜on_p = None ∧ i_p = length CL - 1⌝ ∗ mono_list_auth_own γcl (1/2) CL ) ∨
  (* shot *)
  ( ∃ n_p γ_n_p x_n_p, ⌜on_p = Some n_p⌝ ∗ node_idx γ_n_p (i_p + 1) ∗ node_info γcl n_p γ_n_p (i_p + 1) x_n_p )
  .

Definition node γcl p lv γ_p : iProp :=
  ∃ i_p x_p on_p,
    ⌜lv = [ x_p; #(oblk_to_lit on_p) ]⌝ ∗
    node_idx γ_p i_p ∗
    node_info γcl p γ_p i_p x_p ∗
    node_status γcl i_p on_p
    .

Definition Nodes γe γcl CL ih : iProp :=
  [∗ list] i ↦ info ∈ (drop ih CL).*1, let '(γ_p, p) := info in
    rcu.(Managed) γe p γ_p nodeSize (node γcl) ∗ node_idx γ_p (ih + i).

Definition QueueInternalInv qu γe γcl γh γt : iProp :=
  ∃ CL
    (h : blk) γ_h ih (* current head (sentinel) node *)
    (t : blk) γ_t it (* node pointed to by the tail pointer *),
    (* nodes *)
    Nodes γe γcl CL ih ∗
    mono_list_auth_own γcl (1/2/2) CL ∗
    (* head pointer *)
    (qu +ₗ head) ↦ #h ∗
    mono_nat_auth_own γh (1/2) ih ∗
    (* tail pointer *)
    (qu +ₗ tail) ↦ #t ∗
    mono_nat_auth_own γt 1 it ∗
    ⌜ fst <$> CL !! ih = Some (γ_h,h) ∧
      fst <$> CL !! it = Some (γ_t,t) ∧
      ih ≤ it ⌝.

Lemma get_head_info CL ih γ_h h γe γcl:
  fst <$> CL !! ih = Some (γ_h,h) →
  Nodes γe γcl CL ih -∗ node_idx γ_h ih.
Proof.
  iIntros (Hih) "Nodes". unfold Nodes.
  rewrite fmap_drop.
  iDestruct (big_sepL_lookup _ _ 0 (γ_h, h) with "Nodes") as "[_ #Idx_h]";
  try (rewrite lookup_drop list_lookup_fmap); rewrite Nat.add_0_r; done.
Qed.

Lemma get_tail_info CL ih it γ_t t γe γcl :
  ih ≤ it →
  fst <$> CL !! it = Some (γ_t,t) →
  Nodes γe γcl CL ih -∗ node_idx γ_t it.
Proof.
  iIntros (LE Hit) "Nodes". unfold Nodes.
  rewrite fmap_drop.
  have EQ:(ih + (it - ih) = it) by lia.
  iDestruct (big_sepL_lookup _ _ (it - ih) (γ_t, t) with "Nodes") as "[_ #Idx_t]".
  - rewrite lookup_drop list_lookup_fmap EQ. done.
  - rewrite EQ. done.
Qed.

(* Persistent assertions about the queue *)
Definition IsQueue (γe : gname) (γq : gname) (qu : loc) : iProp :=
  ∃ (d : loc) γcl γh γt,
    ⌜γq = encode (γcl, γh, γt)⌝ ∗
    (qu +ₗ domain) ↦□ #d ∗ rcu.(IsRCUDomain) γe d ∗
    inv queueN (QueueInternalInv qu γe γcl γh γt).

Global Instance IsQueue_Persistent γe γq qu : Persistent (IsQueue γe γq qu).
Proof. apply _. Qed.

Lemma node_idx_agree γ_p i_p1 i_p2 :
  node_idx γ_p i_p1 -∗ node_idx γ_p i_p2 -∗ ⌜i_p1 = i_p2⌝.
Proof.
  iIntros "Idx1 Idx2".
  by iCombine "Idx1 Idx2" gives %<-%to_agree_op_inv_L.
Qed.

Lemma Nodes_access {γe γcl} CL ih i_p γ_p p :
  ih ≤ i_p →
  fst <$> CL !! i_p = Some (γ_p, p) →
  Nodes γe γcl CL ih -∗
  rcu.(Managed) γe p γ_p nodeSize (node γcl) ∗ node_idx γ_p i_p ∗
  (rcu.(Managed) γe p γ_p nodeSize (node γcl) -∗ Nodes γe γcl CL ih).
Proof.
  iIntros (Hihi_p Hi_p) "Nodes".
  rewrite -list_lookup_fmap in Hi_p.
  unfold Nodes. rewrite fmap_drop.
  have EQ : ih + (i_p - ih) = i_p by lia.
  have Hi_p' : drop ih CL.*1 !! (i_p - ih) = Some (γ_p,p) by rewrite lookup_drop EQ.
  iDestruct (big_sepL_lookup_acc _ _ _ _ Hi_p' with "Nodes") as "[[? #?] Nodes]".
  rewrite EQ. iFrame "∗#". iIntros. iApply "Nodes". iFrame "∗#".
Qed.

Lemma Nodes_insert {γe γcl} CL ih i_p γ_p p x_p :
  ih ≤ i_p →
  i_p = length CL →
  Nodes γe γcl CL ih -∗
  rcu.(Managed) γe p γ_p nodeSize (node γcl) -∗
  node_idx γ_p i_p -∗
  Nodes γe γcl (CL ++ [(γ_p,p,x_p)]) ih.
Proof.
  iIntros (? ->) "Nodes G_p Idx_p".
  unfold Nodes. rewrite !fmap_drop fmap_app /=.
  rewrite drop_app_le; last by rewrite length_fmap.
  iApply big_sepL_snoc. iFrame "Nodes".
  rewrite length_drop length_fmap.
  replace (ih + (length CL - ih)) with (length CL) by lia. iFrame.
Qed.

Lemma guard_Nodes_agree {γe γcl} CL ih i_p1 i_p2 γ_p1 γ_p2 p g γg :
  ih ≤ i_p1 →
  fst <$> CL !! i_p1 = Some (γ_p1,p) →
  rcu.(NodeInfo) γe γg p γ_p2 nodeSize (node γcl) -∗
  rcu.(Guard) γe g (Activated γg) -∗
  node_idx γ_p2 i_p2 -∗
  Nodes γe γcl CL ih -∗
  ⌜γ_p1 = γ_p2 ∧ i_p1 = i_p2⌝.
Proof.
  iIntros (Hihi_p Hi_p1) "#Info_p2 G Idx_p2 Nodes".
  iDestruct (Nodes_access _ _ i_p1 with "Nodes") as "(Gl & Idx_p1 & Nodes)"; [done..|].
  iDestruct (rcu.(guard_managed_agree) with "Info_p2 G Gl") as %<-.
  by iDestruct (node_idx_agree with "Idx_p1 Idx_p2") as %<-.
Qed.

Lemma node_case {γcl} p lv γ_p i_p :
  node_idx γ_p i_p -∗ node γcl p lv γ_p -∗
  ∃ x_p on_p,
    ⌜lv =  [ x_p; #(oblk_to_lit on_p) ]⌝ ∗
    node_info γcl p γ_p i_p x_p ∗
    ( (* pending *)
      ( ∃ CL, ⌜on_p = None ∧ i_p = length CL - 1⌝ ∗
          mono_list_auth_own γcl (1/2) CL ∗
          ( (* read *)
            ( mono_list_auth_own γcl (1/2) CL -∗
              node γcl p [x_p; #(oblk_to_lit on_p)] γ_p ) ∧
            (* shot *)
            ( ∀ (n_p : blk) γ_n_p x_n_p,
                node_idx γ_n_p (i_p + 1) -∗
                node_info γcl n_p γ_n_p (i_p + 1) x_n_p -∗
                node γcl p [x_p; #n_p] γ_p) ) ) ∨
      (* shot *)
      ( ∃ n_p γ_n_p x_n_p, ⌜on_p = Some n_p⌝ ∗
          node_idx γ_n_p (i_p + 1) ∗
          node_info γcl n_p γ_n_p (i_p + 1) x_n_p ∗
          node γcl p lv γ_p) ).
Proof.
  iIntros "Idx_p".
  iDestruct 1 as (? x_p on_p ->) "(#Idx_p' & #Info_p & Gt_p)".
  iDestruct (node_idx_agree with "Idx_p Idx_p'") as %<-. iClear "Idx_p'".
  iExists x_p, on_p. iSplit; [done|]. iFrame "Info_p".
  iDestruct "Gt_p" as "[Gt_p|Gt_p]".
  - iDestruct "Gt_p" as (? [-> ?]) "●CL_T". simpl. iLeft.
    iExists CL. iSplit; [done|]. iFrame "●CL_T". iSplit.
    + iIntros. iExists i_p, x_p, None. iFrame "∗#%". iSplit; [done|]. iLeft. iExists CL. iFrame. done.
    + iIntros. iExists i_p, x_p, (Some n_p). iFrame "∗#%". iSplit; [done|]. iRight. done.
  - iDestruct "Gt_p" as (n_p γ_n_p x_n_p ->) "#[Idx_n_p Info_n_p]". simpl. iRight.
    iExists _,_,_. iSplit; [done|]. iFrame "#".
    iExists (Some n_p). iFrame "∗#". iSplit; [done|]. iRight. done.
Qed.

Lemma queue_new_spec :
  queue_new_spec' queueN rcuN queue_new rcu Queue IsQueue.
Proof.
  iIntros (γe d Φ) "!> #IED HΦ".
  wp_lam. wp_alloc s as "s↦" "†s". wp_pures.
  wp_apply (wp_store_offset with "s↦") as "s↦"; [by simplify_list_eq|]; wp_pures.
  wp_alloc qu as "qu↦" "†qu"; wp_pures.
  repeat (wp_apply (wp_store_offset with "qu↦") as "qu↦"; [by simplify_list_eq|]; wp_pures).
  iEval (rewrite !array_cons !Loc.add_assoc //) in "qu↦".
  iDestruct "qu↦" as "(qu.h↦ & qu.t↦ & qu.d↦ & _)".
  iMod (pointsto_persist with "qu.d↦") as "#qu.d↦".
  iMod (own_alloc (to_agree 0)) as (γ_s) "#Idx_s"; [done|].
  iMod (mono_list_own_alloc [(γ_s,s,#0)]) as (γcl) "[[●CL_T ●CL] #◯CL]".
  iDestruct (mono_list_idx_own_get 0 with "◯CL") as "Info_s"; [done|].
  iAssert (node_status _ 0 None) with "[●CL_T]" as "Gt_s"; first by (iLeft; exfr).
  iMod (rcu.(rcu_domain_register) (node γcl) with "IED [$s↦ $†s Gt_s]") as "G_s"; [solve_ndisj|by exfr|].
  iDestruct "●CL" as "[●CL_I ●CL_Q]".
  iMod (mono_nat_own_alloc 0) as (γh) "[[●ih_I ●ih_Q] _]".
  iMod (mono_nat_own_alloc 0) as (γt) "[●it _]".
  remember (encode (γcl, γh, γt)) as γq eqn:Hγq.
  iAssert (Queue γq []) with "[●CL_Q ●ih_Q]" as "Q"; first by exfr.
  iMod (inv_alloc queueN _ (QueueInternalInv qu _ _ γh γt) with "[-HΦ Q]") as "#Inv".
  { iNext. repeat iExists _. iFrame "∗#". simpl. iFrame. done. }
  iAssert (IsQueue _ _ _) as "IQ"; first by exfr.
  iApply ("HΦ" with "[$IQ $Q]").
Qed.

Lemma try_advance_tail_spec qu γe γcl γh γt g γg t γ_t i_t x_t n γ_n x_n :
  {{{ inv queueN (QueueInternalInv qu γe γcl γh γt) ∗
      rcu.(NodeInfo) γe γg t γ_t nodeSize (node γcl) ∗
      rcu.(Guard) γe g (Activated γg) ∗
      node_idx γ_t i_t ∗
      node_info γcl t γ_t i_t x_t ∗
      node_idx γ_n (i_t+1) ∗
      node_info γcl n γ_n (i_t+1) x_n ∗
      mono_nat_lb_own γt i_t }}}
    CAS #(qu +ₗ tail) #t #n
  {{{ b, RET b;
      rcu.(Guard) γe g (Activated γg) ∗
      mono_nat_lb_own γt (i_t+1) }}}.
Proof.
  iIntros (Φ) "(#Inv & #tInfo & G & #Idx_t & #Info_t & #Idx_n & #Info_n & #◯it) HΦ".
  wp_bind (CmpXchg _ _ _).
  iInv "Inv" as (CL1 h1 γ_h1 ih1 t1 γ_t1 it1)
              "[Nodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F1)]".

  case (decide (t = t1)) as [->|NE_t1]; last first.
  { (* Someone else advanced the tail already. *)
    iDestruct (mono_nat_lb_own_valid with "●it ◯it") as %[_ LE_it1].
    iDestruct (mono_list_auth_idx_lookup with "●CL_I Info_t") as %Hit.
    have NE_it1 : i_t ≠ it1.
    { intros ->. destruct F1 as (_ & Hit1 & _).
      apply (f_equal (fmap fst)) in Hit. simpl in Hit. simplify_eq. }
    have {LE_it1 NE_it1} LT_it1 : i_t + 1 ≤ it1 by lia.
    iDestruct (mono_nat_lb_own_get with "●it") as "#◯it1".
    iDestruct (mono_nat_lb_own_le _ LT_it1 with "◯it1") as "#◯it'".
    wp_cmpxchg_fail.
    (* close internal inv *)
    iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes"; first by exfr.
    wp_pure. by iApply ("HΦ" with "[$G $◯it']"). }

  (* I update the tail pointer *)
  (* Agree *)
  iDestruct (guard_Nodes_agree with "tInfo G Idx_t Nodes") as "#>[<- <-]"; [by destruct_and! F1..|].
  iDestruct (mono_list_auth_idx_lookup with "●CL_I Info_n") as %Hit1'.
  wp_cmpxchg_suc.
  iMod (mono_nat_own_update (it1+1) with "●it") as "[●it #◯it1']"; [lia|].
  (* close inv *)
  iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes".
  { repeat iExists _. iFrame "∗#%". iPureIntro.
    destruct_and!. split_and!; [done| |lia].
    by apply (f_equal (fmap fst)) in Hit1'. }
  iSpecialize ("HΦ" with "[G]"); first by iFrame "∗#".
  wp_pure. iApply "HΦ".
Qed.

Lemma find_tail_spec qu γe γcl γh γt (d : loc) g γg :
  {{{ (qu +ₗ domain) ↦□ #d ∗ rcu.(IsRCUDomain) γe d ∗
      inv queueN (QueueInternalInv qu γe γcl γh γt) ∗
      rcu.(Guard) γe g (Activated γg) }}}
    find_tail #qu
  {{{ γ_t i_t (t : blk), RET #t;
      rcu.(Guard) γe g (Activated γg) ∗
      rcu.(NodeInfo) γe γg t γ_t nodeSize (node γcl) ∗
      node_idx γ_t i_t ∗
      mono_nat_lb_own γt i_t }}}.
Proof using All.
  iIntros (Φ) "(#qu.d↦ & #IED & #Inv & G) HΦ". iLöb as "IH".
  wp_lam. wp_pures. wp_bind (! _)%E.

  (* get protected pointer from tail pointer *)
  iInv "Inv" as (CL1 h1 γ_h1 ih1 t1 γ_t1 it1)
              "[Nodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F1)]".
  iDestruct (get_tail_info with "Nodes") as "#Idx_t1"; [by destruct_and! F1..| ].
  (* snapshots *)
  iDestruct (mono_nat_lb_own_get with "●it") as "#◯it1".
  (* Access the node pointed by the tail pointer *)
  iDestruct (Nodes_access _ _ it1 with "Nodes") as "(G_t1 & _ & Nodes)"; [by destruct_and! F1..|].
  wp_load.
  iMod (rcu.(guard_protect) with "IED G_t1 G") as "(G_t1 & G & #t1Info)"; [solve_ndisj|].
  iSpecialize ("Nodes" with "G_t1").
  (* close internal inv *)
  iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes"; first by exfr.

  wp_pures. wp_bind (! _)%E.
  iInv "t1Info" as (lv) "(_ & t1↦ & >N_t1 & G)".
  (* It this node actual tail? *)
  iDestruct (node_case with "Idx_t1 N_t1") as (x_t1 on_t1 ->) "(#Info_t1 & [CASE|CASE])".
  all: wp_apply (wp_load_offset with "t1↦") as "t1↦"; [by simplify_list_eq|].
  { (* actual tail *)
    iDestruct "CASE" as (? [-> ?]) "[●CL_T [N_t1 _]]".
    iSpecialize ("N_t1" with "●CL_T").
    iModIntro. iSplitL "t1↦ N_t1". { iExists ([_;_]). by iFrame. }
    wp_pures. by iApply ("HΦ" with "[$G $Idx_t1 $◯it1 $t1Info]"). }

  (* Not tail *)
  iDestruct "CASE" as (n_t1 γ_n_t1 x_n_t1 ->) "(#Idx_n_t1 & #Info_n_t1 & N_t1)".
  iModIntro. iSplitL "t1↦ N_t1". { iExists ([_;_]). by iFrame. }

  wp_pures.

  (* Try advancing the tail *)
  wp_apply (try_advance_tail_spec with "[$Inv $G $Idx_t1 $Info_t1 $Idx_n_t1 $Info_n_t1 $◯it1 $t1Info]") as (?) "[G _]".
  wp_seq. iApply ("IH" with "G HΦ").
Qed.


Lemma queue_push_spec :
  queue_push_spec' queueN rcuN (queue_push rcu) rcu Queue IsQueue.
Proof using All.
  iIntros (γe γq qu x g).
  iDestruct 1 as (???? Hγq) "#(qu.d↦ & IED & Inv)".
  iIntros "G" (Φ) "AU".

  wp_lam. wp_alloc n as "n↦" "†n". wp_pures.
  repeat (wp_apply (wp_store_offset with "n↦") as "n↦"; [by simplify_list_eq|]; wp_pures).
  wp_apply (rcu.(guard_activate_spec) with "IED G") as (?) "G"; [solve_ndisj|].
  wp_seq.

  (* start push loop *)
  iLöb as "IH".
  wp_rec. wp_pures.

  wp_apply (find_tail_spec with "[$qu.d↦ $IED $Inv $G]") as (γ_t i_t t) "(G & #tInfo & #Idx_t & #◯it)".
  wp_let. wp_op.

  (* Try [next] field CAS. Is this node the actual tail? *)
  wp_bind (CmpXchg _ _ _).
  iInv "tInfo" as (lv) "(_ & t↦ & >N_t & G)".
  iDestruct (node_case with "Idx_t N_t") as (x_t on_t ->) "(#Info_t & [CASE|CASE])"; last first.
  { (* not tail; CAS failure *)
    iDestruct "CASE" as (n_t γ_n_t x_n_t ->) "(#Idx_n_t & #Info_n_t & N_t)". simpl.
    wp_apply (wp_cmpxchg_fail_offset with "t↦") as "t↦"; [by simplify_list_eq|done|naive_solver|].
    iModIntro. iSplitL "t↦ N_t". { iExists ([_;_]). by iFrame. }
    wp_pure. wp_if. iApply ("IH" with "AU †n n↦ G"). }

  (* [t] is the actual tail. *)
  iDestruct "CASE" as (? [-> ?]) "[●CL_T [_ N_t]]". simpl.
  iInv "Inv" as (CL1 h1 γ_h1 ih1 t1 γ_t1 it1)
              "[Nodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F1)]".
  iMod "AU" as (xs) "[Q [_ Commit]]".
  iDestruct "Q" as (??????) "(●CL_Q & ●ih_Q & %)".
  encode_agree Hγq.
  (* agree *)
  iDestruct (mono_list_auth_own_agree with "●CL_I ●CL_Q") as %[_ <-].
  iDestruct (mono_list_auth_own_agree with "●CL_I ●CL_T") as %[_ <-].
  iDestruct (mono_nat_auth_own_agree with "●ih_I ●ih_Q") as %[_ <-].
  iDestruct (mono_nat_lb_own_valid with "●it ◯it") as %[_ LE_it1].
  iDestruct (mono_list_auth_idx_lookup with "●CL_I Info_t") as %Hit.
  (* snapshots *)
  iDestruct (mono_list_lb_own_get with "●CL_I") as "#◯CL1".
  (* [t = t1] because [i_t ≤ it1] and [i_t] is the actual tail. *)
  assert (i_t = it1) as ->.
  { subst i_t. destruct F1 as (_ & ?%lookup_fmap_lt_Some & _). (* [length CL1 > 0] *) lia. }
  assert (t = t1) as ->.
  { destruct_and!. apply (f_equal (fmap fst)) in Hit. simpl in Hit. congruence. }
  (* updates *)
  iCombine "●CL_T ●CL_I ●CL_Q" as "●CL".

  iMod (own_alloc (to_agree (it1+1))) as (γ_n) "#Idx_n"; [done|].
  iMod (mono_list_auth_own_update_app [(γ_n,n,x)] with "●CL") as "[[●CL_T ●CL] #◯CL1']".
  set (CL1' := CL1 ++ [(γ_n, n, x)]) in *.
  have Hit1' : CL1' !! (it1 + 1) = Some (γ_n, n, x).
  { subst CL1' it1. destruct F1 as (_ & ?%lookup_fmap_lt_Some & _). (* [length CL > 0] *)
    rewrite lookup_app_r; [|lia].
    by replace (length CL1 - 1 + 1 - length CL1) with 0 by lia. }
  (* required for advancing the tail pointer *)
  iDestruct (mono_list_idx_own_get _ _ Hit1' with "◯CL1'") as "Info_n".
  (* register the enqueued node *)
  iAssert (node γcl n _ γ_n) with "[●CL_T]" as "N_n".
  { iExists (it1+1), x, None. iSplit; [done|]. iFrame "Idx_n Info_n". iLeft.
    iExists _. iFrame "●CL_T". iPureIntro. split; [done|].
    rewrite length_app /=.
    apply lookup_lt_Some in Hit. (* [length CL1 > 0] *) lia. }
  iMod (rcu.(rcu_domain_register) (node γcl) with "IED [$n↦ $†n $N_n]") as "G_n"; [solve_ndisj|].

  iDestruct "●CL" as "[●CL_I ●CL_Q]".

  wp_apply (wp_cmpxchg_suc_offset with "t↦") as "t↦"; [by simplify_list_eq|done|naive_solver|].
  (* commit *)
  iMod ("Commit" with "[●CL_Q ●ih_Q]") as "HΦ".
  { repeat iExists _. iFrame "∗#%". iPureIntro.
    subst xs CL1'. rewrite !fmap_drop fmap_app /=.
    rewrite drop_app_le //. rewrite length_fmap.
    destruct F1 as [?%lookup_fmap_lt_Some _]. lia. }
  iModIntro. iModIntro.
  iDestruct (Nodes_insert _ _ (it1+1) with "Nodes G_n Idx_n") as "Nodes"; [lia| |].
  { apply lookup_lt_Some in Hit. (* [length CL1 > 0] *) lia. }
  (* close internal inv *)
  iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes".
  { repeat iExists _. iFrame "∗#%". iPureIntro.
    destruct F1 as (Hih1 & Hit1 & LE). split_and!;
    try (eapply prefix_lookup_fmap; [done|by eexists]); lia. }
  iSpecialize ("N_t" with "Idx_n Info_n").
  iModIntro. iSplitL "t↦ N_t". { iExists ([_;_]). by iFrame. }

  wp_pures.

  (* Try advancing the tail *)
  wp_apply (try_advance_tail_spec with "[$Inv $G $Idx_t $Info_t $Idx_n $Info_n $◯it $tInfo]") as (?) "[G _]".
  wp_pures. wp_apply (rcu.(guard_deactivate_spec) with "IED G"); [solve_ndisj|]. auto.
Qed.

Lemma queue_pop_spec :
  queue_pop_spec' queueN rcuN (queue_pop rcu) rcu Queue IsQueue.
Proof using All.
  iIntros (γe γq qu g).
  iDestruct 1 as (???? Hγq) "#(qu.d↦ & IED & Inv)".
  iIntros "G" (Φ) "AU".

  wp_lam. wp_pures.
  wp_apply (rcu.(guard_activate_spec) with "IED G") as (?) "G"; [solve_ndisj|].
  wp_seq.

  wp_bind ((queue_pop_loop rcu) _). iLöb as "IH".
  wp_rec. wp_pures. wp_bind (! _)%E.

  iInv "Inv" as (CL1 h1 γ_h1 ih1 t1 γ_t1 it1)
              "[Nodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F1)]".
  iDestruct (get_head_info with "Nodes") as "#Idx_h1"; [by destruct_and! F1|].
  iDestruct (Nodes_access _ _ ih1 with "Nodes") as "(G_h1 & _ & Nodes)"; [by destruct_and! F1..|].
  wp_load.
  iMod (rcu.(guard_protect) with "IED G_h1 G") as "(G_h1 & G & #h1Info)"; [solve_ndisj|].
  iDestruct (mono_list_lb_own_get with "●CL_I") as "#◯CL1".
  iDestruct (mono_nat_lb_own_get with "●ih_I") as "#◯ih1".
  iSpecialize ("Nodes" with "G_h1").
  iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes"; first by exfr.

  wp_pures. wp_bind (! _)%E.

  (* Read the head's next field. If it's null, commit empty pop. *)
  iInv "Inv" as (CL2 h2 γ_h2 ih2 t2 γ_t2 it2)
              "[Nodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F2)]".
  (* agree *)
  iDestruct (mono_list_auth_lb_valid with "●CL_I ◯CL1") as %[_ PF_CL12].
  iDestruct (mono_nat_lb_own_valid with "●ih_I ◯ih1") as %[_ LE_ih12].

  (* snapshots *)
  iDestruct (mono_nat_lb_own_get with "●ih_I") as "#◯ih2".
  iDestruct (mono_list_lb_own_get with "●CL_I") as "#◯CL2".
  (* Access the protected node *)
  iInv "h1Info" as (?) "(_ & h1↦ & >N_h1 & G)".
  (* Case analysis on the status of node [ih1]. *)
  iDestruct (node_case with "Idx_h1 N_h1") as (x_h1 on_h1 ->) "(#Info_h1 & [CASE|CASE])".
  { (* [head.next] is null (tail). Commit empty pop *)
    iDestruct "CASE" as (? [-> ?]) "[●CL_T [N_h1 _]]". simpl.
    iMod "AU" as (xs2) "[Q [_ Commit]]".
    iDestruct "Q" as (??????) "(●CL_Q & ●ih_Q & %Hxs2)".
    encode_agree Hγq.
    (* agree *)
    iDestruct (mono_list_auth_own_agree with "●CL_I ●CL_Q") as %[_ <-].
    iDestruct (mono_list_auth_own_agree with "●CL_I ●CL_T") as %[_ <-].
    iDestruct (mono_nat_auth_own_agree with "●ih_I ●ih_Q") as %[_ <-].
    assert (ih1 = ih2) as ->; last clear LE_ih12.
    { destruct F2 as (?%lookup_fmap_lt_Some & _). lia. }
    assert (CL1 = CL2) as ->; last clear PF_CL12.
    { subst ih2.
      destruct F1 as (?%lookup_fmap_lt_Some & _).
      destruct PF_CL12 as [L ->].
      rename select (_ < length CL1) into HL. clear -HL.
      rewrite length_app in HL.
      assert (length L = 0) as ->%nil_length_inv by lia.
      by rewrite app_nil_r. }
    assert (xs2 = []) as ->.
    { subst ih2 xs2.
      destruct F2 as (_ & ?%lookup_fmap_lt_Some & _).
      rewrite fmap_drop drop_ge //. rewrite length_fmap. lia. }
    (* Commit empty pop *)
    wp_apply (wp_load_offset with "h1↦") as "h1↦"; [by simplify_list_eq|].
    iMod ("Commit" with "[●CL_Q ●ih_Q]") as "HΦ"; first by exfr.
    do 2 iModIntro. iSpecialize ("N_h1" with "●CL_T"). iSplitL "h1↦ N_h1".
    { iExists ([_;_]). by iFrame. }
    iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes"; first by exfr.

    wp_pures. wp_apply (rcu.(guard_deactivate_spec) with "IED [G]") as "G"; [solve_ndisj|by simplify_map_eq|].
    wp_seq. iApply "HΦ". by iFrame. }

  (* [head.next] is not null. *)
  iDestruct "CASE" as (n_h1 γ_n_h1 x_n_h1 ->) "(#Idx_n_h1 & #Info_n_h1 & N_h1)". simpl.
  wp_apply (wp_load_offset with "h1↦") as "h1↦"; [by simplify_list_eq|].
  iModIntro. iSplitL "h1↦ N_h1". { iExists ([_;_]). by iFrame. }
  iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes"; first by exfr.

  wp_pures. wp_bind (! _)%E.

  (* read tail pointer *)
  iInv "Inv" as (CL3 h3 γ_h3 ih3 t3 γ_t3 it3)
              "[Nodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F3)]".
  (* agree *)
  iDestruct (mono_nat_lb_own_valid with "●ih_I ◯ih1") as %[_ LE_ih13].
  (* snapshots *)
  iDestruct (mono_nat_lb_own_get with "●ih_I") as "#◯ih3".
  iDestruct (mono_nat_lb_own_get with "●it") as "#◯it3".
  iDestruct (mono_nat_lb_own_valid with "●ih_I ◯ih2") as %[_ LE_ih23].
  iDestruct (mono_list_auth_lb_valid with "●CL_I ◯CL2") as %[_ PF_CL23].
  (* If the head guard and the tail pointer value are the same, they point to
  the same logical node. *)
  wp_load.
  iAssert ⌜h1 = t3 → ih1 = it3⌝%I as %Hih1it3.
  { iIntros (->). iDestruct (guard_Nodes_agree with "h1Info G Idx_h1 Nodes") as %[<- <-]; by destruct_and! F3. }

  (* close internal inv *)
  iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes"; first by exfr.

  wp_pures. wp_bind (if: _ then _ else _)%E.

  (* Try advancing the tail. *)
  set (fix_tail := (if: #(bool_decide _) then _ else _)%E) in *.
  iAssert (
    {{{ rcu.(Guard) γe g (Activated γg) }}}
      fix_tail
    {{{ v, RET v; rcu.(Guard) γe g (Activated γg) ∗ mono_nat_lb_own γt (ih1+1) }}}
  )%I as "HT_fix_tail".
  { subst fix_tail.
    iIntros (Φ') "!> G HΦ'".
    case (decide (h1 = t3)) as [->|NE_ht].
    - rewrite bool_decide_eq_true_2; last done.
      specialize (Hih1it3 eq_refl) as ->. (* [ih1 = it3] *)
      wp_pures.
      wp_apply (try_advance_tail_spec with "[$Inv $G $Idx_h1 $Info_h1 $Idx_n_h1 $Info_n_h1 $◯it3 $h1Info]") as (?) "[G #◯it3']".
      by iApply ("HΦ'" with "[$G $◯it3']").
    - rewrite bool_decide_eq_false_2; last naive_solver.
      wp_pures.
      destruct F3 as (? & ? & LE_ih3it3).
      have NE_ih1it3 : ih1 ≠ it3.
      { intros ->. destruct F1 as [Hh1 _].
        assert (CL1 `prefix_of` CL3) as PF_CL13. { by transitivity CL2. }
        have ? := prefix_lookup_fmap _ _ _ _ _ Hh1 PF_CL13.
        congruence. }
      have {LE_ih13 LE_ih3it3 NE_ih1it3}LE_ih1'it3 : ih1 + 1 ≤ it3 by lia.
      iDestruct (mono_nat_lb_own_le _ LE_ih1'it3 with "◯it3") as "#◯it_ih1'".
      iApply ("HΦ'" with "[$G $◯it_ih1']"). }

  wp_apply ("HT_fix_tail" with "G") as (v_clear) "[G #◯it_ih1']".
  wp_seq.
  iClear (fix_tail Hih1it3 v_clear) "HT_fix_tail".

  wp_pures. wp_bind (CmpXchg _ _ _)%E.

  (* Pop CAS *)
  iInv "Inv" as (CL4 h4 γ_h4 ih4 t4 γ_t4 it4)
              "[Nodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F4)]".

  (* Has the head pointer changed? *)
  case (decide (h1 = h4)) as [->|NE_h14]; last first.
  { wp_cmpxchg_fail.
    (* close internal inv *)
    iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes"; first by exfr.
    wp_pure. wp_if. wp_apply ("IH" with "AU G"). }

  (* protect next *)

  (* agree *)
  iDestruct (guard_Nodes_agree _ _ ih4 with "h1Info G Idx_h1 Nodes") as "#>[<- <-]"; [by destruct_and! F4..|].
  iClear "Idx_h1".
  iDestruct (mono_nat_lb_own_valid with "●it ◯it_ih1'") as %[_ LE_ih5it5].

  (* lookup *)
  iDestruct (mono_list_auth_idx_lookup with "●CL_I Info_n_h1") as %Hih4'.
  iDestruct (Nodes_access _ _ (ih4+1) with "Nodes") as "(G_n_h1 & ? & Nodes)";[lia|..].
  { apply (f_equal (fmap fst)) in Hih4'. by simplify_map_eq. }

  wp_cmpxchg_suc.

  iMod (rcu.(guard_protect) with "IED G_n_h1 G") as "(G_n_h1 & G & n_h1Info)"; [solve_ndisj|].

  (* clean up *)
  iSpecialize ("Nodes" with "G_n_h1").
  iClear "◯ih3".

  (* access AU *)
  iMod "AU" as (xs4) "[Q [_ Commit]]".
  iDestruct "Q" as (??????) "(●CL_Q & ●ih_Q & %Hxs4)".
  encode_agree Hγq.
  (* agree *)
  iDestruct (mono_list_auth_own_agree with "●CL_I ●CL_Q") as %[_ <-].
  iDestruct (mono_nat_auth_own_agree with "●ih_I ●ih_Q") as %[_ <-].
  iDestruct (mono_nat_lb_own_valid with "●it ◯it_ih1'") as %[_ LE_ih4'it4].
  iDestruct (mono_list_auth_lb_valid with "●CL_I ◯CL2") as %[_ PF_CL24].

  (* abstract state *)
  rewrite (drop_S _ _ _ Hih4') -Nat.add_1_r fmap_cons /= in Hxs4.
  (* update *)
  iCombine ("●ih_I ●ih_Q") as "●ih".
  iMod (mono_nat_own_update (ih4+1) with "●ih") as "[[●ih_I ●ih_Q] _]"; [lia|].
  (* unlinked: take managed from the inv *)
  iAssert (rcu.(Managed) γe h4 γ_h4 nodeSize (node γcl) ∗ Nodes γe γcl CL4 (ih4+1))%I
            with "[Nodes]" as "[G_h4 Nodes]".
  { unfold Nodes. destruct F4 as (Hih4 & ? & ?).
    rewrite !fmap_drop. rewrite -list_lookup_fmap in Hih4.
    rewrite (drop_S _ _ _ Hih4). rewrite big_sepL_cons.
    rewrite Nat.add_0_r. iDestruct "Nodes" as "[[$ _] Nodes]".
    iApply (big_sepL_mono' with "Nodes").
    - intros i ?. by replace (ih4 + S i) with (ih4 + 1 + i) by lia.
    - by rewrite -Nat.add_1_r. }
  (* commit *)
  iMod ("Commit" with "[●CL_Q ●ih_Q]") as "HΦ"; first by (subst xs4; exfr).
  (* close internal inv *)
  iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes".
  { repeat iExists _. iFrame "∗#%". iPureIntro. destruct_and! F4. split_and!;
    try done. by apply (f_equal (fmap fst)) in Hih4'. }

  wp_pures. wp_bind (! _)%E.

  (* Read data *)
  iInv "n_h1Info" as (lv) "(_ & n_h1↦ & >N_n_h1 & G)".
  iDestruct "N_n_h1" as (i_n_h1' x_n_h1' on_n_h1' ->) "(#Idx_n_h1' & #Info_n_h1' & Gt_n_h1)".
  iDestruct (node_idx_agree with "Idx_n_h1 Idx_n_h1'") as %<-.
  iDestruct (mono_list_idx_agree with "Info_n_h1 Info_n_h1'") as %[= <-].
  iClear "Idx_n_h1' Info_n_h1'".
  wp_apply (wp_load_offset with "n_h1↦") as "n_h1↦"; [by simplify_list_eq|].
  iAssert (node _ n_h1 _ _) with "[Gt_n_h1]" as "N_n_h1"; first by exfr.
  iModIntro. iSplitL "n_h1↦ N_n_h1". { iExists ([_;_]). by iFrame. }

  wp_pures. wp_load.
  wp_apply (rcu.(rcu_domain_retire_spec) with "IED G_h4") as "_"; [solve_ndisj|].
  wp_pures.
  wp_apply (rcu.(guard_deactivate_spec) with "IED G") as "G"; [solve_ndisj|].
  subst xs4.
  wp_pures. iApply "HΦ". by iFrame.
Qed.

#[export] Typeclasses Opaque Queue IsQueue.

End ms_queue.
