From iris.algebra Require Import agree.
From iris.base_logic Require Import lib.mono_nat lib.invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr.base_logic Require Import lib.mono_list.
From smr Require Import helpers hazptr.spec_hazptr hazptr.spec_queue hazptr.code_ms.

Set Printing Projections.

Local Open Scope nat_scope.

Class msG Σ := MSG {
  ms_inG :> inG Σ (agreeR natO);
  ms_mono_listG :> mono_listG (gname * blk * val) Σ;
  ms_mono_natG :> mono_natG Σ;
}.

Definition msΣ : gFunctors := #[GFunctor (agreeR natO); mono_listΣ (gname * blk * val); mono_natΣ].

Global Instance subG_msΣ {Σ} :
  subG msΣ Σ → msG Σ.
Proof. solve_inG. Qed.

Section ms_queue.
Context `{!heapGS Σ, !msG Σ}.
Notation iProp := (iProp Σ).
Context (queueN hazptrN : namespace) (DISJN : hazptrN ## queueN).

(* iExists + iFrame *)
Ltac exfr := repeat (repeat iExists _; iFrame "∗#%").

Variable (hazptr : hazard_pointer_spec Σ hazptrN).

Implicit Types
  (γz γcl γh γt : gname)
  (CL : list (gname * blk * val))
  (ih it : nat).

(* Abstract state of the queue *)
Definition Queue (γq : gname) (xs : list val) : iProp :=
  ∃ γz γcl γh γt CL ih,
    ⌜γq = encode (γz, γcl, γh, γt)⌝ ∗
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

Definition Nodes γz γcl CL ih : iProp :=
  [∗ list] i ↦ info ∈ (drop ih CL).*1, let '(γ_p, p) := info in
    hazptr.(Managed) γz p γ_p nodeSize (node γcl) ∗ node_idx γ_p (ih + i).

Definition QueueInternalInv qu γz γcl γh γt : iProp :=
  ∃ CL
    (h : blk) γ_h ih (* current head (sentinel) node *)
    (t : blk) γ_t it (* node pointed to by the tail pointer *),
    (* nodes *)
    Nodes γz γcl CL ih ∗
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

Lemma get_head_info CL ih γ_h h γz γcl :
  fst <$> CL !! ih = Some (γ_h,h) →
  Nodes γz γcl CL ih -∗ node_idx γ_h ih.
Proof.
  iIntros (Hih) "Nodes". unfold Nodes.
  rewrite fmap_drop.
  iDestruct (big_sepL_lookup _ _ 0 (γ_h, h) with "Nodes") as "[_ #Idx_h]";
  try (rewrite lookup_drop list_lookup_fmap); rewrite Nat.add_0_r; done.
Qed.

Lemma get_tail_info CL ih it γ_t t γz γcl :
  ih ≤ it →
  fst <$> CL !! it = Some (γ_t,t) →
  Nodes γz γcl  CL ih -∗ node_idx γ_t it.
Proof.
  iIntros (LE Hit) "Nodes". unfold Nodes.
  rewrite fmap_drop.
  have EQ:(ih + (it - ih) = it) by lia.
  iDestruct (big_sepL_lookup _ _ (it - ih) (γ_t, t) with "Nodes") as "[_ #Idx_t]".
  - rewrite lookup_drop list_lookup_fmap EQ. done.
  - rewrite EQ. done.
Qed.

(* Persistent assertions about the queue *)
Definition IsQueue (γq : gname) (qu : loc) : iProp :=
  ∃ (d : loc) γz γcl γh γt,
    ⌜γq = encode (γz, γcl, γh, γt)⌝ ∗
    (qu +ₗ domain) ↦□ #d ∗ hazptr.(IsHazardDomain) γz d ∗
    inv queueN (QueueInternalInv qu γz γcl γh γt).

Global Instance IsQueue_Persistent γq qu : Persistent (IsQueue γq qu).
Proof. apply _. Qed.

Lemma node_idx_agree γ_p i_p1 i_p2 :
  node_idx γ_p i_p1 -∗ node_idx γ_p i_p2 -∗ ⌜i_p1 = i_p2⌝.
Proof.
  iIntros "Idx1 Idx2".
  by iCombine "Idx1 Idx2" gives %<-%to_agree_op_inv_L.
Qed.

Lemma Nodes_access {γz γcl} CL ih i_p γ_p p :
  ih ≤ i_p →
  fst <$> CL !! i_p = Some (γ_p, p) →
  Nodes γz γcl CL ih -∗
  hazptr.(Managed) γz p γ_p nodeSize (node γcl) ∗ node_idx γ_p i_p ∗
  (hazptr.(Managed) γz p γ_p nodeSize (node γcl) -∗ Nodes γz γcl CL ih).
Proof.
  iIntros (Hihi_p Hi_p) "Nodes".
  rewrite -list_lookup_fmap in Hi_p.
  unfold Nodes. rewrite fmap_drop.
  have EQ : ih + (i_p - ih) = i_p by lia.
  have Hi_p' : drop ih CL.*1 !! (i_p - ih) = Some (γ_p,p) by rewrite lookup_drop EQ.
  iDestruct (big_sepL_lookup_acc _ _ _ _ Hi_p' with "Nodes") as "[[? #?] Nodes]".
  rewrite EQ. iFrame "∗#". iIntros. iApply "Nodes". iFrame "∗#".
Qed.

Lemma Nodes_insert {γz γcl} CL ih i_p γ_p p x_p :
  ih ≤ i_p →
  i_p = length CL →
  Nodes γz γcl CL ih -∗
  hazptr.(Managed) γz p γ_p nodeSize (node γcl) -∗
  node_idx γ_p i_p -∗
  Nodes γz γcl (CL ++ [(γ_p,p,x_p)]) ih.
Proof.
  iIntros (? ->) "Nodes G_p Idx_p".
  unfold Nodes. rewrite !fmap_drop fmap_app /=.
  rewrite drop_app_le; last by rewrite fmap_length.
  iApply big_sepL_snoc. iFrame "Nodes".
  rewrite drop_length fmap_length.
  replace (ih + (length CL - ih)) with (length CL) by lia. iFrame.
Qed.

Lemma shield_Nodes_agree {γz γcl} CL ih i_p1 i_p2 γ_p1 γ_p2 p s R :
  ih ≤ i_p1 →
  fst <$> CL !! i_p1 = Some (γ_p1,p) →
  hazptr.(Shield) γz s (Validated p γ_p2 R nodeSize) -∗
  node_idx γ_p2 i_p2 -∗
  Nodes γz γcl CL ih -∗
  ⌜γ_p1 = γ_p2 ∧ i_p1 = i_p2⌝.
Proof.
  iIntros (Hihi_p Hi_p1) "S Idx_p2 Nodes".
  iDestruct (Nodes_access _ _ i_p1 with "Nodes") as "(G & Idx_p1 & Nodes)"; [done..|].
  iDestruct (hazptr.(shield_managed_agree) with "S G") as %->.
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
  iDestruct 1 as (? x_p on_p ->) "(#Idx_p' & #Info_p & St_p)".
  iDestruct (node_idx_agree with "Idx_p Idx_p'") as %<-. iClear "Idx_p'".
  iExists x_p, on_p. iSplit; [done|]. iFrame "Info_p".
  iDestruct "St_p" as "[St_p|St_p]".
  - iDestruct "St_p" as (? [-> ?]) "●CL_T". simpl. iLeft.
    iExists CL. iSplit; [done|]. iFrame "●CL_T". iSplit.
    + iIntros. iExists i_p, x_p, None. iFrame "∗#%". iSplit; [done|]. iLeft. iExists CL. iFrame. done.
    + iIntros. iExists i_p, x_p, (Some n_p). iFrame "∗#%". iSplit; [done|].
      iRight. iExists _,_,_. iFrame "#". done.
  - iDestruct "St_p" as (n_p γ_n_p x_n_p ->) "#[Idx_n_p Info_n_p]". simpl. iRight.
    iExists _,_,_. iSplit; [done|]. iFrame "#".
    iIntros. iExists _, x_p, (Some n_p). iFrame "∗#". iSplit; [done|]. iRight.
    iExists _,_,_. iFrame "#". done.
Qed.

Lemma queue_new_spec :
  queue_new_spec' queueN hazptrN queue_new hazptr Queue IsQueue.
Proof.
  iIntros (γz d Φ) "!> #IHD HΦ".
  wp_lam. wp_alloc s as "s↦" "†s". wp_pures.
  wp_apply (wp_store_offset with "s↦") as "s↦"; [by simplify_map_eq|]. wp_pures.
  wp_alloc qu as "qu↦" "†qu". wp_pures.
  repeat (wp_apply (wp_store_offset with "qu↦") as "qu↦"; [by simplify_list_eq|]; wp_pures).
  iEval (rewrite !array_cons !loc_add_assoc //) in "qu↦".
  iDestruct "qu↦" as "(qu.h↦ & qu.t↦ & qu.d↦ & _)".
  iMod (mono_list_own_alloc []) as (γcl) "[●CL _]".
  iMod (mapsto_persist with "qu.d↦") as "#qu.d↦".
  iMod (own_alloc (to_agree 0)) as (γ_s) "#Idx_s"; [done|].
  iMod (mono_list_auth_own_update_app [(γ_s,s,#0)] with "●CL") as "[[●CL_T ●CL] #◯CL]".
  iDestruct (mono_list_idx_own_get 0 with "◯CL") as "Info_s"; [done|].
  iAssert (node_status _ 0 None) with "[●CL_T]" as "St_s"; first by (iLeft; exfr).
  iMod (hazptr.(hazard_domain_register) (node γcl) with "IHD [$s↦ $†s St_s]") as "G_s"; [solve_ndisj|by exfr|].
  iDestruct "●CL" as "[●CL_I ●CL_Q]".
  iMod (mono_nat_own_alloc 0) as (γh) "[[●ih_I ●ih_Q] _]".
  iMod (mono_nat_own_alloc 0) as (γt) "[●it _]".
  remember (encode (γz, γcl, γh, γt)) as γq eqn:Hγq.
  iAssert (Queue γq []) with "[●CL_Q ●ih_Q]" as "Q"; first by exfr.
  iMod (inv_alloc queueN _ (QueueInternalInv qu _ _ γh γt) with "[-HΦ Q]") as "#Inv".
  { iNext. repeat iExists _. iFrame "∗#". simpl. iFrame. done. }
  iAssert (IsQueue _ _) with "[]" as "IQ"; first by exfr.
  iApply ("HΦ" with "[$IQ $Q]").
Qed.

Lemma try_advance_tail_spec qu γz γcl γh γt s t γ_t i_t x_t n γ_n x_n R :
  {{{ inv queueN (QueueInternalInv qu γz γcl γh γt) ∗
      hazptr.(Shield) γz s (Validated t γ_t R nodeSize) ∗
      node_idx γ_t i_t ∗
      node_info γcl t γ_t i_t x_t ∗
      node_idx γ_n (i_t+1) ∗
      node_info γcl n γ_n (i_t+1) x_n ∗
      mono_nat_lb_own γt i_t }}}
    CAS #(qu +ₗ tail) #t #n
  {{{ b, RET b;
      hazptr.(Shield) γz s (Validated t γ_t R nodeSize) ∗
      mono_nat_lb_own γt (i_t+1) }}}.
Proof.
  iIntros (Φ) "(#Inv & S & #Idx_t & #Info_t & #Idx_n & #Info_n & #◯it) HΦ".
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
    (* close internal inv *) iModIntro.
    iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes"; first by exfr.
    wp_pure. iApply ("HΦ" with "[$S $◯it']"). }

  (* I update the tail pointer *)
  (* Agree *)
  iDestruct (shield_Nodes_agree with "S Idx_t Nodes") as "#>[<- <-]"; [by destruct_and! F1..|].
  iDestruct (mono_list_auth_idx_lookup with "●CL_I Info_n") as %Hit1'.
  wp_cmpxchg_suc.
  iMod (mono_nat_own_update (it1+1) with "●it") as "[●it #◯it1']"; [lia|].
  (* close inv *) iModIntro.
  iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes".
  { repeat iExists _. iFrame "∗#%". iPureIntro.
    destruct_and!. split_and!; [done| |lia].
    by apply (f_equal (fmap fst)) in Hit1'. }
  wp_pure. iApply ("HΦ" with "[$S $◯it1']").
Qed.

Lemma find_tail_spec qu γz γcl γh γt (d : loc) s s_st :
  {{{ (qu +ₗ domain) ↦□ #d ∗ hazptr.(IsHazardDomain) γz d ∗
      inv queueN (QueueInternalInv qu γz γcl γh γt) ∗
      hazptr.(Shield) γz s s_st }}}
    (find_tail hazptr) #qu #s
  {{{ γ_t i_t (t : blk), RET #t;
      hazptr.(Shield) γz s (Validated t γ_t (node γcl) nodeSize) ∗
      node_idx γ_t i_t ∗
      mono_nat_lb_own γt i_t }}}.
Proof using All.
  iIntros (Φ) "(#qu.d↦ & #IHD & #Inv & S) HΦ". iLöb as "IH" forall (s_st).
  wp_lam. wp_pures.

  (* get protected pointer from tail pointer *)
  awp_apply (hazptr.(shield_protect_spec) with "IHD S"); [solve_ndisj|].
  iInv "Inv" as (CL1 h1 γ_h1 ih1 t1 γ_t1 it1)
              "[Nodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F1)]".
  (* snapshots *)
  iDestruct (get_tail_info with "Nodes") as "#Idx_t1"; [by destruct_and! F1..|].
  iDestruct (mono_nat_lb_own_get with "●it") as "#◯it1".
  (* Access the node pointed by the tail pointer *)
  iDestruct (Nodes_access _ _ it1 with "Nodes") as "(G_t1 & _ & Nodes)"; [by destruct_and! F1..|].
  iAaccIntro with "[qu.t↦ G_t1]".
  1: instantiate (1 := [tele_arg (Some _); _; _; _]); iFrame. all: simpl.
  { iIntros "[qu.t↦ G_t1] !>". exfr. by iApply "Nodes". }
  iIntros "(qu.t↦ & G_t1 & S)".
  (* close internal inv *) iModIntro.
  iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes G_t1".
  { iNext. repeat iExists _. iFrame "∗#%". by iApply "Nodes". }

  iIntros "_". wp_pures.

  wp_bind (! _)%E. iInv "S" as (?) "(_ & t1↦ & >N_t1 & S)".
  (* It this node actual tail? *)
  iDestruct (node_case with "Idx_t1 N_t1") as (x_t1 on_t1 ->) "(#Info_t1 & [CASE|CASE])".
  all: wp_apply (wp_load_offset with "t1↦") as "t1↦"; [by simplify_list_eq|].
  { (* actual tail *)
    iDestruct "CASE" as (? [-> ?]) "[●CL_T [N_t1 _]]".
    iSpecialize ("N_t1" with "●CL_T").
    iModIntro. iSplitL "t1↦ N_t1"; [iExists ([_;_]); by iFrame|].
    wp_pures. iApply ("HΦ" with "[$S $Idx_t1 $◯it1]"). }

  (* Not tail *)
  iDestruct "CASE" as (n_t1 γ_n_t1 x_n_t1 ->) "(#Idx_n_t1 & #Info_n_t1 & N_t1)". simpl.
  iModIntro. iSplitL "t1↦ N_t1". { iExists _. by iFrame "t1↦ N_t1". }

  wp_pures.

  (* Try advancing the tail *)
  wp_apply (try_advance_tail_spec with "[$Inv $S $Idx_t1 $Info_t1 $Idx_n_t1 $Info_n_t1 $◯it1]") as (?) "[S _]".
  wp_seq. iApply ("IH" with "S HΦ").
Qed.

Lemma queue_push_spec :
  queue_push_spec' queueN hazptrN (queue_push hazptr) Queue IsQueue.
Proof using All.
  iIntros (γq qu x).
  iDestruct 1 as (????? Hγq) "#(qu.d↦ & IHD & Inv)".
  iIntros (Φ) "AU".

  wp_lam. wp_alloc n as "n↦" "†n". wp_pures.
  do 2 (wp_apply (wp_store_offset with "n↦") as "n↦"; [by simplify_list_eq|]; wp_pures).
  wp_load.
  wp_apply (hazptr.(shield_new_spec) with "IHD [//]") as (s) "S"; [solve_ndisj|].
  wp_let.

  (* start push loop *)
  move: Deactivated => s_st.
  iLöb as "IH" forall (s_st).
  wp_rec. wp_pures.

  wp_apply (find_tail_spec with "[$qu.d↦ $IHD $Inv $S]") as (γ_t i_t t) "(S & #Idx_t & #◯it)".

  wp_let. wp_op.

  (* Try [next] field CAS. Is this node the actual tail? *)
  wp_bind (CmpXchg _ _ _).
  iInv "S" as (?) "(_ & t↦ & >N_t & S)".
  iDestruct (node_case with "Idx_t N_t") as (x_t on_t ->) "(#Info_t & [CASE|CASE])"; last first.
  { (* not tail; CAS failure *)
    iDestruct "CASE" as (n_t γ_n_t x_n_t ->) "(#Idx_n_t & #Info_n_t & N_t)". simpl.
    wp_apply (wp_cmpxchg_fail_offset with "t↦") as "t↦"; [by simplify_list_eq|done|naive_solver|].
    iModIntro. iSplitL "t↦ N_t"; [iExists ([_;_]); by iFrame|].
    wp_pure. wp_if. iApply ("IH" with "AU †n n↦ S"). }

  (* [t] is the actual tail. *)
  iDestruct "CASE" as (? [-> ?]) "[●CL_T [_ N_t]]". simpl.
  iInv "Inv" as (CL1 h1 γ_h1 ih1 t1 γ_t1 it1)
              "[Nodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F1)]".
  iMod "AU" as (xs) "[Q [_ Commit]]".
  iDestruct "Q" as (???????) "(●CL_Q & ●ih_Q & %)".
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
    rewrite app_length /=.
    apply lookup_lt_Some in Hit. (* [length CL1 > 0] *) lia. }
  iMod (hazptr.(hazard_domain_register) (node γcl) with "IHD [$n↦ $†n $N_n]") as "G_n"; [solve_ndisj|].
  iDestruct "●CL" as "[●CL_I ●CL_Q]".

  wp_apply (wp_cmpxchg_suc_offset with "t↦") as "t↦"; [by simplify_list_eq|done|naive_solver|].
  (* commit *)
  iMod ("Commit" with "[●CL_Q ●ih_Q]") as "HΦ".
  { repeat iExists _. iFrame "∗#%". iPureIntro.
    subst xs CL1'. rewrite !fmap_drop fmap_app /= drop_app_le // fmap_length.
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
  iSplitL "t↦ N_t"; [iExists ([_;_]); by iFrame|].
  iModIntro. wp_pures.

  (* Try advancing the tail *)
  wp_apply (try_advance_tail_spec with "[$Inv $S $Idx_t $Info_t $Idx_n $Info_n $◯it]") as (?) "[S _]".
  wp_pures.
  wp_apply (hazptr.(shield_drop_spec) with "IHD S"); [solve_ndisj|]. auto.
Qed.

Lemma queue_pop_spec :
  queue_pop_spec' queueN hazptrN (queue_pop hazptr) Queue IsQueue.
Proof using All.
  iIntros (γq qu).
  iDestruct 1 as (????? Hγq) "#(qu.d↦ & IHD & Inv)".
  iIntros (Φ) "AU".

  wp_lam. wp_load. wp_let.
  wp_apply (hazptr.(shield_new_spec) with "IHD [//]") as (s_h) "HeadS"; [solve_ndisj|].
  wp_let.
  move: Deactivated => hs_st.
  wp_apply (hazptr.(shield_new_spec) with "IHD [//]") as (s_n) "NextS"; [solve_ndisj|].
  wp_let.
  move: Deactivated => ns_st.

  wp_bind ((queue_pop_loop hazptr) _). iLöb as "IH" forall (hs_st ns_st).
  wp_rec. wp_pures.

  (* protect head and recover AU *)
  awp_apply (hazptr.(shield_protect_spec) with "IHD HeadS"); [solve_ndisj|].
  (* NOTE: "iInv: cannot eliminate invariant" when given Hclose *)
  iInv "Inv" as (CL1 h1 γ_h1 ih1 t1 γ_t1 it1)
              "[Nodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F1)]".
  iDestruct (get_head_info with "Nodes") as "#Idx_h1"; [by destruct_and! F1|].
  iDestruct (Nodes_access _ _ ih1 with "Nodes") as "(G_h1 & _ & Nodes)"; [by destruct_and! F1..|].
  (* snapshots *)
  iDestruct (mono_list_lb_own_get with "●CL_I") as "#◯CL1".
  iDestruct (mono_nat_lb_own_get with "●ih_I") as "#◯ih1".

  iAaccIntro with "[qu.h↦ G_h1]".
  1: instantiate (1 := [tele_arg (Some _); _; _; _]); iFrame. all: simpl.
  { iIntros "[qu.h↦ G_h1] !>". exfr. by iApply "Nodes". }
  iIntros "(qu.h↦ & G_h1 & HeadS)".
  (* close internal inv *)
  iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes G_h1".
  { iNext. repeat iExists _. iFrame "∗#%". by iApply "Nodes". }

  iIntros "_". wp_pures. wp_bind (! _)%E.

  (* Read the head's next field. If it's null, commit empty pop. *)
  iInv "Inv" as (CL2 h2 γ_h2 ih2 t2 γ_t2 it2)
              "[Nodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F2)]".
  (* agree *)
  iDestruct (mono_list_auth_lb_valid with "●CL_I ◯CL1") as %[_ PF_CL12].
  iDestruct (mono_nat_lb_own_valid with "●ih_I ◯ih1") as %[_ LE_ih12].
  (* snapshots *)
  iDestruct (mono_nat_lb_own_get with "●ih_I") as "#◯ih2".
  (* Access the protected node *)
  iInv "HeadS" as (?) "(_ & h1↦ & >N_h1 & HeadS)".
  (* Case analysis on the status of node [ih1]. *)
  iDestruct (node_case with "Idx_h1 N_h1") as (x_h1 on_h1 ->) "(#Info_h1 & [CASE|CASE])".
  { (* [head.next] is null (tail). Commit empty pop *)
    iDestruct "CASE" as (? [-> ?]) "[●CL_T [N_h1 _]]". simpl.
    iMod "AU" as (xs2) "[Q [_ Commit]]".
    iDestruct "Q" as (???????) "(●CL_Q & ●ih_Q & %Hxs2)".
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
      rewrite app_length in HL.
      assert (length L = 0) as ->%nil_length_inv by lia.
      by rewrite app_nil_r. }
    assert (xs2 = []) as ->.
    { subst ih2 xs2.
      destruct F2 as (_ & ?%lookup_fmap_lt_Some & _).
      rewrite fmap_drop drop_ge //. rewrite fmap_length. lia. }
    (* Commit empty pop *)
    wp_apply (wp_load_offset with "h1↦") as "h1↦"; [by simplify_list_eq|].
    iMod ("Commit" with "[●CL_Q ●ih_Q]") as "HΦ"; first by exfr.
    iSpecialize ("N_h1" with "●CL_T").
    iSplitL "h1↦ N_h1"; [iExists ([_;_]); by iFrame|]. do 3 iModIntro.
    iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes"; first by exfr.

    wp_pures.
    wp_apply (hazptr.(shield_drop_spec) with "IHD HeadS") as "_"; [solve_ndisj|].
    wp_seq.
    wp_apply (hazptr.(shield_drop_spec) with "IHD NextS") as "_"; [solve_ndisj|].
    wp_seq. iApply "HΦ". by iFrame. }

  (* [head.next] is not null. *)
  iDestruct "CASE" as (n_h1 γ_n_h1 x_n_h1 ->) "(#Idx_n_h1 & #Info_n_h1 & N_h1)". simpl.
  wp_apply (wp_load_offset with "h1↦") as "h1↦"; [by simplify_list_eq|].
  iSplitL "h1↦ N_h1"; [iExists ([_;_]); by iFrame|]. do 2 iModIntro.
  iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes"; first by exfr.

  wp_pures.

  (* protect *)
  wp_apply (hazptr.(shield_set_spec) (Some _) with "IHD NextS") as "NextS"; [solve_ndisj..|].
  wp_pures. wp_bind (! _)%E.

  (* validate *)
  iInv "Inv" as (CL3 h3 γ_h3 ih3 t3 γ_t3 it3)
              "[Nodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F3)]".
  iDestruct (get_head_info with "Nodes") as "#Idx_h3"; [by destruct_and! F3|].
  (* Has the head pointer changed since the protection of [h1]? *)
  case (decide (h1 = h3)) as [->|NE_h13]; last first.
  { (* If changed, validation fails *)
    wp_load.
    (* close internal inv *)
    iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes"; first by exfr.

    wp_pures.
    rewrite bool_decide_eq_false_2; last by (intro; simplify_eq).
    wp_if. wp_apply ("IH" with "AU HeadS NextS"). }

  wp_load.

  (* Head pointer hasn't changed. [ih1 = ih3] *)
  iDestruct (shield_Nodes_agree _ _ ih3 with "HeadS Idx_h1 Nodes") as %[<- <-]; [by destruct_and! F3..|].
  (* clean up *)
  iAssert ⌜ih2 = ih3⌝%I as %->; last clear LE_ih12.
  { iDestruct (mono_nat_lb_own_valid with "●ih_I ◯ih2") as %[_ ?]. iPureIntro. lia. }
  iRename "◯ih1" into "◯ih3". iClear "◯ih2".
  (* snapshot *)
  iDestruct (mono_list_lb_own_get with "●CL_I") as "#◯CL3".

  (* The invariant has [Managed] of the next node. *)
  iDestruct (mono_list_auth_idx_lookup with "●CL_I Info_n_h1") as %Hih3'.
  iDestruct (Nodes_access _ _ (ih3+1) with "Nodes") as "(G_n_h1 & _ & Nodes)"; [lia|..].
  { apply (f_equal (fmap fst)) in Hih3'. simpl in Hih3'. done. }
  (* Validate *)
  iMod (hazptr.(shield_validate) with "IHD G_n_h1 NextS") as "[G_n_h1 NextS]"; [solve_ndisj..|].
  iSpecialize ("Nodes" with "G_n_h1").

  (* close internal inv *)
  iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes"; first by exfr.

  wp_pures. rewrite bool_decide_eq_true_2; [|done]. wp_pures. wp_bind (! _)%E.

  (* read tail pointer *)
  iInv "Inv" as (CL4 h4 γ_h4 ih4 t4 γ_t4 it4)
              "[Nodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F4)]".
  (* snapshots *)
  iDestruct (mono_nat_lb_own_get with "●ih_I") as "#◯ih4".
  iDestruct (mono_nat_lb_own_get with "●it") as "#◯it4".
  iDestruct (mono_nat_lb_own_valid with "●ih_I ◯ih3") as %[_ LE_ih34].
  iDestruct (mono_list_auth_lb_valid with "●CL_I ◯CL3") as %[_ PF_CL34].
  (* If the head shield and the tail pointer value are the same, they point to
  the same logical node. *)
  wp_load.
  iAssert (⌜h3 = t4 → ih3 = it4⌝)%I as %Hih3it4.
  { iIntros (->).
    by iDestruct (shield_Nodes_agree with "HeadS Idx_h3 Nodes") as %[<- <-]; [by destruct_and! F4..|]. }
  (* close internal inv *) iModIntro.
  iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes"; first by exfr.

  wp_pures. wp_bind (if: _ then _ else _)%E.

  (* Try advancing the tail. *)
  set (fix_tail := (if: #(bool_decide _) then _ else _)%E) in *.
  iAssert (
    {{{ hazptr.(Shield) γz s_h (Validated h3 γ_h3 (node γcl) nodeSize) }}}
      fix_tail
    {{{ v, RET v;
        hazptr.(Shield) γz s_h (Validated h3 γ_h3 (node γcl) nodeSize) ∗
        mono_nat_lb_own γt (ih3+1) }}}
  )%I as "HT_fix_tail".
  { subst fix_tail.
    iIntros (Φ') "!> HeadS HΦ'".
    case (decide (h3 = t4)) as [->|NE_ht].
    - rewrite bool_decide_eq_true_2; last done.
      specialize (Hih3it4 eq_refl) as ->. (* [ih3 = it4] *)
      wp_pures.
      wp_apply (try_advance_tail_spec with "[$Inv $HeadS $Idx_h1 $Info_h1 $Idx_n_h1 $Info_n_h1 $◯it4]") as (?) "[HeadS #◯it4']".

      by iApply ("HΦ'" with "[$HeadS $◯it4']").
    - rewrite bool_decide_eq_false_2; last first.
      { unfold not. intros H. by inversion H. }
      wp_pures.
      destruct F4 as (? & ? & LE_ih4it4).
      have NE_ih3it4 : ih3 ≠ it4.
      { intros ->. destruct F3 as [Hh3 _].
        have ? := prefix_lookup_fmap _ _ _ _ _ Hh3 PF_CL34. congruence. }
      have {LE_ih34 LE_ih4it4 NE_ih3it4}LE_ih3'it4 : ih3 + 1 ≤ it4 by lia.
      iDestruct (mono_nat_lb_own_le _ LE_ih3'it4 with "◯it4") as "#◯it_ih3'".
      iApply ("HΦ'" with "[$HeadS $◯it_ih3']"). }

  wp_apply ("HT_fix_tail" with "[$HeadS]") as (v_clear) "[HeadS #◯it_ih3']".
  wp_seq.
  iClear (fix_tail Hih3it4 v_clear) "HT_fix_tail".

  wp_pures. wp_bind (CmpXchg _ _ _)%E.

  (* Pop CAS *)
  iInv "Inv" as (CL6 h6 γ_h6 ih6 t6 γ_t6 it6)
              "[Nodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F6)]".

  (* Has the head pointer changed? *)
  case (decide (h3 = h6)) as [->|NE_h36]; last first.
  { wp_cmpxchg_fail.
    (* close internal inv *)
    iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes"; first by exfr.
    wp_pure. wp_if. wp_apply ("IH" with "AU HeadS NextS"). }

  wp_cmpxchg_suc.

  (* Agree *)
  iDestruct (shield_Nodes_agree _ _ ih6 with "HeadS Idx_h3 Nodes") as %[<- <-]; [by destruct_and! F6..|].
  (* clean up *)
  iAssert (⌜ih4 = ih6⌝)%I as %->; last clear LE_ih34.
  { iDestruct (mono_nat_lb_own_valid with "●ih_I ◯ih4") as %[_ ?]. iPureIntro. lia. }
  iRename "◯ih3" into "◯ih6". rename Hih3' into Hih6'. iClear "◯ih4".

  (* access AU *)
  iMod "AU" as (xs6) "[Q [_ Commit]]".
  iDestruct "Q" as (???????) "(●CL_Q & ●ih_Q & %Hxs6)".
  encode_agree Hγq.
  (* agree *)
  iDestruct (mono_list_auth_own_agree with "●CL_I ●CL_Q") as %[_ <-].
  iDestruct (mono_nat_auth_own_agree with "●ih_I ●ih_Q") as %[_ <-].
  iDestruct (mono_nat_lb_own_valid with "●it ◯it_ih3'") as %[_ LE_ih6'it6].
  iDestruct (mono_list_auth_lb_valid with "●CL_I ◯CL3") as %[_ PF_CL36].
  have {}Hih6' := prefix_lookup_Some _ _ _ _ Hih6' PF_CL36.
  (* abstract state *)
  rewrite (drop_S _ _ _ Hih6') -Nat.add_1_r fmap_cons /= in Hxs6.
  (* update *)
  iCombine ("●ih_I ●ih_Q") as "●ih".
  iMod (mono_nat_own_update (ih6+1) with "●ih") as "[[●ih_I ●ih_Q] _]"; [lia|].
  (* unlinked: take managed from the inv *)
  iAssert (hazptr.(Managed) γz h6 γ_h6 nodeSize (node γcl) ∗ Nodes γz γcl CL6 (ih6+1))%I
            with "[Nodes]" as "[G_h6 Nodes]".
  { unfold Nodes. destruct F6 as (Hih6 & ? & ?).
    rewrite !fmap_drop. rewrite -list_lookup_fmap in Hih6.
    rewrite (drop_S _ _ _ Hih6) big_sepL_cons Nat.add_0_r.
    iDestruct "Nodes" as "[[$ _] Nodes]".
    iApply (big_sepL_mono' with "Nodes").
    - intros i ?. by replace (ih6 + S i) with (ih6 + 1 + i) by lia.
    - by rewrite -Nat.add_1_r. }

  (* commit *)
  iMod ("Commit" with "[●CL_Q ●ih_Q]") as "HΦ"; first by (subst xs6; exfr).
  (* close internal inv *)
  iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes".
  { repeat iExists _. iFrame "∗#%". iPureIntro. destruct_and! F6. split_and!; try done.
    by apply (f_equal (fmap fst)) in Hih6'. }

  wp_pures.

  (* Read data *)
  wp_bind (! _)%E.
  iInv "NextS" as (?) "(_ & n_h1↦ & >N_n_h1 & NextS)".
  iDestruct "N_n_h1" as (i_n_h1' x_n_h1' on_n_h1' ->) "(#Idx_n_h1' & #Info_n_h1' & St_n_h1)".
  iDestruct (node_idx_agree with "Idx_n_h1 Idx_n_h1'") as %<-.
  iDestruct (mono_list_idx_agree with "Info_n_h1 Info_n_h1'") as %[= <-].
  iClear "Idx_n_h1' Info_n_h1'".
  wp_apply (wp_load_offset with "n_h1↦") as "n_h1↦"; [by simplify_list_eq|].
  iAssert (node _ n_h1 _ _) with "[St_n_h1]" as "N_n_h1"; first by exfr.
  iSplitL "n_h1↦ N_n_h1"; [iExists ([_;_]); by iFrame|].
  iModIntro. wp_pures. wp_load.
  wp_apply (hazptr.(hazard_domain_retire_spec) with "IHD [$G_h6]") as "_"; [solve_ndisj|].
  wp_pures.
  wp_apply (hazptr.(shield_drop_spec) with "IHD HeadS") as "_"; [solve_ndisj|].
  wp_seq.
  wp_apply (hazptr.(shield_drop_spec) with "IHD NextS") as "_"; [solve_ndisj|].
  wp_pures.
  subst xs6. iApply "HΦ". by iFrame.
Qed.

#[export] Typeclasses Opaque Queue IsQueue.

End ms_queue.
