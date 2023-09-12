From iris.algebra Require Import agree.
From iris.base_logic Require Import lib.mono_nat lib.invariants lib.ghost_var.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr.base_logic Require Import lib.mono_list.
From smr Require Import helpers hazptr.spec_hazptr hazptr.spec_queue hazptr.code_dglm.

Set Printing Projections.

Local Open Scope nat_scope.

Class dglmG Σ := DGLMG {
  dglm_inG :> inG Σ (agreeR natO);
  dglm_mono_listG :> mono_listG (gname * blk * val) Σ;
  dglm_mono_natG :> mono_natG Σ;
  dglm_ghost_varG :> ghost_varG Σ bool;
}.

Definition dglmΣ : gFunctors := #[GFunctor (agreeR natO); mono_listΣ (gname * blk *val); mono_natΣ; ghost_varΣ bool].

Global Instance subG_dglmΣ {Σ} :
  subG dglmΣ Σ → dglmG Σ.
Proof. solve_inG. Qed.

Section dglm_queue.
Context `{!heapGS Σ, !dglmG Σ}.
Notation iProp := (iProp Σ).
Context (queueN hazptrN : namespace) (DISJN : hazptrN ## queueN).

(* iExists + iFrame *)
Ltac exfr := repeat (repeat iExists _; iFrame "∗#%").

Variable (hazptr : hazard_pointer_spec Σ hazptrN).

Implicit Types
  (γz γcl γh γt γi_p γr_p : gname)
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

Definition node_idx γ_p i_p : iProp :=
  ∃ γi_p γr_p, ⌜ γ_p = encode (γi_p, γr_p) ⌝ ∗
  (own γi_p (to_agree (i_p : nat))).

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

Definition node_reaped γ_p qp (b: bool): iProp :=
  ∃ γi_p γr_p, ⌜ γ_p = encode (γi_p, γr_p) ⌝ ∗
    ghost_var γr_p qp b.


Definition Nodes γz γcl CL ih : iProp :=
  [∗ list] i ↦ info ∈ (drop ih CL).*1, let '(γ_p, p) := info in
  hazptr.(Managed) γz p γ_p nodeSize (node γcl) ∗ node_idx γ_p (ih + i) ∗ node_reaped γ_p 1 false.

Definition Zombies γz γcl CL ih it: iProp :=
  [∗ list] i ↦ info ∈ (take ih CL).*1, let '(γ_p, p) := info in
    ∃ b, node_reaped γ_p (1/2) b ∗
    (⌜ (b = true ∧ i + 1 ≤ it) ⌝ ∨ (hazptr.(Managed) γz p γ_p nodeSize (node γcl) ∗ node_idx γ_p i) ).

Definition AllNodes γz γcl CL ih it: iProp :=
  Nodes γz γcl CL ih ∗ Zombies γz γcl CL ih it.

Definition QueueInternalInv qu γz γcl γh γt : iProp :=
  ∃ CL
    (h : blk) γ_h ih (* current head (sentinel) node *)
    (t : blk) γ_t it (* node pointed to by the tail pointer *),
    (* nodes *)
    AllNodes γz γcl CL ih it ∗
    mono_list_auth_own γcl (1/2/2) CL ∗
    (* head pointer *)
    (qu +ₗ head) ↦ #h ∗
    mono_nat_auth_own γh (1/2) ih ∗
    (* tail pointer *)
    (qu +ₗ tail) ↦ #t ∗
    mono_nat_auth_own γt 1 it ∗
    ⌜ fst <$> CL !! ih = Some (γ_h,h) ∧
      fst <$> CL !! it = Some (γ_t,t) ∧
      length CL - 2 ≤ it ⌝.

Lemma tail_lags_at_most_one CL ih γ_h h it:
  fst <$> CL !! ih = Some (γ_h, h) →
  length CL - 2 ≤ it →
  ih - 1 ≤ it.
Proof.
  iIntros (Hhmap).
  have Hih: (ih < length CL). {
    rewrite -list_lookup_fmap in Hhmap.
    remember (lookup_lt_Some _ _ _ Hhmap) as H. clear HeqH.
    rewrite fmap_length in H. done.
  }
  lia.
Qed.

Lemma Zombies_mono_to_it γz γcl CL ih it1 it2:
  it1 ≤ it2 →
  Zombies γz γcl CL ih it1  -∗
  Zombies γz γcl CL ih it2.
Proof.
  iIntros (Hit_inc) "Zombies". unfold Zombies.
  iApply (big_sepL_mono' with "Zombies"); [| done].
  intros i (?, blk). iIntros "[%b (? & H)]". iExists b. iFrame "∗". iDestruct "H" as "[(%H1 & %H2) | H]".
  - iLeft. iPureIntro. split; [done|lia].
  - iRight. done.
Qed.

Lemma AllNodes_mono_to_it γz γcl CL ih it1 it2:
  it1 ≤ it2 →
  AllNodes γz γcl CL ih it1  -∗
  AllNodes γz γcl CL ih it2.
Proof.
  iIntros (Hit_inc) "[Nodes Zombies]". iFrame. iApply Zombies_mono_to_it; done.
Qed.


Lemma get_head_info CL ih γ_h h γz γcl :
  fst <$> CL !! ih = Some (γ_h, h) →
  Nodes γz γcl CL ih -∗
  node_idx γ_h ih.
Proof.
  iIntros (Hih) "Nodes". unfold Nodes.
  rewrite fmap_drop.
  iDestruct (big_sepL_lookup _ _ 0 (γ_h, h) with "Nodes") as "(_ & #Idx_h & _)".
  - rewrite lookup_drop list_lookup_fmap. rewrite Nat.add_0_r. done.
  - rewrite Nat.add_0_r. done.
Qed.

Lemma get_head_info_from_AllNodes CL ih it γ_h h γz γcl  :
  fst <$> CL !! ih = Some (γ_h, h) →
  AllNodes γz γcl CL ih it -∗
  node_idx γ_h ih.
Proof.
  iIntros (Hih) "[Nodes _]". iApply (get_head_info with "Nodes"). done.
Qed.

Lemma get_tail_info CL ih it γ_t t γz γcl :
  fst <$> CL !! it = Some (γ_t, t) →
  AllNodes γz γcl CL ih it -∗
  node_idx γ_t it.
Proof.
  iIntros (Hit) "AllNodes".
  have Cases: (it < ih ∨ ih ≤ it) by lia. destruct Cases.
  - {
    iDestruct "AllNodes" as "[_ Zombies]".  unfold Zombies. rewrite fmap_take.
    iDestruct (big_sepL_lookup _ _ it (γ_t, t) with "Zombies") as (b) "Hb".
    { rewrite lookup_take; [| lia]. rewrite list_lookup_fmap. done. }
    iDestruct "Hb" as "(_ & [[_ %contra] | [_ #Idx_h]])"; [exfalso; lia | ]. done.
  }
  - {
    iDestruct "AllNodes" as "[Nodes _]". unfold Nodes. rewrite fmap_drop.
    have EQ:(ih + (it - ih) = it) by lia.
    iDestruct (big_sepL_lookup _ _ (it - ih) (γ_t, t) with "Nodes") as "(_ & #Idx_h & _)".
    - rewrite lookup_drop list_lookup_fmap EQ. done.
    - rewrite EQ. done.
  }
Qed.


(* Persistent assertions about the queue *)
Definition IsQueue (γq : gname) (qu : loc) : iProp :=
  ∃ (d : loc) γz γcl γh γt,
    ⌜γq = encode (γz, γcl, γh, γt)⌝ ∗
    (qu +ₗ 2) ↦□ #d ∗ hazptr.(IsHazardDomain) γz d ∗
    inv queueN (QueueInternalInv qu γz γcl γh γt).

Global Instance IsQueue_Persistent γq qu : Persistent (IsQueue γq qu).
Proof. apply _. Qed.

Lemma node_idx_agree γ_p i_p1 i_p2 :
  node_idx γ_p i_p1 -∗ node_idx γ_p i_p2 -∗ ⌜i_p1 = i_p2⌝.
Proof.
  iIntros "(%γi_p1 & %γr_p1 & %Henc1 & Idx1) (%γi_p2 & %γr_p2 & %Henc2 & Idx2)".
  encode_agree Henc1.
  by iCombine "Idx1 Idx2" gives %<-%to_agree_op_inv_L.
Qed.

Lemma node_reaped_agree γ_p p1 p2 b1 b2:
  node_reaped γ_p p1 b1 -∗ node_reaped γ_p p2 b2 -∗ ⌜ b1 = b2 ⌝.
Proof.
  iIntros "(%γi_p1 & %γr_p1 & %Henc1 & gv1) (%γi_p2 & %γr_p2 & %Henc2 & gv2)".
  encode_agree Henc1.
  iDestruct (ghost_var_agree with "gv1 gv2") as %<-. done.
Qed.

Lemma node_reaped_update_halves b' γ_p b:
  node_reaped γ_p (1/2) b -∗ node_reaped γ_p (1/2) b ==∗
  node_reaped γ_p (1/2) b' ∗ node_reaped γ_p (1/2) b'.
Proof.
  iIntros "(%γi_p1 & %γr_p1 & %Henc1 & gv1) (%γi_p2 & %γr_p2 & %Henc2 & gv2)".
  encode_agree Henc1.
  iMod (ghost_var_update_halves b' with "gv1 gv2") as "[gv1' gv2']".
  iModIntro. unfold node_reaped. iSplitL "gv1'"; iExists _, _; iFrame "∗%".
Qed.

Lemma AllNodes_access {γz γcl} CL ih it i_p γ_p p :
  ih ≤ i_p ∨ (i_p + 1 = ih ∧ it + 1 = ih) →
  fst <$> CL !! i_p = Some (γ_p, p) →
  AllNodes γz γcl CL ih it -∗
  hazptr.(Managed) γz p γ_p nodeSize (node γcl) ∗ node_idx γ_p i_p ∗
  (hazptr.(Managed) γz p γ_p nodeSize (node γcl) -∗ AllNodes γz γcl CL ih it).
Proof.
  iIntros (H Hi_p) "[Nodes Zombies]".
  rewrite -list_lookup_fmap in Hi_p.
  destruct H as [Hihi_p | [Hihi_p Hihit]].
  -
    unfold Nodes.
    rewrite fmap_drop.
    have EQ : ih + (i_p - ih) = i_p by lia.
    have Hi_p' : drop ih CL.*1 !! (i_p - ih) = Some (γ_p, p) by rewrite lookup_drop EQ.
    iDestruct (big_sepL_lookup_acc _ _ _ _ Hi_p' with "Nodes") as "[(? & #? & ?) Nodes]".
    rewrite EQ. subst. iFrame "∗#". iIntros. rewrite -fmap_drop. iApply "Nodes". iFrame "∗#".
  -
    unfold Zombies.
    rewrite fmap_take. subst.
    have Hi_p': take (i_p + 1) CL.*1 !! i_p = Some (γ_p, p) by  rewrite lookup_take; [done | lia].
    iDestruct (big_sepL_lookup_acc _ _ _ _ Hi_p' with "Zombies") as "[[%b (? & [(_ & %Htaken_contra) | (? & #?)])] Zombies]".
    + exfalso. lia. (* Since ~(it > i_p), we can guarantee that the node is not yet reaped by a dequeuer. *)
    + iFrame "∗#". iIntros. rewrite -fmap_take. iApply "Zombies". iExists b. iFrame. iRight. iFrame "∗#".
Qed.

Lemma Nodes_insert {γz γcl} CL ih i_p γ_p p x_p :
  ih ≤ i_p →
  i_p = length CL →
  Nodes γz γcl CL ih -∗
  hazptr.(Managed) γz p γ_p nodeSize (node γcl) -∗
  node_idx γ_p i_p -∗
  node_reaped γ_p 1 false -∗
  Nodes γz γcl (CL ++ [(γ_p, p, x_p)]) ih.
Proof.
  iIntros (? ->) "Nodes G_p Idx_p Taken_p".
  unfold Nodes. rewrite !fmap_drop fmap_app /=.
  rewrite drop_app_le; last by rewrite fmap_length.
  iApply big_sepL_snoc. iFrame "Nodes".
  rewrite drop_length fmap_length.
  replace (ih + (length CL - ih)) with (length CL) by lia.
  iFrame.
Qed.

Lemma Zombies_insert {γz γcl} CL ih it γ_p p x_p:
  ih ≤ length CL - 1 →
  Zombies γz γcl (CL) ih it -∗
  Zombies γz γcl (CL ++ [(γ_p, p, x_p)]) ih it.
Proof.
  iIntros (Hih) "Zombies". unfold Zombies.
  replace (take ih (CL ++ [(γ_p, p, x_p)])) with ((take ih CL)); [done |].
  rewrite take_app_le; [done | lia].
Qed.

Lemma shield_AllNodes_agree {γz γcl} CL ih it i_p1 i_p2 γ_p1 γ_p2 p s R :
  ih ≤ i_p1 ∨ (i_p1 + 1 = ih ∧ it + 1 = ih) →
  fst <$> CL !! i_p1 = Some (γ_p1, p) →
  hazptr.(Shield) γz s (Validated p γ_p2 R nodeSize) -∗
  node_idx γ_p2 i_p2 -∗
  AllNodes γz γcl CL ih it -∗
  ⌜γ_p1 = γ_p2 ∧ i_p1 = i_p2⌝.
Proof.
  iIntros (Hihi_p Hi_p1) "S Idx_p2 AllNodes".
  iDestruct (AllNodes_access _ _ _ i_p1 with "AllNodes") as "(G & Idx_p1 & AllNodes)"; [done.. |].
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
  iDestruct 1 as (? x_p on_p) "(%EQ & #Idx_p' & #Info_p & St_p)". subst lv.
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

Lemma alloc_node_resources idx:
  ⊢ |==> ∃ γ_p , node_idx γ_p idx ∗ node_reaped γ_p 1 false.
Proof.
  iMod (own_alloc (to_agree idx)) as (γi_s) "Idx_s'"; [done|].
  iMod (ghost_var_alloc false) as (γr_s) "γr_s".
  remember (encode (γi_s, γr_s)) as γ_s eqn: Henc.
  iAssert (node_idx γ_s idx) with "[Idx_s']" as "Idx_s".
  { iExists γi_s, γr_s. iFrame "∗%". }
  iAssert (node_reaped γ_s 1 false) with "[γr_s]" as "Reaped".
  { iExists _, _. iFrame "∗%". }
  iExists γ_s. iFrame "∗#". done.
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
  iMod (alloc_node_resources 0) as (γ_s) "(#Idx_s & Reaped)".
  iMod (mono_list_auth_own_update_app [(γ_s,s,#0)] with "●CL") as "[[●CL_T ●CL] #◯CL]".
  iDestruct (mono_list_idx_own_get 0 with "◯CL") as "Info_s"; [done|].
  iMod (hazptr.(hazard_domain_register) (node γcl) with "IHD [$s↦ $†s ●CL_T]") as "G_s"; [solve_ndisj| |].
  { iExists _,_,None. iSplit; [done|]. exfr. iLeft. by exfr. }
  iDestruct "●CL" as "[●CL_I ●CL_Q]".
  iMod (mono_nat_own_alloc 0) as (γh) "[[●ih_I ●ih_Q] _]".
  iMod (mono_nat_own_alloc 0) as (γt) "[●it _]".
  remember (encode (γz, γcl, γh, γt)) as γq eqn:Hγq.
  iAssert (Queue γq []) with "[●CL_Q ●ih_Q]" as "Q"; first by exfr.
  iMod (inv_alloc queueN _ (QueueInternalInv qu _ _ γh γt) with "[-HΦ Q]") as "#Inv".
  { iNext. repeat iExists _. iFrame "∗#". unfold Zombies. simpl. iFrame.  done. }
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
    CAS #(qu +ₗ 1) #t #n
  {{{ b, RET b;
      hazptr.(Shield) γz s (Validated t γ_t R nodeSize) ∗
      mono_nat_lb_own γt (i_t+1) }}}.
Proof.
  iIntros (Φ) "(#Inv & S & #Idx_t & #Info_t & #Idx_n & #Info_n & #◯it) HΦ".
  wp_bind (CmpXchg _ _ _).
  iInv "Inv" as (CL1 h1 γ_h1 ih1 t1 γ_t1 it1)
              "[AllNodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F1)]".

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
    iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it AllNodes"; first by exfr.
    wp_pure. iApply ("HΦ" with "[$S $◯it']"). }

  (* I update the tail pointer *)
  have Hht: (ih1 - 1 ≤ it1) by eapply tail_lags_at_most_one; destruct_and! F1.
  have Hht': (ih1 ≤ it1 ∨ (it1 + 1 = ih1 ∧ it1 + 1 = ih1)) by lia.

  (* Agree *)
  iDestruct (shield_AllNodes_agree with "S Idx_t AllNodes") as "#>[<- <-]"; [by destruct_and! F1..|].
  iDestruct (mono_list_auth_idx_lookup with "●CL_I Info_n") as %Hit1'.
  wp_cmpxchg_suc.
  iMod (mono_nat_own_update (it1+1) with "●it") as "[●it #◯it1']"; [lia|].
  (* close inv *) iModIntro.

  iAssert (AllNodes γz γcl CL1 ih1 (it1 + 1)) with "[AllNodes]" as "AllNodes".
  { iApply AllNodes_mono_to_it; [| done]. lia. }
  iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it AllNodes".
  { repeat iExists _. iFrame "∗#%". iPureIntro.
    destruct_and!. split_and!; [done| |lia].
    by apply (f_equal (fmap fst)) in Hit1'. }
  wp_pure. iApply ("HΦ" with "[$S $◯it1']").
Qed.

Lemma find_tail_spec qu γz γcl γh γt (d : loc) s s_st :
  {{{ (qu +ₗ 2) ↦□ #d ∗ hazptr.(IsHazardDomain) γz d ∗
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
              "[AllNodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F1)]".
  (* snapshots *)

  have Hht: (ih1 - 1 ≤ it1) by eapply tail_lags_at_most_one; destruct_and! F1.
  have Hht': (ih1 ≤ it1 ∨ (it1 + 1 = ih1 ∧ it1 + 1 = ih1)) by lia.

  iDestruct (get_tail_info with "AllNodes") as "#Idx_t1"; [by destruct_and! F1..|].
  iDestruct (mono_nat_lb_own_get with "●it") as "#◯it1".
  (* Access the node pointed by the tail pointer *)
  iDestruct (AllNodes_access _ _ it1 with "AllNodes") as "(G_t1 & _ & AllNodes)"; [by destruct_and! F1..|].
  iAaccIntro with "[qu.t↦ G_t1]".
  1: instantiate (1 := [tele_arg (Some _); _; _; _]); iFrame. all: simpl.
  { iIntros "[qu.t↦ G_t1] !>". exfr. by iApply "AllNodes". }
  iIntros "(qu.t↦ & G_t1 & S)".
  (* close internal inv *) iModIntro.
  iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it AllNodes G_t1".
  { iNext. repeat iExists _. iFrame "∗#%". by iApply "AllNodes". }

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
              "[[Nodes Zombies] >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F1)]".
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

  iMod (alloc_node_resources (it1 + 1)) as (γ_n) "(#Idx_n & Reaped)".
  iMod (mono_list_auth_own_update_app [(γ_n,n,x)] with "●CL") as "[[●CL_T ●CL] #◯CL1']".
  set (CL1' := CL1 ++ [(γ_n, n, x)]) in *.
  have Hit1' : CL1' !! (it1 + 1) = Some (γ_n, n, x).
  { subst CL1' it1. destruct F1 as (_ & ?%lookup_fmap_lt_Some & _). (* [length CL > 0] *)
    remember(length CL1) as l eqn: EQ.
    rewrite lookup_app_r; rewrite -EQ; [| lia].
    by replace (l - 1 + 1 - l) with 0 by lia.
  }
  (* required for advancing the tail pointer *)
  iDestruct (mono_list_idx_own_get _ _ Hit1' with "◯CL1'") as "Info_n".
  (* register the enqueued node *)
  iAssert (node γcl n _ γ_n) with "[●CL_T]" as "N_n".
  { iExists (it1+1), x, None. iSplit; [done|]. iFrame "Idx_n Info_n". iLeft.
    iExists _. iFrame "●CL_T". iPureIntro. split; [done|].
    rewrite app_length /=.
    apply lookup_lt_Some in Hit. (* [length CL1 > 0] *) lia. }

  iMod (hazptr.(hazard_domain_register) (node γcl) with "IHD [$n↦ $†n $N_n]") as "G_n"; [solve_ndisj|..].
  iDestruct "●CL" as "[●CL_I ●CL_Q]".

  wp_apply (wp_cmpxchg_suc_offset with "t↦") as "t↦"; [by simplify_list_eq|done|naive_solver|].
  (* commit *)
  iMod ("Commit" with "[●CL_Q ●ih_Q]") as "HΦ".
  { repeat iExists _. iFrame "∗#%". iPureIntro.
    subst xs CL1'. rewrite !fmap_drop fmap_app /=.
    rewrite drop_app_le //. rewrite fmap_length.
    destruct F1 as [?%lookup_fmap_lt_Some _]. lia. }

  iModIntro. iModIntro.
  iDestruct (Nodes_insert _ _ (it1+1) with "Nodes G_n Idx_n Reaped") as "Nodes".
  { destruct_and! F1. destruct (tail_lags_at_most_one CL1 ih1 γ_h1 h1 it1); try lia; done. }
  { apply lookup_lt_Some in Hit. (* [length CL1 > 0] *) lia. }
  iDestruct (Zombies_insert _ ih1 it1 with "Zombies") as "Zombies".
  { destruct F1 as (Hih1 & _). clear -Hih1.  rewrite -list_lookup_fmap in Hih1.
    remember (lookup_lt_Some _ _ _ Hih1) as H. clear HeqH.
    rewrite fmap_length in H. lia. }

  (* close internal inv *)
  iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes Zombies".
  { repeat iExists _. iFrame "∗#%". iPureIntro.
    destruct F1 as (Hih1 & Hit1 & LE). split_and!.
    - eapply prefix_lookup_fmap; [done|by eexists].
    - eapply prefix_lookup_fmap; [done|by eexists].
    - rewrite app_length. simpl. lia. }
  iSpecialize ("N_t" with "Idx_n Info_n").
  iModIntro. iSplitL "t↦ N_t"; [iExists ([_;_]); by iFrame|].
  wp_pures.

  (* Try advancing the tail *)
  wp_apply (try_advance_tail_spec with "[$Inv $S $Idx_t $Info_t $Idx_n $Info_n $◯it]") as (?) "[S _]".

  wp_pures. wp_apply (hazptr.(shield_drop_spec) with "IHD S"); [solve_ndisj|]. auto.
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
              "[AllNodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F1)]".

  iDestruct (get_head_info_from_AllNodes with "AllNodes") as "#Idx_h1"; [by destruct_and! F1|].
  iDestruct (AllNodes_access _ ih1 it1 ih1 with "AllNodes") as "(G_h1 & _ & AllNodes)"; [left; lia | by destruct_and! F1|].

  (* snapshots *)
  iDestruct (mono_list_lb_own_get with "●CL_I") as "#◯CL1".
  iDestruct (mono_nat_lb_own_get with "●ih_I") as "#◯ih1".

  iAaccIntro with "[qu.h↦ G_h1]".
  1: instantiate (1 := [tele_arg (Some _); _; _; _]); iFrame. all: simpl.
  { iIntros "[qu.h↦ G_h1] !>". exfr. by iApply "AllNodes". }
  iIntros "(qu.h↦ & G_h1 & HeadS)".
  (* close internal inv *)
  iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it AllNodes G_h1".
  { iNext. repeat iExists _. iFrame "∗#%". by iApply "AllNodes". }

  iIntros "_". wp_pures.

  (* Read the head's next field. If it's null, commit empty pop. *)
  wp_bind (! _)%E.
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
    wp_seq.
    iApply "HΦ". by iFrame. }

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
              "[AllNodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F3)]".
  iDestruct (get_head_info_from_AllNodes with "AllNodes") as "#Idx_h3"; [by destruct_and! F3|].
  (* Has the head pointer changed since the protection of [h1]? *)
  case (decide (h1 = h3)) as [->|NE_h13]; last first.
  { (* If changed, validation fails *)
    wp_load.
    (* close internal inv *)
    iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it AllNodes"; first by exfr.

    wp_pures.
    rewrite bool_decide_eq_false_2; last by (intro; simplify_eq).
    wp_if. wp_apply ("IH" with "AU HeadS NextS"). }

  wp_load.

  (* Head pointer hasn't changed. [ih1 = ih3] *)
  iDestruct (shield_AllNodes_agree _ _ _ ih3 with "HeadS Idx_h1 AllNodes") as %[<- <-]; [lia | by destruct_and! F3 |].
  (* clean up *)
  iAssert ⌜ih2 = ih3⌝%I as %->; last clear LE_ih12.
  { iDestruct (mono_nat_lb_own_valid with "●ih_I ◯ih2") as %[_ ?]. iPureIntro. lia. }
  iRename "◯ih1" into "◯ih3". iClear "◯ih2".
  (* snapshot *)
  iDestruct (mono_list_lb_own_get with "●CL_I") as "#◯CL3".

  (* The invariant has [Managed] of the next node. *)
  iDestruct (mono_list_auth_idx_lookup with "●CL_I Info_n_h1") as %Hih3'.
  iDestruct (AllNodes_access _ _ _ (ih3+1) with "AllNodes") as "(G_n_h1 & _ & Nodes)"; [lia|..].
  { apply (f_equal (fmap fst)) in Hih3'. simpl in Hih3'. done. }
  (* Validate *)
  iMod (hazptr.(shield_validate) with "IHD G_n_h1 NextS") as "[G_n_h1 NextS]"; [solve_ndisj..|].
  iSpecialize ("Nodes" with "G_n_h1").

  (* close internal inv *)
  iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes"; first by exfr.

  wp_pures. rewrite bool_decide_eq_true_2; [|done]. wp_pures. wp_bind (CmpXchg _ _ _)%E.

  (* Pop CAS *)
  iInv "Inv" as (CL4 h4 γ_h4 ih4 t4 γ_t4 it4)
              "[AllNodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F4)]".

  (* Has the head pointer changed? *)
  case (decide (h3 = h4)) as [->|NE_h34]; last first.
  { wp_cmpxchg_fail.
    (* close internal inv *) iModIntro.
    iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it AllNodes"; first by exfr.
    wp_pures. wp_apply ("IH" with "AU HeadS NextS"). }

  wp_cmpxchg_suc.

  (* Agree *)
  iDestruct (shield_AllNodes_agree _ _ _ ih4 with "HeadS Idx_h3 AllNodes") as %[<- <-]; [lia | by destruct_and! F4 |].
  (* clean up *)
  rename Hih3' into Hih4'. iRename "◯ih3" into "◯ih4".

  (* access AU *)
  iMod "AU" as (xs4) "[Q [_ Commit]]".
  iDestruct "Q" as (???????) "(●CL_Q & ●ih_Q & %Hxs4)".
  encode_agree Hγq.
  (* agree *)
  iDestruct (mono_list_auth_own_agree with "●CL_I ●CL_Q") as %[_ <-].
  iDestruct (mono_nat_auth_own_agree with "●ih_I ●ih_Q") as %[_ <-].
  iDestruct (mono_list_auth_lb_valid with "●CL_I ◯CL3") as %[_ PF_CL34].
  iDestruct (mono_list_lb_own_get with "●CL_I") as "#◯CL4".
  have {}Hih4' := prefix_lookup_Some _ _ _ _ Hih4' PF_CL34.
  (* abstract state *)
  rewrite (drop_S _ _ _ Hih4') -Nat.add_1_r fmap_cons /= in Hxs4.
  (* update *)
  iCombine ("●ih_I ●ih_Q") as "●ih".
  iMod (mono_nat_own_update (ih4+1) with "●ih") as "[[●ih_I ●ih_Q] _]"; [lia|].
  (* snapshots *)
  iDestruct (mono_nat_lb_own_get with "●ih_I") as "#◯ih4'".

  (* unlinked: from inv, get the permission to take managed later *)
  iAssert (node_reaped γ_h4 (1/2) false ∗ AllNodes γz γcl CL4 (ih4 + 1) it4)%I
     with "[AllNodes]" as "[Reap_token AllNodes]".
  { unfold AllNodes. iDestruct "AllNodes" as "[Nodes Zombies]".
    destruct F4 as (Hih4 & ? & ?). unfold Nodes. rewrite !fmap_drop.
    rewrite -list_lookup_fmap in Hih4. rewrite (drop_S _ _ _ Hih4). rewrite big_sepL_cons.
    rewrite Nat.add_0_r. iDestruct "Nodes" as "[(Managed & Idx & Reaped) Nodes]".
    iAssert (node_reaped γ_h4 (1/2) false ∗ node_reaped γ_h4 (1/2) false)%I
      with "[Reaped]" as "[$ Reaped_half]".
    { unfold node_reaped. iDestruct "Reaped" as (γi_p γr_p) "[%Enc [gv1 gv2]]".
      iSplitL "gv1"; iExists _, _; iFrame "%∗". }
    iSplitL "Nodes".
    - iApply (big_sepL_mono' with "Nodes").
      + intros i ?. by replace (ih4 + S i) with (ih4 + 1 + i) by lia.
      + by rewrite -Nat.add_1_r.
    - unfold Zombies. rewrite !fmap_take. replace (ih4 +1) with (S ih4) by lia. rewrite (take_S_r _ _ _ Hih4).
      rewrite big_sepL_app. simpl. iFrame. iSplitL; try done. iExists false. iFrame. iRight.
      rewrite take_length_le; last first.
      { remember (lookup_lt_Some _ _ _ Hih4) as Hl. clear HeqHl.
        remember (length CL4.*1) as l eqn: Eq. rewrite -Eq. lia. }
      rewrite Nat.add_0_r. iFrame.
  }

  (* commit *)
  iMod ("Commit" with "[●CL_Q ●ih_Q]") as "HΦ"; first by (subst xs4; exfr).
  (* close internal inv *)
  iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it AllNodes".
  { repeat iExists _. iFrame "∗#%". iPureIntro. destruct_and! F4. split_and!; try done.
    by apply (f_equal (fmap fst)) in Hih4'. }

  wp_pures. wp_bind (! _)%E.
  (* Read the tail pointer *)
  iInv "Inv" as (CL5 h5 γ_h5 ih5 t5 γ_t5 it5)
              "[AllNodes >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F5)]".

  have Hihit5: (ih5 - 1 ≤ it5) by eapply tail_lags_at_most_one; destruct_and! F5.
  have Hihit5': (ih5 ≤ it5 ∨ (it5 + 1 = ih5 ∧ it5 + 1 = ih5)) by lia.
  (* agree *)
  iDestruct (mono_nat_lb_own_get with "●it") as "#◯it5".
  iDestruct (mono_list_auth_lb_valid with "●CL_I ◯CL4") as %[_ PF_CL45].
  iDestruct (mono_nat_lb_own_valid with "●ih_I ◯ih4'") as %[_ LE_ih45].

  (* If the head guard and the tail pointer value are the same, they point to
  the same logical node. *)
  wp_load.
  iAssert ⌜h4 = t5 → ih4 = it5⌝%I as %Hih4it5.
  { iIntros (->).
    iDestruct (shield_AllNodes_agree with "HeadS Idx_h3 AllNodes") as %[<- <-]; by destruct_and! F5. }


  (* close internal inv *)
  iModIntro. iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it AllNodes"; first by exfr.

  wp_pures. wp_bind (if: _ then _ else _)%E.

  (* Try advancing the tail. *)
  set (fix_tail := (if: #(bool_decide _) then _ else _)%E) in *.
  iAssert (
    {{{ hazptr.(Shield) γz s_h (Validated h4 γ_h4 (node γcl) nodeSize) }}}
      fix_tail
    {{{ v, RET v;
        hazptr.(Shield) γz s_h (Validated h4 γ_h4 (node γcl) nodeSize) ∗
        mono_nat_lb_own γt (ih4+1) }}}
  )%I as "HT_fix_tail".
  { subst fix_tail.
    iIntros (Φ') "!> HeadS HΦ'".
    case (decide (h4 = t5)) as [->|NE_ht].
    - rewrite bool_decide_eq_true_2; last done.
      specialize (Hih4it5 eq_refl) as ->. (* [ih4 = it5] *)
      wp_pures.
      wp_apply (try_advance_tail_spec with "[$Inv $HeadS $Idx_h3 $Info_h1 $Idx_n_h1 $Info_n_h1 $◯it5]") as (?) "[HeadS #◯it5']".

      by iApply ("HΦ'" with "[$HeadS $◯it5']").
    - rewrite bool_decide_eq_false_2; last first.
      { unfold not. intros H. by inversion H. }
     (* ih4(head) ≠ it5 ∧ ih4 <= ih5 - 1 <= it5  →  ih4 + 1 <= it5 *)
      wp_pures.
      have NE_ih4it5 : ih4 ≠ it5.
      { intros ->. destruct F4 as [Hh4 _].
        destruct F5 as (? & Hlookup_it5 & ?).
        have ? := prefix_lookup_fmap _ _ _ _ _ Hh4 PF_CL45.
        congruence. }
      have {LE_ih45 Hihit5 NE_ih4it5}LE_ih4'it5: ih4 + 1 <= it5 by lia.
      iDestruct (mono_nat_lb_own_le _ LE_ih4'it5 with "◯it5") as "#◯it_ih4'".
      iApply ("HΦ'" with "[$HeadS $◯it_ih4']"). }

  wp_apply ("HT_fix_tail" with "[$HeadS]") as (v_clear) "[HeadS #◯it_ih4']".
  wp_seq.
  iClear (fix_tail Hih4it5 v_clear) "HT_fix_tail".

  wp_op. wp_bind (! _)%E.

  (* Read data *)
  iInv "NextS" as (?) "(_ & n_h1↦ & >N_n_h1 & NextS)".
  iDestruct "N_n_h1" as (i_n_h1' x_n_h1' on_n_h1' ->) "(#Idx_n_h1' & #Info_n_h1' & St_n_h1)".
  iDestruct (node_idx_agree with "Idx_n_h1 Idx_n_h1'") as %<-.
  iDestruct (mono_list_idx_agree with "Info_n_h1 Info_n_h1'") as %[= <-].
  iClear "Idx_n_h1' Info_n_h1'".
  wp_apply (wp_load_offset with "n_h1↦") as "n_h1↦"; [by simplify_list_eq|].
  iAssert (node _ n_h1 _ _) with "[St_n_h1]" as "N_n_h1"; first by exfr.
  iSplitL "n_h1↦ N_n_h1"; [iExists ([_;_]); by iFrame|].
  iModIntro. wp_pures.


  (* Take 'Managed' from inv using the reap token. *)
  wp_apply (fupd_wp).
  iInv "Inv" as (CL6 h6 γ_h6 ih6 t6 γ_t6 it6)
  "[[Nodes Zombies] >(●CL_I & qu.h↦ & ●ih_I & qu.t↦ & ●it & %F6)]".
  iDestruct (mono_list_auth_lb_valid with "●CL_I ◯CL4") as %[_ PF_CL46].
  iDestruct (mono_nat_lb_own_valid with "●ih_I ◯ih4'") as %[_ LE_ih46].
  iDestruct (mono_nat_lb_own_valid with "●it ◯it_ih4'") as %[_ LE_ih4it6].

  iDestruct (big_sepL_lookup_acc _ _ ih4 (γ_h4, h4) with "Zombies") as "[[%b (>Rh & Hz)] Zombies]".
  { rewrite fmap_take. rewrite lookup_take; [| lia]. rewrite list_lookup_fmap.
    eapply prefix_lookup_fmap; by destruct_and! F4. }
  iDestruct (node_reaped_agree with "Reap_token Rh") as %<-.
  iDestruct "Hz" as "[[>%contra _] | (G_h6 & _)]"; [done |].
  iMod (node_reaped_update_halves true with "Reap_token Rh") as "[Rh _]".

  (* close *)
  iModIntro.
  iSplitL "●CL_I qu.h↦ ●ih_I qu.t↦ ●it Nodes Zombies Rh".
  { repeat iExists _. iFrame "∗#%". iNext. iApply "Zombies". iExists true. iFrame. iLeft. done. }

  iModIntro. wp_load.
  wp_apply (hazptr.(hazard_domain_retire_spec) with "IHD [$G_h6]") as "_"; [solve_ndisj|].
  wp_pures.
  wp_apply (hazptr.(shield_drop_spec) with "IHD HeadS") as "_"; [solve_ndisj|].
  wp_seq.
  wp_apply (hazptr.(shield_drop_spec) with "IHD NextS") as "_"; [solve_ndisj|].
  wp_pures.
  subst xs4. iApply "HΦ". by iFrame.
Qed.

#[export] Typeclasses Opaque Queue IsQueue.

End dglm_queue.
