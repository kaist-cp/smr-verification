From iris.algebra Require Import excl_auth csum.
From iris.base_logic.lib Require Import invariants token.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr Require Import helpers no_recl.spec_rdcss no_recl.code_rdcss.

Class rdcssG Σ := RdcssG {
  #[local] rdcss_valG :: inG Σ (excl_authR valO);
  #[local] rdcss_tokenG :: tokenG Σ;
  #[local] rdcss_one_shotG :: inG Σ (csumR (exclR unitO) unitR);
}.

Definition rdcssΣ : gFunctors := #[GFunctor (excl_authR valO); tokenΣ; GFunctor (csumR (exclR unitO) unitR)].

Global Instance subG_rdcssΣ {Σ} :
  subG rdcssΣ Σ → rdcssG Σ.
Proof. solve_inG. Qed.

Section rdcss.
Context `{!heapGS Σ, !rdcssG Σ}.
Notation iProp := (iProp Σ).
Context (rdcssN : namespace).
Let descrN := rdcssN .@ "descr".
Let rdcssIntN := rdcssN .@ "rdcss".

(* iExists + iFrame *)
Ltac exfr := repeat (repeat iExists _; iFrame "∗#%").
Ltac exefr := iExists _; eauto 15 with iFrame.

Definition Rdcss_auth γ_n (n : val) : iProp := own γ_n (●E n).

Definition Rdcss γ_n (n : val) : iProp := own γ_n (◯E n).

Lemma sync_values γ_n (n m : val) :
  Rdcss_auth γ_n n -∗ Rdcss γ_n m -∗ ⌜n = m⌝.
Proof.
  iIntros "H● H◯".
  by iCombine "H● H◯" gives %?%excl_auth_agree_L.
Qed.

Lemma update_value γ_n (n1 n2 m : val) :
  Rdcss_auth γ_n n1 -∗ Rdcss γ_n n2 ==∗
    Rdcss_auth γ_n m ∗ Rdcss γ_n m.
Proof.
  iIntros "H● H◯".
  iCombine "H● H◯" as "H".
  iMod (own_update _ _ (●E m ⋅ ◯E m) with "H") as "[$ $]"; [|done].
  { by apply excl_auth_update. }
Qed.

(* Definition of the invariant *)
Definition proph_extract_winner (pvs : list (val * val)) : option proph_id :=
  match pvs with
  | (_, LitV (LitProphecy tid)) :: _ => Some tid
  | _                                => None
  end.

Inductive abstract_state : Set :=
  | Quiescent : val → abstract_state
  | Updating  : loc → loc → val → val → val → proph_id → abstract_state.

Definition state_to_val (s : abstract_state) : val :=
  match s with
  | Quiescent n => InjLV n
  | Updating l_descr _ _ _ _ _ => InjRV #l_descr
  end.

Definition own_token γ := token γ.

Definition pending_state P (n1 : val) (proph_winner : option proph_id) tid_ghost_winner γ_n γ_a : iProp :=
  P ∗ ⌜from_option (λ p, p = tid_ghost_winner) True proph_winner⌝ ∗ Rdcss_auth γ_n n1 ∗ own_token γ_a.

Definition accepted_state Q (proph_winner : option proph_id) (tid_ghost_winner : proph_id) : iProp :=
  (∃ vs, proph tid_ghost_winner vs) ∗ Q ∗ ⌜from_option (λ p, p = tid_ghost_winner) True proph_winner⌝.

Definition done_state Qn l_descr (tid_ghost_winner : proph_id) (γ_t γ_a : gname) : iProp :=
  (Qn ∨ own_token γ_t) ∗
  (∃ vs, proph tid_ghost_winner vs) ∗
  (∃ v, l_descr ↦{# 1/2} v) ∗
  own_token γ_a.

Definition descr_inv P Q p n (l_n l_descr : loc) (tid_ghost_winner : proph_id) γ_n γ_t γ_s γ_a : iProp :=
  ∃ vs,
    proph p vs ∗
    (l_n ↦{# 1/2} (InjRV #l_descr) ∗ own γ_s (Cinl $ Excl ()) ∗
      (pending_state P n (proph_extract_winner vs) tid_ghost_winner γ_n γ_a
       ∨ accepted_state (Q n) (proph_extract_winner vs) tid_ghost_winner)
     ∨ own γ_s (Cinr ()) ∗ done_state (Q n) l_descr tid_ghost_winner γ_t γ_a).

Definition rdcss_au γ_n Q l_m m1 n1 n2 : iProp :=
  AU <{ ∃∃ (m n : val), (l_m ↦_(λ _, True) m) ∗ Rdcss γ_n n }>
    @ ⊤∖(↑rdcssN ∪ ↑inv_heapN),∅
  <{ (l_m ↦_(λ _, True) m) ∗ (Rdcss γ_n (if (decide ((m = m1) ∧ (n = n1))) then n2 else n)), COMM Q n }>.

Definition rdcss_inv (γ_n : gname) (l_n : loc) : iProp :=
  ∃ (st : abstract_state),
    l_n ↦{# 1/2} (state_to_val st) ∗
    match st with
    | Quiescent n =>
      l_n ↦{# 1/2} (InjLV n) ∗ Rdcss_auth γ_n n
    | Updating l_descr l_m m1 n1 n2 p =>
      ∃ q Q tid_ghost_winner (γ_t γ_s γ_a : gname),
        ⌜val_is_unboxed m1⌝ ∗
        l_descr ↦{# 1/2 + q} (#l_m, m1, n1, n2, #p)%V ∗
        inv descrN (descr_inv (rdcss_au γ_n Q l_m m1 n1 n2) Q p n1 l_n l_descr tid_ghost_winner γ_n γ_t γ_s γ_a) ∗
        l_m ↦_(λ _, True) □
    end.

Definition IsRdcss γ_n (l_n : loc) : iProp :=
    (inv rdcssIntN (rdcss_inv γ_n l_n) ∧ inv_heap_inv ∧ ⌜rdcssN ## inv_heapN⌝).

Local Instance Rdcss_auth_Timeless γ_n n : Timeless (Rdcss_auth γ_n n) := _.
Global Instance IsRdcss_Persistent γ_n l_n : Persistent (IsRdcss γ_n l_n) := _.
Global Instance Rdcss_Timeless γ_n n : Timeless (Rdcss γ_n n) := _.
Global Instance abstract_state_inhabited: Inhabited abstract_state := populate (Quiescent #0).

Lemma Rdcss_exclusive γ_n n1 n2 :
  Rdcss γ_n n1 -∗ Rdcss γ_n n2 -∗ False.
Proof.
  iIntros "H● H◯".
  by iCombine "H● H◯" gives %?%excl_auth_frag_op_valid.
Qed.

Lemma state_done_extract_Q P Q p n l_n l_d tid_ghost γ_n γ_t γ_s γ_a :
  inv descrN (descr_inv P Q p n l_n l_d tid_ghost γ_n γ_t γ_s γ_a) -∗
  own γ_s (Cinr ()) -∗
  □(own_token γ_t ={⊤}=∗ ▷ (Q n)).
Proof.
  iIntros "#Hinv #Hs !# Ht".
  iInv descrN as (vs) "(Hp & [NotDone | Done])".
  - iDestruct "NotDone" as "(_ & >Hs' & _)".
    iCombine "Hs Hs'" gives %?. contradiction.
  - iDestruct "Done" as "(_ & QT & Hrest)".
    iDestruct "QT" as "[Qn | >T]"; last first.
    { iCombine "Ht T" gives %Contra. by inversion Contra. }
    iSplitR "Qn"; last done.
    iExists _. iFrame "Hp". iRight. by iFrame "∗#%".
Qed.

Lemma new_rdcss_spec :
  new_rdcss_spec' rdcssN new_rdcss Rdcss IsRdcss.
Proof.
  iIntros (n Hdisj) "#InvGC".
  iIntros (Φ) "!> _ HΦ".
  wp_lam. wp_pures. wp_alloc l_n as "l_n↦" "†l_n".
  do 2 rewrite array_cons. iDestruct "l_n↦" as "(l_n.p↦ & l_n.d↦ & _)".
  wp_pures. rewrite Loc.add_0. wp_store.
  (* Allocate resources for [Rdcss] and [IsRdcss] *)
  iMod (own_alloc (●E n ⋅ ◯E n)) as (γ_n) "[Hn● Hn◯]"; first by apply excl_auth_valid.
  iMod (pointsto_persist with "l_n.d↦") as "#l_n.d↦".
  iMod (inv_alloc rdcssIntN _ (rdcss_inv γ_n l_n) with "[l_n.p↦ Hn●]") as "#InvR".
  { iExists (Quiescent n). iDestruct "l_n.p↦" as "[l_n.p↦ l_n.p'↦]". iFrame "∗#%". }
  iApply "HΦ". by iFrame "∗#%".
Qed.

Lemma complete_succeeding_thread_pending (γ_n γ_t γ_s γ_a : gname) (l_n l_descr l_m : loc) P Q p (m1 n1 n2 n : val) (tid_ghost : proph_id) Φ :
  inv rdcssIntN (rdcss_inv γ_n l_n) -∗
  inv descrN (descr_inv P Q p n1 l_n l_descr tid_ghost γ_n γ_t γ_s γ_a) -∗
  own_token γ_a -∗
  (□(own_token γ_t ={⊤}=∗ ▷ (Q n1)) -∗ Φ #()) -∗
  Rdcss_auth γ_n n -∗
  WP Resolve (CmpXchg #l_n (InjRV #l_descr) (InjLV n)) #p #tid_ghost;; #() {{ v, Φ v }}.
Proof.
  iIntros "#InvR #InvD Token_a HΦ Hn●".
  wp_bind (Resolve _ _ _)%E.
  iInv "InvR" as (st) "(>l_n.p↦ & Hst)".
  iInv "InvD" as (vs) "(>Hp & [NotDone | [#Hs Done]])"; last first.
  { (* [Done] state : contradiction *)
    iDestruct "Done" as "(_ & _ & _ & >Token_a')".
    by iCombine "Token_a Token_a'" gives %?. }
  iDestruct "NotDone" as "(>l_n.p'↦ & >Hs & [Pending | Accepted])".
  { (* [Pending] state : contradiction *)
    iDestruct "Pending" as "[_ >(_ & _ & Token_a')]".
    by iCombine "Token_a Token_a'" gives %?. }
  (* We are in [Accepted] state *)
  destruct st as [n' | l_descr' l_m' m1' n1' n2' p'].
  { simpl. iDestruct (pointsto_agree with "l_n.p↦ l_n.p'↦") as %EQ. inversion EQ. }
  iDestruct (pointsto_agree with "l_n.p↦ l_n.p'↦") as %[= ->]. simpl.
  iCombine "l_n.p↦ l_n.p'↦" as "l_n.p↦".
  wp_apply (wp_resolve with "Hp"); first done. wp_cmpxchg_suc.

  iDestruct "Hst" as (??????) "(%Hn1_unbox & [l_descr↦ _] & _ & #isGC)".
  iIntros "!>" (vs'' ->) "Hp'". simpl.
  (* Update to [Done] *)
  iDestruct "Accepted" as "[Hp_phost_inv [Q Heq]]".
  iMod (own_update _ _ (Cinr ()) with "Hs") as "#Hs"; first by apply cmra_update_exclusive.
  (* Close descr inv *)
  iModIntro. iSplitL "Hp_phost_inv Token_a Q Hp' l_descr↦"; first by exefr.
  (* Close rdcss inv *)
  iModIntro. iSplitR "HΦ".
  { iNext. iDestruct "l_n.p↦" as "[l_n.p↦ l_n.p'↦]". iExists (Quiescent n). iFrame. }
  wp_pures. iApply "HΦ". iModIntro. iApply state_done_extract_Q; done.
Qed.

Lemma complete_failing_thread (γ_n γ_t γ_s γ_a : gname) (l_n l_m l_descr : loc) P Q p (n1 n2 n m1 v : val) tid_ghost_inv tid_ghost Φ :
  tid_ghost_inv ≠ tid_ghost →
  inv rdcssIntN (rdcss_inv γ_n l_n) -∗
  inv descrN (descr_inv P Q p n1 l_n l_descr tid_ghost_inv γ_n γ_t γ_s γ_a) -∗
  (□(own_token γ_t ={⊤}=∗ ▷ (Q n1)) -∗ Φ #()) -∗
  WP Resolve (CmpXchg #l_n (InjRV #l_descr) (InjLV n)) #p #tid_ghost;; #() {{ v, Φ v }}.
Proof.
  iIntros (Hn1) "#InvR #InvD HΦ". wp_bind (Resolve _ _ _)%E.
  iInv "InvR" as (st) "(>l_n.p↦ & Hst)".
  iInv "InvD" as (vs) "(>Hp & [NotDone | [#Hs Done]])".
  { (* In this case, we should succeed CmpXchg --> prophecy was wrong, contradiction *)
    iDestruct "NotDone" as "(>l_n.p'↦ & _ & State)".
    iDestruct (pointsto_agree with "l_n.p↦ l_n.p'↦") as %->.
    iCombine "l_n.p↦ l_n.p'↦" as "l_n.p↦".
    wp_apply (wp_resolve with "Hp"); first done. wp_cmpxchg_suc.
    iIntros "!>" (vs'' ->). simpl.
    iDestruct "State" as "[Pending | Accepted]".
    + iDestruct "Pending" as "[_ [%Hvs _]]". by inversion Hvs.
    + iDestruct "Accepted" as "[_ [_ %Hvs]]". by inversion Hvs. }
  (* [Done] state *)
  destruct st as [n' | l_descr' l_m' m1' n1' n2' p'].
  - (* (InjL n) is the currernt value, hence the CmpXchg fails *)
    wp_apply (wp_resolve with "Hp"); first done. wp_cmpxchg_fail.
    iIntros "!>" (vs'' ->) "Hp".
    iModIntro. iSplitL "Done Hp"; first by exefr.
    iModIntro. iSplitL "l_n.p↦ Hst"; first by exfr.
    wp_pures. iApply "HΦ". iFrame.
    iApply state_done_extract_Q; done.
  - (* (InjR l_descr') is the current value *)
    destruct (decide (l_descr' = l_descr)) as [-> | Hn].
    + (** The [descr] protocol is [done] while still being an active protocol,
          which is a contradiction *)
      iDestruct "Done" as "(_ & _ & >[% l_descr↦] & _)".
      iDestruct "Hst" as (??????) "(_ & >[l_descr'↦ l_descr''↦] & _ & _)".
      iDestruct (pointsto_combine with "l_descr↦ l_descr'↦") as "[l_descr↦ _]".
      rewrite dfrac_op_own Qp.half_half.
      by iDestruct (pointsto_ne with "l_descr↦ l_descr''↦") as %[].
    + (* CmpXchg fails *)
      wp_apply (wp_resolve with "Hp"); first done. wp_cmpxchg_fail.
      iIntros "!>" (vs'' ->) "Hp".
      iModIntro. iSplitL "Done Hp"; first by exefr.
      iModIntro. iSplitL "l_n.p↦ Hst"; first by (iExists _; do 2 iFrame).
      wp_pures. iApply "HΦ". iFrame.
      iApply state_done_extract_Q; done.
Qed.

Lemma complete_spec (l_n l_m l_descr : loc) (m1 n1 n2 : val) p (γ_n γ_t γ_s γ_a : gname) tid_ghost_inv Q q :
  val_is_unboxed m1 →
  rdcssN ## inv_heapN →
  inv rdcssIntN (rdcss_inv γ_n l_n) -∗
  inv descrN (descr_inv (rdcss_au γ_n Q l_m m1 n1 n2) Q p n1 l_n l_descr tid_ghost_inv γ_n γ_t γ_s γ_a ) -∗
  l_m ↦_(λ _, True) □ -∗
  inv_heap_inv -∗
  {{{ l_descr ↦{q} (#l_m, m1, n1, n2, #p) }}}
    complete #l_descr #l_n
    {{{ RET #(); □ (own_token γ_t ={⊤}=∗ ▷(Q n1)) }}}.
Proof.
  iIntros (Hm_unbox Hdisj) "#InvR #InvD #isGC #InvGC !>".
  iIntros (Φ) "l_descr HΦ".
  wp_pures. wp_lam. wp_pure credit:"Hlc". wp_pures. wp_bind (! _)%E.
  rewrite Loc.add_0. wp_load. wp_pures.
  wp_apply (wp_new_proph with "[//]") as (vs_ghost tid_ghost) "Htid_ghost". wp_pures.
  wp_bind (! _)%E.
  (* open outer invariant *)
  iInv "InvR" as (st) "(>l_n.p↦ & Hst)".
  destruct (decide (tid_ghost_inv = tid_ghost)) as [-> | Hnl].
  - (* we are the succeeding thread *)
    iInv "InvD" as (vs) "(>Hp & [(>Hln & >γ_s & [Pending | Accepted]) | [#Hs Done]])".
    + (* Pending: update to accepted *)
      iDestruct "Pending" as "[AU >(Hvs & Hn● & Token_a)]".
      iMod (lc_fupd_elim_later with "Hlc AU") as "AU".
      iMod (inv_pointsto_own_acc_strong with "InvGC") as "Hgc"; first solve_ndisj.
      (* open and commit AU, sync B location l_n and A location l_m *)
      iMod "AU" as (m' n') "[CC [_ Hclose]]".
      iDestruct "CC" as "[Hgc_lm Hn◯]".
      iDestruct (sync_values with "Hn● Hn◯") as %->.
      iMod (update_value _ _ _ (if decide (m' = m1 ∧ n' = n') then n2 else n') with "Hn● Hn◯") as "[Hn● Hn◯]".
      (* get access to A location *)
      iDestruct ("Hgc" with "Hgc_lm") as "(_ & Hl & Hgc_close)".
      (* read A location *)
      wp_load.
      (* sync A location *)
      iMod ("Hgc_close" with "[//] Hl") as "[Hgc_lm Hgc_close]".
      (* give back access to A location *)
      iMod ("Hclose" with "[Hn◯ $Hgc_lm]") as "Q"; first done.
      iModIntro. iMod "Hgc_close" as "_".
      (* close descr inv *)
      do 2 iModIntro. iSplitL "Q Htid_ghost Hp Hvs γ_s Hln"; first by exefr.
      (* close outer inv *)
      iSplitR "Token_a HΦ Hn●"; first by exfr.

      iModIntro.
      destruct (decide (m' = m1)) as [-> | ?]; wp_op;
      case_bool_decide; simplify_eq; wp_if; wp_pures;
      iApply (complete_succeeding_thread_pending with "InvR InvD Token_a HΦ"); try done.
      * rewrite decide_True; done.
      * rewrite decide_False; naive_solver.
    + (* Accepted : contradiction *)
      iDestruct "Accepted" as "[>Htid_ghost_inv _]".
      iDestruct "Htid_ghost_inv" as (?) "Htid_ghost_inv".
      by iDestruct (proph_exclusive with "Htid_ghost Htid_ghost_inv") as %?.
    + (* Done : contradiction *)
      iDestruct "Done" as "[_ >[Htid_ghost_inv _]]".
      iDestruct "Htid_ghost_inv" as (?) "Htid_ghost_inv".
      by iDestruct (proph_exclusive with "Htid_ghost Htid_ghost_inv") as %?.
  - (* we are failing thread *)
    (* close invariant *)
    iMod (inv_pointsto_acc with "InvGC isGC") as (v) "(_ & Hlm & Hclose)"; first solve_ndisj.
    wp_load. iMod ("Hclose" with "Hlm") as "_".
    do 2 iModIntro. iSplitL "l_n.p↦ Hst"; first by exfr.
    wp_pures. case_bool_decide; wp_pures.
    all: iApply (complete_failing_thread with "InvR InvD HΦ"); done.
Qed.

Lemma get_spec :
  get_spec' rdcssN get Rdcss IsRdcss.
Proof.
  iIntros (γ l_n).
  iDestruct 1 as "(#InvR & #InvGC & %Hdisj)".
  iIntros (Φ) "AU". iLöb as "IH".
  wp_lam. wp_bind (! _)%E.
  iInv "InvR" as (st) "(>l_n.p↦ & Hst)".
  wp_load.
  destruct st as [n | l_descr l_m m1 n1 n2 p].
  - iMod "AU" as (au_n) "[Hn◯ [_ Hclose]]".
    iDestruct "Hst" as "[l_n.p'↦ Hn●]".
    iDestruct (sync_values with "Hn● Hn◯") as %->.
    iMod ("Hclose" with "Hn◯") as "HΦ".
    iModIntro. iSplitR "HΦ"; first by exfr.
    wp_pures. by iApply "HΦ".
  - iDestruct "Hst" as (q Q tid_ghost γ_t γ_s γ_a) "(% & [l_descr↦ [l_descr'↦ l_descr''↦]] & #InvD & #GC)".
    iModIntro. iSplitR "AU l_descr'↦"; first by exfr.
    wp_pures. wp_apply (complete_spec with "InvR InvD GC InvGC l_descr'↦") as "_"; try done.
    wp_pures. by iApply "IH".
Qed.

Lemma rdcss_spec :
  rdcss_spec' rdcssN rdcss Rdcss IsRdcss.
Proof.
  iIntros (γ l_n l_m m1 n1 n2 Hn1_unbox Hm1_unbox).
  iDestruct 1 as "(#InvR & #InvGC & %Hdisj)".
  iIntros (Φ) "AU".
  wp_lam. wp_pures.
  wp_apply (wp_new_proph with "[//]") as (proph_values p) "Hp". wp_pures.
  wp_alloc l_descr as "l_descr↦" "†l_descr". wp_pures.
  iLöb as "IH".
  wp_bind (CmpXchg _ _ _)%E.
  iInv "InvR" as (st) "(>l_n.p↦ & Hst)".
  destruct st as [n | l_descr' l_m' m1' n1' n2' p'].
  - (* l_n ↦ InjL n *)
    iDestruct "Hst" as ">[l_n.p'↦ Hn●]".
    destruct (decide (n1 = n)) as [<- | NEQ].
    + iCombine "l_n.p↦ l_n.p'↦" as "l_n.p↦".
      wp_cmpxchg_suc.
      (* Take a "peek" at [AU] and abort immediately to get [gc_is_gc f]. *)
      iMod "AU" as (b' n') "[[Hf CC] [Hclose _]]".
      iDestruct (inv_pointsto_own_inv with "Hf") as "#Hgc".
      iMod ("Hclose" with "[Hf CC]") as "AU"; first by iFrame.
      (* Initialize new [descr] protocol .*)
      iMod token_alloc as (γ_t) "Token_t".
      iMod token_alloc as (γ_a) "Token_a".
      iMod (own_alloc (Cinl $ Excl ())) as (γ_s) "Hs"; first done.
      iDestruct "l_n.p↦" as "[l_n.p↦ l_n.p'↦]".
      set (winner := default p (proph_extract_winner proph_values)).
      iMod (inv_alloc descrN _ (descr_inv _ _ _ _ _ _ winner _ _ _ _)
            with "[AU Hs Hp l_n.p'↦ Hn● Token_a]") as "#InvD".
      { iExists _. iFrame "Hp". iLeft. iFrame. iLeft.
        iFrame. destruct (proph_extract_winner proph_values); simpl; (iSplit; last done); iExact "AU". }
      (* Close invariant *)
      iModIntro.
      iDestruct "l_descr↦" as "[l_descr↦ [l_descr'↦ l_descr''↦]]". rewrite !array_singleton.
      iSplitR "Token_t l_descr''↦".
      { (* close outer invariant *)
        iExists (Updating l_descr l_m m1 n1 n2 p). iFrame. exfr. }
      wp_pures. wp_apply (complete_spec with "InvR InvD Hgc InvGC l_descr''↦") as "Ht"; try done.
      iMod ("Ht" with "Token_t") as "HΦ".
      wp_pures. by iApply "HΦ".
    + (* values do not match --> CmpXchg fails, and we can commit here *)
      wp_cmpxchg_fail.
      iMod "AU" as (m'' n'') "[[Hm◯ Hn◯] [_ Hclose]]". simpl.
      iDestruct (sync_values with "Hn● Hn◯") as %<-.
      iMod ("Hclose" with "[Hm◯ Hn◯]") as "HΦ".
      { rewrite decide_False; [|naive_solver]. iFrame. }
      iModIntro. iSplitR "l_descr↦ †l_descr HΦ".
      { iExists (Quiescent n). iFrame. }
      wp_free; [done|]. by iApply "HΦ".
  - (* l_n ↦ InjR l_descr' --> helping *)
    wp_cmpxchg_fail.
    iDestruct "Hst" as (q Q tid_ghost γ_t γ_s γ_a) "(%Hm1'_unbox & [l_descr'↦ [l_descr''↦ l_descr'''↦]] & #InvD & #P_GC)".
    iModIntro. iSplitR "AU Hp l_descr↦ †l_descr l_descr'''↦".
    { iExists (Updating l_descr' l_m' m1' n1' n2' p'). iFrame.
      repeat iExists _. iFrame "∗#%". }
    wp_pures. wp_apply (complete_spec with "InvR InvD P_GC InvGC l_descr'''↦") as "_"; try done.
    wp_pures. iApply ("IH" with "AU Hp l_descr↦ †l_descr").
Qed.

#[export] Typeclasses Opaque Rdcss IsRdcss.

End rdcss.
