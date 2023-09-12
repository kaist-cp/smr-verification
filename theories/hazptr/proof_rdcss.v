From iris.algebra Require Import excl agree csum.
From iris.base_logic.lib Require Import invariants ghost_var ghost_map.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr Require Import helpers hazptr.spec_hazptr hazptr.spec_rdcss hazptr.code_rdcss.

Class rdcssG Σ := RdcssG {
  rdcss_valG :> inG Σ (authR $ optionUR $ exclR $ valO);
  rdcss_tokenG :> inG Σ (exclR unitO);
  rdcss_one_shotG :> inG Σ (csumR (exclR unitO) (agreeR unitO));
  rdcss_managed_valG :> inG Σ (agreeR valO);
  rdcss_managed_gvarG :> ghost_varG Σ unit;
}.

Definition rdcssΣ : gFunctors := #[GFunctor (authR $ optionUR $ exclR $ valO); GFunctor (exclR unitO); GFunctor (csumR (exclR unitO) (agreeR unitO)); GFunctor (agreeR valO); ghost_varΣ unit].

Global Instance subG_rdcssΣ {Σ} :
  subG rdcssΣ Σ → rdcssG Σ.
Proof. solve_inG. Qed.

Section rdcss.
Context `{!heapGS Σ, !rdcssG Σ}.
Notation iProp := (iProp Σ).
Context (rdcssN hazptrN : namespace) (DISJN : hazptrN ## rdcssN).
Let descrN := rdcssN .@ "descr".
Let rdcssIntN := rdcssN .@ "rdcss".

(* iExists + iFrame *)
Ltac exfr := repeat (repeat iExists _; iFrame "∗#%").
Ltac exefr := iExists _; eauto 15 with iFrame.

Variable (hazptr : hazard_pointer_spec Σ hazptrN).

Definition Rdcss_auth γ (n : val) : iProp :=
  ∃ (γ_z γ_n : gname), ⌜γ = encode (γ_z, γ_n)⌝ ∗ own γ_n (● Excl' n).

Definition Rdcss γ (n : val) : iProp :=
  ∃ (γ_z γ_n : gname), ⌜γ = encode (γ_z, γ_n)⌝ ∗ own γ_n (◯ Excl' n).

Lemma sync_values γ (n m : val) :
  Rdcss_auth γ n -∗ Rdcss γ m -∗ ⌜n = m⌝.
Proof.
  iIntros "H● H◯".
  iDestruct "H●" as (?? Hγ) "H●".
  iDestruct "H◯" as (?? Hγ') "H◯".
  encode_agree Hγ.
  iCombine "H● H◯" as "H".
  by iDestruct (own_valid with "H") as %[?%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
Qed.

Lemma update_value γ (n1 n2 m : val) :
  Rdcss_auth γ n1 -∗ Rdcss γ n2 ==∗
    Rdcss_auth γ m ∗ Rdcss γ m.
Proof.
  iIntros "H● H◯".
  iDestruct "H●" as (?? Hγ) "H●".
  iDestruct "H◯" as (?? Hγ') "H◯".
  encode_agree Hγ.
  iCombine "H● H◯" as "H".
  iMod (own_update _ _ (● Excl' m ⋅ ◯ Excl' m) with "H") as "[H● H◯]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  iModIntro. iSplitL "H●"; repeat iExists _; iFrame "∗#%".
Qed.

(* Definition of the invariant *)
Definition proph_extract_winner (pvs : list (val * val)) : option proph_id :=
  match pvs with
  | (_, LitV (LitProphecy tid)) :: _ => Some tid
  | _                                => None
  end.

Inductive abstract_state : Set :=
  | Quiescent : val → abstract_state
  | Updating  : blk → loc → val → val → val → proph_id → abstract_state.

Definition state_to_val (s : abstract_state) : val :=
  match s with
  | Quiescent n => InjLV n
  | Updating l_descr _ _ _ _ _ => InjRV #l_descr
  end.

Definition own_token γ := (own γ (Excl ()))%I.

Definition pending_state P (n1 : val) (proph_winner : option proph_id) tid_ghost_winner γ γ_a : iProp :=
  P ∗ ⌜from_option (λ p, p = tid_ghost_winner) True proph_winner⌝ ∗ Rdcss_auth γ n1 ∗ own_token γ_a.

Definition accepted_state Q (proph_winner : option proph_id) (tid_ghost_winner : proph_id) : iProp :=
  (∃ vs, proph tid_ghost_winner vs) ∗ Q ∗ ⌜from_option (λ p, p = tid_ghost_winner) True proph_winner⌝.

Definition done_state Qn (tid_ghost_winner : proph_id) (γ_t γ_a γ_d : gname) : iProp :=
  (Qn ∨ own_token γ_t) ∗
  (∃ vs, proph tid_ghost_winner vs) ∗
  (∃ (γ_dv γ_dq : gname), ⌜γ_d = encode (γ_dv, γ_dq)⌝ ∗ ghost_var γ_dq (1/2)%Qp ()) ∗
  own_token γ_a.

Definition descr_inv P Q p n (l_n l_d : loc) (tid_ghost_winner : proph_id) γ γ_t γ_s γ_a γ_d : iProp :=
  ∃ vs,
    proph p vs ∗
    (l_n ↦{# 1/2} (InjRV #l_d) ∗ own γ_s (Cinl $ Excl ()) ∗
      (pending_state P n (proph_extract_winner vs) tid_ghost_winner γ γ_a
       ∨ accepted_state (Q n) (proph_extract_winner vs) tid_ghost_winner)
     ∨ own γ_s (Cinr $ to_agree ()) ∗ done_state (Q n) tid_ghost_winner γ_t γ_a γ_d).

Definition rdcss_au γ Q l_m m1 n1 n2 : iProp :=
  AU << ∃∃ (m n : val), (l_m ↦_(λ _, True) m) ∗ Rdcss γ n >>
    @ ⊤∖(↑rdcssN ∪ ↑ptrsN hazptrN ∪ ↑inv_heapN),↑mgmtN hazptrN
  << (l_m ↦_(λ _, True) m) ∗ (Rdcss γ (if (decide ((m = m1) ∧ (n = n1))) then n2 else n)), COMM Q n >>.

Definition node (p : loc) lv γ_p : iProp :=
  ∃ (l_m : loc) (m1 n1 n2 : val) (pid : proph_id) (γ_pv γ_pq : gname),
    ⌜γ_p = encode (γ_pv, γ_pq)⌝ ∗
    ⌜lv = [ (#l_m, m1, n1, n2, #pid)%V ]⌝ ∗
    own γ_pv (to_agree (#l_m, m1, n1, n2, #pid)%V).

Definition rdcss_inv (γ γ_z γ_n : gname) (l_n : loc) : iProp :=
  ∃ (st : abstract_state),
    l_n ↦{# 1/2} (state_to_val st) ∗
    match st with
    | Quiescent n =>
      l_n ↦{# 1/2} (InjLV n) ∗ Rdcss_auth γ n
    | Updating l_descr l_m m1 n1 n2 p =>
      ∃ q Q tid_ghost_winner (γ_d γ_dv γ_dq γ_t γ_s γ_a : gname),
        ⌜val_is_unboxed m1⌝ ∗
        ⌜γ_d = encode (γ_dv, γ_dq)⌝ ∗
        hazptr.(Managed) γ_z l_descr γ_d 1 node ∗
        own γ_dv (to_agree (#l_m, m1, n1, n2, #p)%V) ∗
        ghost_var γ_dq (1/2 + q)%Qp () ∗
        inv descrN (descr_inv (rdcss_au γ Q l_m m1 n1 n2) Q p n1 l_n l_descr tid_ghost_winner γ γ_t γ_s γ_a γ_d) ∗
        l_m ↦_(λ _, True) □
    end.

Definition IsRdcss γ (l_n : loc) : iProp :=
  ∃ (γ_z γ_n : gname) (d : loc),
    ⌜γ = encode (γ_z, γ_n)⌝ ∗
    (l_n +ₗ 1) ↦□ #d ∗ hazptr.(IsHazardDomain) γ_z d ∗
    (inv rdcssIntN (rdcss_inv γ γ_z γ_n l_n) ∧ inv_heap_inv ∧ ⌜rdcssN ## inv_heapN⌝).

Local Instance Rdcss_auth_Timeless γ n : Timeless (Rdcss_auth γ n) := _.
Global Instance IsRdcss_Persistent γ l_n : Persistent (IsRdcss γ l_n) := _.
Global Instance Rdcss_Timeless γ n : Timeless (Rdcss γ n) := _.
Global Instance abstract_state_inhabited: Inhabited abstract_state := populate (Quiescent #0).

Lemma Rdcss_exclusive γ n1 n2 :
  Rdcss γ n1 -∗ Rdcss γ n2 -∗ False.
Proof.
  iIntros "H● H◯".
  iDestruct "H●" as (?? Hγ) "H●".
  iDestruct "H◯" as (?? Hγ') "H◯".
  encode_agree Hγ.
  by iCombine "H● H◯" gives %?%auth_frag_op_valid_1.
Qed.

Lemma state_done_extract_Q P Q p n l_n l_d tid_ghost γ γ_t γ_s γ_a γ_d :
  inv descrN (descr_inv P Q p n l_n l_d tid_ghost γ γ_t γ_s γ_a γ_d) -∗
  own γ_s (Cinr (to_agree ())) -∗
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
  new_rdcss_spec' rdcssN hazptrN new_rdcss hazptr Rdcss IsRdcss.
Proof.
  iIntros (γ_z d n Hdisj) "#InvGC".
  iIntros (Φ) "!> #IHD HΦ".
  wp_lam. wp_pures. wp_alloc l_n as "l_n↦" "†l_n".
  do 2 rewrite array_cons. iDestruct "l_n↦" as "(l_n.p↦ & l_n.d↦ & _)".
  wp_pures. rewrite loc_add_0. wp_store. wp_pures. wp_store.
  (* Allocate resources for [Rdcss] and [IsRdcss] *)
  iMod (own_alloc (● Excl' n ⋅ ◯ Excl' n)) as (γ_n) "[Hn● Hn◯]"; first by apply auth_both_valid_discrete.
  remember (encode (γ_z, γ_n)) as γ eqn:Hγ.
  iMod (mapsto_persist with "l_n.d↦") as "#l_n.d↦".
  iMod (inv_alloc rdcssIntN _ (rdcss_inv γ γ_z γ_n l_n) with "[l_n.p↦ Hn●]") as "#InvR".
  { iExists (Quiescent n). iDestruct "l_n.p↦" as "[l_n.p↦ l_n.p'↦]". exfr. }
  iApply ("HΦ" $! γ). iModIntro. iFrame "∗#%".
  iSplitR; repeat iExists _; by iFrame "∗#%".
Qed.

Lemma complete_succeeding_thread_pending (γ γ_z γ_n γ_t γ_s γ_a γ_d γ_dq γ_dv : gname) (l_n l_dom l_m s : loc) (l_descr : blk) P Q p (m1 n1 n2 n : val) (tid_ghost : proph_id) Φ :
  γ = encode (γ_z, γ_n) →
  γ_d = encode (γ_dv, γ_dq) →
  inv rdcssIntN (rdcss_inv γ γ_z γ_n l_n) -∗
  inv descrN (descr_inv P Q p n1 l_n l_descr tid_ghost γ γ_t γ_s γ_a γ_d) -∗
  hazptr.(IsHazardDomain) γ_z l_dom -∗
  hazptr.(Shield) γ_z s (Validated l_descr γ_d node 1) -∗
  own γ_dv (to_agree (#l_m, m1, n1, n2, #p)%V) -∗
  own_token γ_a -∗
  (□(own_token γ_t ={⊤}=∗ ▷ (Q n1)) ∗ hazptr.(Shield) γ_z s (Validated l_descr γ_d node 1) -∗ Φ #()) -∗
  Rdcss_auth γ n -∗
  WP let: "r" := Resolve (CmpXchg #l_n (InjRV #l_descr) (InjLV n)) #p #tid_ghost in
     if: Snd "r" then hazard_domain_retire hazptr #l_dom #l_descr #1%nat
     else #() {{ v, Φ v }}.
Proof using DISJN.
  iIntros (Hγ Hγ_d) "#InvR #InvD #IHD S #γ_dv Token_a HΦ Hn●". wp_bind (Resolve _ _ _)%E.
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
  { simpl. iDestruct (mapsto_agree with "l_n.p↦ l_n.p'↦") as %EQ. inversion EQ. }
  iDestruct (mapsto_agree with "l_n.p↦ l_n.p'↦") as %[= ->].
  iCombine "l_n.p↦ l_n.p'↦" as "l_n.p↦".
  wp_apply (wp_resolve with "Hp"); first done. wp_cmpxchg_suc.
  iDestruct "Hst" as (?????????) "(%Hm1'_unbox & %Hγ_d' & G_l_descr & #γ_dv' & γ_dq & #InvD' & #isGC)".
  iDestruct (hazptr.(shield_managed_agree) with "S G_l_descr") as %<-.
  encode_agree Hγ_d.
  iCombine "γ_dv γ_dv'" gives %[= <- <- <- <- <-]%to_agree_op_inv_L. iClear "γ_dv'".
  iIntros "!>" (vs'' ->) "Hp'". simpl.
  (* Update to [Done] *)
  iDestruct "Accepted" as "[Hp_phost_inv [Q Heq]]".
  iMod (own_update with "Hs") as "Hs"; first by apply (cmra_update_exclusive (Cinr (to_agree ()))).
  iDestruct "Hs" as "#Hs'". iDestruct "γ_dq" as "[γ_dq _]".
  (* Close descr inv *)
  iModIntro. iSplitL "Hp_phost_inv Token_a Q Hp' γ_dq"; first by exefr.
  (* Close rdcss inv *)
  iModIntro. iSplitR "HΦ G_l_descr S".
  { iExists (Quiescent n). iDestruct "l_n.p↦" as "[l_n.p↦ l_n.p'↦]". iFrame "∗#%". }
  wp_pures.
  wp_apply (hazptr.(hazard_domain_retire_spec) with "IHD G_l_descr") as "_"; [solve_ndisj|].
  iApply "HΦ". iFrame.
  iApply state_done_extract_Q; done.
Qed.

Lemma complete_failing_thread (γ γ_z γ_n γ_t γ_s γ_a γ_d γ_dv γ_dq : gname) (l_n l_m l_dom s : loc) (l_descr : blk) P Q p (n1 n2 n m1 v : val) tid_ghost_inv tid_ghost Φ :
  γ = encode (γ_z, γ_n) →
  γ_d = encode (γ_dv, γ_dq) →
  tid_ghost_inv ≠ tid_ghost →
  inv rdcssIntN (rdcss_inv γ γ_z γ_n l_n) -∗
  inv descrN (descr_inv P Q p n1 l_n l_descr tid_ghost_inv γ γ_t γ_s γ_a γ_d) -∗
  hazptr.(IsHazardDomain) γ_z l_dom -∗
  hazptr.(Shield) γ_z s (Validated l_descr γ_d node 1) -∗
  own γ_dv (to_agree (#l_m, m1, n1, n2, #p)%V) -∗
  (□(own_token γ_t ={⊤}=∗ ▷ (Q n1)) ∗ hazptr.(Shield) γ_z s (Validated l_descr γ_d node 1) -∗ Φ #()) -∗
  WP let: "r" := Resolve (CmpXchg #l_n (InjRV #l_descr) (InjLV n)) #p #tid_ghost in
     if: Snd "r" then hazard_domain_retire hazptr #l_dom #l_descr #1%nat
     else #() {{ v, Φ v }}.
Proof.
  iIntros (Hγ Hγ_d Hn1) "#InvR #InvD #IHD S #γ_dv HΦ". wp_bind (Resolve _ _ _)%E.
  iInv "InvR" as (st) "(>l_n.p↦ & Hst)".
  iInv "InvD" as (vs) "(>Hp & [NotDone | [#Hs Done]])".
  { (* In this case, we should succeed CmpXchg --> prophecy was wrong, contradiction *)
    iDestruct "NotDone" as "(>l_n.p'↦ & _ & State)".
    iDestruct (mapsto_agree with "l_n.p↦ l_n.p'↦") as %->.
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
      iDestruct "Done" as "(_ & _ & >Hld & _)".
      iDestruct "Hld" as (???) "γ_dq".
      iDestruct "Hst" as (?????????) "(_ & >% & M & _ & >γ_dq' & _)".
      iDestruct (hazptr.(shield_managed_agree) with "S M") as "#><-".
      do 2 encode_agree Hγ_d.
      iDestruct (ghost_var_valid_2 with "γ_dq γ_dq'") as %[H _].
      rewrite Qp.add_assoc Qp.half_half in H.
      by apply Qp.not_add_le_l in H.
    + (* CmpXchg fails *)
      wp_apply (wp_resolve with "Hp"); first done. wp_cmpxchg_fail.
      iIntros "!>" (vs'' ->) "Hp".
      iModIntro. iSplitL "Done Hp"; first by exefr.
      iModIntro. iSplitL "l_n.p↦ Hst".
      { iExists _. do 2 iFrame. }
      wp_pures. iApply "HΦ". iFrame.
      iApply state_done_extract_Q; done.
Qed.

Lemma complete_spec (l_n l_m l_dom s : loc) (l_descr : blk) (m1 n1 n2 : val) p (γ γ_z γ_n γ_t γ_s γ_a γ_d γ_dv γ_dq : gname) tid_ghost_inv Q :
  val_is_unboxed m1 →
  rdcssN ## inv_heapN →
  γ = encode (γ_z, γ_n) →
  γ_d = encode (γ_dv, γ_dq) →
  inv rdcssIntN (rdcss_inv γ γ_z γ_n l_n) -∗
  inv descrN (descr_inv (rdcss_au γ Q l_m m1 n1 n2) Q p n1 l_n l_descr tid_ghost_inv γ γ_t γ_s γ_a γ_d) -∗
  hazptr.(IsHazardDomain) γ_z l_dom -∗
  l_m ↦_(λ _, True) □ -∗
  inv_heap_inv -∗
  {{{ hazptr.(Shield) γ_z s (Validated l_descr γ_d node 1) ∗
      own γ_dv (to_agree (#l_m, m1, n1, n2, #p)%V) }}}
    (complete hazptr) #l_descr #l_n #l_dom
  {{{ RET #(); □ (own_token γ_t ={⊤}=∗ ▷(Q n1)) ∗ hazptr.(Shield) γ_z s (Validated l_descr γ_d node 1) }}}.
Proof using DISJN.
  iIntros (Hm_unbox Hdisj Hγ Hγ_d) "#InvR #InvD #IHD #isGC #InvGC !>".
  iIntros (Φ) "(S & #γ_dv) HΦ".
  wp_pures. wp_lam. wp_pure credit:"Hlc". wp_pures.
  wp_apply (shield_read with "S") as (??) "(S & Hnode & %EQ)"; [solve_ndisj|lia|].
  iDestruct "Hnode" as (???????) "(% & -> & γ_dv')".
  encode_agree Hγ_d. injection EQ as [= <-].
  iCombine "γ_dv γ_dv'" gives %[= <- <- <- <- <-]%to_agree_op_inv_L. iClear "γ_dv'".
  wp_pures. wp_apply (wp_new_proph with "[//]") as (vs_ghost tid_ghost) "Htid_ghost". wp_pures.
  wp_bind (! _)%E.
  (* open outer invariant *)
  iInv "InvR" as (st) "(>l_n.p↦ & Hst)".
  destruct (decide (tid_ghost_inv = tid_ghost)) as [-> | Hnl].
  - (* we are the succeeding thread *)
    iInv "InvD" as (vs) "(>Hp & [(>l_n.p'↦ & >γ_s & [Pending | Accepted]) | [#Hs Done]])".
    + (* Pending: update to accepted *)
      iDestruct "Pending" as "[AU >(Hvs & Hn● & Token_a)]".
      iMod (lc_fupd_elim_later with "Hlc AU") as "AU".
      iMod (inv_mapsto_own_acc_strong with "InvGC") as "Hgc"; first solve_ndisj.
      (* open and commit AU, sync B location l_n and A location l_m *)
      iMod "AU" as (m' n') "[CC [_ Hclose]]"; [solve [eauto 15 with ndisj]|].
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
      do 2 iModIntro. iSplitL "Q Htid_ghost Hp Hvs γ_s l_n.p'↦"; first by exefr.
      (* close outer inv *)
      iSplitR "Token_a HΦ Hn● S"; first by exfr.

      iModIntro.
      destruct (decide (m' = m1)) as [-> | ?]; wp_op;
      case_bool_decide; simplify_eq; wp_if; wp_pures;
      iApply (complete_succeeding_thread_pending with "InvR InvD IHD S γ_dv Token_a HΦ [Hn●]");
      try done.
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
    iMod (inv_mapsto_acc with "InvGC isGC") as (v) "(_ & Hlm & Hclose)"; first solve_ndisj.
    wp_load. iMod ("Hclose" with "Hlm") as "_".
    do 2 iModIntro. iSplitL "l_n.p↦ Hst"; first by exfr.
    wp_pures. case_bool_decide; wp_pures.
    all: iApply (complete_failing_thread with "InvR InvD IHD S γ_dv HΦ"); try done.
Qed.

Lemma get_spec :
  get_spec' rdcssN hazptrN (get hazptr) Rdcss IsRdcss.
Proof using DISJN.
  iIntros (γ l_n).
  iDestruct 1 as (γ_z γ_n d) "(%Hγ & #l_n.d↦ & #IHD & #InvR & #InvGC & %Hdisj)".
  iIntros (Φ) "AU".
  iLöb as "IH".
  wp_lam. wp_pures. wp_load. wp_pures. wp_bind (! _)%E.
  iInv "InvR" as (st) "(>l_n.p↦ & Hst)".
  wp_load.
  destruct st as [n | l_descr l_m m1 n1 n2 p].
  - (* We found real value : here is commit point *)
    iDestruct "Hst" as "[l_n.p'↦ H●]".
    iMod "AU" as (au_n) "[H◯ [_ Hclose]]".
    iDestruct (sync_values with "H● H◯") as %<-.
    iMod ("Hclose" with "H◯") as "HΦ".
    (* close the invariant *)
    iModIntro. iSplitL "l_n.p↦ l_n.p'↦ H●"; first by exfr.
    wp_pures. by iApply "HΦ".
  - (* We found descriptor *)
    iDestruct "Hst" as (q Q tid_ghost γ_d γ_dv γ_dq γ_t γ_s γ_a) "(%Hm_unbox & %Hγ_d & M & #γ_dv & γ_dq & #InvD & #GC)".
    (* Close the invariant *)
    iModIntro. iSplitL "l_n.p↦ γ_dq M"; first by exfr.
    (* Protect the descriptor before access, with validation *)
    wp_pures. wp_apply (hazptr.(shield_new_spec) with "IHD [//]") as (s) "S"; [solve_ndisj|].
    wp_pures.
    wp_apply (hazptr.(shield_set_spec) (Some _) with "IHD S") as "S"; [solve_ndisj|].
    wp_pures. wp_bind (! _)%E.
    (* Validation *)
    iInv "InvR" as (st) "(>l_n.p↦ & Hst)".
    wp_load. iClear "InvD γ_dv GC". clear l_m Hm_unbox m1 n1 n2 p Hγ_d γ_d γ_dv γ_dq.
    destruct st as [n' | l_descr' l_m m1 n1 n2 p].
    + (* Read [InjLV n] --> validation failed *)
      iModIntro. iSplitL "l_n.p↦ Hst"; first by exfr.
      wp_pures. wp_apply (hazptr.(shield_drop_spec) with "IHD S") as "_"; [solve_ndisj|].
      wp_pures. by iApply "IH".
    + (* Read [InjRV descr'], check whether [descr = descr'] holds *)
      destruct (decide (l_descr = l_descr')) as [<-|NEQ].
      * (* Same descriptor --> validation success *)
        iDestruct "Hst" as (?????????) "(%Hm1_unbox & %Hγ_d & G_l_descr & #γ_dv & γ_dq & #InvD & #GC)".
        iMod (hazptr.(shield_validate) with "IHD G_l_descr S") as "[G_l_descr S]"; [solve_ndisj|].
        iModIntro. iSplitR "AU S"; first by exfr.
        wp_pures. case_bool_decide; last contradiction.
        wp_pures. wp_apply (complete_spec with "InvR InvD IHD GC InvGC [$S $γ_dv]"); try done.
        iIntros "[_ S]". wp_pures.
        wp_apply (hazptr.(shield_drop_spec) with "IHD S") as "_"; [solve_ndisj|].
        wp_pures. by iApply "IH".
      * (* Different descriptor --> validation failed *)
        iModIntro. iSplitR "AU S".
        { repeat iExists _. do 2 iFrame. }
        wp_pures. case_bool_decide.
        { inversion H as [H1]. symmetry in H1. contradiction. }
        wp_pures. wp_apply (hazptr.(shield_drop_spec) with "IHD S") as "_"; [solve_ndisj|].
        wp_pures. by iApply "IH".
Qed.

Lemma rdcss_spec :
  rdcss_spec' rdcssN hazptrN (rdcss hazptr) Rdcss IsRdcss.
Proof using DISJN.
  iIntros (γ l_n l_m m1 n1 n2 Hn1_unbox Hm1_unbox).
  iDestruct 1 as (γ_z γ_n d) "(%Hγ & #l_n.d↦ & #IHD & #InvR & #InvGC & %Hdisj)".
  iIntros (Φ) "AU".
  wp_lam. wp_pures. wp_load. wp_let.
  wp_apply (hazptr.(shield_new_spec) with "IHD [//]") as (s_descr) "S_descr"; [solve_ndisj|].
  wp_let.
  wp_apply (wp_new_proph with "[//]") as (proph_values p) "Hp".
  wp_pures.
  wp_alloc l_descr as "l_descr↦" "†l_descr". wp_let.

  (* Create a new [managed] for descriptor *)
  iMod (own_alloc (to_agree (#l_m, m1, n1, n2, #p)%V)) as (γ_dv) "#γ_dv"; [done|].
  iMod (ghost_var_alloc ()) as (γ_dq) "γ_dq".
  remember (encode (γ_dv, γ_dq)) as γ_d eqn:Hγ_d.
  iMod (hazptr.(hazard_domain_register) node with "IHD [$l_descr↦ $†l_descr]") as "G"; [solve_ndisj|by exfr|].
  wp_apply (hazptr.(shield_set_spec) (Some _) with "IHD S_descr") as "S_descr"; [solve_ndisj|].


  (* We can immediately validate [S_descr], since there's no any other concurrent access yet *)
  iMod (hazptr.(shield_validate) with "IHD G S_descr") as "[G S_descr]"; [solve_ndisj|].
  do 3 wp_pure.

  iLöb as "IH".
  wp_pures. wp_bind (CmpXchg _ _ _)%E.
  iInv "InvR" as (st) "(>l_n.p↦ & Hst)".
  destruct st as [n | l_descr' l_m' m1' n1' n2' p'].
  - (* l_n ↦ InjLV n *)
    iDestruct "Hst" as ">[l_n.p'↦ Hn●]".
    destruct (decide (n1 = n)) as [<- | NEQ].
    + iCombine "l_n.p↦ l_n.p'↦" as "l_n.p↦".
      wp_cmpxchg_suc.
      (* Take a "peek" at [AU] and abort immediately to get [gc_is_gc f]. *)
      iMod "AU" as (b' n') "[[Hf CC] [Hclose _]]".
      iDestruct (inv_mapsto_own_inv with "Hf") as "#Hgc".
      iMod ("Hclose" with "[Hf CC]") as "AU"; first by iFrame.
      (* Initialize new [descr] protocol .*)
      iMod (own_alloc (Excl ())) as (γ_t) "Token_t"; first done.
      iMod (own_alloc (Excl ())) as (γ_a) "Token_a"; first done.
      iMod (own_alloc (Cinl $ Excl ())) as (γ_s) "Hs"; first done.
      iDestruct "l_n.p↦" as "[l_n.p↦ l_n.p'↦]".
      set (winner := default p (proph_extract_winner proph_values)).
      iMod (inv_alloc descrN _ (descr_inv _ _ _ _ _ _ winner _ _ _ _ _)
            with "[AU Hs Hp l_n.p'↦ Hn● Token_a]") as "#InvD".
      { iExists _. iFrame "Hp". iLeft. iFrame. iLeft.
        iFrame. destruct (proph_extract_winner proph_values); simpl; (iSplit; last done); iExact "AU". }
      (* Close invariant *)
      iModIntro. iSplitR "Token_t S_descr".
      { (* close outer invariant *)
        iExists (Updating l_descr l_m m1 n1 n2 p). iFrame.
        iExists (1/2)%Qp. repeat iExists _. rewrite Qp.half_half. iFrame "∗#%". }
      wp_pures. wp_apply (complete_spec with "InvR InvD IHD Hgc InvGC [$S_descr $γ_dv]"); try done.
      iIntros "[Ht S_descr]". wp_pures.
      iMod ("Ht" with "Token_t") as "HΦ".
      wp_apply (hazptr.(shield_drop_spec) with "IHD S_descr") as "_"; [solve_ndisj|].
      wp_pures. by iApply "HΦ".
    + (* values do not match --> CmpXchg fails, and we can commit here *)
      wp_cmpxchg_fail.
      iMod "AU" as (m'' n'') "[[Hm◯ Hn◯] [_ Hclose]]". simpl.
      iDestruct (sync_values with "Hn● Hn◯") as %<-.
      iMod ("Hclose" with "[Hm◯ Hn◯]") as "HΦ".
      { rewrite decide_False; [|naive_solver]. iFrame. }
      iModIntro. iSplitR "HΦ S_descr G".
      { iExists (Quiescent n). iFrame. }
      wp_pures.
      wp_apply (hazptr.(hazard_domain_retire_spec) with "IHD G") as "_"; [solve_ndisj|].
      wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "IHD S_descr") as "_"; [solve_ndisj|].
      wp_pures. by iApply "HΦ".
  - (* l_n ↦ InjRV #l_descr --> try helping *)
    wp_cmpxchg_fail.
    iModIntro. iSplitL "l_n.p↦ Hst".
    { repeat iExists _. do 2 iFrame. }
    wp_pures. wp_apply (hazptr.(shield_new_spec) with "IHD [//]") as (s) "S"; [solve_ndisj|].
    wp_pures.
    wp_apply (hazptr.(shield_set_spec) (Some _) with "IHD S") as "S"; [solve_ndisj|].
    wp_pures. wp_bind (! _)%E.
    (* Validation *)
    iInv "InvR" as (st) "(>l_n.p↦ & Hst)".
    wp_load.
    destruct st as [n'' | l_descr'' l_m'' m1'' n1'' n2'' p''].
    + (* l_n ↦ InjLV n'' --> validation failed *)
      iModIntro. iSplitL "l_n.p↦ Hst"; first by exfr.
      wp_pures. wp_apply (hazptr.(shield_drop_spec) with "IHD S") as "_"; [solve_ndisj|].
      do 2 wp_pure. iApply ("IH" with "AU Hp γ_dq G S_descr").
    + (* l_n ↦ InjRV l_descr'' *)
      destruct (decide (l_descr' = l_descr'')) as [<-|NEQ].
      * (* Validation success *)
        iDestruct "Hst" as (?????????) "(%Hm1''_unbox & %Hγ_d' & G_l_descr' & #γ_dv'' & γ_dq'' & #InvD & #isGC)".
        iMod (hazptr.(shield_validate) with "IHD G_l_descr' S") as "[G_l_descr' S]"; [solve_ndisj|].
        iModIntro. iSplitL "G_l_descr' γ_dq'' l_n.p↦"; first by exfr.
        wp_pures. case_bool_decide; last contradiction. wp_pures.
        wp_apply (complete_spec with "InvR InvD IHD isGC InvGC [$S $γ_dv'']") as "[_ S]"; try done.
        wp_pures. wp_apply (hazptr.(shield_drop_spec) with "IHD S") as "_"; [solve_ndisj|].
        do 2 wp_pure. iApply ("IH" with "AU Hp γ_dq G S_descr").
      * (* Validation failed *)
        iModIntro. iSplitL "l_n.p↦ Hst".
        { iExists _. do 2 iFrame. }
        wp_pures. case_bool_decide; [naive_solver|].
        wp_pures. wp_apply (hazptr.(shield_drop_spec) with "IHD S") as "_"; [solve_ndisj|].
        do 2 wp_pure. iApply ("IH" with "AU Hp γ_dq G S_descr").
Qed.

#[export] Typeclasses Opaque Rdcss IsRdcss.

End rdcss.
