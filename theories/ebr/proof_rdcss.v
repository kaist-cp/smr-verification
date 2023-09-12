From iris.algebra Require Import excl agree csum.
From iris.base_logic.lib Require Import invariants ghost_var ghost_map.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr Require Import helpers ebr.spec_rcu_simple ebr.spec_rdcss ebr.code_rdcss.

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
Context (rdcssN rcuN : namespace) (DISJN : rcuN ## rdcssN).
Let descrN := rdcssN .@ "descr".
Let rdcssIntN := rdcssN .@ "rdcss".

(* iExists + iFrame *)
Ltac exfr := repeat (repeat iExists _; iFrame "∗#%").
Ltac exefr := iExists _; eauto 15 with iFrame.

Variable (rcu : rcu_simple_spec Σ rcuN).

Definition Rdcss_auth γ_n (n : val) : iProp := own γ_n (● Excl' n).

Definition Rdcss γ_n (n : val) : iProp := own γ_n (◯ Excl' n).

Lemma sync_values γ_n (n m : val) :
  Rdcss_auth γ_n n -∗ Rdcss γ_n m -∗ ⌜n = m⌝.
Proof.
  iIntros "H● H◯".
  iCombine "H● H◯" as "H".
  by iDestruct (own_valid with "H") as %[?%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
Qed.

Lemma update_value γ_n (n1 n2 m : val) :
  Rdcss_auth γ_n n1 -∗ Rdcss γ_n n2 ==∗
    Rdcss_auth γ_n m ∗ Rdcss γ_n m.
Proof.
  iIntros "H● H◯".
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

Definition pending_state P (n1 : val) (proph_winner : option proph_id) tid_ghost_winner γ_n γ_a : iProp :=
  P ∗ ⌜from_option (λ p, p = tid_ghost_winner) True proph_winner⌝ ∗ Rdcss_auth γ_n n1 ∗ own_token γ_a.

Definition accepted_state Q (proph_winner : option proph_id) (tid_ghost_winner : proph_id) : iProp :=
  (∃ vs, proph tid_ghost_winner vs) ∗ Q ∗ ⌜from_option (λ p, p = tid_ghost_winner) True proph_winner⌝.

Definition done_state Qn (tid_ghost_winner : proph_id) (γ_t γ_a γ_d : gname) : iProp :=
  (Qn ∨ own_token γ_t) ∗
  (∃ vs, proph tid_ghost_winner vs) ∗
  (∃ (γ_dv γ_dq : gname), ⌜γ_d = encode (γ_dv, γ_dq)⌝ ∗ ghost_var γ_dq (1/2)%Qp ()) ∗
  own_token γ_a.

Definition descr_inv P Q p n (l_n l_descr : loc) (tid_ghost_winner : proph_id) γ_n γ_t γ_s γ_a γ_d : iProp :=
  ∃ vs,
    proph p vs ∗
    (l_n ↦{# 1/2} (InjRV #l_descr) ∗ own γ_s (Cinl $ Excl ()) ∗
      (pending_state P n (proph_extract_winner vs) tid_ghost_winner γ_n γ_a
       ∨ accepted_state (Q n) (proph_extract_winner vs) tid_ghost_winner)
     ∨ own γ_s (Cinr $ to_agree ()) ∗ done_state (Q n) tid_ghost_winner γ_t γ_a γ_d).

Definition rdcss_au γ_n Q l_m m1 n1 n2 : iProp :=
  AU << ∃∃ (m n : val), (l_m ↦_(λ _, True) m) ∗ Rdcss γ_n n >>
    @ ⊤∖(↑rdcssN ∪ ↑ptrsN rcuN ∪ ↑inv_heapN),↑mgmtN rcuN
  << (l_m ↦_(λ _, True) m) ∗ (Rdcss γ_n (if (decide ((m = m1) ∧ (n = n1))) then n2 else n)), COMM Q n >>.

Definition node (p : blk) lv γ_p : iProp :=
  ∃ (l_m : loc) (m1 n1 n2 : val) (pid : proph_id) (γ_pv γ_pq : gname),
    ⌜γ_p = encode (γ_pv, γ_pq)⌝ ∗
    ⌜lv = [ (#l_m, m1, n1, n2, #pid)%V ]⌝ ∗
    own γ_pv (to_agree (#l_m, m1, n1, n2, #pid)%V).

Definition rdcss_inv (γ_e γ_n : gname) (l_n : loc) : iProp :=
  ∃ (st : abstract_state),
    l_n ↦{# 1/2} (state_to_val st) ∗
    match st with
    | Quiescent n =>
      l_n ↦{# 1/2} (InjLV n) ∗ Rdcss_auth γ_n n
    | Updating l_descr l_m m1 n1 n2 p =>
      ∃ q Q tid_ghost_winner (γ_d γ_dv γ_dq γ_t γ_s γ_a : gname),
        ⌜val_is_unboxed m1⌝ ∗
        ⌜γ_d = encode (γ_dv, γ_dq)⌝ ∗
        rcu.(Managed) γ_e l_descr γ_d 1 node ∗
        own γ_dv (to_agree (#l_m, m1, n1, n2, #p)%V) ∗
        ghost_var γ_dq (1/2 + q)%Qp () ∗
        inv descrN (descr_inv (rdcss_au γ_n Q l_m m1 n1 n2) Q p n1 l_n l_descr tid_ghost_winner γ_n γ_t γ_s γ_a γ_d) ∗
        l_m ↦_(λ _, True) □
    end.

Definition IsRdcss γ_e γ_n (l_n : loc) : iProp :=
  ∃ (d : loc),
    (l_n +ₗ 1) ↦□ #d ∗ rcu.(IsRCUDomain) γ_e d ∗
    (inv rdcssIntN (rdcss_inv γ_e γ_n l_n) ∧ inv_heap_inv ∧ ⌜rdcssN ## inv_heapN⌝).

Local Instance Rdcss_auth_Timeless γ_n n : Timeless (Rdcss_auth γ_n n) := _.
Global Instance IsRdcss_Persistent γ_e γ_n l_n : Persistent (IsRdcss γ_e γ_n l_n) := _.
Global Instance Rdcss_Timeless γ_n n : Timeless (Rdcss γ_n n) := _.
Global Instance abstract_state_inhabited: Inhabited abstract_state := populate (Quiescent #0).

Lemma Rdcss_exclusive γ_n n1 n2 :
  Rdcss γ_n n1 -∗ Rdcss γ_n n2 -∗ False.
Proof.
  iIntros "H● H◯".
  by iCombine "H● H◯" gives %?%auth_frag_op_valid_1.
Qed.

Lemma state_done_extract_Q P Q p n l_n l_d tid_ghost γ_n γ_t γ_s γ_a γ_d :
  inv descrN (descr_inv P Q p n l_n l_d tid_ghost γ_n γ_t γ_s γ_a γ_d) -∗
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
  new_rdcss_spec' rdcssN rcuN new_rdcss rcu Rdcss IsRdcss.
Proof.
  iIntros (γ_e d n Hdisj) "#InvGC".
  iIntros (Φ) "!> #IED HΦ".
  wp_lam. wp_pures. wp_alloc l_n as "l_n↦" "†l_n".
  do 2 rewrite array_cons. iDestruct "l_n↦" as "(l_n.p↦ & l_n.d↦ & _)".
  wp_pures. rewrite loc_add_0. wp_store. wp_pures. wp_store.
  (* Allocate resources for [Rdcss] and [IsRdcss] *)
  iMod (own_alloc (● Excl' n ⋅ ◯ Excl' n)) as (γ_n) "[Hn● Hn◯]"; first by apply auth_both_valid_discrete.
  iMod (mapsto_persist with "l_n.d↦") as "#l_n.d↦".
  iMod (inv_alloc rdcssIntN _ (rdcss_inv γ_e γ_n l_n) with "[l_n.p↦ Hn●]") as "#InvR".
  { iExists (Quiescent n). iDestruct "l_n.p↦" as "[l_n.p↦ l_n.p'↦]". iFrame "∗#%". }
  iApply "HΦ". iFrame "∗#%". iExists _. by iFrame "∗#%".
Qed.

Lemma complete_succeeding_thread_pending (γ_e γ_n γ_t γ_s γ_a γ_d γ_dq γ_dv : gname) (l_n l_dom l_m g : loc) (l_descr : blk) P Q p (m1 n1 n2 n : val) (tid_ghost : proph_id) Φ γg :
  γ_d = encode (γ_dv, γ_dq) →
  inv rdcssIntN (rdcss_inv γ_e γ_n l_n) -∗
  inv descrN (descr_inv P Q p n1 l_n l_descr tid_ghost γ_n γ_t γ_s γ_a γ_d) -∗
  rcu.(IsRCUDomain) γ_e l_dom -∗
  rcu.(NodeInfo) γ_e γg l_descr γ_d 1 node -∗
  rcu.(Guard) γ_e g (Activated γg) -∗
  own γ_dv (to_agree (#l_m, m1, n1, n2, #p)%V) -∗
  own_token γ_a -∗
  (□(own_token γ_t ={⊤}=∗ ▷ (Q n1)) ∗ rcu.(Guard) γ_e g (Activated γg) -∗ Φ #()) -∗
  Rdcss_auth γ_n n -∗
  WP let: "r" := Resolve (CmpXchg #l_n (InjRV #l_descr) (InjLV n)) #p #tid_ghost in
     if: Snd "r" then rcu.(rcu_domain_retire) #l_dom #l_descr #1%nat
     else #() {{ v, Φ v }}.
Proof using DISJN.
  iIntros (Hγ_d) "#InvR #InvD #IED #dInfo G #γ_dv Token_a HΦ Hn●".
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
  { simpl. iDestruct (mapsto_agree with "l_n.p↦ l_n.p'↦") as %EQ. inversion EQ. }
  iDestruct (mapsto_agree with "l_n.p↦ l_n.p'↦") as %[= ->]. simpl.
  iCombine "l_n.p↦ l_n.p'↦" as "l_n.p↦".
  wp_apply (wp_resolve with "Hp"); first done. wp_cmpxchg_suc.

  iDestruct "Hst" as (?????????) "(%Hn1_unbox & %Hγ_d' & G_l_descr & #γ_dv' & γ_dq & #InvD' & #isGC)".
  iDestruct (rcu.(guard_managed_agree) with "dInfo G G_l_descr") as %<-.
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
  iModIntro. iSplitR "HΦ G_l_descr G".
  { iNext. iDestruct "l_n.p↦" as "[l_n.p↦ l_n.p'↦]". iExists (Quiescent n). iFrame. }
  wp_pures. wp_apply (rcu.(rcu_domain_retire_spec) with "IED G_l_descr") as "_"; [solve_ndisj|].
  iApply "HΦ". iFrame. iApply state_done_extract_Q; done.
Qed.

Lemma complete_failing_thread (γ_e γ_n γ_t γ_s γ_a γ_d γ_dv γ_dq : gname) (l_n l_m l_dom g : loc) (l_descr : blk) P Q p (n1 n2 n m1 v : val) tid_ghost_inv tid_ghost Φ γg :
  γ_d = encode (γ_dv, γ_dq) →
  tid_ghost_inv ≠ tid_ghost →
  inv rdcssIntN (rdcss_inv γ_e γ_n l_n) -∗
  inv descrN (descr_inv P Q p n1 l_n l_descr tid_ghost_inv γ_n γ_t γ_s γ_a γ_d) -∗
  rcu.(IsRCUDomain) γ_e l_dom -∗
  rcu.(NodeInfo) γ_e γg l_descr γ_d 1 node -∗
  rcu.(Guard) γ_e g (Activated γg) -∗
  own γ_dv (to_agree (#l_m, m1, n1, n2, #p)%V) -∗
  (□(own_token γ_t ={⊤}=∗ ▷ (Q n1)) ∗ rcu.(Guard) γ_e g (Activated γg) -∗ Φ #()) -∗
  WP let: "r" := Resolve (CmpXchg #l_n (InjRV #l_descr) (InjLV n)) #p #tid_ghost in
     if: Snd "r" then rcu.(rcu_domain_retire) #l_dom #l_descr #1%nat
     else #() {{ v, Φ v }}.
Proof.
  iIntros (Hγ_d Hn1) "#InvR #InvD #IED #dInfo G #γ_dv HΦ". wp_bind (Resolve _ _ _)%E.
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
      iDestruct (rcu.(guard_managed_agree) with "dInfo G M") as "#><-".
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

Lemma complete_spec (l_n l_m l_dom g : loc) (l_descr : blk) (m1 n1 n2 : val) p (γ_e γ_n γ_t γ_s γ_a γ_d γ_dv γ_dq : gname) tid_ghost_inv Q γg :
  val_is_unboxed m1 →
  rdcssN ## inv_heapN →
  γ_d = encode (γ_dv, γ_dq) →
  inv rdcssIntN (rdcss_inv γ_e γ_n l_n) -∗
  inv descrN (descr_inv (rdcss_au γ_n Q l_m m1 n1 n2) Q p n1 l_n l_descr tid_ghost_inv γ_n γ_t γ_s γ_a γ_d) -∗
  rcu.(IsRCUDomain) γ_e l_dom -∗
  l_m ↦_(λ _, True) □ -∗
  inv_heap_inv -∗
  rcu.(NodeInfo) γ_e γg l_descr γ_d 1 node -∗
  {{{ rcu.(Guard) γ_e g (Activated γg) ∗
      own γ_dv (to_agree (#l_m, m1, n1, n2, #p)%V) }}}
    (complete rcu) #l_descr #l_n #l_dom
  {{{ RET #(); □ (own_token γ_t ={⊤}=∗ ▷(Q n1)) ∗ rcu.(Guard) γ_e g (Activated γg) }}}.
Proof using DISJN.
  iIntros (Hm_unbox Hdisj Hγ_d) "#InvR #InvD #IED #isGC #InvGC #dInfo !>".
  iIntros (Φ) "(G & #γ_dv) HΦ".
  wp_pures. wp_lam. wp_pure credit:"Hlc". wp_pures.
  wp_apply (guard_read node with "[$dInfo $G]") as (??) "(G & #Hnode & %EQ)"; [solve_ndisj|lia|].
  iDestruct "Hnode" as (???????) "(% & -> & γ_dv')".
  encode_agree Hγ_d.
  iCombine "γ_dv γ_dv'" gives %[= <- <- <- <- <-]%to_agree_op_inv_L. iClear "γ_dv'". injection EQ as [= <-].
  wp_pures.
  wp_apply (wp_new_proph with "[//]") as (vs_ghost tid_ghost) "Htid_ghost".
  wp_pures.
  wp_bind (! _)%E.
  (* open outer invariant *)
  iInv "InvR" as (st) "(>l_n.p↦ & Hst)".
  destruct (decide (tid_ghost_inv = tid_ghost)) as [-> | Hnl].
  - (* we are the succeeding thread *)
    iInv "InvD" as (vs) "(>Hp & [(>Hln & >γ_s & [Pending | Accepted]) | [#Hs Done]])".
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
      do 2 iModIntro. iSplitL "Q Htid_ghost Hp Hvs γ_s Hln"; first by exefr.
      (* close outer inv *)
      iSplitR "Token_a HΦ Hn● G"; first by exfr.

      iModIntro.
      destruct (decide (m' = m1)) as [-> | ?]; wp_op;
      case_bool_decide; simplify_eq; wp_if; wp_pures;
      iApply (complete_succeeding_thread_pending with "InvR InvD IED dInfo G γ_dv Token_a HΦ"); try done.
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
    all: iApply (complete_failing_thread with "InvR InvD IED dInfo G γ_dv HΦ"); done.
Qed.

Lemma get_spec :
  get_spec' rdcssN rcuN (get rcu) rcu Rdcss IsRdcss.
Proof using DISJN.
  iIntros (γ_e γ_n l_n g).
  iDestruct 1 as (d) "(#l_n.d↦ & #IED & #InvR & #InvGC & %Hdisj)".
  iIntros "G". iIntros (Φ) "AU".
  wp_lam. wp_pures. wp_load. wp_pures.
  wp_apply (rcu.(guard_activate_spec) with "IED G") as (?) "G"; [solve_ndisj|].
  wp_seq. wp_bind (get_inner _ _ _)%E.
  iLöb as "IH".
  wp_lam. wp_pures. wp_bind (! _)%E.
  iInv "InvR" as (st) "(>l_n.p↦ & Hst)".
  destruct st as [n | l_descr l_m m1 n1 n2 p]; wp_load.
  - (* We found real value : here is commit point *)
    iDestruct "Hst" as "[l_n.p'↦ H●]".
    iMod "AU" as (au_n) "[H◯ [_ Hclose]]".
    iDestruct (sync_values with "H● H◯") as %<-.
    iMod ("Hclose" with "H◯") as "HΦ".
    (* close the invariant *)
    iModIntro. iSplitL "l_n.p↦ l_n.p'↦ H●"; first by exfr.
    wp_pures. wp_apply (rcu.(guard_deactivate_spec) with "IED G") as "G"; [solve_ndisj|].
    wp_pures. iApply ("HΦ" with "G").
  - (* We found descriptor *)
    iDestruct "Hst" as (q Q tid_ghost γ_d γ_dv γ_dq γ_t γ_s γ_a) "(%Hm_unbox & %Hγ_d & M & #γ_dv & γ_dq & #InvD & #GC)".
    (* Protect the descriptor location *)
    iMod (rcu.(guard_protect) with "IED M G") as "(M & G & #dInfo)"; [solve_ndisj|].
    (* Close the invariant *)
    iModIntro. iSplitL "l_n.p↦ γ_dq M"; first by exfr.
    wp_pures. wp_apply (complete_spec with "InvR InvD IED GC InvGC dInfo [$G $γ_dv]") as "[_ G]"; try done.
    wp_pures. iApply ("IH" with "AU G").
Qed.

Lemma rdcss_spec :
  rdcss_spec' rdcssN rcuN (rdcss rcu) rcu Rdcss IsRdcss.
Proof using DISJN.
  iIntros (γ_e γ_n l_n l_m g m1 n1 n2 Hn1_unbox Hm1_unbox).
  iDestruct 1 as (d) "(#l_n.d↦ & #IED & #InvR & #InvGC & %Hdisj)".
  iIntros "G". iIntros (Φ) "AU".
  wp_lam. wp_pures. wp_load. wp_let.
  wp_apply (rcu.(guard_activate_spec) with "IED G") as (?) "G"; [solve_ndisj|].
  wp_seq.
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
      iDestruct (inv_mapsto_own_inv with "Hf") as "#Hgc".
      iMod ("Hclose" with "[Hf CC]") as "AU"; first by iFrame.
      (* Create a new [Managed] for l_descr *)
      iMod (own_alloc (to_agree (#l_m, m1, n1, n2, #p)%V)) as (γ_dv) "#γ_dv"; [done|].
      iMod (ghost_var_alloc ()) as (γ_dq) "γ_dq".
      remember (encode (γ_dv, γ_dq)) as γ_d eqn:Hγ_d.
      iMod (rcu.(rcu_domain_register) node with "IED [$l_descr↦ $†l_descr]") as "G_l_descr"; [solve_ndisj|by exfr|..].
      iMod (rcu.(guard_protect) with "IED G_l_descr G") as "(G_l_descr & G & #dInfo)"; [solve_ndisj|].
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
      iModIntro. iSplitR "Token_t G".
      { (* close outer invariant *)
        iExists (Updating l_descr l_m m1 n1 n2 p). iFrame.
        repeat iExists _. iDestruct "γ_dq" as "[$ $]". iFrame "∗#%". }
      wp_pures. wp_apply (complete_spec with "InvR InvD IED Hgc InvGC dInfo [$G $γ_dv]") as "[Ht G]"; try done.
      wp_pures.
      iMod ("Ht" with "Token_t") as "HΦ".
      wp_apply (rcu.(guard_deactivate_spec) with "IED G") as "G"; [solve_ndisj|].
      wp_pures. by iApply "HΦ".
    + (* values do not match --> CmpXchg fails, and we can commit here *)
      wp_cmpxchg_fail.
      iMod "AU" as (m'' n'') "[[Hm◯ Hn◯] [_ Hclose]]". simpl.
      iDestruct (sync_values with "Hn● Hn◯") as %<-.
      iMod ("Hclose" with "[Hm◯ Hn◯]") as "HΦ".
      { rewrite decide_False; [|naive_solver]. iFrame. }
      iModIntro. iSplitR "l_descr↦ †l_descr HΦ G".
      { iExists (Quiescent n). iFrame. }
      wp_pures.
      wp_free; [done|]. wp_pures.
      wp_apply (rcu.(guard_deactivate_spec) with "IED G") as "G"; [solve_ndisj|].
      wp_pures. by iApply "HΦ".
  - (* l_n ↦ InjR l_descr' --> helping *)
    wp_cmpxchg_fail.
    iDestruct "Hst" as (q Q tid_ghost γ_d γ_dv γ_dq γ_t γ_s γ_a) "(%Hm1'_unbox & %Hγ_d & M & #γ_dv & γ_dq & #InvD & #P_GC)".
    iMod (rcu.(guard_protect) with "IED M G") as "(M & G & #dInfo)"; [solve_ndisj|].
    iModIntro. iSplitR "AU Hp G l_descr↦ †l_descr".
    { iExists (Updating l_descr' l_m' m1' n1' n2' p'). iFrame. exfr. }
    wp_pures. wp_apply (complete_spec with "InvR InvD IED P_GC InvGC dInfo [$G $γ_dv]") as "[_ G]"; try done.
    wp_pures. iApply ("IH" with "AU G Hp l_descr↦ †l_descr").
Qed.

#[export] Typeclasses Opaque Rdcss IsRdcss.

End rdcss.
