From iris.algebra Require Import list excl_auth.
From iris.bi Require Import derived_laws_later.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants.
From smr Require Import ghost_var mono_list mono_nat atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.
From smr.ebr Require Import spec_cldeque code_cldeque.
From smr Require Import helpers ebr.spec_rcu_simple.

Local Ltac extended_auto :=
  eauto;
  try rewrite Nat2Z.id;
  try rewrite length_replicate;
  try rewrite Qp.half_half;
  repeat rewrite Loc.add_0; repeat rewrite Loc.add_assoc;
  try by (
    repeat iNext; repeat iIntros; repeat intros;
    try case_decide; try iPureIntro;
    try rewrite lookup_lt_is_Some;
    try lia; done
  ).
Local Ltac fr :=
  repeat iIntros; repeat iSplit; extended_auto;
  repeat iIntros; repeat iExists _;
  try iFrame "arr↦"; try iFrame "arr↦1"; try iFrame "arr↦2";
  iFrame; eauto.

(** Ghost state for the deque *)

Class cldequeG Σ := CLDequeG {
    (* spec *)
    #[local] deque_tokG :: inG Σ (excl_authR $ listO valO);
    (* info: era, arrptr, C, bot, popping *)
    #[local] deque_infoG :: ghost_varG Σ (nat * blk * list val * nat * bool * gname);
    (* RA *)
    #[local] topbotG :: mono_natG Σ;
    #[local] topeltG :: mono_listG val Σ;
    #[local] roomG :: mono_listG (gname * gname * nat) Σ;
    #[local] museumG :: mono_listG (list val * nat * nat) Σ;
    (* SMR *)
    #[local] smrG :: ghost_varG Σ (list val);
    #[local] lengthG :: ghost_varG Σ nat
  }.

Definition cldequeΣ : gFunctors :=
  #[ (*invariant *)
    GFunctor (excl_authR $ listO valO);
    ghost_varΣ (nat * blk * list val * nat * bool * gname);
    (* RA *)
    mono_natΣ;
    mono_listΣ val;
    mono_listΣ (gname * gname * nat);
    mono_listΣ (list val * nat * nat);
    (* SMR *)
    ghost_varΣ (list val);
    ghost_varΣ nat
  ].

Global Instance subG_cldequeΣ {Σ} : subG cldequeΣ Σ → cldequeG Σ.
Proof. solve_inG. Qed.

Section dqst.
  Context `{!heapGS Σ, !cldequeG Σ}.
  Notation iProp := (iProp Σ).
  Definition dqst_gnames : Type := gname*gname*gname*gname.

  Definition top_bot_state (t b : nat) : nat :=
    2*t + (if bool_decide (t < b) then 1 else 0).

  Definition dqst_frag (γdqst : dqst_gnames) (era : nat)
  (γebr : gname) (l : list val) (t b : nat) : iProp :=
    let (γ'              , γmus) := γdqst in
    let (γ''      , γroom) := γ' in
    let (γtb, γelt) := γ'' in
    ∃ (γtbe : gname),
    ⌜1 ≤ t ≤ b ∧ b < t + length l ∧ length l ≠ 0⌝ ∗
    (* top-bot profile *)
    ( mono_nat_lb_own γtb (top_bot_state t b) ∗
      mono_nat_lb_own γtbe (top_bot_state t b)
    ) ∗
    (* top element preservation *)
    ( ∃ (elts : list val),
      mono_list_lb_own γelt elts ∗
      ⌜t = b ∨ mod_get l t = elts !! t⌝
    ) ∗
    (* museum of past gnames and circles *)
    ( ∃ (room : list (gname * gname * nat)),
      ⌜room !! era = Some (γtbe, γebr, length l)⌝ ∗
      mono_list_lb_own γroom room
    ).

  Definition dqst_archived (γdqst : dqst_gnames) (era : nat)
  (γebr : gname) (l : list val) (t b : nat) : iProp :=
    let (γ'              , γmus) := γdqst in
    let (γ''      , γroom) := γ' in
    let (γtb, γelt) := γ'' in
    ∃ (γtbe : gname),
    ⌜1 ≤ t ≤ b ∧ b < t + length l ∧ length l ≠ 0⌝ ∗
    (* top-bot profile *)
    ( mono_nat_lb_own γtb (top_bot_state t b) ∗
      mono_nat_persistent γtbe (top_bot_state t b)
    ) ∗
    (* top element preservation *)
    ( ∃ (elts : list val),
      mono_list_lb_own γelt elts ∗
      ⌜t = b ∨ mod_get l t = elts !! t⌝
    ) ∗
    (* museum of past gnames and circles *)
    ( ∃ (room : list (gname * gname * nat))
        (museum : list (list val * nat * nat)),
      ⌜room !! era = Some (γtbe, γebr, length l)⌝ ∗
      ⌜museum !! era = Some (l, t, b)⌝ ∗
      mono_list_lb_own γroom room ∗
      mono_list_lb_own γmus museum
    ) ∗
    (* persistent circle *)
    persistent_ghost_var γebr l.

  Definition dqst_auth (γdqst : dqst_gnames) (era : nat)
  (γebr : gname) (l : list val) (t b : nat) : iProp :=
    let (γ'              , γmus) := γdqst in
    let (γ''      , γroom) := γ' in
    let (γtb, γelt) := γ'' in
    ∃ (γtbe : gname),
    ⌜1 ≤ t ≤ b ∧ b < t + length l ∧ length l ≠ 0⌝ ∗
    (* top-bot profile *)
    (mono_nat_auth_own γtb 1 (top_bot_state t b) ∗
      mono_nat_auth_own γtbe 1 (top_bot_state t b)
    ) ∗
    (* top element preservation *)
    (∃ (elts : list val),
      mono_list_auth_own γelt 1 elts ∗
      ⌜if (bool_decide (t = b))
        then length elts = t
        else (length elts = S t ∧ mod_get l t = elts !! t)⌝
    ) ∗
    (* museum of past gnames and circles *)
    ( ∃ (proom : list (gname * gname * nat))
        (museum : list (list val * nat * nat)),
      ⌜length proom = era ∧ length museum = era⌝ ∗
      mono_list_auth_own γroom 1 (proom ++ [(γtbe, γebr, length l)]) ∗
      mono_list_auth_own γmus 1 museum ∗
      [∗ list] i ↦ gne ; ltbi ∈ proom ; museum, (
        dqst_archived γdqst i (gne.1.2) (ltbi.1.1) (ltbi.1.2) (ltbi.2)
      )
    ).

  (* Timeless & Persistent *)
  Ltac desγ H :=
    destruct H as (((γtb, γelt), γroom), γmuseum).

  Global Instance dqst_frag_timeless γdqst era γebr l t b :
    Timeless (dqst_frag γdqst era γebr l t b).
  Proof. desγ γdqst. apply _. Qed.

  Global Instance dqst_frag_persistent γdqst era γebr l t b :
    Persistent (dqst_frag γdqst era γebr l t b).
  Proof. desγ γdqst. apply _. Qed.

  Global Instance dqst_archived_timeless γdqst era γebr l t b :
    Timeless (dqst_archived γdqst era γebr l t b).
  Proof. desγ γdqst. apply _. Qed.

  Global Instance dqst_archived_persistent γdqst era γebr l t b :
    Persistent (dqst_archived γdqst era γebr l t b).
  Proof. desγ γdqst. apply _. Qed.

  Global Instance dqst_auth_timeless γdqst era γebr l t b :
    Timeless (dqst_auth γdqst era γebr l t b).
  Proof. desγ γdqst. apply _. Qed.

  Lemma top_bot_state_le t1 b1 t2 b2 :
    top_bot_state t1 b1 ≤ top_bot_state t2 b2 ↔
    t1 ≤ t2 ∧ (t1 = t2 ∧ t1 < b1 → t2 < b2).
  Proof. unfold top_bot_state. do 2 case_bool_decide; lia. Qed.

  Lemma dqst_auth_alloc γebr l :
    length l ≠ 0 →
    ⊢ |==> ∃ (γdqst : dqst_gnames),
      dqst_auth γdqst 0 γebr l 1 1.
  Proof.
    intros Hl. unfold dqst_auth.
    iMod (mono_nat_own_alloc 2) as (γtb) "[tb _]".
    iMod (mono_nat_own_alloc 2) as (γtbe) "[tbe _]".
    iMod (mono_list_own_alloc ([NONEV])) as (γelt) "[topelt _]".
    iMod (mono_list_own_alloc ([(γtbe, γebr, length l)])) as (γroom) "[room _]".
    iMod (mono_list_own_alloc ([] : list (list val * nat * nat))) as (γmus) "[museum _]".
    iExists (γtb, γelt, γroom, γmus).
    iModIntro. fr. fr.
    iSplit; fr.
  Qed.

  Lemma dqst_frag_agree γdqst era γebr1 l1 t1 b1 γebr2 l2 t2 b2 :
    dqst_frag γdqst era γebr1 l1 t1 b1 -∗
    dqst_frag γdqst era γebr2 l2 t2 b2 -∗
    ⌜γebr1 = γebr2 ∧ length l1 = length l2⌝.
  Proof.
    desγ γdqst.
    iIntros "F1 F2".
      iDestruct "F1" as (γtbe1) "(%Hlt1 & tb1 & elt1 & muse1)".
      iDestruct "muse1" as (room1) "[%Hroom1 Lb1]".
      iDestruct "F2" as (γtbe2) "(%Hlt2 & tb2 & elt2 & muse2)".
      iDestruct "muse2" as (room2) "[%Hroom2 Lb2]".
    iDestruct (mono_list_lb_valid with "Lb1 Lb2") as "[%Pref|%Pref]".
    - eapply prefix_lookup_Some in Hroom1; eauto.
      rewrite Hroom2 in Hroom1. by injection Hroom1.
    - eapply prefix_lookup_Some in Hroom2; eauto.
      rewrite Hroom2 in Hroom1. by injection Hroom1.
  Qed.

  Lemma dqst_get_frag γdqst era γebr l t b :
    dqst_auth γdqst era γebr l t b -∗
    dqst_frag γdqst era γebr l t b.
  Proof with extended_auto.
    desγ γdqst.
    iIntros "Auth".
      iDestruct "Auth" as (γtbeO) "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "eltO" as (elts) "[Elt %Heltslen]".
      iDestruct "museO" as (room museum) "museO".
      iDestruct "museO" as "([%Hroomlen %Hmuslen] & museO)".
      iDestruct "museO" as "(Room & Museum & Archives)".
    iDestruct (mono_nat_lb_own_get with "tbO") as "#lb".
    iDestruct (mono_nat_lb_own_get with "tbeO") as "#lbe".
    iDestruct (mono_list_lb_own_get with "Elt") as "#eltlb".
    iDestruct (mono_list_lb_own_get with "Room") as "#rlb".
    fr. fr.
    - fr. case_bool_decide; [iLeft|iRight]... destruct Heltslen...
    - fr. rewrite lookup_app_r... replace (era - length room) with 0...
  Qed.

  Lemma dqst_get_archived γdqst era1 γebr1 l1 t1 b1
  era2 γebr2 l2 t2 b2 :
    (* era1 is later than era2 *)
    era1 ≠ era2 →
    dqst_auth γdqst era1 γebr1 l1 t1 b1 -∗
    dqst_frag γdqst era2 γebr2 l2 t2 b2 -∗
    ∃ l' t' b', dqst_archived γdqst era2 γebr2 l' t' b'.
  Proof with extended_auto.
    desγ γdqst.
    iIntros (Hneq) "Auth F".
      iDestruct "Auth" as (γtbeO) "(%HltO & tbO & eltO & museO)".
      iDestruct "museO" as (room museum) "museO".
      iDestruct "museO" as "([%Hroomlen %Hmuslen] & museO)".
      iDestruct "museO" as "(Room & Museum & Archives)".
      iDestruct "F" as (γtbe) "(%Hlt & tb & elt & muse)".
      iDestruct "muse" as (room') "[%Hroom'2 Lb']".
    iDestruct (mono_list_auth_lb_valid with "Room Lb'") as "%Pref".
      destruct Pref as [_ Pref].
      eapply prefix_lookup_Some in Hroom'2; eauto.
    assert (era2 < era1) as Hera21.
    { apply lookup_lt_Some in Hroom'2.
      rewrite length_app Hroomlen in Hroom'2. simpl in Hroom'2... }
    assert (is_Some (museum !! era2)) as [ltbera2 Hltbera2].
    { rewrite lookup_lt_is_Some... }
    rewrite lookup_app_l in Hroom'2...
    iDestruct (big_sepL2_lookup with "Archives") as "Arch2"...
  Qed.

  Lemma dqst_get_lb γdqst era1 γebr1 l1 t1 b1
  era2 γebr2 l2 t2 b2 :
    (* era1 is later than era2 *)
    dqst_auth γdqst era1 γebr1 l1 t1 b1 -∗
    dqst_frag γdqst era2 γebr2 l2 t2 b2 -∗
    ⌜t2 ≤ t1 ∧ (
      (t2 = t1 ∧ t2 < b2) →
      (t1 < b1 ∧ mod_get l2 t2 = mod_get l1 t1)
    )⌝.
  Proof with extended_auto.
    desγ γdqst.
    iIntros "Auth F".
      iDestruct "Auth" as (γtbeO) "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "F" as (γtbe) "(%Hlt & [tb tbe] & elt & muse)".
    iDestruct (mono_nat_lb_own_valid with "tbO tb") as "[_ %Htb]".
      apply top_bot_state_le in Htb as [Ht21 Htb21]. fr.
    iIntros ([H1 Ht1b2]). subst t2. assert (t1 < b1) as Htb1... fr.
    iDestruct "elt" as (elts') "[lb %Helts]"...
      destruct Helts as [NO|Helts]...
      iDestruct "eltO" as (elts) "[Elts %Heltslen]".
      iDestruct (mono_list_auth_lb_lookup t1 with "Elts lb") as "%Heqg"...
      { rewrite -lookup_lt_is_Some -Helts. apply mod_get_is_Some... }
      iDestruct (mono_list_auth_lb_valid with "Elts lb") as "[_ %Pref]".
      case_bool_decide... destruct Heltslen as [_ Hget].
    rewrite Hget Helts...
  Qed.

  Lemma dqst_archived_get_array γdqst era γebr l t b :
    dqst_archived γdqst era γebr l t b -∗
    persistent_ghost_var γebr l.
  Proof.
    desγ γdqst.
    iIntros "Arc".
    by iDestruct "Arc" as (γtbeA) "(_&_&_&_& pers)".
  Qed.

  Lemma dqst_archived_get_frag γdqst era γebr l t b :
    dqst_archived γdqst era γebr l t b -∗
    dqst_frag γdqst era γebr l t b.
  Proof.
    desγ γdqst.
    iIntros "Arc".
      iDestruct "Arc" as (γtbeA) "(%Hlt & [tb tbe] & elt & muse & pers)".
      iDestruct "muse" as (room museum) "(%Hroom & Hmuseum & Room & Museum)".
    fr. fr. by iApply mono_nat_persistent_lb_own_get.
  Qed.

  Lemma dqst_archived_get_lb γdqst era γebr l1 t1 b1 l2 t2 b2 :
    dqst_archived γdqst era γebr l1 t1 b1 -∗
    dqst_frag γdqst era γebr l2 t2 b2 -∗
    ⌜t2 ≤ t1 ∧ (
      (t2 = t1 ∧ t2 < b2) →
      (t1 < b1 ∧ mod_get l2 t2 = mod_get l1 t1)
    )⌝.
  Proof with extended_auto.
    desγ γdqst.
    iIntros "Arc F".
      iDestruct "Arc" as (γtbeA) "(%Hlt1 & [tb1 tbe1] & elt1 & muse1 & pers1)".
      iDestruct "muse1" as (room1 museum1) "muse1".
      iDestruct "muse1" as "(%Hroom1 & %Hmuse1 & Lbroom1 & Lbmuse1)".
      iDestruct "F" as (γtbe) "(%Hlt2 & [tb2 tbe2] & elt2 & muse2)".
      iDestruct "muse2" as (room2) "[%Hroom2 Lbroom2]".
    iDestruct (mono_list_lb_lookup era with "Lbroom1 Lbroom2") as "%Hr12".
      { apply lookup_lt_Some in Hroom1... }
      { apply lookup_lt_Some in Hroom2... }
      rewrite Hroom1 Hroom2 in Hr12. injection Hr12 as [= <-].
    iDestruct (mono_nat_persistent_lb_own_valid with "tbe1 tbe2") as "%Htb2".
    apply top_bot_state_le in Htb2 as [Hlt21 Htb2].
      fr. iIntros ([<- Hlt]). clear Hlt21.
      assert (t2 < b1) as Hlt21...
    iSplit...
    iDestruct "elt1" as (elts1) "[lb1 [%NO|%Hget1]]"...
    iDestruct "elt2" as (elts2) "[lb2 [%NO|%Hget2]]"...
    rewrite Hget1 Hget2.
    iApply (mono_list_lb_lookup with "lb2 lb1").
    - rewrite -lookup_lt_is_Some -Hget2. apply mod_get_is_Some...
    - rewrite -lookup_lt_is_Some -Hget1. apply mod_get_is_Some...
  Qed.

  Lemma dqst_auth_write_bot v γdqst era γebr l t b :
    dqst_auth γdqst era γebr l t b -∗
    dqst_auth γdqst era γebr (mod_set l b v) t b.
  Proof.
    desγ γdqst.
    iIntros "Auth".
      iDestruct "Auth" as (γtbeO) "(%HltO & tbO & eltO & museO)".
      iDestruct "eltO" as (elts) "[Elts %Heltslen]".
    unfold dqst_auth. rewrite mod_set_length. fr.
    fr. case_bool_decide; auto. rewrite mod_set_get_ne; auto.
    apply neq_symm, close_mod_neq; lia.
  Qed.

  Lemma dqst_auth_update γdqst era γebr l t b :
    t < b →
    dqst_auth γdqst era γebr l t b ==∗
    dqst_auth γdqst era γebr l (S t) b.
  Proof with extended_auto.
    desγ γdqst.
    iIntros (Hlt) "Auth".
      iDestruct "Auth" as (γtbeO) "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "eltO" as (elts) "[Elts %Heltslen]".
    iMod (mono_nat_own_update (top_bot_state (S t) b)
      with "tbO") as "[tbO _]".
    { unfold top_bot_state. do 2 case_bool_decide... }
    iMod (mono_nat_own_update (top_bot_state (S t) b)
      with "tbeO") as "[tbeO _]".
    { unfold top_bot_state. do 2 case_bool_decide... }

    destruct (decide (S t = b)).
    { iModIntro. fr. fr. do 2 case_bool_decide... }
    destruct (mod_get_is_Some l (S t)) as [v Hv]...
    iMod (mono_list_auth_own_update_app [v] with "Elts") as "[Elts _]".
    iModIntro. fr. fr. do 2 case_bool_decide...
    rewrite length_app lookup_app_r; simpl...
    replace (S t - length elts) with 0; simpl... fr.
  Qed.

  Lemma dqst_auth_push γdqst era γebr l t b :
    S b < t + length l →
    dqst_auth γdqst era γebr l t b ==∗
    dqst_auth γdqst era γebr l t (S b).
  Proof with extended_auto.
    desγ γdqst.
    iIntros (Hlt) "Auth".
      iDestruct "Auth" as (γtbeO) "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "eltO" as (elts) "[Elts %Heltslen]".
    iMod (mono_nat_own_update (top_bot_state t (S b))
      with "tbO") as "[tbO _]".
    { unfold top_bot_state. do 2 case_bool_decide... }
    iMod (mono_nat_own_update (top_bot_state t (S b))
      with "tbeO") as "[tbeO _]".
    { unfold top_bot_state. do 2 case_bool_decide... }

    case_bool_decide; last first.
    { iModIntro. fr. fr. }
    destruct (mod_get_is_Some l t) as [v Hv]...
    iMod (mono_list_auth_own_update_app [v] with "Elts") as "[Elts _]".
    iModIntro. fr. fr. case_bool_decide...
    rewrite length_app lookup_app_r; simpl...
    replace (t - length elts) with 0; simpl... fr.
  Qed.

  Lemma dqst_auth_pop γdqst era γebr l t b :
    t < b - 1 →
    dqst_auth γdqst era γebr l t b ==∗
    dqst_auth γdqst era γebr l t (b - 1).
  Proof with extended_auto.
    desγ γdqst.
    iIntros (Hlt) "Auth".
      iDestruct "Auth" as (γtbeO) "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "eltO" as (elts) "[Elts %Heltslen]".
    replace (top_bot_state t b) with (top_bot_state t (b-1)).
      2: unfold top_bot_state; repeat case_bool_decide...
    iModIntro. fr. fr. case_bool_decide...
  Qed.

  Lemma dqst_auth_archive γebr' l' γdqst era γebr l t b :
    length l ≤ length l' →
    circ_slice l t b = circ_slice l' t b →
    ghost_var γebr (1/2) l -∗
    dqst_auth γdqst era γebr l t b ==∗
    dqst_archived γdqst era γebr l t b ∗
    dqst_auth γdqst (S era) γebr' l' t b.
  Proof with extended_auto.
    desγ γdqst.
    iIntros (Hlong Heqs) "Own Auth".
      iDestruct "Auth" as (γtbeO) "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "eltO" as (elts) "[Elts %Heltslen]".
      iDestruct "museO" as (proom museum) "museO".
      iDestruct "museO" as "([%Hproomlen %Hmuslen] & museO)".
      iDestruct "museO" as "(Room & Museum & Archives)".

    (* archive *)
    iMod (ghost_var_persist with "Own") as "#PC".
    iDestruct (mono_nat_lb_own_get with "tbO") as "#tb".
    iMod (mono_nat_own_persist with "tbeO") as "#tbe".
    iDestruct (mono_list_lb_own_get with "Elts") as "#eltslb".
    iDestruct (mono_list_lb_own_get with "Room") as "#roomlb".
    iMod (mono_list_auth_own_update_app [(l, t, b)] with "Museum") as "[Museum #muslb]".
    iSplitR.
    { iModIntro. fr. fr. all: fr.
      - case_bool_decide... iRight. destruct Heltslen...
      - rewrite lookup_app_r... replace (era - length proom) with 0...
      - rewrite lookup_app_r... replace (era - length museum) with 0...
    }

    (* new era *)
    iMod (mono_nat_own_alloc (top_bot_state t b)) as (γtbe') "[tbeO _]".
    iMod (mono_list_auth_own_update_app [(γtbe', γebr', length l')]
      with "Room") as "[Room #rlb]".

    (* frame *)
    iModIntro. fr. fr.
    { fr. case_bool_decide... fr.
      destruct Heltslen as [_ Hget].
      apply (circ_slice_split_eq (S t)) in Heqs as [Heqs _]...
      destruct (circ_slice_singleton l t) as [x [Hx Hsx]]...
      destruct (circ_slice_singleton l' t) as [y [Hy Hsy]]...
      rewrite Hsx Hsy in Heqs. injection Heqs as [= <-].
      rewrite Hy -Hget Hx...
    }
    { rewrite length_app -Hproomlen. simpl... }
    { rewrite length_app -Hmuslen. simpl... }
    simpl. fr. all: fr.
    - case_bool_decide... iRight. destruct Heltslen...
    - rewrite lookup_app_l...
      2: rewrite length_app; simpl...
      rewrite lookup_app_r...
      replace (length proom + 0 - length proom) with 0...
    - rewrite lookup_app_r...
      replace (length proom + 0 - length museum) with 0...
  Qed.
End dqst.

Section proof.
  Context `{!heapGS Σ, !cldequeG Σ} (dequeN rcuN : namespace) (DISJ : rcuN ## dequeN).
  Variable (rcu : rcu_simple_spec Σ rcuN).
  Notation iProp := (iProp Σ).

  Definition node (p : blk) lv γ_p : iProp :=
    ∃ (l : list val),
      ⌜lv = #(length l) :: l⌝ ∗ ghost_var γ_p (1/2) l.

  Definition deque_inv (γq γera γe : gname) (γdqst : dqst_gnames) (q : blk) : iProp :=
    ∃ (era : nat) (C : blk) (l : list val) (t b : nat) (pop : bool) (γebr : gname),
      ⌜1 ≤ t ≤ b ∧ b < t + length l ∧ length l ≠ 0⌝ ∗
      (* abstract *)
      own γq (●E (circ_slice l t b)) ∗
      ghost_var γera (1/2) (era, C, l, b, pop, γebr) ∗
      dqst_auth γdqst era γebr l t b ∗
      (* physical *)
      (q +ₗ circle) ↦ #C ∗
      ( rcu.(Managed) γe C (γebr) (S (length l)) node ∗
        ghost_var γebr (1/2) l ) ∗
      (q +ₗ qtop) ↦ #t ∗
      (q +ₗ qbot) ↦{#1/2} #(if pop then b-1 else b).

  Definition IsDeque (γe γ : gname) (q : blk) : iProp :=
    ∃ (γq γera : gname) (γdqst : dqst_gnames) (d : blk),
      ⌜γ = encode (γq, γera, γdqst)⌝ ∗
      (q +ₗ qdom) ↦□ #d ∗ rcu.(IsRCUDomain) γe d ∗
      inv dequeN (deque_inv γq γera γe γdqst q).
  Global Instance IsDeque_persistent γe γ q :
    Persistent (IsDeque γe γ q) := _.

  Definition Deque (γ : gname) (frag : list val) : iProp :=
    ∃ (γq γera : gname) (γdqst : dqst_gnames),
      ⌜γ = encode (γq, γera, γdqst)⌝ ∗
      own γq (◯E frag).
  Global Instance Deque_timeless γ frag :
    Timeless (Deque γ frag) := _.

  (* owner of the deque who can call push and pop *)
  Definition OwnDeque (γ : gname) (q : blk) : iProp :=
    ∃ (γq γera : gname) (γdqst : dqst_gnames) (era : nat)
    (l : list val) (C : blk) (b : nat) (γebr : gname),
      ⌜γ = encode (γq, γera, γdqst)⌝ ∗
      ghost_var γera (1/2) (era, C, l, b, false, γebr) ∗
      (q +ₗ qbot) ↦{#1/2} #b.

  Lemma own_ea_agree γ a b :
    own γ (●E a) -∗ own γ (◯E b) -∗ ⌜a = b⌝.
  Proof.
    iIntros "● ◯".
    by iCombine "● ◯" gives %?%excl_auth_agree_L.
  Qed.

  Lemma own_ea_update a' γ a b :
    own γ (●E a) -∗ own γ (◯E b) ==∗ own γ (●E a') ∗ own γ (◯E a').
  Proof.
    iIntros "● ◯".
    iMod (own_update_2 γ _ _ (●E a' ⋅ ◯E a') with "● ◯") as "[● ◯]".
    - apply excl_auth_update.
    - by iFrame.
  Qed.

  Lemma deque_new_spec :
    deque_new_spec' dequeN rcuN deque_new rcu Deque IsDeque OwnDeque.
  Proof with extended_auto.
    iIntros (γe d n Hsz Φ) "!> #IRD HΦ". wp_lam.

    (* allocate *)
    wp_alloc q as "q↦" "†q". wp_pures.
      do 4 rewrite array_cons. iDestruct "q↦" as "(C & T & B & D & _)".
    wp_lam. wp_alloc C as "SzA" "†SzA"... wp_pures.
      replace (Z.to_nat (1 + n)) with (1 + n)...
      rewrite replicate_add array_cons. iDestruct "SzA" as "[Sz A]".
    wp_store. wp_pures... wp_store. wp_pures. wp_store. wp_store. wp_store.
    iDestruct "B" as "[B1 B2]".

    (* make resources *)
    iMod (pointsto_persist with "D") as "#D".
    iMod (own_alloc (●E [] ⋅ ◯E [])) as (γq) "[γq● γq◯]". 1: apply excl_auth_valid.
    iMod (ghost_var_alloc (replicate n #0)) as (γebr) "[ml1 ml2]".
    iMod (ghost_var_alloc (0, C, (replicate n #0), 1, false, γebr)) as (γera) "[Era1 Era2]".
    iMod (dqst_auth_alloc γebr (replicate n #0)) as (γdqst) "Auth"...
    iCombine "Sz A" as "SzA". rewrite -array_cons.
    iMod (rcu.(rcu_domain_register) node with "IRD [$SzA †SzA ml2]") as "Man"...
    { rewrite /= length_replicate. iFrame. fr. }
    iMod (inv_alloc dequeN _ (deque_inv γq γera γe γdqst q)
      with "[C T B1 Man γq● Auth Era1 ml1]") as "Inv".
    { fr. fr. }

    (* apply Φ *)
    iApply "HΦ". iModIntro. iSplitL "Inv"; first fr.
    iSplitL "γq◯"; fr.
  Qed.

  Lemma managed_get_circle E γe d C γebr l :
    ↑(ptrN rcuN C) ⊆ E →
    IsRCUDomain rcu γe d -∗
    (Managed rcu γe C γebr (S (length l)) node ∗ ghost_var γebr (1 / 2) l)
    ={E,E∖↑(ptrN rcuN C)}=∗
      (Managed rcu γe C γebr (S (length l)) node ∗ ghost_var γebr (1 / 2) l) ∗
      ghost_var γebr (1/2) l ∗
      (C +ₗ csz) ↦ #(length l) ∗ (C +ₗ carr) ↦∗ l ∗
      ∀ l' : list val,
        ⌜length l = length l'⌝ ∗
        (C +ₗ csz) ↦ #(length l) ∗ (C +ₗ carr) ↦∗ l' ∗
        ghost_var γebr (1/2) l'
          ={E ∖ ↑ptrN rcuN C,E}=∗ True.
  Proof with extended_auto.
    iIntros (HN) "#IRD [Man man]".
    iInv "Man" as (l') "(_ & SzA & man' & Man)" "Ret".
    unfold node. iDestruct "man'" as (larr) ">(%Hl' & man')".
    iDestruct (ghost_var_agree with "man man'") as "%". subst larr.
    rewrite Hl' array_cons. iDestruct "SzA" as "[Sz A]". fr.
    iIntros "!>" (lp) "(%Hlenp & Szp & Ap & Rest)".
    iMod ("Ret" with "[Szp Ap Rest]")...
    iExists (#(length l) :: lp). fr...
    1: simpl... fr. rewrite Hlenp...
  Qed.

  Lemma circle_grow_rec_spec (E : coPset) (γe : gname) (γebr : gname)
  (d C : blk) (arr' : loc) (l l' : list val) (n m t b : nat) :
    ↑(ptrN rcuN C) ⊆ E →
    length l = n → length l' = m →
    0 < n < m →
    t ≤ b < t + n →
    rcu.(IsRCUDomain) γe d -∗
    arr' ↦∗ l' -∗
    <<{ ∀∀ (_ : ()), ▷ rcu.(Managed) γe C γebr (S (length l)) node ∗
          ghost_var γebr (1 / 2) l }>>
      circle_grow_rec #(C +ₗ carr) #n #arr' #m #t #b @ E,∅,↑(ptrN rcuN C)
    <<{ ∃∃ (l2' : list val),
      ⌜length l2' = m⌝ ∗
      ⌜circ_slice l t b = circ_slice l2' t b⌝ ∗
      ⌜∀ i, b ≤ i < t + length l → mod_get l' i = mod_get l2' i⌝ ∗
      ▷ rcu.(Managed) γe C γebr (S (length l)) node ∗
      ghost_var γebr (1 / 2) l |
      RET #(); arr' ↦∗ l2'
    }>>.
  Proof with extended_auto.
    iIntros "%HE %Hn %Hm %Hlen %Hlt #IRD A'" (Φ) "AU". wp_pures.
      iRevert "A' AU". iRevert (b l' Hm Hlt).
    iLöb as "IH". iIntros (b l') "%Hm %Hlt A' AU".
    wp_pures. wp_lam. unfold circ_access. wp_pures.
    remember (C +ₗ carr) as Carr.

    case_bool_decide; last first; wp_pure credit:"£".
    { (* end loop *)
      iMod "AU" as (_) "[Cont [_ Commit]]".
      iMod ("Commit" $! l' with "[Cont]") as "HΦ"; fr.
      1: repeat rewrite circ_slice_nil...
      iApply "HΦ"...
    }

    (* read b *)
    wp_pures.
    destruct b as [|b]...
    replace (Z.of_nat (S b) - 1)%Z with (Z.of_nat b)...
      rewrite rem_mod_eq...
    wp_bind (! _)%E.
      iMod "AU" as (_) "[[A man] [Abort _]]".
      iMod (lc_fupd_elim_later with "£ A") as "A".
      iMod (managed_get_circle with "[] [A man]") as "(A & man & Sz' & Ap & Ret)"... 1: fr.
        rewrite -HeqCarr.
      destruct (mod_get_is_Some l b) as [v Hv]...
      wp_apply (wp_load_offset with "Ap") as "Ap". 1: rewrite -Hn...
      iMod ("Ret" with "[Sz' Ap man]") as "_". 1: fr.
      iMod ("Abort" with "[A]") as "AU". 1: iDestruct "A" as "[Man man]"; fr.
    iApply (fupd_mask_intro)... iIntros "Close". iMod "Close".
    iModIntro. wp_pures.

    (* write b *)
    wp_bind (_ <- _)%E.
      rewrite rem_mod_eq...
      destruct (mod_get_is_Some l' b) as [v' Hv']...
      iApply (wp_store_offset with "A'"). 1: rewrite -Hm...
    iIntros "!> A'". wp_pures.

    (* recurse *)
    iApply ("IH" $! b (<[b `mod` m:=v]> l') with "[] [] [A']")...
      1: rewrite length_insert...
    iAuIntro.
    rewrite /atomic_acc /=.
      iMod "AU" as (_) "[Cont AC]".
      iModIntro. iExists (). iFrame "Cont".
      iSplit.
      { iIntros "Cont".
        iDestruct "AC" as "[Abort _]".
        iMod ("Abort" with "Cont") as "AU". fr. }
    iIntros (l2') "(%Hm' & %Heqs & %Hlast & A)".
      iDestruct "AC" as "[_ Commit]".
    iMod ("Commit" $! l2' with "[A]") as "HΦ".
    { iFrame. iPureIntro. repeat split...
      - rewrite (circ_slice_shrink_right _ _ _ v)...
        2: replace (S b - 1) with b...
        rewrite (circ_slice_shrink_right _ _ (S b) v)...
        all: replace (S b - 1) with b...
        + rewrite Heqs...
        + rewrite -Hlast... unfold mod_get.
          rewrite length_insert Hm list_lookup_insert...
          rewrite Hm. apply Nat.mod_upper_bound...
      - intros i Hi. rewrite -Hlast... unfold mod_get.
        rewrite length_insert Hm list_lookup_insert_ne...
        apply close_mod_neq...
    }
    iIntros "!> A'". iApply "HΦ"...
  Qed.

  Lemma circle_grow_spec (E : coPset) (γe : gname) (γebr : gname)
  (d C : blk) (l : list val) (t b : nat) :
    ↑(ptrN rcuN C) ⊆ E →
    0 < length l →
    t ≤ b < t + length l →
    rcu.(IsRCUDomain) γe d -∗
    <<{ ∀∀ (_ : ()),
        ▷ rcu.(Managed) γe C γebr (S (length l)) node ∗
          ghost_var γebr (1 / 2) l }>>
      circle_grow #C #t #b #(length l) @ E,∅,↑(ptrN rcuN C)
    <<{ ∃∃ (C' : blk) (l' : list val),
      ⌜length l < length l'⌝ ∗
      ⌜circ_slice l t b = circ_slice l' t b⌝ ∗
      ▷ rcu.(Managed) γe C γebr (S (length l)) node ∗
      ghost_var γebr (1 / 2) l |
    RET #C';
      (C' +ₗ csz) ↦ #(length l') ∗ (C' +ₗ carr) ↦∗ l' ∗ † C' … Z.to_nat (S (length l')) }>>.
  Proof with extended_auto.
    iIntros "%HE %Hlen %Hlt #IRD" (Φ) "AU".
    wp_lam. wp_pures. wp_lam. wp_pures.
    wp_alloc SzA' as "SzA'" "†SzA'"... wp_pures.
      replace (Z.to_nat (1 + 2 * length l)) with (1 + 2 * length l)...
      rewrite replicate_add array_cons. iDestruct "SzA'" as "[Sz' A']".
    wp_store. wp_pures.
    replace (2 * Z.of_nat (length l))%Z with (Z.of_nat (2 * length l))...

    (* make l' *)
    awp_apply (circle_grow_rec_spec with "[] [A']")... unfold atomic_acc.
    iMod "AU" as (_) "[A AC]".
    iModIntro. iExists (). iFrame "A". iSplit.
    { iIntros "A". iDestruct "AC" as "[Abort _]". fr.
      iApply ("Abort" with "A").
    }

    iIntros (l2') "(%Hlen' & %Heqs & %Hrest & A & A2)".
      iCombine "A A2" as "A".
      iDestruct "AC" as "[_ Commit]".
      iMod ("Commit" $! SzA' l2' with "[A]") as "HΦ"; fr.
    iIntros "!> A'".
    wp_pures. iModIntro. iApply "HΦ". fr. rewrite Hlen'. fr.
  Qed.

  Lemma deque_push_spec :
    deque_push_spec' dequeN rcuN deque_push rcu Deque IsDeque OwnDeque.
  Proof with extended_auto using All.
    iIntros (γe γ q g v).
    iIntros "#Is Own G" (Φ) "AU".
      iDestruct "Own" as (γq γera γdqst) "Own".
        iDestruct "Own" as (era l C b γebr) "Own".
        iDestruct "Own" as "(%Enc & eraOwn & bOwn)".
        remember (C +ₗ Z.of_nat 1) as Carr.
      iDestruct "Is" as (γq' γera' γdqst') "Inv".
        iDestruct "Inv" as (d) "(%Enc' & D & IRD & Inv)".
        encode_agree Enc.
    wp_lam. unfold circ_access. wp_pures.
    wp_load. wp_pures.

    (* 1. load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (era1 C1 l1 t1 b1 pop1 γebr1) "Invs".
        iDestruct "Invs" as "(>%Htb1 & ● & >Era & Dqst & C & A & >T & B)".
      iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
      iDestruct (dqst_get_frag with "Dqst") as "#F1".
      wp_load.
    iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l. fr. }
    wp_pures...

    (* Q. get circle *)
    wp_bind (! _)%E.
      iInv "Inv" as (eraQ CQ lQ tQ bQ popQ γebrQ) "Invs"...
        iDestruct "Invs" as "(>%HtbQ & ● & >Era & Dqst & >C & A & T & B)".
      iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
      wp_load.
    iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l. fr. }
    wp_pure credit:"£". wp_pures.

    (* A. read size *)
    wp_bind (! _)%E.
      iInv "Inv" as (eraA CA lA tA bA popA γebrA) "Invs".
        iMod (lc_fupd_elim_later with "£ Invs") as "Invs".
        iDestruct "Invs" as "(%HtbA & ● & Era & Dqst & C & A & T & B)".
      iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-]...
      iMod (managed_get_circle with "[] [A]") as "(A & man & Sz' & A' & Ret)"... 1: solve_ndisj.
      wp_load.
      iMod ("Ret" $! l with "[man Sz' A']") as "_". 1: fr.
    iModIntro. iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l. fr. }
    wp_pure credit:"£". wp_pures.

    case_bool_decide; last first; wp_pures...
    - (* W. reload circle *)
      wp_bind (! _)%E.
        iInv "Inv" as (eraW CW lW tW bW popW γebrW) "Invs"...
          iDestruct "Invs" as "(>%HtbW & ● & >Era & Dqst & >C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
        wp_load.
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l. fr. }

      (* B. get size *)
      wp_pures...
      wp_bind (! _)%E.
        iInv "Inv" as (eraB CB lB tB bB popB γebrB) "Invs".
          iMod (lc_fupd_elim_later with "£ Invs") as "Invs".
          iDestruct "Invs" as "(%HtbB & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-]...
        iMod (managed_get_circle with "[] [A]") as "(A & man & Sz' & A' & Ret)"... 1: solve_ndisj.
        wp_load.
        iMod ("Ret" $! l with "[man Sz' A']") as "_". 1: fr.
      iModIntro. iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l. fr. }

      (* 2. write to circle *)
      wp_pure credit:"£". wp_pures.
      rewrite -HeqCarr rem_mod_eq...
      wp_bind (_ <- _)%E.
        iInv "Inv" as (era2 C2 l2 t2 b2 pop2 γebr2) "Invs".
          iMod (lc_fupd_elim_later with "£ Invs") as "Invs".
          iDestruct "Invs" as "(%Htb2 & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
        iMod (ghost_var_update_halves (era, C, (mod_set l b v), b, false, γebr)
          with "eraOwn Era") as "[eraOwn Era]".
        iDestruct (dqst_auth_write_bot v with "Dqst") as "Dqst".
        iMod (managed_get_circle with "[] [A]") as "([Man man1] & man2 & Sz' & A' & Ret)"... 1: solve_ndisj.
          iMod (ghost_var_update_halves (<[b `mod` length l:=v]> l)
            with "man1 man2") as "[man1 man2]".
          rewrite -HeqCarr.
          iApply (wp_store_offset with "A'"). 1: apply mod_get_is_Some...
        iIntros "!> A'".
        iMod ("Ret" $! (<[b `mod` length l:=v]> l) with "[man2 Sz' A']") as "_".
          1: rewrite length_insert; fr.
        iCombine "Man man1" as "A".
      iModIntro. iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,(mod_set l b v),t2,b.
        rewrite mod_set_length circ_slice_update_right... fr. }
      wp_pures.

      (* 3. increment bot *)
      iInv "Inv" as (era3 C3 l3 t3 b3 pop3 γebr3) "Invs".
        iDestruct "Invs" as "(>%Htb3 & ● & >Era & >Dqst & C & A & T & >B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
        iMod (ghost_var_update_halves (era, C, (mod_set l b v), S b, false, γebr)
          with "eraOwn Era") as "[eraOwn Era]".
        iDestruct (dqst_get_lb with "Dqst F1") as "%Ht13".
          iMod (dqst_auth_push with "Dqst") as "Dqst". 1: rewrite mod_set_length...
        iCombine "bOwn B" as "B". wp_store.
          replace (Z.of_nat b + 1)%Z with (Z.of_nat (S b))...
        iDestruct "B" as "[bOwn B]".
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γera' γbglob') "[%Enc' ◯]". encode_agree Enc.
        iDestruct (own_ea_agree with "● ◯") as "%Hl'".
        iMod (own_ea_update (l' ++ [v]) with "● ◯") as "[● ◯]".
        iMod ("Commit" with "[◯]") as "HΦ". 1: fr.
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists era, C, (mod_set l b v), t3, (S b). fr.
        rewrite (circ_slice_extend_right _ _ _ v)... 2: rewrite mod_set_get...
        subst l'. fr. rewrite mod_set_length... }
      iApply "HΦ". fr.
    - (* X. grow *)
      awp_apply circle_grow_spec...
        iInv "Inv" as (eraX CX lX tX bX popX γebrX) "Invs".
          iDestruct "Invs" as "(>%HtbX & ● & >Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
        iDestruct "A" as "[Man >man]". iCombine "Man man" as "A".
          iAaccIntro with "A".
          { iIntros "A". iSplitL "● Era Dqst C A T B". 2: fr.
            iExists _,_,l. fr. fr. }
        iIntros (CX lX) "(%HlenX & %Heqs & A)".
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l. fr. fr. }
      iIntros "(SzOwn & [AX †SzAX])". wp_pures...
        replace (CX +ₗ 1) with (CX +ₗ Z.of_nat 1)...
        remember (CX +ₗ Z.of_nat 1) as CXarr.

      (* Y. replace array *)
      wp_bind (_ <- _)%E.
        iInv "Inv" as (eraY caY lY tY bY popY γebrY) "Invs".
          iMod (lc_fupd_elim_later with "£ Invs") as "Invs".
          iDestruct "Invs" as "(%HtbY & ● & Era & Dqst & C & [Man A] & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
        iMod (ghost_var_alloc lX) as (γebrY) "[man1 man2]".
        iMod (ghost_var_alloc (length lX)) as (γnY) "mann".
          iMod (ghost_var_persist with "mann") as "#mann".
        iMod (ghost_var_update_halves (S era, CX, lX, b, false, γebrY)
          with "eraOwn Era") as "[eraOwn Era]".
          iDestruct (dqst_get_lb with "Dqst F1") as "%Ht1Y".
          apply (circ_slice_split_eq tY) in Heqs as Heqsd... destruct Heqsd as [_ HeqsR]...
        iCombine "SzOwn AX" as "AX". iEval (rewrite HeqCXarr -array_cons) in "AX".
        iMod (rcu.(rcu_domain_register) node with "IRD [$AX †SzAX man2]") as "AX"; [solve_ndisj| |].
          { fr. }
        iMod (dqst_auth_archive γebrY with "[A] [Dqst]") as "[#Arch Dqst]"; [|exact HeqsR|..]...
        wp_store.
      iSplitL "● Era Dqst C AX man1 T B".
      { iModIntro; iNext. iExists _,_,lX.
        fr. fr. rewrite -HeqsR. fr. }
      iModIntro. wp_pures...

      (* W. reload circle *)
      wp_bind (! _)%E.
        iInv "Inv" as (eraW CW lW tW bW popW γebrW) "Invs"...
          iDestruct "Invs" as "(>%HtbW & ● & >Era & Dqst & >C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
        wp_load.
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,lX. fr. }
      wp_pure credit:"£". wp_pures.

      (* B. get size *)
      wp_bind (! _)%E.
        iInv "Inv" as (eraB CB lB tB bB popB γebrB) "Invs".
          iMod (lc_fupd_elim_later with "£ Invs") as "Invs".
          iDestruct "Invs" as "(%HtbB & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-]...
        iMod (managed_get_circle with "[] [A]") as "(A & man & Sz' & A' & Ret)"... 1: solve_ndisj.
        wp_load.
        iMod ("Ret" $! lX with "[man Sz' A']") as "_". 1: fr.
      iModIntro. iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,lX. fr. }

      (* 2. write to circle *)
      wp_pure credit:"£". wp_pures.
      rewrite -HeqCXarr rem_mod_eq...
      wp_bind (_ <- _)%E.
        iInv "Inv" as (era2 C2 l2 t2 b2 pop2 γebr2) "Invs".
          iMod (lc_fupd_elim_later with "£ Invs") as "Invs".
          iDestruct "Invs" as "(%Htb2 & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
        iMod (ghost_var_update_halves (S era, CX, (mod_set lX b v), b, false, γebrY)
          with "eraOwn Era") as "[eraOwn Era]".
        iDestruct (dqst_auth_write_bot v with "Dqst") as "Dqst".
        iClear "Man".
        iMod (managed_get_circle with "[] [A]") as "([Man man1] & man2 & Sz' & A' & Ret)"... 1: solve_ndisj.
          iMod (ghost_var_update_halves (<[b `mod` length lX:=v]> lX)
            with "man1 man2") as "[man1 man2]".
          rewrite -HeqCXarr.
          iApply (wp_store_offset with "A'"). 1: apply mod_get_is_Some...
        iIntros "!> A'".
        iMod ("Ret" $! (<[b `mod` length lX:=v]> lX) with "[man2 Sz' A']") as "_".
          1: rewrite length_insert; fr.
        iCombine "Man man1" as "A".
      iModIntro. iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,(mod_set lX b v),t2,b.
        rewrite mod_set_length circ_slice_update_right... fr. }
      wp_pures.

      (* 3. increment bot *)
      iInv "Inv" as (era3 C3 l3 t3 b3 pop3 γebr3) "Invs".
        iDestruct "Invs" as "(>%Htb3 & ● & >Era & >Dqst & C & A & T & >B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
        iMod (ghost_var_update_halves (S era, CX, (mod_set lX b v), S b, false, γebrY)
          with "eraOwn Era") as "[eraOwn Era]".
        iDestruct (dqst_get_lb with "Dqst F1") as "%Ht13".
          iMod (dqst_auth_push with "Dqst") as "Dqst". 1: rewrite mod_set_length...
        iCombine "bOwn B" as "B". wp_store.
          replace (Z.of_nat b + 1)%Z with (Z.of_nat (S b))...
        iDestruct "B" as "[bOwn B]".
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γera' γbglob') "[%Enc' ◯]". encode_agree Enc.
        iDestruct (own_ea_agree with "● ◯") as "%Hl'".
        iMod (own_ea_update (l' ++ [v]) with "● ◯") as "[● ◯]".
        iMod ("Commit" with "[◯]") as "HΦ". 1: fr.
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists (S era), CX, (mod_set lX b v), t3, (S b). fr.
        rewrite (circ_slice_extend_right _ _ _ v)... 2: rewrite mod_set_get...
        subst l'. fr. rewrite mod_set_length... }
      iApply "HΦ". fr.
    Unshelve. done.
  Qed.

  Lemma deque_pop_spec :
    deque_pop_spec' dequeN rcuN deque_pop rcu Deque IsDeque OwnDeque.
  Proof with extended_auto using All.
    iIntros (γe γ q g).
    iIntros "#Is Own G" (Φ) "AU".
      iDestruct "Own" as (γq γera γdqst) "Own".
        iDestruct "Own" as (era l C b γebr) "Own".
        iDestruct "Own" as "(%Enc & eraOwn & bOwn)".
        remember (C +ₗ Z.of_nat 1) as Carr.
      iDestruct "Is" as (γq' γera' γdqst') "Inv".
        iDestruct "Inv" as (d) "(%Enc' & D & IRD & Inv)".
        encode_agree Enc.
    wp_lam. unfold circ_access. wp_pures.
    wp_load. wp_pures...

    (* Q. get circle *)
    wp_bind (! _)%E.
      iInv "Inv" as (eraQ CQ lQ tQ bQ popQ γebrQ) "Invs"...
        iDestruct "Invs" as "(>%HtbQ & ● & >Era & Dqst & >C & A & T & B)".
      iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
      wp_load.
    iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l. fr. }
    wp_pure credit:"£". wp_pures...

    (* A. read size *)
    wp_bind (! _)%E.
      iInv "Inv" as (eraA CA lA tA bA popA γebrA) "Invs".
        iMod (lc_fupd_elim_later with "£ Invs") as "Invs".
        iDestruct "Invs" as "(%HtbA & ● & Era & Dqst & C & A & T & B)".
      iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-]...
      iMod (managed_get_circle with "[] [A]") as "(A & man & Sz' & A' & Ret)"... 1: solve_ndisj.
      wp_load.
      iMod ("Ret" $! l with "[man Sz' A']") as "_". 1: fr.
    iModIntro. iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l. fr. }
    wp_pures.

    (* 1. decrement bot *)
    wp_bind (_ <- _)%E.
      iInv "Inv" as (era1 C1 l1 t1 b1 pop1 γebr1) "Invs".
        iDestruct "Invs" as "(>%Htb1 & ● &> Era & Dqst & C & A & T & >B)".
      iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
      iMod (ghost_var_update_halves (era, C, l, b, true, γebr)
        with "eraOwn Era") as "[eraOwn Era]".
      iCombine "bOwn B" as "B". wp_store.
      iDestruct "B" as "[bOwn B]".
    iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l. fr. }
    wp_pures.

    (* 2. load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (era2 C2 l2 t2 b2 pop2 γebr2) "Invs".
        iDestruct "Invs" as "(>%Htb2 & ● & >Era & Dqst & C & A & >T & B)".
      iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
      wp_load.

    destruct (decide (t2 < b-1)).
    { (* normal case, this point is the commit point *)
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γera' γdqst') "[%Enc' ◯]". encode_agree Enc.
        destruct (mod_get_is_Some l (b-1)) as [x Hx]...
        iDestruct (own_ea_agree with "● ◯") as "%Eq". subst l'.
        iMod (own_ea_update (circ_slice l t2 (b-1)) with "● ◯") as "[● ◯]".
        iMod (ghost_var_update_halves (era, C, l, b-1, false, γebr)
          with "eraOwn Era") as "[eraOwn Era]".
        iMod (dqst_auth_pop with "Dqst") as "Dqst"...
      iMod ("Commit" $! (circ_slice l t2 (b-1)) (SOMEV x) with "[◯]") as "HΦ".
      { fr. rewrite -circ_slice_extend_right... replace (S (b-1)) with b... }
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l,t2. fr. fr. replace (Z.of_nat b - 1)%Z with (Z.of_nat (b - 1))%Z... }
      wp_pures.

      case_bool_decide... wp_pure credit:"£". wp_pures. rewrite -HeqCarr.
      replace (Z.of_nat b - 1)%Z with (Z.of_nat (b - 1))%Z... rewrite rem_mod_eq...
      wp_bind (! _)%E.

      (* S. read array *)
      wp_bind (! _)%E.
        iInv "Inv" as (eraS caS lS tS bS popS γebrS) "Invs".
          iMod (lc_fupd_elim_later with "£ Invs") as "Invs".
          iDestruct "Invs" as "(%HtbS & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
        iMod (managed_get_circle with "[] A") as "(A & man & Sz' & A' & Ret)"... 1: solve_ndisj.
          rewrite -HeqCarr.
        iApply (wp_load_offset with "A'"). { unfold mod_get in Hx. rewrite Hx... }
        iIntros "!> A'".
        iMod ("Ret" $! l with "[Sz' A' man]") as "_". 1: fr.
      iModIntro. iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l. fr. }
      wp_pures. case_bool_decide... wp_pures.
      iApply "HΦ". fr.
    }

    iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l. fr. }
    wp_pures.

    case_bool_decide; wp_pure credit:"£"; wp_pures.
    { (* empty *)
      wp_pures. assert (t2 = b)... subst t2.
      (* 3. roll back bot *)
      wp_bind (_ <- _)%E.
        iInv "Inv" as (era3 C3 l3 t3 b3 pop3 γebr3) "Invs".
          iDestruct "Invs" as "(>%Htb3 & ● & >Era & Dqst & C & A & T & >B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
        iMod (ghost_var_update_halves (era, C, l, b, false, γebr)
          with "eraOwn Era") as "[eraOwn Era]".
        iCombine "bOwn B" as "B". wp_store.
        iDestruct "B" as "[bOwn B]".
        iMod "AU" as (l') "[Cont [_ Commit]]".
      iMod ("Commit" $! l' NONEV with "[Cont]") as "HΦ"...
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l. fr. }
      wp_pures. iApply "HΦ". fr.
    }

    (* non-empty *)
    rewrite -HeqCarr.
    replace (Z.of_nat b - 1)%Z with (Z.of_nat (b - 1))%Z... rewrite rem_mod_eq...

    (* S. read array *)
    wp_bind (! _)%E.
      destruct (mod_get_is_Some l (b-1)) as [x Hx]...
      iInv "Inv" as (eraS caS lS tS bS popS γebrS) "Invs".
        iMod (lc_fupd_elim_later with "£ Invs") as "Invs".
        iDestruct "Invs" as "(%HtbS & ● & Era & Dqst & C & A & T & B)".
      iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
      iMod (managed_get_circle with "[] A") as "(A & man & Sz' & A' & Ret)"... 1: solve_ndisj.
        rewrite -HeqCarr.
      iApply (wp_load_offset with "A'"). { unfold mod_get in Hx. rewrite Hx... }
      iIntros "!> A'".
      iMod ("Ret" $! l with "[Sz' A' man]") as "_". 1: fr.
    iModIntro. iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l. fr. }
    wp_pures. case_bool_decide... wp_pure credit:"£". wp_pures.

    (* 3. CAS for one-element case *)
    assert (b = S t2)... subst b.
    wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (era3 C3 l3 t3 b3 pop3 γebr3) "Invs".
        iMod (lc_fupd_elim_later with "£ Invs") as "Invs".
        iDestruct "Invs" as "(%Htb3 & ● & Era & Dqst & C & A & T & B)".
      iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
    destruct (decide (t2 = t3)).
    + (* success *)
      subst t3. wp_cmpxchg_suc.
        replace (Z.of_nat t2 + 1)%Z with (Z.of_nat (S t2))...
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γera' γdqst') "[%Enc' ◯]". encode_agree Enc.
        iMod (dqst_auth_update with "Dqst") as "Dqst"...
        iDestruct (own_ea_agree with "● ◯") as "%Eq". subst l'.
        iMod (own_ea_update [] with "● ◯") as "[● ◯]".
      iMod ("Commit" $! [] (SOMEV x) with "[◯]") as "HΦ".
      { fr. rewrite (circ_slice_extend_right _ _ _ x)...
        1: rewrite circ_slice_nil... replace t2 with (S t2 - 1)... }
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists era, C, l, (S t2), (S t2).
        rewrite circ_slice_nil... fr. fr. }
      wp_pures.

      (* 4. roll back bot *)
      wp_bind (_ <- _)%E.
        iInv "Inv" as (era4 C4 l4 t4 b4 pop4 γebr4) "Invs".
          iDestruct "Invs" as "(>%Htb4 & ● & >Era & Dqst & C & A & T & >B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
        replace (Z.of_nat (S t2 - 1))%Z with (Z.of_nat t2)%Z...
        replace (Z.of_nat (S t2) - 1)%Z with (Z.of_nat t2)%Z...
        iMod (ghost_var_update_halves (era, C, l, S t2, false, γebr)
          with "eraOwn Era") as "[eraOwn Era]".
        iCombine "bOwn B" as "B". wp_store.
          replace (Z.of_nat t2 + 1)%Z with (Z.of_nat (S t2))%Z...
        iDestruct "B" as "[bOwn B]".
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l. fr. }
      wp_pures. iApply "HΦ". fr.
    + (* fail *)
      wp_cmpxchg_fail.
      iMod "AU" as (l') "[Cont [_ Commit]]".
      iMod ("Commit" $! l' NONEV with "[Cont]") as "HΦ"...
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l. fr. }
      wp_pures.

      (* 4. roll back bot *)
      wp_bind (_ <- _)%E.
        iInv "Inv" as (era4 C4 l4 t4 b4 pop4 γebr4) "Invs".
          iDestruct "Invs" as "(>%Htb4 & ● & >Era & Dqst & C & A & T & >B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <- <-].
        replace (Z.of_nat (S t2 - 1))%Z with (Z.of_nat t2)%Z...
        replace (Z.of_nat (S t2) - 1)%Z with (Z.of_nat t2)%Z...
        iMod (ghost_var_update_halves (era, C, l, S t2, false, γebr)
          with "eraOwn Era") as "[eraOwn Era]".
        iCombine "bOwn B" as "B". wp_store.
          replace (Z.of_nat t2 + 1)%Z with (Z.of_nat (S t2))%Z...
        iDestruct "B" as "[bOwn B]".
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l. fr. }
      wp_pures. iApply "HΦ". fr.
  Qed.

  Lemma deque_steal_spec :
    deque_steal_spec' dequeN rcuN (deque_steal rcu) rcu Deque IsDeque.
  Proof with extended_auto using All.
    iIntros (γe γ q g).
    iIntros "#Is G" (Φ) "AU".
    iDestruct "Is" as (γq γera γdqst) "Inv".
      iDestruct "Inv" as (d) "(%Enc & D & IRD & Inv)".
    wp_lam. unfold circ_access. wp_pures.

    (* 1. load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (era1 C1 l1 t1 b1 pop1 γebr1) "Invs".
        iDestruct "Invs" as "(>%Htb1 & ● & Era & Dqst & C & A & >T & B)".
      iDestruct (dqst_get_frag with "Dqst") as "#F1".
      wp_load.
    iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l1. fr. }
    wp_pures.

    (* 2. load bot *)
    wp_bind (! _)%E.
      iInv "Inv" as (era2 C2 l2 t2 b2 pop2 γebr2) "Invs".
        iDestruct "Invs" as "(>%Htb2 & ● & Era & >Dqst & C & A & T & >B)".
      iDestruct (dqst_get_frag with "Dqst") as "#F2".
      iDestruct (dqst_get_lb with "Dqst F1") as "%Lb12".
      wp_load.
    iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l2. fr. }
    wp_pure credit:"£". wp_pures.
    wp_apply (guard_activate_spec with "[] G") as (?) "G"... wp_pures...

    (* 3. load array *)
    wp_bind (! _)%E.
      iInv "Inv" as (era3 C3 l3 t3 b3 pop3 γebr3) "Invs".
        iMod (lc_fupd_elim_later with "£ Invs") as "Invs".
        iDestruct "Invs" as "(%Htb3 & ● & Era & Dqst & C & A & T & B)"...
        iDestruct "A" as "[A man]".
      iDestruct (dqst_get_frag with "Dqst") as "#F3".
      iDestruct (dqst_get_lb with "Dqst F2") as "%Lb23".
      iMod (guard_protect with "[//] A G") as "(A & G & #AInfo)"; [solve_ndisj|].
      wp_load.
    iModIntro. iSplitL "● Era Dqst C A T B man".
    { iExists _,_,l3. fr. }
    replace (if pop2 then LitInt (Z.of_nat b2 - 1)%Z else LitInt (Z.of_nat b2))
      with (LitInt (Z.of_nat (if pop2 then (b2 - 1) else b2))).
      2: { destruct pop2... replace (Z.of_nat b2 - 1)%Z with (Z.of_nat (b2 - 1))... }
    wp_pures...

    (* A. read size *)
    wp_bind (! _)%E.
      iInv "AInfo" as (?) "(%HLenA & C3 & >node & G)".
        iDestruct "node" as (l3' ->) "man'".
        assert (length l3' = length l3) as Hlen3'... rewrite Hlen3'.
        rewrite array_cons. iDestruct "C3" as "[Sz3 A3]".
      wp_load.
      iModIntro. iSplitL "man' Sz3 A3".
      { fr. fr. rewrite Hlen3'... }
    wp_pures.

    (* no chance to steal *)
    case_bool_decide as Hif; wp_pures.
    { wp_apply (guard_deactivate_spec with "[] G") as "G"... wp_pures.
      iMod "AU" as (l) "[Cont [_ Commit]]".
      iMod ("Commit" $! l NONEV with "[Cont]") as "Φ"...
      iApply "Φ"... }
    assert (t1 < b2) as Htb12. 1: destruct pop2...

    (* 4. get_circle *)
    rewrite rem_mod_eq. 2: lia.
    wp_bind (! _)%E.
      iInv "Inv" as (era4 C4 l4 t4 b4 pop4) "Invs".
        iDestruct "Invs" as (γebr4) "(>%Htb4 & ● & Era & >Dqst & C & A & T & B)".
      iDestruct (dqst_get_frag with "Dqst") as "#F4".
      iDestruct (dqst_get_lb with "Dqst F3") as "%Lb34".
    destruct (decide (era3 = era4)) as [eqγ|neqγ].
    - (* array was not archived *)
      subst era4.
        iDestruct (dqst_frag_agree with "F3 F4") as "(%Hγ34 & %Hlen)".
          subst γebr4. rewrite Hlen. clear Hlen.
        remember (C3 +ₗ 1%nat) as C3arr.
        destruct (mod_get_is_Some l4 t1) as [v Hv]...
        iInv "AInfo" as (lv) "(%Hlen4 & C4 & >node & G)".
          iDestruct "node" as (l4' ->) "man'".
          iDestruct "A" as "[Man >man]".
          iDestruct (ghost_var_agree with "man man'") as "%". subst l4'.
          rewrite array_cons. iDestruct "C4" as "[Sz4 A4]".
          replace (C3 +ₗ 1) with C3arr...
        iApply (wp_load_offset with "A4")...
        iIntros "!> A4". iModIntro. iSplitL "man' Sz4 A4".
        { iExists (_ :: _). fr. replace (C3 +ₗ 1) with C3arr. fr. }
      iModIntro. iSplitL "● Era Dqst C Man man T B".
      { iExists _,_,l4. fr. }
      wp_pures.
      wp_apply (guard_deactivate_spec with "IRD G") as "G"; [done|]. wp_pures.

      (* 5. CAS *)
      wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (era5 C5 l5 t5 b5 pop5 γebr5) "Invs".
        iDestruct "Invs" as "(>%Htb5 & ● & Era & >Dqst & C & A & T & B)".
        iDestruct (dqst_get_frag with "Dqst") as "#F5".
        iDestruct (dqst_get_lb with "Dqst F4") as "%Lb45".
      destruct (decide (t1 = t5)); last first.
      { (* fail *)
        wp_cmpxchg_fail.
        iMod "AU" as (lau) "[Cont [_ Commit]]".
        iMod ("Commit" $! lau NONEV with "[Cont]") as "HΦ"...
        iModIntro. iSplitL "● Era Dqst C A T B".
        { iExists _,_,l5. fr. }
        wp_pures. iApply "HΦ"...
      }
      (* success *)
      subst t5. wp_cmpxchg_suc.
        replace (Z.of_nat t1 + 1)%Z with (Z.of_nat (S t1))...
        assert (t1 = t2)... subst t2.
        assert (t1 = t3)... subst t3. assert (t1 < b3) as Htb13...
        assert (t1 = t4)... subst t4. assert (t1 < b4) as Htb14...
        assert (t1 < b5) as Htb15...
        assert (mod_get l5 t1 = Some v) as Hv5.
        { replace (mod_get l5 t1) with (mod_get l4 t1)...
          apply Lb45... }
      iMod "AU" as (lau) "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γera' γdqst') "[%Enc' ◯]". encode_agree Enc'.
        iDestruct (own_ea_agree with "● ◯") as "%Hlau". subst lau.
        rewrite (circ_slice_shrink_left _ _ _ v)...
        iMod (own_ea_update (circ_slice l5 (S t1) b5)
          with "● ◯") as "[● ◯]".
        iMod (dqst_auth_update with "Dqst") as "Dqst"...
      iMod ("Commit" $! (circ_slice l5 (S t1) b5) (SOMEV v)
        with "[◯]") as "HΦ"; fr.
      iModIntro. iSplit.
      { fr. }
      wp_pures. iApply "HΦ"...
    - (* array was archived *)
      remember (C3 +ₗ 1%nat) as C3arr.
      iDestruct (dqst_get_archived with "Dqst F3")
        as (l' t' b') "#Arch"...
        iDestruct (dqst_archived_get_lb with "Arch F3") as "%Ht3'".
        iDestruct (dqst_archived_get_frag with "Arch") as "F'".
        iDestruct (dqst_get_lb with "Dqst F'") as "%Lb'4".
        iDestruct (dqst_frag_agree with "F3 F'") as "[_ %Hl3']".
        rewrite Hl3'. destruct (mod_get_is_Some l' t1) as [v Hv]...
          iDestruct (dqst_archived_get_array with "Arch") as "Parr".
        iInv "AInfo" as (lv) "(%Hlen4 & C4 & >node & G)".
          iDestruct "node" as (l4' ->) "man'".
          iCombine "Parr man'" gives %[_ ?]. subst l4'.
          rewrite array_cons. iDestruct "C4" as "[Sz4 A4]".
          replace (C3 +ₗ 1) with C3arr...
        iApply (wp_load_offset with "A4")...
        iIntros "!> A4". iModIntro. iSplitL "man' Sz4 A4".
        { iExists (_::_). fr. replace (C3 +ₗ 1) with C3arr. fr. }
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l4. fr. }
      wp_pures.
      wp_apply (guard_deactivate_spec with "[] G") as "G"... wp_pures.

      (* 5. CAS *)
      wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (era5 C5 l5 t5 b5 pop5 γebr5) "Invs".
        iDestruct "Invs" as "(>%Htb5 & ● & Era & >Dqst & C & A & T & B)".
        iDestruct (dqst_get_frag with "Dqst") as "#F5".
        iDestruct (dqst_get_lb with "Dqst F4") as "%Lb45".
      destruct (decide (t1 = t5)); last first.
      { (* fail *)
        wp_cmpxchg_fail.
        iMod "AU" as (lau) "[Cont [_ Commit]]".
        iMod ("Commit" $! lau NONEV with "[Cont]") as "HΦ". 1: fr.
        iModIntro. iSplitL "● Era Dqst C A T B".
        { iExists _,_,l5. fr. }
        wp_pures. iApply "HΦ"...
      }
      (* success *)
      subst t5. wp_cmpxchg_suc.
        replace (Z.of_nat t1 + 1)%Z with (Z.of_nat (S t1))...
        assert (t1 = t2)... subst t2.
        assert (t1 = t3)... subst t3. assert (t1 < b3) as Htb13...
        assert (t1 = t4)... subst t4. assert (t1 < b4) as Htb14...
        assert (t1 = t')... subst t'. assert (t1 < b') as Htb1'...
        assert (t1 < b5) as Htb15...
        assert (mod_get l5 t1 = Some v) as Hv5.
        { replace (mod_get l5 t1) with (mod_get l4 t1)...
          - rewrite -Hv. symmetry. apply Lb'4...
          - apply Lb45... }
      iMod "AU" as (lau) "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γera' γdqst') "[%Enc' ◯]". encode_agree Enc'.
        iDestruct (own_ea_agree with "● ◯") as "%Hlau". subst lau.
        rewrite (circ_slice_shrink_left _ _ _ v)...
        iMod (own_ea_update (circ_slice l5 (S t1) b5)
          with "● ◯") as "[● ◯]".
        iMod (dqst_auth_update with "Dqst") as "Dqst"...
      iMod ("Commit" $! (circ_slice l5 (S t1) b5) (SOMEV v)
        with "[◯]") as "HΦ"; fr.
      iModIntro. iSplit.
      { fr. }
      wp_pures. iApply "HΦ"...
  Qed.

#[export] Typeclasses Opaque Deque IsDeque.

End proof.

