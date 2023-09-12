From iris.algebra Require Import list excl_auth.
From iris.bi Require Import derived_laws_later.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants ghost_var.
From smr Require Import mono_list mono_nat atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.
From smr.no_recl Require Import spec_cldeque code_cldeque.
From smr Require Import helpers.

Local Ltac extended_auto :=
  eauto;
  try rewrite Nat2Z.id;
  try rewrite replicate_length;
  try rewrite Qp.half_half;
  repeat rewrite loc_add_0; repeat rewrite loc_add_assoc;
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
    deque_tokG :> inG Σ (excl_authR $ listO valO);
    (* info: era, arrptr, C, bot, popping *)
    deque_infoG :> ghost_varG Σ (nat * blk * list val * nat * bool);
    (* RA *)
    topbotG :> mono_natG Σ;
    topeltG :> mono_listG val Σ;
    roomG :> mono_listG (gname * blk * nat) Σ;
    museumG :> mono_listG (list val * nat * nat) Σ
  }.

Definition cldequeΣ : gFunctors :=
  #[ (*invariant *)
    GFunctor (excl_authR $ listO valO);
    ghost_varΣ (nat * blk * list val * nat * bool);
    (* RA *)
    mono_natΣ;
    mono_listΣ val;
    mono_listΣ (gname * blk * nat);
    mono_listΣ (list val * nat * nat)
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
  (C : blk) (l : list val) (t b : nat) : iProp :=
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
    ( ∃ (room : list (gname * blk * nat)),
      ⌜room !! era = Some (γtbe, C, length l)⌝ ∗
      mono_list_lb_own γroom room
    ).

  Definition dqst_archived (γdqst : dqst_gnames) (era : nat)
  (C : blk) (l : list val) (t b : nat) : iProp :=
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
    ( ∃ (room : list (gname * blk * nat))
        (museum : list (list val * nat * nat)),
      ⌜room !! era = Some (γtbe, C, length l)⌝ ∗
      ⌜museum !! era = Some (l, t, b)⌝ ∗
      mono_list_lb_own γroom room ∗
      mono_list_lb_own γmus museum
    ) ∗
    (* persistent circle *)
    (C +ₗ carr) ↦∗□ l.

  Definition dqst_auth (γdqst : dqst_gnames) (era : nat)
  (C : blk) (l : list val) (t b : nat) : iProp :=
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
    ( ∃ (proom : list (gname * blk * nat))
        (museum : list (list val * nat * nat)),
      ⌜length proom = era ∧ length museum = era⌝ ∗
      mono_list_auth_own γroom 1 (proom ++ [(γtbe, C, length l)]) ∗
      mono_list_auth_own γmus 1 museum ∗
      [∗ list] i ↦ gcl ; ltbi ∈ proom ; museum, (
        dqst_archived γdqst i (gcl.1.2) (ltbi.1.1) (ltbi.1.2) (ltbi.2)
      )
    ).

  (* Timeless & Persistent *)
  Ltac desγ H :=
    destruct H as (((γtb, γelt), γroom), γmuseum).

  Global Instance dqst_frag_timeless γdqst era C l t b :
    Timeless (dqst_frag γdqst era C l t b).
  Proof. desγ γdqst. apply _. Qed.

  Global Instance dqst_frag_persistent γdqst era C l t b :
    Persistent (dqst_frag γdqst era C l t b).
  Proof. desγ γdqst. apply _. Qed.

  Global Instance dqst_archived_timeless γdqst era C l t b :
    Timeless (dqst_archived γdqst era C l t b).
  Proof. desγ γdqst. apply _. Qed.

  Global Instance dqst_archived_persistent γdqst era C l t b :
    Persistent (dqst_archived γdqst era C l t b).
  Proof. desγ γdqst. apply _. Qed.

  Global Instance dqst_auth_timeless γdqst era C l t b :
    Timeless (dqst_auth γdqst era C l t b).
  Proof. desγ γdqst. apply _. Qed.

  Lemma top_bot_state_le t1 b1 t2 b2 :
    top_bot_state t1 b1 ≤ top_bot_state t2 b2 ↔
    t1 ≤ t2 ∧ (t1 = t2 ∧ t1 < b1 → t2 < b2).
  Proof. unfold top_bot_state. do 2 case_bool_decide; lia. Qed.

  Lemma dqst_auth_alloc C l :
    length l ≠ 0 →
    ⊢ |==> ∃ (γdqst : dqst_gnames),
      dqst_auth γdqst 0 C l 1 1.
  Proof.
    intros Hl. unfold dqst_auth.
    iMod (mono_nat_own_alloc 2) as (γtb) "[tb _]".
    iMod (mono_nat_own_alloc 2) as (γtbe) "[tbe _]".
    iMod (mono_list_own_alloc ([NONEV])) as (γelt) "[topelt _]".
    iMod (mono_list_own_alloc ([(γtbe, C, length l)])) as (γroom) "[room _]".
    iMod (mono_list_own_alloc ([] : list (list val * nat * nat))) as (γmus) "[museum _]".
    iExists (γtb, γelt, γroom, γmus).
    iModIntro. fr. fr.
    iSplitL "topelt"; fr. fr.
  Qed.

  Lemma dqst_frag_agree γdqst era C1 l1 t1 b1 C2 l2 t2 b2 :
    dqst_frag γdqst era C1 l1 t1 b1 -∗
    dqst_frag γdqst era C2 l2 t2 b2 -∗
    ⌜C1 = C2 ∧ length l1 = length l2⌝.
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

  Lemma dqst_get_frag γdqst era C l t b :
    dqst_auth γdqst era C l t b -∗
    dqst_frag γdqst era C l t b.
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

  Lemma dqst_get_archived γdqst era1 C1 l1 t1 b1
  era2 C2 l2 t2 b2 :
    (* era1 is later than era2 *)
    era1 ≠ era2 →
    dqst_auth γdqst era1 C1 l1 t1 b1 -∗
    dqst_frag γdqst era2 C2 l2 t2 b2 -∗
    ∃ l' t' b', dqst_archived γdqst era2 C2 l' t' b'.
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
      rewrite app_length Hroomlen in Hroom'2. simpl in Hroom'2... }
    assert (is_Some (museum !! era2)) as [ltbera2 Hltbera2].
    { rewrite lookup_lt_is_Some... }
    rewrite lookup_app_l in Hroom'2...
    iDestruct (big_sepL2_lookup with "Archives") as "Arch2"...
  Qed.

  Lemma dqst_get_lb γdqst era1 C1 l1 t1 b1
  era2 C2 l2 t2 b2 :
    (* era1 is later than era2 *)
    dqst_auth γdqst era1 C1 l1 t1 b1 -∗
    dqst_frag γdqst era2 C2 l2 t2 b2 -∗
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

  Lemma dqst_archived_get_array γdqst era C l t b :
    dqst_archived γdqst era C l t b -∗
    (C +ₗ carr) ↦∗□ l.
  Proof.
    desγ γdqst.
    iIntros "Arc".
    by iDestruct "Arc" as (γtbeA) "(_&_&_&_& pers)".
  Qed.

  Lemma dqst_archived_get_frag γdqst era C l t b :
    dqst_archived γdqst era C l t b -∗
    dqst_frag γdqst era C l t b.
  Proof.
    desγ γdqst.
    iIntros "Arc".
      iDestruct "Arc" as (γtbeA) "(%Hlt & [tb tbe] & elt & muse & pers)".
      iDestruct "muse" as (room museum) "(%Hroom & Hmuseum & Room & Museum)".
    fr. fr. by iApply mono_nat_persistent_lb_own_get.
  Qed.

  Lemma dqst_archived_get_lb γdqst era C l1 t1 b1 l2 t2 b2 :
    dqst_archived γdqst era C l1 t1 b1 -∗
    dqst_frag γdqst era C l2 t2 b2 -∗
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

  Lemma dqst_auth_write_bot v γdqst era C l t b :
    dqst_auth γdqst era C l t b -∗
    dqst_auth γdqst era C (mod_set l b v) t b.
  Proof.
    desγ γdqst.
    iIntros "Auth".
      iDestruct "Auth" as (γtbeO) "(%HltO & tbO & eltO & museO)".
      iDestruct "eltO" as (elts) "[Elts %Heltslen]".
    unfold dqst_auth. rewrite mod_set_length. fr.
    fr. case_bool_decide; auto. rewrite mod_set_get_ne; auto.
    apply neq_symm, close_mod_neq; lia.
  Qed.

  Lemma dqst_auth_update γdqst era C l t b :
    t < b →
    dqst_auth γdqst era C l t b ==∗
    dqst_auth γdqst era C l (S t) b.
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
    rewrite app_length lookup_app_r; simpl...
    replace (S t - length elts) with 0; simpl... fr.
  Qed.

  Lemma dqst_auth_push γdqst era C l t b :
    S b < t + length l →
    dqst_auth γdqst era C l t b ==∗
    dqst_auth γdqst era C l t (S b).
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
    { iModIntro. fr. fr. case_bool_decide... }
    destruct (mod_get_is_Some l t) as [v Hv]...
    iMod (mono_list_auth_own_update_app [v] with "Elts") as "[Elts _]".
    iModIntro. fr. fr. case_bool_decide...
    rewrite app_length lookup_app_r; simpl...
    replace (t - length elts) with 0; simpl... fr.
  Qed.

  Lemma dqst_auth_pop γdqst era C l t b :
    t < b - 1 →
    dqst_auth γdqst era C l t b ==∗
    dqst_auth γdqst era C l t (b - 1).
  Proof with extended_auto.
    desγ γdqst.
    iIntros (Hlt) "Auth".
      iDestruct "Auth" as (γtbeO) "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "eltO" as (elts) "[Elts %Heltslen]".
    replace (top_bot_state t b) with (top_bot_state t (b-1)).
      2: unfold top_bot_state; repeat case_bool_decide...
    iModIntro. fr. fr. case_bool_decide...
  Qed.

  Lemma dqst_auth_archive ca' l' γdqst era (C : blk) l t b :
    length l ≤ length l' →
    circ_slice l t b = circ_slice l' t b →
    (C +ₗ carr) ↦∗ l -∗
    dqst_auth γdqst era C l t b ==∗
    dqst_archived γdqst era C l t b ∗
    dqst_auth γdqst (S era) ca' l' t b.
  Proof with extended_auto.
    desγ γdqst.
    iIntros (Hlong Heqs) "Own Auth".
      iDestruct "Auth" as (γtbeO) "(%HltO & [tbO tbeO] & eltO & museO)".
      iDestruct "eltO" as (elts) "[Elts %Heltslen]".
      iDestruct "museO" as (proom museum) "museO".
      iDestruct "museO" as "([%Hproomlen %Hmuslen] & museO)".
      iDestruct "museO" as "(Room & Museum & Archives)".

    (* archive *)
    iMod (array_persist with "Own") as "#PC".
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
    iMod (mono_list_auth_own_update_app [(γtbe', ca', length l')]
      with "Room") as "[Room #rlb]".

    (* frame *)
    iModIntro. fr. fr.
    iSplitL "Elts".
    { fr. case_bool_decide... fr.
      destruct Heltslen as [_ Hget].
      apply (circ_slice_split_eq (S t)) in Heqs as [Heqs _]...
      destruct (circ_slice_singleton l t) as [x [Hx Hsx]]...
      destruct (circ_slice_singleton l' t) as [y [Hy Hsy]]...
      rewrite Hsx Hsy in Heqs. injection Heqs as [= <-].
      rewrite Hy -Hget Hx...
    }
    fr. fr.
    { rewrite app_length -Hproomlen. simpl... }
    { rewrite app_length -Hmuslen. simpl... }
    simpl. fr. all: fr.
    - case_bool_decide... iRight. destruct Heltslen...
    - rewrite lookup_app_l...
      2: rewrite app_length; simpl...
      rewrite lookup_app_r...
      replace (length proom + 0 - length proom) with 0...
    - rewrite lookup_app_r...
      replace (length proom + 0 - length museum) with 0...
  Qed.
End dqst.

Section proof.
  Context `{!heapGS Σ, !cldequeG Σ} (dequeN : namespace).
  Notation iProp := (iProp Σ).

  Definition deque_inv (γq γera : gname) (γdqst : dqst_gnames) (q : blk) : iProp :=
    ∃ (era : nat) (C : blk) (l : list val) (t b : nat) (pop : bool),
      ⌜1 ≤ t ≤ b ∧ b < t + length l ∧ length l ≠ 0⌝ ∗
      (C +ₗ csz) ↦□ #(length l) ∗
      (* abstract *)
      own γq (●E (circ_slice l t b)) ∗
      ghost_var γera (1/2) (era, C, l, b, pop) ∗
      dqst_auth γdqst era C l t b ∗
      (* physical *)
      (q +ₗ circle) ↦{#1/2} #C ∗
      (C +ₗ carr) ↦∗{#1/2} l ∗
      (q +ₗ qtop) ↦ #t ∗
      (q +ₗ qbot) ↦{#1/2} #(if pop then b-1 else b).

  Definition IsDeque (γ : gname) (q : blk) : iProp :=
    ∃ (γq γera : gname) (γdqst : dqst_gnames),
      ⌜γ = encode (γq, γera, γdqst)⌝ ∗
      inv dequeN (deque_inv γq γera γdqst q).
  Global Instance IsDeque_persistent γ q :
    Persistent (IsDeque γ q) := _.

  Definition Deque (γ : gname) (frag : list val) : iProp :=
    ∃ (γq γera : gname) (γdqst : dqst_gnames),
      ⌜γ = encode (γq, γera, γdqst)⌝ ∗
      own γq (◯E frag).
  Global Instance Deque_timeless γ frag :
    Timeless (Deque γ frag) := _.

  (* owner of the deque who can call push and pop *)
  Definition OwnDeque (γ : gname) (q : blk) : iProp :=
    ∃ (γq γera : gname) (γdqst : dqst_gnames) (era : nat)
    (l : list val) (C : blk) (b : nat),
      ⌜γ = encode (γq, γera, γdqst)⌝ ∗
      (C +ₗ csz) ↦□ #(length l) ∗
      ghost_var γera (1/2) (era, C, l, b, false) ∗
      (q +ₗ circle) ↦{#1/2} #C ∗
      (C +ₗ carr) ↦∗{#1/2} l ∗
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
    deque_new_spec' dequeN deque_new Deque IsDeque OwnDeque.
  Proof with extended_auto.
    iIntros (n Hsz Φ) "!> _ HΦ". wp_lam.

    (* allocate *)
    wp_alloc q as "q↦" "†q". wp_pures.
      do 3 rewrite array_cons. iDestruct "q↦" as "(C & T & B & _)".
    wp_lam. wp_alloc C as "SzA" "†SzA"... wp_pures.
      replace (Z.to_nat (1 + n)) with (1 + n)...
      rewrite replicate_add array_cons. iDestruct "SzA" as "[Sz A]".
    wp_store. wp_pures... wp_store. wp_pures. wp_store. wp_store.
    iDestruct "C" as "[C1 C2]". iDestruct "B" as "[B1 B2]".
    iDestruct "A" as "[A1 A2]".

    (* make resources *)
    iMod (mapsto_persist with "Sz") as "#Sz".
    iMod (own_alloc (●E [] ⋅ ◯E [])) as (γq) "[γq● γq◯]". 1: apply excl_auth_valid.
    iMod (ghost_var_alloc (0, C, (replicate n #0), 1, false)) as (γera) "[Era1 Era2]".
    iMod (dqst_auth_alloc C (replicate n #0)) as (γdqst) "Auth"...
    iMod (inv_alloc dequeN _ (deque_inv γq γera γdqst q)
      with "[C1 T B1 A1 γq● Auth Era1]") as "Inv".
    { fr. fr. }

    (* apply Φ *)
    iApply "HΦ". iModIntro. iSplitL "Inv"; first fr.
    iSplitL "γq◯"; fr. fr.
  Qed.

  Lemma circle_grow_rec_spec (arr arr' : loc)
  (l l' : list val) (n m t b : nat) :
    length l = n → length l' = m →
    0 < n < m →
    t ≤ b < t + n →
    arr' ↦∗ l' -∗
    <<< ∀∀ (_ : ()), arr ↦∗ l >>>
      circle_grow_rec #arr #n #arr' #m #t #b @ ∅
    <<< ∃∃ (l2' : list val),
      ⌜length l2' = m⌝ ∗
      ⌜circ_slice l t b = circ_slice l2' t b⌝ ∗
      ⌜∀ i, b ≤ i < t + length l → mod_get l' i = mod_get l2' i⌝ ∗
      arr ↦∗ l,
      RET #(), arr' ↦∗ l2'
    >>>.
  Proof with extended_auto.
    iIntros "%Hn %Hm %Hlen %Hlt A'" (Φ) "AU".
      iRevert "A' AU". iRevert (b l' Hm Hlt).
    iLöb as "IH". iIntros (b l') "%Hm %Hlt A' AU".
    wp_lam. unfold circ_access. wp_pures.

    case_bool_decide; last first; wp_pures.
    { (* end loop *)
      iMod "AU" as (_) "[Cont [_ Commit]]".
      iMod ("Commit" $! l' with "[Cont]") as "HΦ"; fr.
      1: repeat rewrite circ_slice_nil...
      iApply "HΦ"...
    }

    (* read b *)
    destruct b as [|b]...
    replace (Z.of_nat (S b) - 1)%Z with (Z.of_nat b)...
      rewrite rem_mod_eq...
    wp_bind (! _)%E.
      iMod "AU" as (_) "[A [Abort _]]".
      destruct (mod_get_is_Some l b) as [v Hv]...
      wp_apply (wp_load_offset with "A") as "A". 1: rewrite -Hn...
      iMod ("Abort" with "A") as "AU". 1: fr.
    iModIntro. wp_pures.

    (* write b *)
    wp_bind (_ <- _)%E.
      rewrite rem_mod_eq...
      destruct (mod_get_is_Some l' b) as [v' Hv']...
      iApply (wp_store_offset with "A'"). 1: rewrite -Hm...
    iIntros "!> A'". wp_pures.

    (* recurse *)
    iApply ("IH" $! b (<[b `mod` m:=v]> l') with "[] [] [A']")...
      1: rewrite insert_length...
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
          rewrite insert_length Hm list_lookup_insert...
          rewrite Hm. apply Nat.mod_upper_bound...
      - intros i Hi. rewrite -Hlast... unfold mod_get.
        rewrite insert_length Hm list_lookup_insert_ne...
        apply close_mod_neq...
    }
    iIntros "!> A'". iApply "HΦ"...
  Qed.

  Lemma circle_grow_spec (C : blk) (l : list val) (t b : nat) :
    0 < length l →
    t ≤ b < t + length l →
    (C +ₗ csz) ↦□ #(length l) -∗
    <<< ∀∀ (_ : ()), (C +ₗ carr) ↦∗ l >>>
      circle_grow #C #t #b @ ∅
    <<< ∃∃ (C' : blk) (l' : list val),
      ⌜length l < length l'⌝ ∗
      ⌜circ_slice l t b = circ_slice l' t b⌝ ∗
      (C +ₗ carr) ↦∗ l,
    RET #C',
      (C' +ₗ csz) ↦ #(length l') ∗ (C' +ₗ carr) ↦∗ l' >>>.
  Proof with extended_auto.
    iIntros "%Hlen %Hlt Sz" (Φ) "AU".
    wp_lam. wp_pures. wp_load. wp_pures.
    wp_lam. wp_alloc SzA' as "SzA'" "†SzA'"... wp_pures.
      replace (Z.to_nat (1 + 2 * length l)) with (1 + 2 * length l)...
      rewrite replicate_add array_cons. iDestruct "SzA'" as "[Sz' A']".
    wp_store. wp_pures.
    replace (2 * Z.of_nat (length l))%Z with (Z.of_nat (2 * length l))...

    (* make l' *)
    awp_apply (circle_grow_rec_spec with "[A']")... unfold atomic_acc.
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
    wp_pures. iModIntro. iApply "HΦ". fr. rewrite Hlen'...
  Qed.

  Lemma deque_push_spec :
    deque_push_spec' dequeN deque_push Deque IsDeque OwnDeque.
  Proof with extended_auto.
    iIntros (γ q v).
    iIntros "#Is Own" (Φ) "AU".
      iDestruct "Own" as (γq γera γdqst) "Own".
        iDestruct "Own" as (era l C b) "Own".
        iDestruct "Own" as "(%Enc & #Sz & eraOwn & COwn & AOwn & bOwn)".
        replace (C +ₗ 1) with (C +ₗ Z.of_nat 1)...
        remember (C +ₗ Z.of_nat 1) as Carr.
      iDestruct "Is" as (γq' γera' γdqst') "Inv".
        iDestruct "Inv" as "[%Enc' Inv]".
        encode_agree Enc.
    wp_lam. unfold circ_access. wp_pures.
    wp_load. wp_pures.

    (* 1. load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (era1 C1 l1 t1 b1 pop1) ">Invs".
        iDestruct "Invs" as "(%Htb1 & #Sz1 & ● & Era & Dqst & C & A & T & B)".
      iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
      iDestruct (dqst_get_frag with "Dqst") as "#F1".
      wp_load.
    iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l. fr. }
    wp_pures... wp_load. wp_pures. wp_load. wp_pures.

    case_bool_decide; last first; wp_pures...
    - (* 2. write to circle *)
      wp_load. wp_pures... wp_load. wp_pures.
      rewrite -HeqCarr rem_mod_eq...
      wp_bind (_ <- _)%E.
        iInv "Inv" as (era2 C2 l2 t2 b2 pop2) ">Invs".
          iDestruct "Invs" as "(%Htb2 & #Sz2 & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
          rewrite -HeqCarr.
        iMod (ghost_var_update_halves (era, C, (mod_set l b v), b, false)
          with "eraOwn Era") as "[eraOwn Era]".
        iDestruct (dqst_auth_write_bot v with "Dqst") as "Dqst".
        iCombine "AOwn A" as "A".
          iApply (wp_store_offset with "A"). 1: apply mod_get_is_Some...
        iIntros "!> [AOwn A]".
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,(mod_set l b v),t2,b.
        rewrite mod_set_length circ_slice_update_right... fr.
        rewrite -HeqCarr. fr. }
      wp_pures.

      (* 3. increment bot *)
      iInv "Inv" as (era3 C3 l3 t3 b3 pop3) ">Invs".
        iDestruct "Invs" as "(%Htb3 & #Sz3 & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
        iMod (ghost_var_update_halves (era, C, (mod_set l b v), S b, false)
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
      iApply "HΦ".
        iExists γq, γera, γdqst.
        iExists era, (mod_set l b v), C, (S b).
        rewrite -HeqCarr insert_length. fr.
    - (* X. grow *)
      wp_bind (circle_grow _ _ _)%E.
      awp_apply (circle_grow_spec with "[Sz]")... all: try lia.
        iInv "Inv" as (eraX CX lX tX bX popX) ">Invs".
          iDestruct "Invs" as "(%HtbX & _ & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
          rewrite -HeqCarr.
        iCombine "AOwn A" as "A".
          iAaccIntro with "A".
          { iIntros "[AOwn A]". iSplitL "● Era Dqst C A T B". 2: fr.
            iExists _,_,l. fr. rewrite -HeqCarr. fr. }
        iIntros (CX lX) "(%HlenX & %Heqs & [AOwn A])".
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l. fr. rewrite -HeqCarr. fr. }
      iIntros "(SzOwn & AX)". wp_pures...
        iMod (mapsto_persist with "SzOwn") as "#SzX".
        replace (CX +ₗ 1) with (CX +ₗ Z.of_nat 1)...
        remember (CX +ₗ Z.of_nat 1) as CXarr.

      (* Y. replace array *)
      wp_bind (_ <- _)%E.
        iInv "Inv" as (eraY caY lY tY bY popY) ">Invs".
          iDestruct "Invs" as "(%HtbY & #SzY & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
          rewrite -HeqCarr.
        iMod (ghost_var_update_halves (S era, CX, lX, b, false)
          with "eraOwn Era") as "[eraOwn Era]".
          iDestruct (dqst_get_lb with "Dqst F1") as "%Ht1Y".
          apply (circ_slice_split_eq tY) in Heqs as Heqsd... destruct Heqsd as [_ HeqsR]...
        iCombine "AOwn A" as "A".
          iMod (dqst_auth_archive CX lX with "[A] [Dqst]") as "[#Arch Dqst]".
          2: apply HeqsR. 3: fr. 2: rewrite HeqCarr... 1: lia.
          iDestruct "AX" as "[AOwn A]".
        iCombine "COwn C" as "C". wp_store.
        iDestruct "C" as "[COwn C]".
      iSplitL "● Era Dqst C A T B".
      { iModIntro; iNext. iExists _,_,lX.
        fr. fr. rewrite -HeqsR -HeqCXarr. fr. }
      iModIntro. wp_pures... wp_load. wp_pures... wp_load. wp_pures.
      rewrite -HeqCXarr.
      iRename "Sz" into "SzOld".

      (* 2. write to circle *)
      rewrite rem_mod_eq...
      wp_bind (_ <- _)%E.
        iInv "Inv" as (era2 C2 l2 t2 b2 pop2) ">Invs".
          iDestruct "Invs" as "(%Htb2 & #Sz & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
          rewrite -HeqCXarr.
        iMod (ghost_var_update_halves (S era, CX, (mod_set lX b v), b, false)
          with "eraOwn Era") as "[eraOwn Era]".
        iDestruct (dqst_auth_write_bot v with "Dqst") as "Dqst".
        iCombine "AOwn A" as "A".
          iApply (wp_store_offset with "A"). 1: apply mod_get_is_Some...
        iIntros "!> [AOwn A]".
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,(mod_set lX b v),t2,b.
        rewrite mod_set_length circ_slice_update_right... fr.
        fr. rewrite -HeqCXarr... }
      wp_pures.

      (* 3. increment bot *)
      iInv "Inv" as (era3 C3 l3 t3 b3 pop3) ">Invs".
        iDestruct "Invs" as "(%Htb3 & #Sz3 & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
          rewrite -HeqCXarr.
        iMod (ghost_var_update_halves (S era, CX, (mod_set lX b v), S b, false)
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
      { iExists (S era), CX, (mod_set lX b v), t3, (S b), false. fr.
        1: rewrite mod_set_length... subst l'.
        rewrite (circ_slice_extend_right _ _ _ v)... 2: rewrite mod_set_get...
        rewrite -HeqCXarr. fr. }
      iApply "HΦ".
        iExists γq, γera, γdqst.
        iExists (S era), (mod_set lX b v). fr. fr. rewrite insert_length...
        rewrite -HeqCXarr. fr.
    Unshelve. done.
  Qed.

  Lemma deque_pop_spec :
    deque_pop_spec' dequeN deque_pop Deque IsDeque OwnDeque.
  Proof with extended_auto.
    iIntros (γ q).
    iIntros "#Is Own" (Φ) "AU".
      iDestruct "Own" as (γq γera γdqst) "Own".
        iDestruct "Own" as (era l C b) "Own".
        iDestruct "Own" as "(%Enc & #Sz & eraOwn & COwn & AOwn & bOwn)".
        replace (C +ₗ 1) with (C +ₗ Z.of_nat 1)...
        remember (C +ₗ Z.of_nat 1) as Carr.
      iDestruct "Is" as (γq' γera' γdqst') "Inv".
        iDestruct "Inv" as "[%Enc' Inv]".
        encode_agree Enc.
    wp_lam. unfold circ_access. wp_pures.
    wp_load. wp_pures... wp_load. wp_pures... wp_load. wp_pures.

    (* 1. decrement bot *)
    wp_bind (_ <- _)%E.
      iInv "Inv" as (era1 C1 l1 t1 b1 pop1) ">Invs".
        iDestruct "Invs" as "(%Htb1 & #Sz1 & ● & Era & Dqst & C & A & T & B)".
      iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
        rewrite -HeqCarr.
      iMod (ghost_var_update_halves (era, C, l, b, true)
        with "eraOwn Era") as "[eraOwn Era]".
      iCombine "bOwn B" as "B". wp_store.
      iDestruct "B" as "[bOwn B]".
    iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l. fr. rewrite -HeqCarr. fr. }
    wp_pures.

    (* 2. load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (era2 C2 l2 t2 b2 pop2) ">Invs".
        iDestruct "Invs" as "(%Htb2 & #Sz2 & ● & Era & Dqst & C & A & T & B)".
      iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
        rewrite -HeqCarr.
      wp_load.

    destruct (decide (t2 < b-1)).
    { (* normal case, this point is the commit point *)
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γera' γdqst') "[%Enc' ◯]". encode_agree Enc.
        destruct (mod_get_is_Some l (b-1)) as [x Hx]...
        iDestruct (own_ea_agree with "● ◯") as "%Eq". subst l'.
        iMod (own_ea_update (circ_slice l t2 (b-1)) with "● ◯") as "[● ◯]".
        iMod (ghost_var_update_halves (era, C, l, b-1, false)
          with "eraOwn Era") as "[eraOwn Era]".
        iMod (dqst_auth_pop with "Dqst") as "Dqst"...
      iMod ("Commit" $! (circ_slice l t2 (b-1)) (SOMEV x) with "[◯]") as "HΦ".
      { fr. rewrite -circ_slice_extend_right... replace (S (b-1)) with b... }
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l,t2. fr. fr. replace (Z.of_nat b - 1)%Z with (Z.of_nat (b - 1))%Z...
        rewrite -HeqCarr. fr. }
      wp_pures.

      case_bool_decide... wp_pures. rewrite -HeqCarr.
      replace (Z.of_nat b - 1)%Z with (Z.of_nat (b - 1))%Z... rewrite rem_mod_eq...
      wp_bind (! _)%E. iApply (wp_load_offset with "AOwn")...
      iIntros "!> AOwn". wp_pures.
      case_bool_decide... wp_pures.
      iApply "HΦ". iExists _,_,_, _,l. fr. rewrite -HeqCarr. fr.
    }

    iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l. fr. rewrite -HeqCarr. fr. }
    wp_pures.

    case_bool_decide; wp_pures.
    { (* empty *)
      assert (t2 = b)... subst t2.
      (* 3. roll back bot *)
      wp_bind (_ <- _)%E.
        iInv "Inv" as (era3 C3 l3 t3 b3 pop3) ">Invs".
          iDestruct "Invs" as "(%Htb3 & #Sz3 & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
        iMod (ghost_var_update_halves (era, C, l, b, false)
          with "eraOwn Era") as "[eraOwn Era]".
        iCombine "bOwn B" as "B". wp_store.
        iDestruct "B" as "[bOwn B]".
        iMod "AU" as (l') "[Cont [_ Commit]]".
      iMod ("Commit" $! l' NONEV with "[Cont]") as "HΦ"...
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l. fr. }
      wp_pures. iApply "HΦ". iExists _,_,_, _,l. fr.
      rewrite -HeqCarr. fr.
    }

    (* non-empty *)
    rewrite -HeqCarr.
    replace (Z.of_nat b - 1)%Z with (Z.of_nat (b - 1))%Z... rewrite rem_mod_eq...
    wp_bind (! _)%E.
    destruct (mod_get_is_Some l (b-1)) as [v Hv]...
    iApply (wp_load_offset with "AOwn")...
    iIntros "!> AOwn". wp_pures.

    (* we already did normal case *)
    case_bool_decide... wp_pures.

    (* 3. CAS for one-element case *)
    assert (b = S t2)... subst b.
    wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (era3 C3 l3 t3 b3 pop3) ">Invs".
        iDestruct "Invs" as "(%Htb3 & #Sz3 & ● & Era & Dqst & C & A & T & B)".
      iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
        rewrite -HeqCarr.
    destruct (decide (t2 = t3)).
    + (* success *)
      subst t3. wp_cmpxchg_suc.
        replace (Z.of_nat t2 + 1)%Z with (Z.of_nat (S t2))...
      iMod "AU" as (l') "[Cont [_ Commit]]".
        iDestruct "Cont" as (γq' γera' γdqst') "[%Enc' ◯]". encode_agree Enc.
        destruct (mod_get_is_Some l (S t2 - 1)) as [x Hx]...
          rewrite Hv in Hx. injection Hx as [= <-].
        iMod (dqst_auth_update with "Dqst") as "Dqst"...
        iDestruct (own_ea_agree with "● ◯") as "%Eq". subst l'.
        iMod (own_ea_update [] with "● ◯") as "[● ◯]".
      iMod ("Commit" $! [] (SOMEV v) with "[◯]") as "HΦ".
      { fr. rewrite (circ_slice_extend_right _ _ _ v)...
        1: rewrite circ_slice_nil... replace t2 with (S t2 - 1)... }
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists era, C, l, (S t2), (S t2).
        rewrite circ_slice_nil... fr. fr. rewrite -HeqCarr... }
      wp_pures.

      (* 4. roll back bot *)
      wp_bind (_ <- _)%E.
        iInv "Inv" as (era4 C4 l4 t4 b4 pop4) ">Invs".
          iDestruct "Invs" as "(%Htb4 & #Sz4 & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
        replace (Z.of_nat (S t2 - 1))%Z with (Z.of_nat t2)%Z...
        replace (Z.of_nat (S t2) - 1)%Z with (Z.of_nat t2)%Z...
        iMod (ghost_var_update_halves (era, C, l, S t2, false)
          with "eraOwn Era") as "[eraOwn Era]".
        iCombine "bOwn B" as "B". wp_store.
          replace (Z.of_nat t2 + 1)%Z with (Z.of_nat (S t2))%Z...
        iDestruct "B" as "[bOwn B]".
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l. fr. }
      wp_pures. iApply "HΦ". iExists _,_,_, _,l. fr. rewrite -HeqCarr...
    + (* fail *)
      wp_cmpxchg_fail.
      iMod "AU" as (l') "[Cont [_ Commit]]".
      iMod ("Commit" $! l' NONEV with "[Cont]") as "HΦ"...
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l. fr. rewrite -HeqCarr. fr. }
      wp_pures.

      (* 4. roll back bot *)
      wp_bind (_ <- _)%E.
        iInv "Inv" as (era4 C4 l4 t4 b4 pop4) ">Invs".
          iDestruct "Invs" as "(%Htb4 & #Sz4 & ● & Era & Dqst & C & A & T & B)".
        iDestruct (ghost_var_agree with "eraOwn Era") as "%Eq"; injection Eq as [= <- <- <- <- <-].
        replace (Z.of_nat (S t2 - 1))%Z with (Z.of_nat t2)%Z...
        replace (Z.of_nat (S t2) - 1)%Z with (Z.of_nat t2)%Z...
        iMod (ghost_var_update_halves (era, C, l, S t2, false)
          with "eraOwn Era") as "[eraOwn Era]".
        iCombine "bOwn B" as "B". wp_store.
          replace (Z.of_nat t2 + 1)%Z with (Z.of_nat (S t2))%Z...
        iDestruct "B" as "[bOwn B]".
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l. fr. }
      wp_pures. iApply "HΦ". iExists _,_,_, _,l. fr. rewrite -HeqCarr...
  Qed.

  Lemma deque_steal_spec :
    deque_steal_spec' dequeN deque_steal Deque IsDeque.
  Proof with extended_auto.
    iIntros (γ q).
    iIntros "#Is" (Φ) "AU".
    iDestruct "Is" as (γq γera γdqst) "Inv".
      iDestruct "Inv" as "[%Enc Inv]".
    wp_lam. unfold circ_access. wp_pures.

    (* 1. load top *)
    wp_bind (! _)%E.
      iInv "Inv" as (era1 C1 l1 t1 b1 pop1) ">Invs".
        iDestruct "Invs" as "(%Htb1 & #Sz & ● & Era & Dqst & C & A & T & B)".
      iDestruct (dqst_get_frag with "Dqst") as "#F1".
      wp_load.
    iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l1. fr. }
    wp_pures.

    (* 2. load bot *)
    wp_bind (! _)%E.
      iInv "Inv" as (era2 C2 l2 t2 b2 pop2) ">Invs".
        iDestruct "Invs" as "(%Htb2 & #Sz2 & ● & Era & Dqst & C & A & T & B)".
      iDestruct (dqst_get_frag with "Dqst") as "#F2".
      iDestruct (dqst_get_lb with "Dqst F1") as "%Lb12".
      wp_load.
    iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l2. fr. }
    wp_pures.

    (* 3. load array *)
    wp_bind (! _)%E.
      iInv "Inv" as (era3 C3 l3 t3 b3 pop3) ">Invs".
        iDestruct "Invs" as "(%Htb3 & #Sz3 & ● & Era & Dqst & C & A & T & B)".
      iDestruct (dqst_get_frag with "Dqst") as "#F3".
      iDestruct (dqst_get_lb with "Dqst F2") as "%Lb23".
      wp_load.
    iModIntro. iSplitL "● Era Dqst C A T B".
    { iExists _,_,l3. fr. }
    wp_pures. wp_load. wp_pures.

    (* no chance to steal *)
    replace (if pop2 then LitInt (Z.of_nat b2 - 1)%Z else LitInt (Z.of_nat b2))
      with (LitInt (Z.of_nat (if pop2 then (b2 - 1) else b2))).
      2: { destruct pop2... replace (Z.of_nat b2 - 1)%Z with (Z.of_nat (b2 - 1))... }
    wp_pures.
    case_bool_decide as Hif; wp_pures.
    { iMod "AU" as (l) "[Cont [_ Commit]]".
      iMod ("Commit" $! l NONEV with "[Cont]") as "Φ"...
      iApply "Φ"... }
    assert (t1 < b2) as Htb12. 1: destruct pop2...

    (* 4. get_circle *)
    rewrite rem_mod_eq. 2: lia.
    wp_bind (! _)%E.
      iInv "Inv" as (era4 C4 l4 t4 b4 pop4) ">Invs".
        iDestruct "Invs" as "(%Htb4 & #Sz4 & ● & Era & Dqst & C & A & T & B)".
      iDestruct (dqst_get_frag with "Dqst") as "#F4".
      iDestruct (dqst_get_lb with "Dqst F3") as "%Lb34".
    destruct (decide (era3 = era4)) as [eqγ|neqγ].
    - (* array was not archived *)
      subst era4.
        iDestruct (dqst_frag_agree with "F3 F4") as "[%H34 %Hlen]".
          subst C4. rewrite Hlen. clear Hlen.
        remember (C3 +ₗ 1%nat) as C3arr.
        destruct (mod_get_is_Some l4 t1) as [v Hv]...
        iApply (wp_load_offset with "A")...
        iIntros "!> A".
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l4. fr. rewrite -HeqC3arr. fr. }
      wp_pures.

      (* 5. CAS *)
      wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (era5 C5 l5 t5 b5 pop5) ">Invs".
        iDestruct "Invs" as "(%Htb5 & #Sz5 & ● & Era & Dqst & C & A & T & B)".
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
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l5. fr. fr. }
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
        rewrite -HeqC3arr.
      iApply (wp_persistent_load_offset with "Parr")...
      iIntros "!> _ !>". iSplitL "● Era Dqst C A T B".
      { iExists _,_,l4. fr. }
      wp_pures.

      (* 5. CAS *)
      wp_bind (CmpXchg _ _ _)%E.
      iInv "Inv" as (era5 C5 l5 t5 b5 pop5) ">Invs".
        iDestruct "Invs" as "(%Htb5 & #Sz5 & ● & Era & Dqst & C & A & T & B)".
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
      iModIntro. iSplitL "● Era Dqst C A T B".
      { iExists _,_,l5. fr. fr. }
      wp_pures. iApply "HΦ"...
  Qed.

#[export] Typeclasses Opaque Deque IsDeque.

End proof.

