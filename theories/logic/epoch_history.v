From iris.algebra Require Import auth gset csum excl.
From smr.algebra Require Import coPset coP_auth.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own.
From iris.bi Require Import big_op.
From smr.base_logic.lib Require Import mono_list.

From iris.prelude Require Import options.

From smr Require Import helpers.

Class epoch_historyG Σ := EpochHistoryG {
  #[local] epoch_gnamesG :: mono_listG (gname * gname * gname) Σ;
  #[local] epoch_ownG :: inG Σ (coP_authR (gset_disjUR positive));
  #[local] epoch_snapG :: inG Σ (authUR (gsetUR positive));
  #[local] epoch_finalizedG :: inG Σ (csumR (exclR unitO) (agreeR (gsetUR positive)));
}.

Definition epoch_historyΣ : gFunctors :=
  #[mono_listΣ (gname * gname * gname);
    GFunctor (coP_authR (gset_disjUR positive));
    GFunctor (authUR (gsetUR positive));
    GFunctor (csumR (exclR unitO) (agreeR (gsetUR positive)))].

Global Instance subG_epoch_historyΣ {Σ} :
  subG epoch_historyΣ Σ → epoch_historyG Σ.
Proof. solve_inG. Qed.

Section defs.
Context `{!epoch_historyG Σ}.
Implicit Types (γ γo γs γf : gname) (ehist : list (gset positive)) (e : nat) (unlinked : gset positive).

(* Index is the epoch.
  In each epoch, we use unlinked_e, the [gset positive] of
    unlinked pointers made at that epoch.
  First gname is for [coP_auth (gset_disjUR positive)], the fragment.
  Second gname is for [authUR (gsetUR positive)], the snapshot.
  Third gname is for the oneshot RA, the finalized version if e <= ge-2.
*)
Definition epoch_history_auth γ ehist : iProp Σ :=
  ∃ (gnames : list (gname * gname * gname)),
    ⌜length ehist = length gnames⌝ ∗
    mono_list_auth_own γ 1 gnames ∗
    let ge := length ehist - 1 in
    [∗ list] e ↦ γosf; unlinked_e ∈ gnames; ehist,
      let finalized :=
        if bool_decide (e ≤ ge - 2) then
          Cinr (to_agree unlinked_e)
        else
          Cinl (Excl ()) in
      let '(γo, γs, γf) := γosf in
      own γo (●C (GSet unlinked_e)) ∗
      own γs (● unlinked_e) ∗
      own γf finalized
  .

Definition epoch_history_frag γ e (E : coPneset) : iProp Σ :=
  ∃ γosf unlinked,
    mono_list_idx_own γ e γosf ∗
    own γosf.1.1 (◯C{E} (GSet unlinked)) (* γo *)
  .

Definition epoch_history_snap γ e unlinked : iProp Σ :=
  ∃ γosf,
    mono_list_idx_own γ e γosf ∗
    own γosf.1.2 (◯ unlinked) (* γs *)
  .

(* Finalized epochs when advanced to epoch e. *)
Definition epoch_history_finalized γ (ehistF : list (gset positive)) : iProp Σ :=
  ∃ (gnames : list (gname * gname * gname)),
    mono_list_lb_own γ gnames ∗
    [∗ list] _ ↦ γosf; unlinked_e ∈ gnames; ehistF,
      own γosf.2 (Cinr (to_agree unlinked_e)) (* γf *)
  .

Definition fold_hist ehist : gset positive := foldr (∪) ∅ ehist.
End defs.

Section rules.
Context `{!epoch_historyG Σ}.
Implicit Types (γ γo γs : gname) (ehist : list (gset positive)) (e : nat) (unlinked : gset positive).
Context {γ : gname}.

Local Ltac solve_lookup := (apply lookup_lt_is_Some_2; lia).

(* Typeclass Instances *)

Global Instance epoch_history_auth_timeless : ∀ γ ehist, Timeless (epoch_history_auth γ ehist).
Proof.
  repeat (
    intros ||
    apply bi.sep_timeless || apply bi.exist_timeless ||
    apply big_sepL2_timeless ||
    apply _ || case_match
  ).
Qed.

Global Instance epoch_history_frag_timeless : ∀ γ e E, Timeless (epoch_history_frag γ e E).
Proof. apply _. Qed.

Global Instance epoch_history_snap_timeless : ∀ γ e unlinked, Timeless (epoch_history_snap γ e unlinked).
Proof. apply _. Qed.

Global Instance epoch_history_snap_persistent : ∀ γ e unlinked, Persistent (epoch_history_snap γ e unlinked).
Proof. apply _. Qed.

Global Instance epoch_history_finalized_timeless : ∀ γ ehist, Timeless (epoch_history_finalized γ ehist).
Proof. apply _. Qed.

Global Instance epoch_history_finalized_persistent : ∀ γ ehist, Persistent (epoch_history_finalized γ ehist).
Proof. apply _. Qed.

(* Helpers *)

Lemma own_subset γo E unlinked_auth unlinked :
  own γo (●C (GSet unlinked_auth)) -∗
  own γo (◯C{E} (GSet unlinked)) -∗
  ⌜unlinked ⊆ unlinked_auth⌝.
Proof.
  iIntros "● ◯". iCombine "● ◯" as "●◯".
  iDestruct (own_valid with "●◯") as "%".
  rewrite auth_both_valid_discrete in H. destruct H as [H _].
  rewrite Some_included in H. destruct H.
  - destruct H; simpl in H0.
    by injection H0 as [= <-].
  - rewrite pair_included in H. destruct H as [_ H].
    by rewrite gset_disj_included in H.
Qed.

Lemma snap_subset γs unlinked_auth unlinked :
  own γs (● unlinked_auth) -∗
  own γs (◯ unlinked) -∗
  ⌜unlinked ⊆ unlinked_auth⌝.
Proof.
  iIntros "● ◯". iCombine "● ◯" as "●◯".
  iDestruct (own_valid with "●◯") as "%".
  rewrite auth_both_valid_discrete in H. destruct H as [H _].
  by apply gset_included in H.
Qed.

Lemma own_insert γo E i unlinked_auth unlinked :
  i ∉ unlinked_auth →
  own γo (●C (GSet unlinked_auth)) ∗
  own γo (◯C{E} (GSet unlinked)) ==∗
  own γo (●C (GSet (unlinked_auth ∪ {[i]}))) ∗
  own γo (◯C{E} (GSet (unlinked ∪ {[i]}))).
Proof.
  iIntros (Hi) "[● ◯]".
  iDestruct (own_subset with "● ◯") as %Hsub.
  iCombine "● ◯" as "●◯".
  rewrite (union_comm_L unlinked_auth) (union_comm_L unlinked).
  iMod (own_update _ _
  (●C (GSet ({[i]} ∪ unlinked_auth)) ⋅ ◯C{E} (GSet ({[i]} ∪ unlinked)))
    with "●◯") as "[● ◯]"; last by iFrame.
  apply coP_auth_update, gset_disj_alloc_local_update. set_solver.
Qed.

Lemma snap_insert γs i unlinked :
  own γs (● unlinked) ==∗ own γs (● (unlinked ∪ {[i]})).
Proof.
  iIntros "●".
  iApply own_update; auto.
  eapply auth_update_auth, gset_local_update. set_solver.
Qed.

(* foldr union and fold_hist *)

Lemma foldr_union_start S ehist :
  foldr union S ehist = fold_hist ehist ∪ S.
Proof.
  revert S.
  unfold fold_hist. induction ehist using rev_ind; intros.
  - set_solver.
  - do 2 rewrite foldr_snoc. rewrite union_empty_r_L.
    do 2 rewrite IHehist. set_solver.
Qed.

Lemma fold_hist_singleton unlinked :
  fold_hist [unlinked] = unlinked.
Proof. set_solver. Qed.

Lemma fold_hist_app ehist1 ehist2 :
  fold_hist (ehist1 ++ ehist2) =
  fold_hist ehist1 ∪ fold_hist ehist2.
Proof. unfold fold_hist. by rewrite foldr_app foldr_union_start. Qed.

Lemma fold_hist_snoc ehist unlinked :
  fold_hist (ehist ++ [unlinked]) = fold_hist ehist ∪ unlinked.
Proof. rewrite fold_hist_app. set_solver. Qed.

Lemma elem_of_fold_hist ehist i :
  i ∈ fold_hist ehist ↔
  ∃ e unlinked_e, ehist !! e = Some unlinked_e ∧ i ∈ unlinked_e.
Proof.
  induction ehist using rev_ind.
  { set_solver. }
  rewrite fold_hist_snoc elem_of_union.
  split; intros.
  - destruct H.
    + apply IHehist in H as [e [ue [He1 He2]]].
      exists e, ue. split; auto.
      by rewrite lookup_app He1.
    + exists (length ehist), x. by rewrite snoc_lookup.
  - destruct H as [e [ue [He1 He2]]].
    apply lookup_app_Some in He1 as [He1|[He1 He3]].
    + left. apply IHehist. eauto.
    + right. replace x with ue; auto.
      rewrite list_lookup_singleton_Some in He3.
      by destruct He3.
Qed.

Lemma not_elem_of_fold_hist ehist i :
  i ∉ fold_hist ehist ↔
  ∀ e unlinked_e, ehist !! e = Some unlinked_e → i ∉ unlinked_e.
Proof.
  rewrite elem_of_fold_hist. split; intros.
  - intro. apply H. eauto.
  - intro. destruct H0 as [e [ue [He1 He2]]]. by eapply H.
Qed.

Lemma ehist_elem_in_fold_hist ehist i unlinked :
  ehist !! i = Some unlinked →
  unlinked ⊆ fold_hist ehist.
Proof.
  induction ehist using rev_ind.
  { naive_solver. }
  intros. rewrite fold_hist_snoc.
  rewrite lookup_app_Some in H. destruct H as [H|[H1 H2]].
  - set_solver.
  - rewrite list_lookup_singleton_Some in H2. destruct H2; set_solver.
Qed.

Lemma fold_hist_prefix ehist1 ehist2 :
  ehist1 `prefix_of` ehist2 →
  fold_hist ehist1 ⊆ fold_hist ehist2.
Proof.
  intros. apply prefix_cut in H.
  rewrite H fold_hist_app. set_solver.
Qed.

Lemma not_in_info {A} ehist (info : gmap positive A) i :
  fold_hist ehist ⊆ dom info →
  info !! i = None →
  i ∉ fold_hist ehist.
Proof.
  intros ehist_sub_info Hi i_in_ehist. rewrite elem_of_subseteq in ehist_sub_info.
  apply ehist_sub_info in i_in_ehist. rewrite elem_of_dom in i_in_ehist.
  destruct i_in_ehist. congruence.
Qed.

(* Update rules *)

Lemma epoch_history_alloc :
  ⊢ |==> ∃ γ,
    epoch_history_auth γ [∅; ∅; ∅; ∅] ∗
    epoch_history_frag γ 0 ⊤ ∗ epoch_history_frag γ 1 ⊤ ∗
    epoch_history_frag γ 2 ⊤ ∗ epoch_history_frag γ 3 ⊤.
Proof.
  iIntros. unfold epoch_history_auth.
  iMod (own_alloc ( ●C (GSet ∅) ⋅ ◯C (GSet ∅) )) as (γo0) "[●o0 ◯o0]";
    first by apply coP_auth_valid.
  iMod (own_alloc ( ●C (GSet ∅) ⋅ ◯C (GSet ∅) )) as (γo1) "[●o1 ◯o1]";
    first by apply coP_auth_valid.
  iMod (own_alloc ( ●C (GSet ∅) ⋅ ◯C (GSet ∅) )) as (γo2) "[●o2 ◯o2]";
    first by apply coP_auth_valid.
  iMod (own_alloc ( ●C (GSet ∅) ⋅ ◯C (GSet ∅) )) as (γo3) "[●o3 ◯o3]";
    first by apply coP_auth_valid.
  iMod (own_alloc (● ∅)) as (γs0) "●s0"; first by apply auth_auth_valid.
  iMod (own_alloc (● ∅)) as (γs1) "●s1"; first by apply auth_auth_valid.
  iMod (own_alloc (● ∅)) as (γs2) "●s2"; first by apply auth_auth_valid.
  iMod (own_alloc (● ∅)) as (γs3) "●s3"; first by apply auth_auth_valid.
  iMod (own_alloc ( Cinr (to_agree ∅) )) as (γf0) "●f0"; [done|].
  iMod (own_alloc ( Cinr (to_agree ∅) )) as (γf1) "●f1"; [done|].
  iMod (own_alloc ( Cinl (Excl ()) )) as (γf2) "●f2"; [done|].
  iMod (own_alloc ( Cinl (Excl ()) )) as (γf3) "●f3"; [done|].
  iMod (mono_list_own_alloc
    [(γo0, γs0, γf0); (γo1, γs1, γf1); (γo2, γs2, γf2); (γo3, γs3, γf3) ]
  ) as (γl) "[● #◯]".
  iDestruct (mono_list_idx_own_get 0 ∅ with "◯") as "◯0"; auto.
  iDestruct (mono_list_idx_own_get 1 ∅ with "◯") as "◯1"; auto.
  iDestruct (mono_list_idx_own_get 2 ∅ with "◯") as "◯2"; auto.
  iDestruct (mono_list_idx_own_get 3 ∅ with "◯") as "◯3"; auto.

  iModIntro. iExists γl.
  iSplitL "● ●o0 ●s0 ●f0 ●o1 ●s1 ●f1 ●o2 ●s2 ●f2 ●o3 ●s3 ●f3".
  { iExists _. iFrame. simpl. by iFrame. }
  iSplitL "◯o0"; [iExists _, _; iSplit; auto|].
  iSplitL "◯o1"; [iExists _, _; iSplit; auto|].
  iSplitL "◯o2"; [iExists _, _; iSplit; auto|].
  iExists _, _; iSplit; auto.
Qed.

(* add unlinked pointer i in slot s, to epoch e *)
(* NOTE: If I have frag of [e] then I should be able to retire.
  The finalize rule should require ⊤ frag.
  This is actually enforced by [GE_minus_\d] invariants. *)
Lemma epoch_history_retire ehist s e i :
  length ehist ≥ 3 →
  length ehist - 2 ≤ e →
  e < length ehist →
  i ∉ fold_hist ehist →
  epoch_history_auth γ ehist -∗
  epoch_history_frag γ e {[s]} ==∗
  epoch_history_auth γ (alter (union {[i]}) e ehist) ∗
  epoch_history_frag γ e {[s]}.
Proof.
  iIntros (Hlen He1 He2 Hi) "EH EF".
    iDestruct "EH" as (gnames Hgn) "[●L EH]".
    iDestruct "EF" as ([[γFo γFs] γFf] unlinked) "[◯Le ◯oe]"; simpl.
    rewrite not_elem_of_fold_hist in Hi.

  (* extract ghosts at e *)
  assert (is_Some (ehist !! e)) as [unlinked_e Hue].
  { by apply lookup_lt_is_Some_2. }
  assert (is_Some (gnames !! e)) as [[[γoe γse] γfe] Hγe].
  { apply lookup_lt_is_Some_2. lia. }
  iDestruct (big_sepL2_delete _ _ _ e with "EH") as "[EHe EH]"; eauto; simpl.
    iDestruct "EHe" as "(●oe & ●se & ●fe)".
    rewrite bool_decide_eq_false_2; last lia.
  iDestruct (mono_list_auth_idx_lookup with "●L ◯Le") as "%".
    rewrite Hγe in H. injection H as [= <- <- <-].

  (* update *)
  iMod (own_insert _ _ i with "[$●oe $◯oe]") as "[●oe ◯oe]".
    { by eapply Hi. }
  iMod (snap_insert _ i with "●se") as "●se".

  iModIntro.
  iSplitR "◯Le ◯oe"; last first.
  { iExists (γoe, γse, γfe), _. iFrame. }
  iExists gnames.
  rewrite length_alter. iSplit; auto. iFrame.
  iApply (big_sepL2_delete _ _ _ e); eauto; simpl.
  { rewrite list_lookup_alter. by rewrite Hue. }
  rewrite (union_comm_L unlinked_e).
  rewrite bool_decide_eq_false_2; last lia. iFrame.

  erewrite list_alter_insert; eauto.
  iDestruct (big_sepL2_insert_acc with "EH") as "[_ EH]"; eauto.
  iPoseProof ("EH" $! (γoe, γse, γfe) ({[i]} ∪ unlinked_e)) as "EH".
  rewrite decide_True; auto. rewrite list_insert_id; auto.
  by iApply "EH".
Qed.

(* advance epoch by 1 *)
(* we probably won't use it for unlinked ≠ ∅, but it works anyway *)
Lemma epoch_history_advance ehist unlinked' :
  length ehist ≥ 3 →
  epoch_history_auth γ ehist ==∗
  epoch_history_auth γ (ehist ++ [unlinked']) ∗
  epoch_history_frag γ (length ehist) ⊤.
Proof.
  iIntros (Hlen) "EH".
    iDestruct "EH" as (gnames Hgn) "[●L EH]".

  (* alloc new gnames *)
  iMod (own_alloc (
      (●C (GSet unlinked') ⋅ ◯C (GSet unlinked'))
    )) as (γo') "[●o' ◯o']";
    first by apply coP_auth_valid.
  iMod (own_alloc (● unlinked')) as (γs') "●s'";
    first by apply auth_auth_valid.
  iMod (own_alloc (Cinl (Excl ()))) as (γf') "●f'"; [done|].
  iMod (mono_list_auth_own_update (gnames ++ [(γo', γs', γf')]) with "●L")
    as "[●L ◯lb]". { subst. apply prefix_app_cut. }

  (* update to finalize e-3 *)
  assert (length ehist - 2 < length ehist) as Hdel by lia.
  assert (is_Some (ehist !! (length ehist - 2))) as [u3 Hu3].
  { by apply lookup_lt_is_Some_2. }
  assert (is_Some (gnames !! (length ehist - 2))) as [[[γo3 γs3] γf3] Hγ3].
  { rewrite Hgn. apply lookup_lt_is_Some_2. lia. }
  iDestruct (big_sepL2_delete _ _ _ (length ehist - 2) with "EH")
    as "[EH3 EH]"; eauto; simpl.
    iDestruct "EH3" as "(●o3 & ●s3 & ●f3)".
  rewrite bool_decide_eq_false_2; last lia.
    iMod (own_update _ _ (Cinr (to_agree u3)) with "●f3") as "●f3".
    { by apply cmra_update_exclusive. }

  (* close *)
  iModIntro.
  iSplitR "◯o' ◯lb".
  - iExists (gnames ++ [(γo', γs', γf')]). repeat rewrite snoc_length.
    iFrame. iSplit; auto.
    rewrite bool_decide_eq_false_2; last lia.
    iFrame. iSplit; auto.
    iApply (big_sepL2_delete _ _ _ (length ehist - 2)); eauto. iFrame.
    rewrite bool_decide_eq_true_2; last lia.
    iFrame.
    iApply big_sepL2_mono; last auto.
    iIntros (k [[γ1 γ2] γ3] y2 Hy1 Hy2) "EH".
    case_decide; auto.
    case_bool_decide.
    + rewrite bool_decide_eq_true_2; auto. lia.
    + rewrite bool_decide_eq_false_2; auto. lia.
  - iExists (γo', γs', γf'), _. iFrame.
    by rewrite Hgn snoc_lookup.
Qed.

(* Frag rules *)

Lemma epoch_history_frag_lookup ehist E e :
  epoch_history_auth γ ehist -∗
  epoch_history_frag γ e E -∗
  ⌜e < length ehist⌝.
Proof.
  iIntros "EH EF".
  iDestruct "EH" as (gnames Hgn) "[●L _]".
  iDestruct "EF" as ([[γFo γFs] γFf] unlinked) "[◯Le _]".
  iDestruct (mono_list_auth_idx_lookup with "●L ◯Le") as "%".
  apply lookup_lt_Some in H. by rewrite Hgn.
Qed.

Lemma epoch_history_frag_union e E1 E2 :
  E1 ## E2 →
  epoch_history_frag γ e E1 ∗ epoch_history_frag γ e E2
    ⊣⊢ epoch_history_frag γ e (E1 ∪ E2).
Proof.
  intros D. iIntros. iSplit.
  - iIntros "[F1 F2]".
      iDestruct "F1" as (gnames1 u1) "[◯I1 ◯C1]".
      iDestruct "F2" as (gnames2 u2) "[◯I2 ◯C2]".
    iDestruct (mono_list_idx_agree with "◯I1 ◯I2") as %<-.
    iCombine "◯C1 ◯C2" gives %V.
    apply coP_auth_frag_valid_op in V as [_ V].
    apply gset_disj_valid_op in V.
    iExists gnames1, (u1 ∪ u2). iFrame.
    rewrite -gset_disj_union; auto.
    rewrite coP_auth_frag_op; auto.
    rewrite own_op. iFrame.
  - iIntros "F".
      iDestruct "F" as (gnames u) "[#◯I ◯C]".
    rewrite -(union_empty_r_L u).
    rewrite -gset_disj_union; last set_solver.
    rewrite coP_auth_frag_op; auto.
    rewrite own_op. iDestruct "◯C" as "[◯1 ◯2]".
    iSplitL "◯1". { iExists _, _. iFrame. auto. }
    iExists _, _. iFrame. auto.
Qed.

(* Snapshot rules *)

Lemma epoch_history_snapshot_get e ehist unlinked :
  ehist !! e = Some unlinked →
  epoch_history_auth γ ehist ==∗
  epoch_history_auth γ ehist ∗
  epoch_history_snap γ e unlinked.
Proof.
  iIntros (He) "EH".
    iDestruct "EH" as (gnames Hgn) "[●L EH]".
  assert (is_Some (gnames !! e)) as [[[γo γs] γf] Hγe].
  { apply lookup_lt_is_Some_2. apply lookup_lt_Some in He. lia. }
  iDestruct (mono_list_lb_own_get with "●L") as "#◯L".
  iDestruct (mono_list_idx_own_get with "◯L") as "◯i"; eauto.
  iDestruct (big_sepL2_delete with "EH") as "[●e EH]"; eauto; simpl.
    iDestruct "●e" as "(●o & ●s & ●f)".
  iMod (own_update with "●s") as "●s".
  { apply (auth_update_dfrac_alloc _ _ unlinked). auto. }
  iDestruct "●s" as "[●s ◯s]".
  iModIntro. iSplitR "◯s".
  - iExists _. iFrame. iSplit; auto.
    iApply (big_sepL2_delete); eauto. iFrame.
  - iExists _. iSplit; auto.
Qed.

Lemma epoch_history_snapshot ehist e unlinked :
  epoch_history_auth γ ehist -∗
  epoch_history_snap γ e unlinked -∗
  ⌜∃ unlinked_auth,
    ehist !! e = Some unlinked_auth ∧
    unlinked ⊆ unlinked_auth⌝.
Proof.
  iIntros "EH ES".
    iDestruct "EH" as (gnames Hgn) "[●L EH]".
    iDestruct "ES" as ([[γo γs] γf]) "[◯L ◯s]".
  iDestruct (mono_list_auth_idx_lookup with "●L ◯L") as %Hγ.
  assert (e < length ehist) as Hlen.
  { rewrite Hgn. apply lookup_lt_is_Some_1. done. }
  assert (is_Some (ehist !! e)) as [unlinked_auth Hua].
  { by apply lookup_lt_is_Some_2. }
  iDestruct (big_sepL2_delete _ _ _ e with "EH") as "[● _]"; eauto; simpl.
    iDestruct "●" as "(●o & ●s & ●f)".
  iDestruct (snap_subset with "●s ◯s") as %Hsub.
  eauto.
Qed.

(* Finalized rules *)

Lemma epoch_history_grow_finalized ehist k :
  length ehist ≥ 2 →
  k < length ehist - 2 →
  epoch_history_auth γ ehist -∗
  epoch_history_finalized γ (take k ehist) ==∗
  epoch_history_auth γ ehist ∗
  epoch_history_finalized γ (take (S k) ehist).
Proof.
  iIntros (Hlen Hk) "EH EFin".
    iDestruct "EH" as (gnames Hgn) "[●L EH]".
    iDestruct "EFin" as (gnames') "[#◯L EFin]".
    iDestruct (mono_list_lb_own_get with "●L") as "#◯L+".
  iDestruct (mono_list_auth_lb_valid with "●L ◯L") as %[_ Hpref].
  iDestruct ((big_sepL2_length _ _ (take k ehist)) with "EFin") as %Hgn'.
  rewrite length_take_le in Hgn'; last lia.

  (* copy Cinr at k *)
  assert (is_Some (ehist !! k)) as [unlinked_k Huk].
  { apply lookup_lt_is_Some_2. lia. }
  assert (is_Some (gnames !! k)) as [[[γok γsk] γfk] Hγk].
  { apply lookup_lt_is_Some_2. lia. }
  iDestruct (big_sepL2_lookup_acc _ _ _ k with "EH")
    as "[●k Close]"; eauto; simpl.
    iDestruct "●k" as "(●ok & ●sk & ●fk)".
  rewrite bool_decide_eq_true_2; last lia.
  rewrite -{1}(agree_idemp (to_agree unlinked_k)) Cinr_op own_op.
  iDestruct "●fk" as "[●fk1 ●fk2]".
  iDestruct ("Close" with "[●ok ●sk ●fk1]") as "EH"; [iFrame|].

  (* construct gnames' ++ [γ] *)
  iDestruct (mono_list_lb_own_le (gnames' ++ [(γok, γsk, γfk)])
    with "◯L+") as "◯Lk".
  { apply prefix_cut in Hpref. rewrite Hpref Hgn'.
    apply prefix_app, prefix_singleton.
    by rewrite lookup_drop -plus_n_O. }

  (* close *)
  iModIntro.
  iSplitL "●L EH". { iExists _. iFrame. auto. }
  iExists (gnames' ++ [(γok, γsk, γfk)]). iSplit; auto.
  erewrite take_S_r; last eauto.
  iApply (big_sepL2_app with "EFin"). by iFrame.
Qed.

Lemma epoch_history_get_finalized ehist :
  length ehist ≥ 2 →
  epoch_history_auth γ ehist ==∗
  epoch_history_auth γ ehist ∗
  epoch_history_finalized γ (take (length ehist - 2) ehist).
Proof.
  intros Hlen.
  assert (∀ k, k ≤ length ehist - 2 →
    epoch_history_auth γ ehist ==∗
    epoch_history_auth γ ehist ∗
    epoch_history_finalized γ (take k ehist)
  ); last first.
  { intros. by apply H. }

  iIntros (k). iInduction k as [|k Hk].
  - iIntros (Hlen') "EH".
    iDestruct "EH" as (gnames Hgn) "[●L EH]".
    iDestruct (mono_list_lb_own_get with "●L") as "#◯L".
    iDestruct (mono_list_lb_own_le [] with "◯L") as "◯e".
    { apply prefix_nil. }
    iModIntro. iSplitL. { iExists _. iFrame. auto. }
    iExists []. auto.
  - iIntros (Hlen') "EH".
    iMod ("Hk" with "[] EH") as "[EH EFin]". { iPureIntro. lia. }
    by iApply (epoch_history_grow_finalized with "EH").
Qed.

Lemma epoch_finalized_agree ehistF ehistF' :
  length ehistF = length ehistF' →
  epoch_history_finalized γ ehistF -∗
  epoch_history_finalized γ ehistF' -∗
  ⌜ehistF = ehistF'⌝.
Proof.
  iIntros (HlenFF) "F F'".
    iDestruct "F" as (gnames) "[◯L EF]".
    iDestruct "F'" as (gnames') "[◯L' EF']".
  iDestruct (mono_list_lb_valid with "◯L ◯L'") as %Hgpref.
  iAssert ⌜∀ i, ehistF !! i = ehistF' !! i⌝%I as %Heq; last first.
  { rewrite (list_eq ehistF ehistF'); auto. }
  iIntros (i). destruct (decide (i < length ehistF)); last first.
  { do 2 (rewrite lookup_ge_None_2; last lia). auto. }

  iDestruct ((big_sepL2_length _ _ ehistF) with "EF") as %HlenGF.
  iDestruct ((big_sepL2_length _ _ ehistF') with "EF'") as %HlenGF'.
  assert (gnames = gnames') as <-.
  { destruct Hgpref; [|symmetry]. all: apply prefix_length_eq; auto; lia. }

  Local Ltac lookup_solve := (apply lookup_lt_is_Some_2; lia).
  assert (is_Some (ehistF !! i)) as [ui Hui]; first lookup_solve.
  assert (is_Some (ehistF' !! i)) as [ui' Hui']; first lookup_solve.
  assert (is_Some (gnames !! i)) as [γi Hγi]; first lookup_solve.
  iDestruct (big_sepL2_delete with "EF") as "[EF _]"; eauto.
  iDestruct (big_sepL2_delete with "EF'") as "[EF' _]"; eauto.
  iCombine "EF EF'" gives %V.
  rewrite -Cinr_op Cinr_valid to_agree_op_valid leibniz_equiv_iff in V.
  by rewrite Hui Hui' V.
Qed.

Lemma epoch_history_prefix ehist ehistF :
  epoch_history_auth γ ehist -∗
  epoch_history_finalized γ ehistF -∗
  ⌜ehistF `prefix_of` ehist⌝.
Proof.
  rewrite prefix_forall.
  iIntros "EH EFin". iIntros (i Hi).
    iDestruct "EH" as (gnames Hgn) "[●L EH]".
    iDestruct "EFin" as (gnames') "[◯L EFin]".
  iDestruct (mono_list_auth_lb_valid with "●L ◯L") as %[_ Hpref].
  apply prefix_cut in Hpref as ->.
  iDestruct (big_sepL2_app_inv_l with "EH") as
    (ehist' ehist_suf) "(%Hehapp & EH' & _)".
  iDestruct ((big_sepL2_length _ _ ehistF) with "EFin") as %HgnF.
  iDestruct ((big_sepL2_length _ _ ehist') with "EH'") as %Hgn'.

  (* extract index i *)
  assert (is_Some (gnames' !! i)) as [γi Hγi]; first solve_lookup.
  assert (is_Some (ehistF !! i)) as [eF HeF]; first solve_lookup.
  assert (is_Some (ehist' !! i)) as [e' He']; first solve_lookup.
  iDestruct (big_sepL2_delete _ _ _ i with "EFin") as "[HFi _]"; eauto.
  iDestruct (big_sepL2_delete _ _ _ i with "EH'") as "[H'i _]"; eauto.
  destruct γi as [[γoi γsi] γfi]. simpl.
  iDestruct "H'i" as "(_ & _ & ●)".

  (* unify *)
  case_bool_decide.
  - iCombine "HFi ●" gives %HV.
    rewrite -Cinr_op in HV.
    apply to_agree_op_valid in HV.
    rewrite leibniz_equiv_iff in HV. subst.
    by rewrite HeF lookup_app He'.
  - iCombine "HFi ●" gives %HV. destruct HV.
Qed.

Lemma epoch_history_prefix_strong ehist ehistF :
  3 ≤ length ehist - 1 →
  epoch_history_auth γ ehist -∗
  epoch_history_finalized γ ehistF -∗
  ⌜ehistF `prefix_of` (take (length ehist - 2) ehist)⌝.
Proof.
  rewrite prefix_forall.
  iIntros (LE) "EH EFin". iIntros (i Hi).
    iDestruct "EH" as (gnames Hgn) "[●L EH]".
    iDestruct "EFin" as (gnames') "[◯L EFin]".
  iDestruct (mono_list_auth_lb_valid with "●L ◯L") as %[_ Hpref].
  apply prefix_cut in Hpref as ->.
  iDestruct (big_sepL2_app_inv_l with "EH") as
    (ehist' ehist_suf) "(%Hehapp & EH' & _)".
  iDestruct ((big_sepL2_length _ _ ehistF) with "EFin") as %HgnF.
  iDestruct ((big_sepL2_length _ _ ehist') with "EH'") as %Hgn'.

  (* extract index i *)
  assert (is_Some (gnames' !! i)) as [γi Hγi]; first solve_lookup.
  assert (is_Some (ehistF !! i)) as [eF HeF]; first solve_lookup.
  assert (is_Some (ehist' !! i)) as [e' He']; first solve_lookup.
  iDestruct (big_sepL2_delete _ _ _ i with "EFin") as "[HFi _]"; eauto.
  iDestruct (big_sepL2_delete _ _ _ i with "EH'") as "[H'i _]"; eauto.
  destruct γi as [[γoi γsi] γfi]. simpl.
  iDestruct "H'i" as "(_ & _ & ●)".

  (* unify *)
  case_bool_decide.
  - iCombine "HFi ●" gives %HV.
    rewrite -Cinr_op in HV.
    apply to_agree_op_valid in HV.
    rewrite leibniz_equiv_iff in HV. subst.
    rewrite lookup_take; last lia. by rewrite HeF lookup_app He'.
  - iCombine "HFi ●" gives %HV. destruct HV.
Qed.

Lemma epoch_history_le_strong ehist ehistF :
  3 ≤ length ehist - 1 →
  epoch_history_auth γ ehist -∗
  epoch_history_finalized γ ehistF  -∗
  ⌜length ehistF ≤ length ehist - 2⌝.
Proof.
  iIntros (LE) "EH EFin".
  iDestruct (epoch_history_prefix_strong with "EH EFin") as %PF; [done|].
  iPureIntro. apply prefix_length in PF. rewrite length_take_le in PF; auto. lia.
Qed.

Lemma epoch_history_le ehist ehistF :
  epoch_history_auth γ ehist -∗
  epoch_history_finalized γ ehistF  -∗
  ⌜length ehistF ≤ length ehist⌝.
Proof.
  iIntros "EH EFin".
  iDestruct (epoch_history_prefix with "EH EFin") as %PF.
  iPureIntro. by apply prefix_length in PF.
Qed.

Lemma epoch_history_auth_snap_finalized e ehist unlinked_e ehistF :
  e < length ehistF →
  epoch_history_auth γ ehist -∗
  epoch_history_snap γ e unlinked_e -∗
  epoch_history_finalized γ ehistF -∗
  ⌜unlinked_e ⊆ fold_hist ehistF⌝.
Proof.
  iIntros (He) "A S F".
  iDestruct (epoch_history_snapshot with "A S") as %[ue [Hue Hsub]].
  iDestruct (epoch_history_prefix with "A F") as %Hpref.
  assert (ehistF !! e = Some ue).
  { apply prefix_cut in Hpref.
    rewrite Hpref lookup_app_l in Hue; auto. }
  iPureIntro. etrans; first apply Hsub.
  by eapply ehist_elem_in_fold_hist.
Qed.

Lemma epoch_history_finalized_lookup i ehist ehistF :
  i ∉ fold_hist ehist →
  epoch_history_auth γ ehist -∗
  epoch_history_finalized γ ehistF -∗
  ⌜i ∉ fold_hist ehistF⌝.
Proof.
  iIntros (Hi) "EH EFin".
  iDestruct (epoch_history_prefix with "EH EFin") as %Hpref.
  apply fold_hist_prefix in Hpref.
  iPureIntro. set_solver.
Qed.

End rules.

#[export] Typeclasses Opaque epoch_history_auth epoch_history_frag epoch_history_snap epoch_history_finalized.
