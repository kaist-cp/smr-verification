From iris.base_logic Require Import ghost_map.
From iris.proofmode Require Export tactics.
From smr.base_logic Require Import mono_list.
From iris.prelude Require Import options.
From stdpp Require Export list gmultiset gmap fin_map_dom.
From smr Require Import helpers.

Notation Id := positive (only parsing).

Inductive event :=
  | link (i: Id) (offset: nat) (J: option Id)
  | del (i: Id).

Global Instance event_eq_dec : EqDecision event.
Proof. solve_decision. Defined.

Definition event_id (e: event) : Id :=
  match e with
  | link i _ _ => i
  | del i => i
  end.

Implicit Types (H: list event) (i j: Id).

Definition LiveAt H i := del i ∉ H.

Local Hint Unfold LiveAt : core.

Local Instance LiveAt_Decision: RelDecision LiveAt.
Proof. solve_decision. Defined.

(* NOTE: can be defined from succ_hist_map *)
Local Definition interp H : gmap (Id * nat) Id :=
  fold_left (λ m e,
    match e with
    | link i o (Some new) => <[(i, o) := new]> m
    | link i o None => delete (i, o)  m
    | _ => m
    end
  ) H ∅.

(* Not needed *)
(* Local Definition del_i_max_once H: Prop := *)
(*   ∀ i (a b: nat), H !! a = Some (del i) → H !! b = Some (del i) → a = b. *)

Local Definition no_new_link_to_deleted H: Prop:=
  ∀ i j o (a b: nat), a < b → H !! a = Some (del j) → H !! b = Some (link i o (Some j)) → False.

Local Definition live_points_to_live H: Prop :=
  ∀ i o j, (interp H) !! (i, o) = Some j → LiveAt H i → LiveAt H j.

Local Definition well_formed H : Prop :=
  no_new_link_to_deleted H ∧ live_points_to_live H.

Local Definition succ_hist_map H : gmap (Id * nat) (list (option Id)) :=
  fold_left (λ m e,
    match e with
    | link i o new => <[ (i, o) := (default [] (m !! (i, o))) ++ [new] ]> m
    | del i => m
    end
  ) H ∅.

Definition field_hist H i o : list (option Id) :=
  default [] (succ_hist_map H !! (i, o)).

Local Definition del_map_consistent H (del_map: gmap Id bool): Prop :=
  ∀ i,
  (i ∈ dom del_map → i ∈ event_id <$> H) ∧
  (del_map !! i = Some true → (¬ LiveAt H i)) ∧
  (del_map !! i = Some false → LiveAt H i).

Local Definition pred_map_consistent H (π : gmap Id (gmultiset (Id * nat))) : Prop  :=
  (∀ j, j ∈ dom π → j ∈ event_id <$> H) ∧
  (∀ i o j, (interp H) !! (i, o) = Some j → LiveAt H i → ∃ i_s, (π !! j = Some i_s ∧ (i, o) ∈ i_s)).

Local Definition to_pred_multiset_map (π: gmap Id (gmultiset (Id * nat))): gmap Id (gmultiset Id) :=
  (λ set, list_to_set_disj (fst <$> elements set)) <$> π.


(** * properties of history *)
Section history.

Lemma unregistered_is_alive i H: i ∉ event_id <$> H → LiveAt H i.
Proof.
  intros NotIn. unfold LiveAt. set_unfold. intros del_i. apply NotIn. exists (del i). done.
Qed.

Lemma del_map_unaffected_by_links H H' appended del_map:
  H' = H ++ appended →
  del_map_consistent H del_map →
  (∀ di, del di ∉ appended) →
  del_map_consistent H' del_map.
Proof.
  intros eqnH' prev_consistent no_del i. specialize (prev_consistent i) as (pc1 & pc2 & pc3). subst H'.
  unfold LiveAt in *. set_solver.
Qed.


Lemma unregistered_points_to_nowhere i o H:
  i ∉ event_id <$> H → interp H !! (i, o) = None.
Proof.
  intros. induction H as [| x H' IH] using rev_ind.
  - done.
  - assert (i ∉ event_id <$> H' ∧ i ≠ event_id x) as [i_notin_H' i_notin_x] by set_solver.
    apply IH in i_notin_H'. unfold interp. rewrite fold_left_app. fold (interp H'). destruct x; simpl.
    + destruct J; simpl in *.
      * rewrite lookup_insert_ne; [done | congruence].
      * rewrite lookup_delete_ne; [done | congruence].
    + done.
Qed.

Lemma unregistered_has_no_succ_hist H i o:
  i ∉ event_id <$> H  → (i, o) ∉ dom (succ_hist_map H).
Proof.
  induction H using rev_ind.
  - set_solver.
  - unfold succ_hist_map. rewrite fold_left_app. fold (succ_hist_map H). rewrite fmap_app. destruct x; set_solver.
Qed.

Lemma succ_hist_update H i o Oj hist:
  (succ_hist_map H) !! (i, o) = Some hist →
  succ_hist_map (H ++ [link i o Oj]) = <[ (i, o) := hist ++ [Oj] ]> (succ_hist_map H).
Proof.
  unfold succ_hist_map. rewrite fold_left_app. fold (succ_hist_map H). simpl. intros ->. done.
Qed.

Lemma succ_hist_unaffected_by_del H j:
  succ_hist_map (H ++ [del j]) = succ_hist_map H.
Proof.
  unfold succ_hist_map. rewrite fold_left_app. done.
Qed.

Lemma succ_hist_create H i o Oj:
  (succ_hist_map H) !! (i, o) = None →
  succ_hist_map (H ++ [link i o Oj]) = <[ (i, o) := [Oj] ]> (succ_hist_map H).
Proof.
  unfold succ_hist_map. rewrite fold_left_app. fold (succ_hist_map H). simpl. intros ->. done.
Qed.

Lemma interp_unaffected_by_del H j:
  interp (H ++ [del j]) = interp H.
Proof. unfold interp. rewrite fold_left_app. done. Qed.

Lemma interp_lookup_app_link H i o oj:
  interp (H ++ [link i o oj]) !! (i, o) = oj.
Proof.
  unfold interp. rewrite fold_left_app. simpl. destruct oj.
  - apply lookup_insert.
  - apply lookup_delete.
Qed.

Lemma interp_lookup_app_link_ne H i o i' o' oj:
  (i, o) ≠ (i', o') →
  interp (H ++ [link i o oj]) !! (i', o') = interp H !! (i', o').
Proof.
  intros. unfold interp. rewrite fold_left_app. simpl. destruct oj.
  - by apply lookup_insert_ne.
  - by apply lookup_delete_ne.
Qed.

Lemma last_succ_hist_is_interp H i o sh oj:
  succ_hist_map H !! (i, o) = Some sh →
  last sh = Some oj →
  interp H !! (i, o) = oj.
Proof.
  generalize dependent sh.
  induction H as [| last_event H] using rev_ind; [done|].

  intros sh H_io H_last.
  unfold succ_hist_map in H_io. rewrite fold_left_app in H_io. fold (succ_hist_map H) in H_io.
  unfold interp. rewrite fold_left_app. fold (interp H). simpl in *.

  case (last_event) as [i' o' J | ?].
  - destruct J as [new_j | ].
    + case (decide ((i', o') = (i, o))) as [[= -> ->] | NE].
      * rewrite lookup_insert. rewrite lookup_insert in H_io.
        injection H_io as <-. rewrite last_app in H_last. naive_solver.
      * rewrite lookup_insert_ne; last done. rewrite lookup_insert_ne in H_io; last done. naive_solver.
    + case (decide ((i', o') = (i, o))) as [[= -> ->] | NE].
      * rewrite lookup_delete. rewrite lookup_insert in H_io.
        injection H_io as <-. rewrite last_app in H_last. naive_solver.
      * rewrite lookup_delete_ne; last done. rewrite lookup_insert_ne in H_io; last done. naive_solver.
  - by eapply IHH.
Qed.

Lemma field_hist_lookup_not_in_prefix H Hstart i o n to :
  Hstart `prefix_of` H →
  (* Read something not in Hstart *)
  length (field_hist Hstart i o) ≤ n →
  field_hist H i o !! n = Some to →
  ∃ b, H !! b = Some (link i o to) ∧ length Hstart ≤ b.
Proof.
  intros [rest ->] Seen_n.
  induction rest as [|last_event rest] using rev_ind.
  { rewrite app_nil_r. intros Hio_n. exfalso.
    apply lookup_lt_Some in Hio_n. lia. }

  rewrite app_assoc.
  intros Hio_n.
  rewrite /field_hist /succ_hist_map fold_left_app in Hio_n.
  rewrite -/(succ_hist_map (Hstart ++ rest)) /= in Hio_n.
  case last_event as [i' o' J | ?]; simpl in *; last first.
  { (* del *)
    rewrite -/(field_hist _ _ _) in Hio_n.
    specialize (IHrest Hio_n) as [a [??]]. exists a.
    split; [|done]. by apply lookup_app_l_Some. }

  rewrite -/(field_hist _ _ _) in Hio_n.
  case (decide ((i', o') = (i, o))) as [[= -> ->] | NE]; simpl in *.
  - rewrite lookup_insert /= in Hio_n.
    apply lookup_snoc_Some in Hio_n as [[? Hio_n] | [? ->]].
    + specialize (IHrest Hio_n) as [a [??]]. exists a.
      split; [|done]. by apply lookup_app_l_Some.
    + exists (length (Hstart ++ rest)). rewrite snoc_lookup. split; [done|].
      rewrite app_length. lia.
  - rewrite lookup_insert_ne in Hio_n; last done.
    specialize (IHrest Hio_n) as [a [??]]. exists a.
    split; [|done]. by apply lookup_app_l_Some.
Qed.

Lemma pred_in_pred_multiset H π i o j:
  pred_map_consistent H π →
  (interp H) !! (i, o) = Some j →
  LiveAt H i →
  ∃ pmm, (to_pred_multiset_map π) !! j = Some pmm ∧ i ∈ pmm.
Proof.
  intros [_ pmc] io_points_to i_alive.
  specialize (pmc i o j).
  assert (∃ i_s, π !! j = Some i_s ∧ (i, o) ∈ i_s) as [i_s [πj io_is]] by auto.
  exists (list_to_set_disj (elements i_s).*1).
  unfold to_pred_multiset_map. rewrite lookup_fmap. rewrite πj. simpl. split; try done.
  rewrite elem_of_list_to_set_disj. set_unfold. exists (i, o). rewrite gmultiset_elem_of_elements. done.
Qed.

Lemma succ_hist_map_lookup_prefix H1 H2 h1 io:
  H1 `prefix_of` H2 →
  succ_hist_map H1 !! io = Some h1 →
  ∃ h2, succ_hist_map H2 !! io = Some h2 ∧ h1 `prefix_of` h2.
Proof.
  intros [rest ->] Hh1.
  induction rest using rev_ind.
  - rewrite app_nil_r. eexists. done.
  - rewrite app_assoc. remember (H1 ++ rest) as H1'. clear HeqH1'. unfold succ_hist_map. rewrite fold_left_app. fold (succ_hist_map H1').
    destruct IHrest as (h2' & ? & ?).
    destruct x; simpl.
    + case (decide ((i, offset) = io)) as [-> | NE].
      * rewrite lookup_insert. eexists. split; try done. rewrite H. simpl. apply prefix_app_r. done.
      * rewrite lookup_insert_ne; last done. eauto.
    + eauto.
Qed.

Lemma succ_hist_map_prefix_mono H1 H2 h1 h2 io:
  H1 `prefix_of` H2 →
  succ_hist_map H1 !!! io = h1 →
  succ_hist_map H2 !!! io = h2 →
  h1 `prefix_of` h2.
Proof.
  intros [rest ->] Hh1. move: h2.
  induction rest as [|e ?] using rev_ind.
  - intros h2. rewrite app_nil_r. subst. exists []. rewrite app_nil_r. done.
  - intros h2. rewrite app_assoc. remember (H1 ++ rest) as H1'.
    rewrite /succ_hist_map fold_left_app. fold (succ_hist_map H1').
    destruct e; simpl.
    + case (decide ((i, offset) = io)) as [-> | NE].
      * rewrite lookup_total_insert. intros <-.
        apply prefix_app_r. apply IHrest. done.
      * intros <-. rewrite lookup_total_insert_ne; last done. apply IHrest. done.
    + intros. apply IHrest. done.
Qed.

Lemma field_hist_prefix_lookup_Some H Hlink i o n to :
  Hlink `prefix_of` H →
  field_hist Hlink i o !! n = Some to →
  field_hist H i o !! n = Some to.
Proof.
  intros PF. rewrite /field_hist.
  destruct (succ_hist_map Hlink !! (i, o)) as [Hlink_io|] eqn:Eqn_Hlink_io; [simpl|done].
  specialize (succ_hist_map_lookup_prefix _ _ _ _ PF Eqn_Hlink_io) as (H_io & -> & PF_io). simpl.
  intros Hlink_io_n.
  by apply (prefix_lookup_Some _ _ _ _ Hlink_io_n PF_io).
Qed.

End history.

Class node_link_historyG Σ := NodeLinkHistoryG {
  #[local] node_link_history_historyG :: mono_listG event Σ;
  #[local] node_link_history_successorG :: ghost_mapG Σ (positive * nat) (list (option positive));
  #[local] node_link_history_predecessorG :: ghost_mapG Σ positive (gmultiset positive);
  #[local] node_link_history_deletedG :: ghost_mapG Σ positive bool;
}.

Definition node_link_historyΣ : gFunctors :=
  #[mono_listΣ event;
    ghost_mapΣ (positive * nat) (list (option positive));
    ghost_mapΣ positive (gmultiset positive);
    ghost_mapΣ positive bool].

Global Instance subG_node_link_historyΣ {Σ} :
  subG node_link_historyΣ Σ → node_link_historyG Σ.
Proof. solve_inG. Qed.

(** * Node link history ghost *)
Section ghost.

Context `{!node_link_historyG Σ}.
Notation iProp := (iProp Σ).

Variable (γ: gname).
Implicit Types (γh γt γb γd : gname).

(** ** assertions *)

Definition HistAuth H: iProp :=
  ∃ γh γt γb γd π del_map,
  ⌜ γ = encode (γh, γt, γb, γd) ⌝ ∗
  ⌜ del_map_consistent H del_map ⌝ ∗
  ⌜ pred_map_consistent H π ⌝ ∗
  ⌜ well_formed(H) ⌝ ∗
  mono_list_auth_own γh 1 H ∗
  ghost_map_auth γt 1 (succ_hist_map H) ∗
  ghost_map_auth γb 1 (to_pred_multiset_map π) ∗
  ghost_map_auth γd 1 del_map.

Definition HistSnap H : iProp :=
  ∃ γh γt γb γd,
  ⌜ γ = encode (γh, γt, γb, γd) ⌝ ∗
  ⌜ well_formed H ⌝ ∗
  mono_list_lb_own γh H.

Definition HistPointsTo (i: Id) (o: nat) (Hio: list (option Id)): iProp :=
  ∃ γh γt γb γd Hlink,
  ⌜ γ = encode (γh, γt, γb, γd) ⌝ ∗
  ⌜ Hio = field_hist Hlink i o ⌝ ∗
  mono_list_lb_own γh Hlink ∗
  (i, o) ↪[γt] Hio.

Definition HistPointsToLast i o oj: iProp :=
  ∃ γh γt γb γd Hlink,
  ⌜ γ = encode (γh, γt, γb, γd) ⌝ ∗
  ⌜ last Hlink = Some (link i o oj) ⌝ ∗
  mono_list_lb_own γh Hlink ∗
  (i, o) ↪[γt] ((succ_hist_map Hlink) !!! (i, o)).
(*
Definition HistPointsToLast i o oj: iProp :=
  ∃ Hio,
    ⌜ last Hio = Some oj ⌝ ∗
    HistPointsTo i o Hio.
*)

Definition HistPointedTo (i: Id) (o: nat) (n : nat) (to : option Id): iProp :=
  ∃ γh γt γb γd Hlink,
  ⌜ γ = encode (γh, γt, γb, γd) ⌝ ∗
  ⌜ field_hist Hlink i o !! n = Some to ⌝ ∗
  mono_list_lb_own γh Hlink.

Definition HistPointedBy j (B: gmultiset Id): iProp :=
  ∃ γh γt γb γd,
  ⌜ γ = encode (γh, γt, γb, γd) ⌝ ∗
  j ↪[γb] B ∗
  j ↪[γd] false.

Definition HistDeleted j: iProp :=
  ∃ γh γt γb γd,
  ⌜ γ = encode (γh, γt, γb, γd) ⌝ ∗
  j ↪[γb]□ ∅ ∗
  j ↪[γd]□ true.


(** ** helper lemmas *)

Ltac exfr := repeat (repeat iExists _; iFrame "∗#%").

Global Instance HistAuth_timeless H : Timeless (HistAuth H).
Proof. repeat apply bi.exist_timeless. apply _. Qed.
Global Instance HistSnap_timeless H : Timeless (HistSnap H).
Proof. repeat apply bi.exist_timeless. apply _. Qed.
Global Instance HistSnap_persistent H : Persistent (HistSnap H).
Proof. repeat apply bi.exist_persistent. apply _. Qed.
Global Instance HistPointsTo_timeless i o oj : Timeless (HistPointsToLast i o oj).
Proof. repeat apply bi.exist_timeless. apply _. Qed.
Global Instance HistPointsTo'_timeless i o Hio : Timeless (HistPointsTo i o Hio).
Proof. repeat apply bi.exist_timeless. apply _. Qed.
Global Instance HistPointsToSnap_timeless i o n to : Timeless (HistPointedTo i o n to).
Proof. repeat apply bi.exist_timeless. apply _. Qed.
Global Instance HistPointsToSnap_persistent i o n to : Persistent (HistPointedTo i o n to).
Proof. repeat apply bi.exist_persistent. apply _. Qed.
Global Instance HistPointedBy_timeless j B : Timeless (HistPointedBy j B).
Proof. repeat apply bi.exist_timeless. apply _. Qed.
Global Instance HistDeleted_Persistent j : Persistent (HistDeleted j).
Proof. repeat apply bi.exist_persistent. apply _. Qed.
Global Instance HistDeleted_timeless j : Timeless (HistDeleted j).
Proof. repeat apply bi.exist_timeless. apply _. Qed.

Local Lemma PointsTo_reflects_interp H i o oj:
  HistAuth H -∗
  HistPointsToLast i o oj -∗
  ⌜ interp H !! (i, o) = oj ⌝.
Proof.
  iIntros "HistAuth PointsTo".
  iDestruct "HistAuth" as (??????) "(%Enc & _ & _ & _ &
    _ & ●succ_hist & _ & _)".
  iDestruct "PointsTo" as (?????) "(% & %Hlink_last & ◯Hlink & ◯succ_hist_io)". encode_agree Enc.

  iDestruct (ghost_map_lookup with "●succ_hist ◯succ_hist_io") as "%shm_lookup".
  iPureIntro.
  eapply last_succ_hist_is_interp.
  - exact shm_lookup.
  - rewrite last_Some in Hlink_last. destruct Hlink_last as [Hlink' e]. subst Hlink.
    unfold succ_hist_map. rewrite fold_left_app. fold (succ_hist_map Hlink'). simpl.
    rewrite lookup_total_insert. rewrite last_app. done.
Qed.

Local Lemma remove_deleted_from_PointedBy i j H B π γh γt γb γd:
  γ = encode (γh, γt, γb, γd) →
  i ∈ B →
  pred_map_consistent H  π →
  ¬ LiveAt H i →
  ghost_map_auth γb 1 (to_pred_multiset_map π) -∗
  HistPointedBy j B ==∗

  ∃ πj o, ⌜ π !! j = Some πj ⌝ ∗
    ⌜ (i, o) ∈ πj ⌝ ∗
    ghost_map_auth γb 1 (to_pred_multiset_map (<[ j:= (πj ∖ {[+ (i, o) +]}) ]> π)) ∗
    HistPointedBy j (B ∖ {[+ i +]}).
Proof.
  iIntros (Enc i_in_B pred_map_consistent i_not_alive) "●pred_multiset PointedBy".

  (* access π !! j *)
  iDestruct "PointedBy" as (?????) "[◯pred_j ◯del_map_j]". encode_agree Enc.
  iDestruct (ghost_map_lookup with "●pred_multiset ◯pred_j") as "%pm_lookup".

  unfold to_pred_multiset_map in pm_lookup. rewrite lookup_fmap in pm_lookup.

  destruct (π !! j) as [πj |] eqn: Eqn_πj; last naive_solver. simpl in *.
  injection pm_lookup. intros Eqn_B.

  iMod (ghost_map_update (B ∖ {[+ i +]}) with "●pred_multiset ◯pred_j") as "[●pred_multiset' ◯pred_j']".

  assert (∃ o, (i, o) ∈ πj) as [o io_in_πj]. {
    clear -Eqn_B i_in_B. subst B. induction πj using gmultiset_ind.
    - rewrite gmultiset_elements_empty in i_in_B. set_solver.
    - rewrite gmultiset_elements_disj_union in i_in_B. rewrite fmap_app in i_in_B.
      rewrite list_to_set_disj_app in i_in_B. rewrite gmultiset_elem_of_disj_union in i_in_B.
      destruct i_in_B as [i_is_x | ?].
      + rewrite gmultiset_elements_singleton in i_is_x. assert (i = x.1) by multiset_solver.
        exists x.2. subst i.  replace ((x.1, x.2)) with x; last by destruct x. multiset_solver.
      + specialize (IHπj H) as [o ?]. exists o. multiset_solver.
  }

  remember (πj ∖ {[+ (i, o) +]}) as πj'.
  assert (πj = {[+ (i, o) +]} ⊎ πj') as πj_πj'. { subst πj'. by eapply gmultiset_disj_union_difference'. }
  remember (<[ j := πj' ]> π) as π'.

  assert (<[j:=B ∖ {[+ i +]}]> (to_pred_multiset_map π) = to_pred_multiset_map π') as ->. {
    subst π'. unfold to_pred_multiset_map. rewrite fmap_insert. f_equal. subst B πj.
    rewrite gmultiset_elements_disj_union. rewrite fmap_app. rewrite list_to_set_disj_app.
    rewrite gmultiset_elements_singleton. multiset_solver.
  }
  subst π' πj'.
  exfr. done.
Qed.


(** ** rules *)

Lemma hist_optimistic_traversal i o j Hstart Hcurr :
  LiveAt Hstart i →
  HistAuth Hcurr -∗ HistSnap Hstart -∗ HistPointsToLast i o (Some j) -∗ ⌜ LiveAt Hstart j ⌝.
Proof.
  iIntros (i_liveat_H) "HistAuth Snap PointsTo".
  iDestruct "HistAuth" as (??????) "(%Enc & _ & _ & %well_formed_Hcurr &
    ●Hcurr & ●succ_hist & _ & _)".
  iDestruct "Snap" as (?????) "[%well_formed_H ◯Hstart]". encode_agree Enc.
  iDestruct "PointsTo" as (??????) "(%Hlink_last & ◯Hlink & ◯succ_hist_io)". encode_agree Enc.
  iDestruct (mono_list_auth_lb_valid with "●Hcurr ◯Hlink") as %[_ Hlink_before_Hcurr].
  iDestruct (mono_list_auth_lb_valid with "●Hcurr ◯Hstart") as %[_ Hstart_before_Hcurr].
  iDestruct (mono_list_lb_valid with "◯Hstart ◯Hlink") as %[Hstart_before_Hlink | Hlink_before_Hstart].

  - iPureIntro.
    assert (LiveAt Hlink j); last by eauto using (elem_of_prefix _ _ _ _ Hstart_before_Hlink).
    assert (∀ a, Hlink !! a = Some (del j) → False); last first.
    { unfold LiveAt in *. rewrite elem_of_list_lookup. naive_solver. }
    intros a lookup_Ha. rewrite last_lookup in Hlink_last.
    replace (Init.Nat.pred (length Hlink)) with ((length Hlink) - 1) in *; last lia.
    assert (a < length Hlink - 1) as a_lt_length_Hlink_m1. {
      assert (a ≠ length Hlink - 1) by congruence.
      have ? := lookup_lt_Some _ _ _ lookup_Ha. lia.
    }
    destruct well_formed_Hcurr as (nnltd & _). unfold no_new_link_to_deleted in nnltd.
    eapply nnltd.
    + exact a_lt_length_Hlink_m1.
    + eapply (prefix_lookup_Some Hlink); done.
    + eapply (prefix_lookup_Some Hlink); done.

  - iDestruct (ghost_map_lookup with "●succ_hist ◯succ_hist_io") as "%Eqn_Hcurr_io".
    iPureIntro.
    assert (∃ Hlink_io, succ_hist_map Hlink !! (i, o) = Some Hlink_io ∧ last Hlink_io = Some (Some j))
      as (Hlink_io & Eqn_Hlink_io & last_Hlink_io).
    {
      rewrite last_Some in Hlink_last. destruct Hlink_last as [Hlink' e]. subst Hlink.
      unfold succ_hist_map. rewrite fold_left_app. fold (succ_hist_map Hlink'). simpl.
      eexists. rewrite lookup_insert. split; try done. rewrite last_app. done.
    }
    rewrite -lookup_lookup_total in Eqn_Hcurr_io; last done.
    rewrite Eqn_Hlink_io in Eqn_Hcurr_io.

    assert (succ_hist_map Hstart !! (i, o) = Some Hlink_io). {
      specialize (succ_hist_map_lookup_prefix _ _ _ _ Hlink_before_Hstart Eqn_Hlink_io)
        as (Hstart_io & Eqn_Hstart_io & Hlink_io_po_Hstart_io).
      specialize (succ_hist_map_lookup_prefix _ _ _ _ Hstart_before_Hcurr Eqn_Hstart_io)
        as (Hcurr_io & Eqn_Hcurr_io' & Hstart_io_po_Hcurr_io).
      assert (Hlink_io = Hcurr_io) as <- by congruence. clear Eqn_Hcurr_io'.
      assert (Hlink_io = Hstart_io) as <- by by apply (anti_symm prefix).
      done.
    }
    assert (interp Hstart !! (i, o) = Some j) as io_points_to_j; first by eapply last_succ_hist_is_interp.

    destruct well_formed_H as (_ & lptl).
    unfold live_points_to_live in lptl.
    eapply lptl; done.
Qed.

Lemma HistPointsTo_snap i o Hio n to :
  Hio !! n = Some to → HistPointsTo i o Hio -∗ HistPointedTo i o n to.
Proof.
  iIntros (Hio_n) "PointsTo".
  iDestruct "PointsTo" as (??????) "(%Hio_def & ◯Hlink & ◯succ_hist_io)".
  iFrame "∗%". iPureIntro. congruence.
Qed.

Lemma hist_optimistic_traversal' i o n j Hstart Hcurr :
  LiveAt Hstart i →
  (* read was done with the observation of Hstart *)
  length (field_hist Hstart i o) - 1 ≤ n →
  HistAuth Hcurr -∗
  HistSnap Hstart -∗
  (* read n-th event from (i,o) *)
  HistPointedTo i o n (Some j) -∗
  ⌜ LiveAt Hstart j ⌝.
Proof.
  iIntros (Hstart_i Hstart_io_len_n) "HistAuth Snap PointsTo".
  iDestruct "HistAuth" as (??????) "(%Enc & _ & _ & %well_formed_Hcurr &
    ●Hcurr & ●succ_hist & _ & _)".
  iDestruct "Snap" as (?????) "[%well_formed_Hstart ◯Hstart]". encode_agree Enc.
  iDestruct "PointsTo" as (???? Hlink ?) "(%Hlink_io_n & ◯Hlink)". encode_agree Enc.
  iDestruct (mono_list_auth_lb_valid with "●Hcurr ◯Hlink") as %[_ Hlink_before_Hcurr].
  iDestruct (mono_list_auth_lb_valid with "●Hcurr ◯Hstart") as %[_ H_before_Hcurr].
  iDestruct (mono_list_lb_valid with "◯Hstart ◯Hlink") as %Hstart_Hlink.
  remember (field_hist Hstart i o) as Hstart_io eqn:Hstart_io_def.
  remember (field_hist Hlink i o) as Hlink_io eqn:Hlink_io_def.

  (* Assume j is dead in Hstart *)
  iPureIntro. intros Hstart_j.

  (* by the two assumptions on n, Hstart_io can't be longer than Hlink_io *)
  have {Hstart_Hlink}Hstart_Hio : Hstart_io `prefix_of` Hlink_io.
  { have Hstart_Hio : Hstart_io `prefix_of` Hlink_io ∨ Hlink_io `prefix_of` Hstart_io.
    { destruct Hstart_Hlink as [PF|PF]; [left|right]; by eapply succ_hist_map_prefix_mono. }
    destruct Hstart_Hio as [?|PF]; first done.
    case (decide (Hlink_io = Hstart_io)) as [->|NE]; first done.
    assert (length Hlink_io ≠ length Hstart_io) by auto using prefix_length_eq.
    apply prefix_length in PF. apply lookup_lt_Some in Hlink_io_n. lia. }

  (* n can't be newer than the events in in Hstart_io, because of no_new_link_to_deleted *)
  have n_Hstart_io : n < length Hstart_io.
  { destruct well_formed_Hcurr as [nnltd _]. unfold no_new_link_to_deleted in nnltd.
    apply Nat.lt_nge => {}Hstart_io_len_n.
    (* From [del j ∈ Hstart], get [∃ a, Hstart !! a = Some (del j)] *)
    apply elem_of_list_lookup in Hstart_j. destruct Hstart_j as [a Hstart_j].
    (* From [Hlink_io !! n = Some (Some j)], get [∃ b, Hlink !! b = Some (link i o (Some j))] *)
    (* From [length Hstart_io ≤ n], get [length Hstart ≤ b]. Since [a < length Hstart], [a < b]. *)
    opose proof (field_hist_lookup_not_in_prefix Hcurr Hstart i o n (Some j) H_before_Hcurr _ _) as Hb.
    { subst Hstart_io. done. }
    { subst. eapply (field_hist_prefix_lookup_Some _ Hlink _ _ _ _ Hlink_before_Hcurr). done. }
    destruct Hb as (b & Hcurr_b & Hstart_b).
    refine (nnltd _ _ _ a b _ _ Hcurr_b).
    - apply lookup_lt_Some in Hstart_j. lia.
    - by eapply prefix_lookup_Some. }
  (* combined with the precondition, it follows that n is the last event in Hstart_io *)
  have {n_Hstart_io Hstart_io_len_n} [Hstart_io_len_n Hstart_io_NE] :
    n = length Hstart_io - 1 ∧ length Hstart_io > 0 by lia.
  have {Hstart_io_NE}Hstart_io_n : Hstart_io !! n = Some (Some j).
  { rewrite (prefix_lookup_lt Hstart_io Hlink_io n ltac:(lia) Hstart_Hio). done. }

  (* by live_points_to_live in Hstart, j must be live in Hstart *)
  destruct well_formed_Hstart as [_ lptl]. unfold live_points_to_live in lptl.
  eapply lptl; [|done..].
  eapply (last_succ_hist_is_interp _ _ o Hstart_io).
  - rewrite /field_hist in Hstart_io_def.
    destruct (succ_hist_map Hstart !! (i, o)) eqn:?; by simplify_eq/=.
  - rewrite last_lookup. rewrite -Nat.sub_1_r. congruence.
Qed.

Lemma hist_take_snapshot H:
  HistAuth H -∗ HistSnap H.
Proof.
  iIntros "HistAuth".
  iDestruct "HistAuth" as (??????) "(%Enc & _ & _ & % & ●H & _)".
  unfold HistSnap. repeat iExists _.
  iDestruct (mono_list_lb_own_get with "●H") as "◯H".
  by iFrame.
Qed.

Lemma hist_auth_snap_valid H1 H2:
  HistAuth H1 -∗ HistSnap H2 -∗ ⌜ H2 `prefix_of` H1 ⌝.
Proof.
  iIntros "Auth Snap".
  iDestruct "Auth" as (??????) "(%Enc & _ & _ & _ & ●H & _)".
  iDestruct "Snap" as (?????) "[_ ◯H]". encode_agree Enc.
  iDestruct (mono_list_auth_lb_valid with "●H ◯H") as "[_ $]".
Qed.


Lemma hist_pointsto_is_registered H i o oj:
  HistAuth H -∗ HistPointsToLast i o oj -∗ ⌜ i ∈ event_id <$> H ⌝.
Proof.
  (* NOTE: this can also be proved using 'unregistered_has_no_succ_hist' *)
  iIntros "Auth PointsTo".
  iDestruct "Auth" as (??????) "(%Enc & _ & _ & _ & ●H & _)".
  iDestruct "PointsTo" as (?????? last_hlink) "(◯Hlink & _)". encode_agree Enc.
  iDestruct (mono_list_auth_lb_valid with "●H ◯Hlink") as "[#_ %Hlink_before_H]".
  iPureIntro.
  rewrite last_Some in last_hlink. destruct last_hlink as [l' Eqn_Hlink].
  assert (i ∈ event_id <$> Hlink). {
    subst Hlink. rewrite fmap_app /=. set_solver.
  }
  rewrite prefix_cut in Hlink_before_H. rewrite Hlink_before_H. set_solver.
Qed.


Lemma hist_pointedby_is_registered H j B:
  HistAuth H -∗ HistPointedBy j B -∗ ⌜ j ∈ event_id <$> H ⌝.
Proof.
  iIntros "HistAuth PointedBy".
  iDestruct "HistAuth" as (??????) "(%Enc & %H_del_map_consistent & _ & _ & _ & _ & _ & ●del_map)".
  iDestruct "PointedBy" as (?????) "[◯pred_j ◯del_map_j]". encode_agree Enc.

  simpl. iDestruct (ghost_map_lookup with "●del_map ◯del_map_j") as "%".
  destruct (H_del_map_consistent j) as (Hdom & _). iPureIntro. apply Hdom. eapply elem_of_dom_2. done.
Qed.

Lemma hist_pointedby_is_alive H j B:
  HistAuth H -∗ HistPointedBy j B -∗ ⌜ LiveAt H j ⌝.
Proof.
  iIntros "HistAuth PointedBy".
  iDestruct "HistAuth" as (??????) "(%Enc & %del_map_consistent_b & _ & _ & _ & _ & _ & ●del_map)".
  iDestruct "PointedBy" as (?????) "[◯pred_j ◯del_map_j]". encode_agree Enc.

  iDestruct (ghost_map_lookup with "●del_map ◯del_map_j") as "%". unfold del_map_consistent in *. naive_solver.
Qed.


Lemma hist_deleted_is_not_alive H j:
  HistAuth H -∗ HistDeleted j -∗ ⌜ ¬ LiveAt H j ⌝.
Proof.
  iIntros "Auth #Deleted".
  iDestruct "Auth" as (??????) "(%Enc & %del_map_consistent_b & _ & _ & _ & _ & _ & ●del_map)".
  iDestruct "Deleted" as (?????) "[_ ◯del_map_j]". encode_agree Enc.

  iDestruct (ghost_map_lookup with "●del_map ◯del_map_j") as "%". unfold del_map_consistent in *. naive_solver.
Qed.

Lemma hist_create_node (H: list event) (size: nat) i:
  size > 0 →
  i ∉ event_id <$> H →
  HistAuth H ==∗
  HistAuth (H ++  ((λ o, link i o None) <$> (seq 0 size)) ) ∗ HistPointedBy i ∅ ∗
  ([∗ list] o ∈ seq 0 size, HistPointsToLast i o None).
Proof.
  rename i into new_i.
  iIntros (size_not_0 new_i_is_new) "HistAuth".
  iDestruct "HistAuth" as (??????) "(%Enc & %del_map_consistent_before & %pred_map_consistent_before & %well_formed_before &
    ●H & ●succ_hist & ●pred_multiset & ●del_map)".

  (* updated history H' *)
  remember (H ++ ((λ o : nat, link new_i o None) <$> seq 0 size)) as H'.

  (* helpers *)
  assert (∃ sm1, S sm1 = size) as [sm1 HeqSm1]; first by exists (size - 1); lia.
  assert (new_i ∈ event_id <$> H') as H'_new_i. {
    simpl in HeqH'. set_unfold. exists (link new_i 0 None). set_solver.
  }

  (* update del_map *)
  iMod (ghost_map_insert new_i false with "●del_map") as "[●del_map' ◯del_new_i]". {
    specialize (del_map_consistent_before new_i) as [del_map_domain _].
    apply not_elem_of_dom. auto.
  }
  remember ((<[new_i:=false]> del_map)) as del_map'.
  have del_map_consistent_after: (del_map_consistent H' del_map'). {
    unfold del_map_consistent. intros i.
    case (decide (i = new_i)) as [-> | NE_new_i]; subst del_map'.
    - rewrite lookup_insert. repeat split; try done.
      intros _. assert (LiveAt H new_i) as ?; first by apply unregistered_is_alive. unfold LiveAt in *. set_solver.
    - specialize (del_map_consistent_before i). rewrite lookup_insert_ne; last done. unfold LiveAt in *. set_solver.
  }


  (* update pred_map *)
  iMod (ghost_map_insert new_i ∅ with "●pred_multiset") as "[●pred_multiset' ◯pred_new_i]". {
    unfold to_pred_multiset_map.
    destruct pred_map_consistent_before as (pmc1 & pmc2). specialize (pmc1 new_i).
    assert (new_i ∉ dom π) by auto. assert (π !! new_i = None) as π_new_i_none; first by apply not_elem_of_dom.
    rewrite lookup_fmap. rewrite π_new_i_none. done.
  }
  remember (<[ new_i := ∅ ]> π) as π'.

  assert (new_i ∉ dom π) as H_π_new_i. {
    destruct pred_map_consistent_before as (pmc1 & _). auto.
  }

  have pred_map_consistent_after: (pred_map_consistent H' π'). {
    unfold pred_map_consistent. destruct pred_map_consistent_before as (pmc1 & pmc2). split.
    - subst π'. intros. case (decide (j = new_i)) as [-> | NE_new_i]; try done. set_solver.
    - intros ??? Hinterp ?. case (decide (i = new_i)) as [-> | NE_new_i].
      + exfalso. assert (interp H' !! (new_i, o) = None); last congruence. clear H_π_new_i. rewrite HeqH'.
        unfold interp. rewrite fold_left_app. fold (interp H).
        assert (interp H !! (new_i, o) = None) as interp_H_new_i_None; first by apply unregistered_points_to_nowhere.
        clear -interp_H_new_i_None. induction size as [| s']; first done. replace (S s') with (s' + 1); last lia.
        rewrite seq_app fmap_app fold_left_app. simpl. apply lookup_delete_None. right. done.
      + assert (∃ i_s, π !! j = Some i_s ∧ (i, o) ∈ i_s) as [i_s [π_j io_is]]. {
          apply pmc2.
          - subst H'. clear -Hinterp NE_new_i. induction size as [| s'].
            + simpl in *. replace (H ++ []) with H in *; last by rewrite app_nil_r. done.
            + apply IHs'. replace (S s') with (s' + 1) in Hinterp; last lia.
              rewrite seq_app fmap_app app_assoc in Hinterp.
              remember (H ++ ((λ o : nat, link new_i o None) <$> seq 0 s')) as Hs'.
              unfold interp in Hinterp. rewrite fold_left_app in Hinterp. simpl in *. fold (interp Hs') in Hinterp.
              rewrite lookup_delete_ne in Hinterp; last congruence. done.
          - unfold LiveAt in *. subst H'. set_solver.
        }
        exists i_s. subst π'. assert (j ≠ new_i). {
          assert (j ∈ dom π); first by eapply elem_of_dom_2.
          (* new_i ∉ dom π *) congruence.
        }
        rewrite lookup_insert_ne; done.
  }
  assert (to_pred_multiset_map π' = <[new_i:=∅]> (to_pred_multiset_map π)) as <-. {
    subst π'. unfold to_pred_multiset_map. rewrite fmap_insert. set_solver.
  }


  (* construct HistPointedBy *)
  iAssert (HistPointedBy new_i ∅) with "[◯pred_new_i ◯del_new_i]" as "$"; first by exfr.

  (* update succ_hist_map and ●H *)
  (* These have to be done together because the output HistPointsTos contain snapshots of ●H's intermediate steps *)
  iAssert (|==> mono_list_auth_own γh 1 H' ∗
            ghost_map_auth γt 1 (succ_hist_map H') ∗
            ([∗ list] o ∈ seq 0 size, HistPointsToLast new_i o None) ∗
             ⌜ ∀ s, size ≤ s → succ_hist_map H' !! (new_i, s) = None ⌝ (* to put more information in IH*)
          )%I
        with "[●succ_hist ●H]" as ">(●H' & succ_hist' & $ & _)". {
    subst H'. clear -new_i_is_new Enc. iInduction size as [|s' IH].
    - simpl. rewrite app_nil_r. iFrame. iPureIntro. split; try done. intros.
      apply not_elem_of_dom. apply unregistered_has_no_succ_hist. done.
    - iSpecialize ("IH" with "●succ_hist ●H"). iDestruct "IH" as ">(●H & ●shm & hpts & %ns_new)". replace (S s') with (s' + 1); last lia.
      rewrite seq_app fmap_app app_assoc. simpl. rewrite succ_hist_create; last by auto.
      iMod (ghost_map_insert (new_i, s') [None] with "●shm") as "[●shm' ◯succ_newi_s']"; first by auto.
      iFrame. simpl. remember ((H ++ ((λ o : nat, link new_i o None) <$> seq 0 s'))) as H_prev.
      iMod (mono_list_auth_own_update (H_prev ++ [link new_i s' None]) with "●H") as "[●H' ◯H']"; first by eexists.
      iModIntro. iFrame. iSplitL.
      + exfr. rewrite succ_hist_create; last by auto.
        rewrite last_app. simpl. iSplit; try done. rewrite lookup_total_insert. done.
      + iPureIntro. intros. rewrite lookup_insert_ne; last by injection 1; lia. apply ns_new. lia.
  }

  unfold HistAuth. exfr.

  (* prove well-formedness *)

  iPureIntro. unfold well_formed in *. subst H'. clear -well_formed_before.
  remember ((λ o : nat, link new_i o None) <$> seq 0 size) as appended. destruct well_formed_before as (wfp2 & wfp3).
  assert (∀ i, del i ∉ appended) by set_solver.
  assert (∀ i j o, link i o (Some j) ∉ appended) by set_solver.
  repeat split.
  - unfold no_new_link_to_deleted in *. intros i j o a b Hab Ha Hb.
    repeat rewrite lookup_app_Some in Ha Hb.
    naive_solver (eauto using elem_of_list_lookup_2).
  - unfold live_points_to_live, LiveAt in *. intros i o j H_ij H_i.
    assert (interp H !! (i, o) = Some j). {
      subst appended. clear -H_ij. induction size as [| s'].
      - simpl in *. rewrite app_nil_r in H_ij. done.
      - remember (H ++ ((λ o : nat, link new_i o None) <$> seq 0 s')) as Hb. apply IHs'.
        replace (S s') with (s' + 1) in H_ij; last lia. unfold interp in H_ij.
        rewrite seq_app fmap_app app_assoc fold_left_app -HeqHb in H_ij. fold (interp Hb) in H_ij. simpl in *.
        by eapply lookup_delete_Some.
    }
    set_solver.
Qed.


Lemma hist_delete_node H i:
  HistAuth H -∗ HistPointedBy i ∅ ==∗
  HistAuth (H ++ [del i]) ∗ HistDeleted i.
Proof.
  rename i into rj.
  iIntros "HistAuth PointedBy".
  iDestruct "HistAuth" as (??????) "(%Enc & %del_map_consistent_before & %pred_map_consistent_before & %well_formed_before &
    ●H & ●succ_hist & ●pred_multiset & ●del_map)".

  remember (H ++ [del rj]) as H'.

  (* update H' *)
  iMod (mono_list_auth_own_update H' with "●H") as "[●H' _]"; first by eexists.

  (* destruct HistPointdBy *)
  iDestruct "PointedBy" as (????) "(% & ◯i_pointed_by_∅ & ◯i_not_deleted)". encode_agree Enc.
  iMod (ghost_map_elem_persist with "◯i_pointed_by_∅") as "#◯i_pointed_by_∅".

  (* rj was not deleted before. *)
  iAssert (⌜ LiveAt H rj ⌝ )%I with "[◯i_not_deleted ●del_map]"  as "%rj_LiveAt_H". {
    unfold del_map_consistent in *. iDestruct (ghost_map_lookup with "●del_map ◯i_not_deleted") as "%". iPureIntro. naive_solver.
  }

  iAssert (⌜ ¬ ∃ i o, (interp H) !! (i, o) = Some rj ∧ LiveAt H i ⌝)%I as "%rj_has_no_predecessor". {
    iDestruct (ghost_map_lookup with "●pred_multiset ◯i_pointed_by_∅") as"%".
    iPureIntro. intros (i & o & H_irj & H_i).

    specialize (pred_in_pred_multiset _ _ _ _ _ pred_map_consistent_before H_irj H_i) as (pmm & ? & ?).
    assert (pmm = ∅) as -> by naive_solver. (* i ∈ ∅ → False *) set_solver.
  }

  (* update (del_map !! i) to true. *)
  iMod (ghost_map_update true with "●del_map ◯i_not_deleted") as "[●del_map' ◯i_deleted]".
  iMod (ghost_map_elem_persist with "◯i_deleted") as "#◯i_deleted".
  remember ((<[rj:=true]> del_map)) as del_map'.

  assert (del_map_consistent H' del_map'). {
    subst H' del_map'. clear -del_map_consistent_before. unfold del_map_consistent in *.
    intros. specialize (del_map_consistent_before i) as (dmc1& dmc2 & dmc3). repeat split.
    - rewrite fmap_app. set_solver.
    - unfold LiveAt in *. case (decide (i = rj)) as [-> | NE_i_rj].
      + set_solver.
      + rewrite lookup_insert_ne; last done. set_solver.
    - unfold LiveAt. rewrite lookup_insert_Some. set_solver.
  }

  (* construct HistDeleted *)
  iSplitR "◯i_pointed_by_∅ ◯i_deleted"; last by exfr.

  (* pred_map is unaffected *)
  assert (pred_map_consistent H' π). {
    subst H'. clear -pred_map_consistent_before. unfold pred_map_consistent, LiveAt in *.
    rewrite interp_unaffected_by_del. set_solver.
  }

  unfold HistAuth.

  (* succ_map is unaffected *)
  assert (succ_hist_map H' = succ_hist_map H) as ->; first by subst H'; apply succ_hist_unaffected_by_del.

  exfr.

  (* prove well-formedness *)
  iPureIntro. subst H'. clear -well_formed_before rj_LiveAt_H rj_has_no_predecessor.

  destruct well_formed_before as (wf1 & wf2). unfold LiveAt in *. repeat split.
  - unfold no_new_link_to_deleted in *. intros i j o a b Hab Ha Hb.
    case (decide (b < length H)) as [? | ?].
    + case (decide (a < length H)) as [? | ?].
      * repeat rewrite lookup_app_l in Ha Hb; eauto.
      * lia.
    + rewrite lookup_app_r in Hb; try lia. rewrite list_lookup_singleton_Some in Hb. naive_solver.
  - unfold live_points_to_live in *. rewrite interp_unaffected_by_del. unfold LiveAt in *. set_solver.
Qed.


Lemma hist_points_to_link i o j H B:
  HistAuth H -∗
  HistPointsToLast i o None -∗
  HistPointedBy j B ==∗

  HistAuth (H ++ [link i o (Some j)]) ∗
  HistPointsToLast i o (Some j) ∗
  HistPointedBy j (B ⊎ {[+ i +]}).
Proof.
  iIntros "HistAuth PointsTo PointedBy".

  iDestruct (hist_pointedby_is_alive with "HistAuth PointedBy") as "%j_alive".
  iDestruct "HistAuth" as (??????) "(%Enc & %del_map_consistent_before & %pred_map_consistent_before & %well_formed_before &
    ●H & ●succ_hist & ●pred_multiset & ●del_map)".

  remember (H ++ [link i o (Some j)]) as H'.

  (* update H' *)
  iMod (mono_list_auth_own_update H' with "●H") as "[●H' #◯H']"; first by eexists.

  (* update succ_hist_map and PointsTo*)
  iAssert (|==> ghost_map_auth γt 1 (succ_hist_map H') ∗ HistPointsToLast i o (Some j))%I with "[●succ_hist PointsTo]" as ">[●succ_hist' $]". {
    iDestruct "PointsTo" as (?????) "(% & %Hlink_last & ◯Hlink & ◯succ_hist_io)". encode_agree Enc.

    remember (succ_hist_map Hlink !!! (i, o)) as shm_io_old.
    iDestruct (ghost_map_lookup with "●succ_hist ◯succ_hist_io") as "%shm_lookup".
    specialize (succ_hist_update _ _ _ (Some j) _ shm_lookup) as shm_update. rewrite -HeqH' in shm_update.

    iMod (ghost_map_update (shm_io_old ++ [Some j]) with "●succ_hist ◯succ_hist_io") as "[●succ_hist' ◯succ_hist_io]". rewrite -shm_update.
    assert (succ_hist_map H' !!! (i, o) = shm_io_old ++ [Some j]) as <-. { rewrite shm_update. eapply lookup_total_insert. }

    unfold HistPointsToLast. iFrame. exfr. subst H'. rewrite last_app. done.
  }

  (* del_map stays same *)
  assert (del_map_consistent H' del_map). { eapply del_map_unaffected_by_links; set_solver. }

  iDestruct "PointedBy" as (?????) "[◯pred_j ◯del_map_j]". encode_agree Enc.

  (* update pred_map and PointedBy *)

  (* access π !! j *)
  iDestruct (ghost_map_lookup with "●pred_multiset ◯pred_j") as "%pm_lookup".

  unfold to_pred_multiset_map in pm_lookup. rewrite lookup_fmap in pm_lookup.

  destruct (π !! j) as [πj |] eqn: Eqn_πj; last naive_solver. simpl in *. injection pm_lookup as H_B.

  (* do ghost updates *)
  remember (<[ j := πj ⊎ {[+ (i, o) +]} ]> π) as π'.
  iAssert (|==> ghost_map_auth γb 1 (to_pred_multiset_map π') ∗ HistPointedBy j (B ⊎ {[+ i +]}))%I
      with "[●pred_multiset ◯pred_j ◯del_map_j]" as ">[●pred_multiset PointedBy']". {

    iMod (ghost_map_update (B ⊎ {[+ i +]}) with "●pred_multiset ◯pred_j") as "[●pred_multiset' ◯pred_j']".

    assert (<[j:=B ⊎ {[+ i +]}]> (to_pred_multiset_map π) = to_pred_multiset_map π') as ->. {
      subst π'. unfold to_pred_multiset_map in *. rewrite fmap_insert.
      f_equal.

      rewrite gmultiset_elements_disj_union.  rewrite fmap_app.
      rewrite list_to_set_disj_app. rewrite gmultiset_elements_singleton. multiset_solver.
    }

    by exfr.
  }
  assert (pred_map_consistent H' π'). {
    unfold pred_map_consistent in *. destruct pred_map_consistent_before as [pmc1 pmc2]. subst π' H'. split.
    - intros j' H_j'. rewrite dom_insert_lookup in H_j'; last done. set_solver.
    - intros i' o' j' H_i'j' H_i'. unfold LiveAt in *.
      case (decide ((i', o') = (i, o))) as [[= -> ->] | NE_io].
      + rewrite interp_lookup_app_link in H_i'j'. injection H_i'j' as ->.
        rewrite lookup_insert. eexists. split; set_solver.
      + rewrite interp_lookup_app_link_ne in H_i'j'; last done.
        case (decide (j = j')) as [<- | NE_j].
        * rewrite lookup_insert. eexists. split; set_solver.
        * rewrite lookup_insert_ne; last done. set_solver.
  }

  subst B. exfr. iPureIntro.

  (* prove well-formedness*)

  subst H'. clear -well_formed_before j_alive.
  assert (∀ i1 i2, del i1 ∉ [link i2 o (Some j)]) by set_solver.
  destruct well_formed_before as (wf1 & wf2). repeat split.
  - unfold no_new_link_to_deleted in *. intros ? ? ? a b Hab Ha Hb.
    repeat rewrite lookup_app_Some list_lookup_singleton in Ha Hb.
    destruct Ha, Hb, (b - length H); naive_solver (eauto using elem_of_list_lookup_2).
  - unfold live_points_to_live in *. intros i' o' j' H_i'j' Hi'.
    unfold LiveAt in *. case (decide ((i, o) = (i', o'))) as [[= <- <-] | NE_io].
    + rewrite interp_lookup_app_link in H_i'j'. set_solver.
    + rewrite interp_lookup_app_link_ne in H_i'j'; last done. set_solver.
Qed.


Lemma hist_points_to_unlink i o j H B:
  HistAuth H -∗
  HistPointsToLast i o (Some j) -∗
  HistPointedBy j B ==∗

  HistAuth (H ++ [link i o None]) ∗
  HistPointsToLast i o None ∗
  HistPointedBy j (B ∖ {[+ i +]}).
Proof.
  iIntros "HistAuth PointsTo PointedBy".

  iDestruct (PointsTo_reflects_interp with "HistAuth PointsTo") as "%interp_io_j".

  iDestruct "HistAuth" as (??????) "(%Enc & %del_map_consistent_before & %pred_map_consistent_before & %well_formed_before &
    ●H & ●succ_hist & ●pred_multiset & ●del_map)".

  remember (H ++ [link i o None]) as H'.

  (* update H' *)
  iMod (mono_list_auth_own_update H' with "●H") as "[●H' #◯H']"; first by eexists.

  (* update succ_hist_map and PointsTo*)
  (* NOTE: repeated code (almost same as link rule) *)
  iAssert (|==> ghost_map_auth γt 1 (succ_hist_map H') ∗ HistPointsToLast i o None)%I with "[●succ_hist PointsTo]" as ">[●succ_hist' $]". {
    iDestruct "PointsTo" as (?????) "(% & %Hlink_last & ◯Hlink & ◯succ_hist_io)". encode_agree Enc.

    remember (succ_hist_map Hlink !!! (i, o)) as shm_io_old.
    iDestruct (ghost_map_lookup with "●succ_hist ◯succ_hist_io") as "%shm_lookup".
    specialize (succ_hist_update _ _ _ None _ shm_lookup) as shm_update. rewrite -HeqH' in shm_update.

    iMod (ghost_map_update (shm_io_old ++ [None]) with "●succ_hist ◯succ_hist_io") as "[●succ_hist' ◯succ_hist_io]". rewrite -shm_update.
    assert (succ_hist_map H' !!! (i, o) = shm_io_old ++ [None]) as <-. { rewrite shm_update. eapply lookup_total_insert. }

    unfold HistPointsToLast. iFrame. exfr. subst H'. rewrite last_app. done.
  }

  (* del_map stays same *)
  assert (del_map_consistent H' del_map). { eapply del_map_unaffected_by_links; set_solver. }

  (* update pred_map and PointedBy *)
  iAssert (|==> ∃ π',
      ⌜ pred_map_consistent H' π' ⌝ ∗
      ghost_map_auth γb 1 (to_pred_multiset_map π') ∗ HistPointedBy j (B ∖ {[+ i +]}))%I
      with "[●pred_multiset PointedBy]" as ">(%π' & % & ●pred_multiset & PointedBy')". {

    case (decide (LiveAt H i)) as [i_alive | i_not_alive].
    - (* if i is alive, (i, o) is in π by prev_map consistency. We delete that entry. *)

      (* access π !! j *)
      iDestruct "PointedBy" as (?????) "[◯pred_j ◯del_map_j]". encode_agree Enc.
      iDestruct (ghost_map_lookup with "●pred_multiset ◯pred_j") as "%pm_lookup".

      unfold to_pred_multiset_map in pm_lookup. rewrite lookup_fmap in pm_lookup.

      destruct (π !! j) as [πj |] eqn: Eqn_πj; last naive_solver. simpl in *.
      injection pm_lookup. intros Eqn_B.

      iMod (ghost_map_update (B ∖ {[+ i +]}) with "●pred_multiset ◯pred_j") as "[●pred_multiset' ◯pred_j']".

      assert ((i, o) ∈ πj) as io_in_πj. {
        destruct pred_map_consistent_before as (_ & pmc2). naive_solver.
      }

      remember (πj ∖ {[+ (i, o) +]}) as πj'.
      assert (πj = {[+ (i, o) +]} ⊎ πj') as πj_πj'. { subst πj'. by eapply gmultiset_disj_union_difference'. }
      remember (<[ j := πj' ]> π) as π'.

      assert (<[j:=B ∖ {[+ i +]}]> (to_pred_multiset_map π) = to_pred_multiset_map π') as ->. {
        subst π'. unfold to_pred_multiset_map. rewrite fmap_insert. f_equal. subst B πj.
        rewrite gmultiset_elements_disj_union. rewrite fmap_app. rewrite list_to_set_disj_app.
        rewrite gmultiset_elements_singleton. multiset_solver.
      }
      assert (pred_map_consistent H' π'). {
        destruct pred_map_consistent_before as (pmc1 & pmc2). split.
        - intros j' H_j'. subst π' H'.
          assert (j ∈ dom π); first by eapply elem_of_dom_2.
          assert (j' ∈ dom π). { rewrite dom_insert in H_j'. set_solver. }
          set_solver.
        - intros i' o' j' H_i'j' H_i'.
          case (decide ((i, o) = (i', o'))) as [[= <- <-] | NE].
          + subst H'. exfalso.
            rewrite interp_lookup_app_link in H_i'j'. done.
          + subst H' π'. rewrite interp_lookup_app_link_ne in H_i'j'; last done. unfold LiveAt in *.
            assert (∃ i_s, π !! j' = Some i_s ∧ (i', o') ∈ i_s) as [πj'' [interp H_i'o']]. { apply pmc2; set_solver. }
            case (decide (j = j')) as [<- | NE_j].
            * assert (πj'' = πj) as -> by naive_solver. rewrite lookup_insert. eexists. split; try done.
              subst πj'. clear -NE H_i'o'. multiset_solver.
            * rewrite lookup_insert_ne; last done. naive_solver.
      }

      iExists π'. exfr. done.
    - (* if i is not alive, we can delete any (i, o) without breaking the consistency *)
      case (decide (i ∈ B)) as [i_in_B | i_not_in_B].
      +
        iMod (remove_deleted_from_PointedBy with "●pred_multiset PointedBy") as (πj ?) "(%Eqn_πj & %io'_in_πj & ●pred_multiset & PointedBy')"; try done.
        exfr. iPureIntro.

        (* prove pred_map_consistency after the update *)
        {
          destruct pred_map_consistent_before as (pmc1 & pmc2). split.
          - (* NOTE: repeated code *)
            intros j' H_j'. subst H'.
            assert (j ∈ dom π); first by eapply elem_of_dom_2.
            assert (j' ∈ dom π). { rewrite dom_insert in H_j'. set_solver. }
            set_solver.
          - intros i' o' j' H_i'j' H_i'. unfold LiveAt in *.
            assert (i ≠ i') as NE_i by set_solver. subst H'.
            rewrite interp_lookup_app_link_ne in H_i'j'; last naive_solver.

            (* NOTE: repeated code *)
            assert (∃ i_s, π !! j' = Some i_s ∧ (i', o') ∈ i_s) as [πj'' [? H_i'o']]. { apply pmc2; set_solver. }
            case (decide (j = j')) as [<- | NE_j].
            + assert (πj'' = πj) as -> by naive_solver. rewrite lookup_insert. eexists. split; try done.
              clear -NE_i H_i'o'. multiset_solver.
            + rewrite lookup_insert_ne; last done. naive_solver.
        }
      + (* If i ∉ B, we doesn't have to change anything *)
        assert (B ∖ {[+ i +]} = B) as -> by multiset_solver. iExists π.
        assert (pred_map_consistent H' π). {
          destruct pred_map_consistent_before as (pmc1 & pmc2). split; unfold LiveAt in *.
          - set_solver.
          - intros i' o' j' H_i'j' H_i'.
            subst H'. case (decide ((i, o) = (i', o'))) as [[= <- <-] | NE].
            + exfalso. set_solver +i_not_alive H_i'.
            + rewrite interp_lookup_app_link_ne in H_i'j'; last done. apply pmc2; set_solver.
        }

        exfr. done.
  }

  exfr. iPureIntro.

  (* prove well-formedness *)
  (* NOTE: repeated code from hist_points_to_link *)
  subst H'. clear -well_formed_before.
  assert (∀ i1 i2, del i1 ∉ [link i2 o None]) by set_solver.
  destruct well_formed_before as (wf1 & wf2). repeat split.
  - unfold no_new_link_to_deleted in *. intros ? ? ? a b Hab Ha Hb.
    repeat rewrite lookup_app_Some list_lookup_singleton in Ha Hb.
    destruct Ha, Hb, (b - length H); naive_solver (eauto using elem_of_list_lookup_2).
  - unfold live_points_to_live in *. intros i' o' j' H_i'j' Hi'.
    unfold LiveAt in *. case (decide ((i, o) = (i', o'))) as [[= <- <-] | NE_io].
    + rewrite interp_lookup_app_link in H_i'j'. set_solver.
    + rewrite interp_lookup_app_link_ne in H_i'j'; last done. set_solver.
Qed.

Lemma hist_points_to_unlink_simple i o oj H:
  HistAuth H -∗
  HistPointsToLast i o oj ==∗

  HistAuth (H ++ [link i o None]) ∗
  HistPointsToLast i o None.
Proof.
  iIntros "HistAuth PointsTo".
  iDestruct "HistAuth" as (??????) "(%Enc & %del_map_consistent_before & %pred_map_consistent_before & %well_formed_before &
    ●H & ●succ_hist & ●pred_multiset & ●del_map)".

  set H' := H ++ _.

  (* update H' *)
  iMod (mono_list_auth_own_update H' with "●H") as "[●H' #◯H']"; first by eexists.

  (* update succ_hist_map and PointsTo*)
  (* NOTE: repeated code (same as unlink rule) *)
  iAssert (|==> ghost_map_auth γt 1 (succ_hist_map H') ∗ HistPointsToLast i o None)%I with "[●succ_hist PointsTo]" as ">[●succ_hist' $]". {
    iDestruct "PointsTo" as (?????) "(% & %Hlink_last & ◯Hlink & ◯succ_hist_io)". encode_agree Enc.

    remember (succ_hist_map Hlink !!! (i, o)) as shm_io_old.
    iDestruct (ghost_map_lookup with "●succ_hist ◯succ_hist_io") as "%shm_lookup".
    specialize (succ_hist_update _ _ _ None _ shm_lookup) as shm_update. fold H' in shm_update.

    iMod (ghost_map_update (shm_io_old ++ [None]) with "●succ_hist ◯succ_hist_io") as "[●succ_hist' ◯succ_hist_io]". rewrite -shm_update.
    assert (succ_hist_map H' !!! (i, o) = shm_io_old ++ [None]) as <-. { rewrite shm_update. eapply lookup_total_insert. }

    unfold HistPointsToLast. iFrame. exfr. subst H'. rewrite last_app. done.
  }

  (* del_map stays same *)
  assert (del_map_consistent H' del_map). { eapply del_map_unaffected_by_links; set_solver. }

  (* pred_map also stays same *)
  assert (pred_map_consistent H' π). {
    subst H'. destruct pred_map_consistent_before as [pmc1 pmc2]. split.
    - set_solver.
    - unfold LiveAt in *. intros i' o' j' H_i'j' H_i'. apply pmc2.
      + case (decide ((i, o) = (i', o'))) as [[= <- <-] | NE].
        * rewrite interp_lookup_app_link in H_i'j'. done.
        * rewrite interp_lookup_app_link_ne in H_i'j'; done.
      + set_solver.
  }
  exfr. iPureIntro.

  (* prove well-formedness *)
  (* NOTE: repeated code from hist_points_to_unlink *)
  subst H'. clear -well_formed_before.
  assert (∀ i1 i2, del i1 ∉ [link i2 o None]) by set_solver.
  destruct well_formed_before as (wf1 & wf2). repeat split.
  - unfold no_new_link_to_deleted in *. intros ? ? ? a b Hab Ha Hb.
    repeat rewrite lookup_app_Some list_lookup_singleton in Ha Hb.
    destruct Ha, Hb, (b - length H); naive_solver (eauto using elem_of_list_lookup_2).
  - unfold live_points_to_live in *. intros i' o' j' H_i'j' Hi'.
    unfold LiveAt in *. case (decide ((i, o) = (i', o'))) as [[= <- <-] | NE_io].
    + rewrite interp_lookup_app_link in H_i'j'. set_solver.
    + rewrite interp_lookup_app_link_ne in H_i'j'; last done. set_solver.
Qed.


Lemma hist_points_to_update i o j1 H B1 j2 B2:
  HistAuth H -∗
  HistPointsToLast i o (Some j1) -∗
  HistPointedBy j1 B1 -∗
  HistPointedBy j2 B2 ==∗

  HistAuth (H ++ [link i o None; link i o (Some j2)]) ∗
  HistPointsToLast i o (Some j2) ∗
  HistPointedBy j1 (B1 ∖ {[+ i +]}) ∗
  HistPointedBy j2 (B2 ⊎ {[+ i +]}).
Proof.
  iIntros "Auth PointsTo PointedBy_From PointedBy_To".
  iDestruct (hist_points_to_unlink with "Auth PointsTo PointedBy_From") as ">(Auth' & PointsTo' & PointedBy_From')".
  iDestruct (hist_points_to_link with "Auth' PointsTo' PointedBy_To") as ">(Auth'' & PointsTo'' & PointedBy_To')".

  rewrite -app_assoc. simpl.
  exfr. done.
Qed.


Lemma hist_pointedby_remove_deleted H i j B:
  HistAuth H -∗ HistDeleted i -∗ HistPointedBy j B ==∗ HistAuth H ∗ HistPointedBy j (B ∖ {[+ i +]}).
Proof.
  iIntros "HistAuth #Deleted PointedBy".
  iDestruct "HistAuth" as (??????) "(%Enc & %del_map_consistent_before & %pred_map_consistent_before & %well_formed & ●H & ? & ●pred_multiset & ●del_map)".

  iAssert (⌜ ¬ LiveAt H i ⌝)%I as "%i_not_alive". {
    specialize (del_map_consistent_before i) as (_ & dmc2 & _).
    iDestruct "Deleted" as (?????) "(◯i_pred_empty & ◯i_deleted)". encode_agree Enc.
    iDestruct (ghost_map_lookup with "●del_map ◯i_deleted") as "%del_map_lookup". auto.
  }

  case (decide_rel (∈) i B) as [i_in_B | i_not_in_B].
  -
    iMod (remove_deleted_from_PointedBy with "●pred_multiset PointedBy") as (πj o) "(%Eqn_πj & %io'_in_πj & ●pred_multiset & PointedBy')"; try done.

    assert (pred_map_consistent H (<[j:=πj ∖ {[+ (i, o) +]}]> π)). {
      destruct pred_map_consistent_before as (pmc1 & pmc2). split.
      - intros j' H_j'.
        assert (j ∈ dom π); first by eapply elem_of_dom_2.
        assert (j' ∈ dom π). { rewrite dom_insert in H_j'. set_solver. }
        by apply pmc1.
      - intros i' o' j' H_i'j' Hi'.
        assert (∃ i_s, π !! j' = Some i_s ∧ (i', o') ∈ i_s) as [πj' [interp H_i'o']]. { apply pmc2; set_solver. }
        assert (i' ≠ i) as NE_i by naive_solver.
        case (decide (j = j')) as [<- | NE_j].
        + assert (πj' = πj) as -> by congruence. rewrite lookup_insert.
          eexists. split; try done. clear -NE_i H_i'o'. multiset_solver.
        + rewrite lookup_insert_ne; last done. naive_solver.
    }

    iFrame. done.
  - assert (B ∖ {[+ i +]} = B) as -> by multiset_solver. iFrame. done.
Qed.

End ghost.

Section alloc.

Context `{!node_link_historyG Σ}.

Lemma hist_alloc :
  ⊢ |==> ∃ γ, HistAuth γ [].
Proof.
  unfold HistAuth.

  iMod (mono_list_own_alloc []) as (γh) "[●H _]".
  iMod (ghost_map_alloc (succ_hist_map [])) as (γt) "[●succ_hist _]".
  iMod (ghost_map_alloc (to_pred_multiset_map ∅)) as (γb) "[●pred_multiset _]".
  iMod (ghost_map_alloc_empty) as (γd) "●del_map".
  remember (encode (γh, γt, γb, γd)) as γ.

  repeat iExists _. iFrame "∗%". iPureIntro.
  repeat split; unfold no_new_link_to_deleted, live_points_to_live; try set_solver.
Qed.

End alloc.

#[export] Typeclasses Opaque HistAuth HistSnap HistPointsTo HistPointsToLast HistPointedTo HistPointedBy HistDeleted.
