From stdpp Require Export sorting.
From smr.lang Require Export inf_Z.
From smr.lang Require Import lang.
From smr Require Import helpers.
From iris.algebra Require Import gset.

From iris.prelude Require Import options.

Section sorted_list.
Context {A} (R : relation A) `{∀ x y, Decision (R x y)}.
Implicit Types
  (L : list A)
  (k n m z : A)
  (i j : nat).

Lemma sorted_strict_inc `{!Transitive R, !Irreflexive R} i j L n m :
  Sorted R L → L !! i = Some n → L !! j = Some m →  R n m ↔ i < j .
Proof.
  intros Sorted HLi HLj. split; intros LT.
  - apply not_ge => GE.
    destruct (decide (i = j)) as [->|NE].
    { rewrite HLi in HLj. injection HLj as [= ->].
      apply irreflexivity in LT; done. }
    assert (i > j) as GT by lia.
    assert (R m n) as LT'.
    { apply (elem_of_StronglySorted_app R (take (S j) L) (drop (S j) L) m n).
      - rewrite -(take_drop (S j) L) in Sorted. by apply (Sorted_StronglySorted R).
      - apply elem_of_take; eauto.
      - rewrite elem_of_list_lookup. exists (i - (S j)). rewrite lookup_drop -HLi. f_equal. lia.
    }
    assert (R m m) as EQ.
    { transitivity n; done. }
    apply irreflexivity in EQ; done.
  - apply (elem_of_StronglySorted_app R (take (S i) L) (drop (S i) L) n m).
    + rewrite -(take_drop (S i) L) in Sorted. by apply (Sorted_StronglySorted R).
    + apply elem_of_take. eauto.
    + rewrite elem_of_list_lookup. exists (j - (S i)). rewrite lookup_drop -HLj. f_equal. lia.
Qed.

Lemma sorted_none_in_middle `{!Transitive R, !Irreflexive R} idx n m k L :
  L !! idx = Some n →
  L !! (idx + 1) = Some m →
  R n k →
  R k m →
  Sorted R L →
  k ∉ L.
Proof.
  intros Hn Hm Rnk Rkn Sorted [idx' Hk]%elem_of_list_lookup.
  assert (idx' < idx + 1).
  { apply (sorted_strict_inc idx' (idx + 1) L k m); auto. }
  assert(idx < idx').
  { apply (sorted_strict_inc idx idx' L n k); auto. }
  lia.
Qed.

Lemma sorted_nodup `{!Transitive R, !Irreflexive R} L :
  Sorted R L → NoDup L.
Proof.
  induction L as [|z L IH]; intros Sorted%Sorted_StronglySorted; auto.
  { by apply NoDup_nil. }
  replace (z :: L) with ([z] ++ L) in Sorted; [|by simplify_list_eq].
  apply NoDup_cons. split.
  - intros ElemOf.
    apply (elem_of_StronglySorted_app R [z] L z z) in Sorted; [|by apply elem_of_list_singleton|done].
    by apply irreflexivity in Sorted.
  - apply IH.
    by apply StronglySorted_app_inv_r, StronglySorted_Sorted in Sorted.
Qed.

Lemma drop_sorted `{!Transitive R} i L :
  Sorted R L → Sorted R (drop i L).
Proof.
  intros Sorted. rewrite -(take_drop i L) in Sorted.
  apply Sorted_StronglySorted,StronglySorted_app_inv_r in Sorted; [|done].
  by apply StronglySorted_Sorted.
Qed.

Lemma take_sorted `{!Transitive R} i L :
  Sorted R L → Sorted R (take i L).
Proof.
  intros Sorted. rewrite -(take_drop i L) in Sorted.
  apply Sorted_StronglySorted,StronglySorted_app_inv_l in Sorted; [|done].
  by apply StronglySorted_Sorted.
Qed.

Lemma sorted_app L1 L2 :
  Sorted R L1 →
  Sorted R L2 →
  (∀ (z1 z2 : A), L1 !! (length L1 - 1) = Some z1 → L2 !! 0 = Some z2 → R z1 z2) →
  Sorted R (L1 ++ L2).
Proof.
  intros Sorted_L1 Sorted_L2 LT.
  induction L1 as [|z1 L1 IH]; [done|].
  simpl.
  apply Sorted_cons.
  - apply IH.
    + by apply Sorted_inv in Sorted_L1 as [? _].
    + intros z1' z2' Hl1z1' Hl2z2'. apply LT; [|done].
      rewrite lookup_cons_ne_0 /=.
      { rewrite -Hl1z1'. f_equal. lia. }
      apply lookup_lt_Some in Hl1z1'. lia.
  - destruct L1 as [|z1' L1]; last first.
    { constructor. apply Sorted_inv in Sorted_L1 as [_ Rz1z1'].
      by inversion Rz1z1'.
    }
    destruct L2 as [|z2 L2]; constructor.
    by apply LT.
Qed.

Lemma take_drop_sorted `{!Transitive R, !Irreflexive R} i j L :
  i ≤ j → Sorted R L → Sorted R (take i L ++ drop j L).
Proof.
  intros LT LSort.
  destruct (decide (i = j)) as [->|NE]; [by rewrite take_drop|].
  destruct (decide (i ≤ length L)) as [LE|GT]; last first.
  { rewrite firstn_all2; [|lia].
    rewrite skipn_all2; [|lia].
    by rewrite app_nil_r.
  }
  apply sorted_app.
  { by apply take_sorted. }
  { by apply drop_sorted. }
  intros z1 z2 Hz1 Hz2.
  apply (sorted_strict_inc (length (take i L) - 1) j L z1 z2); auto.
  - destruct i.
    { rewrite take_0 in Hz1. simpl in *. inversion Hz1. }
    rewrite lookup_take in Hz1; [done|]. rewrite length_take_le; lia.
  - by rewrite lookup_drop Nat.add_0_r in Hz2.
  - rewrite length_take_le; lia.
Qed.

Lemma delete_sorted `{!Transitive R, !Irreflexive R} i L :
  Sorted R L → Sorted R (delete i L).
Proof. intros. rewrite delete_take_drop. apply (take_drop_sorted i (S i)); auto. Qed.

Definition insert_middle i k L :=
  take i L ++ [k] ++ drop i L.

Lemma insert_middle_sorted `{!Transitive R} i (k : A) L :
  Sorted R L →
  (∀ (x : A), last (take i L) = Some x → R x k) →
  (∀ (x : A), (drop i L) !! 0 = Some x → R k x) →
  Sorted R (insert_middle i k L).
Proof.
  intros Sorted Htake Hdrop. unfold insert_middle. apply sorted_app; [by apply take_sorted|..].
  { constructor.
    { by apply drop_sorted. }
    set (drop_L := drop i L) in *.
    destruct drop_L as [|z' drop_L]; constructor.
    by apply Hdrop.
  }
  intros z1 z2 Htake' [= ->]. apply Htake.
  rewrite last_lookup -Htake'. f_equal. lia.
Qed.

End sorted_list.

Section sorted_list_inf_Z.
Implicit Types
  (L : list inf_Z)
  (k n m z : inf_Z)
  (i j : nat).

  Definition Sorted_inf_Z :=
    (Sorted inf_Z.lt).

  Lemma sorted_inf_Z_nodup L :
    Sorted_inf_Z L → NoDup L.
  Proof. apply (sorted_nodup inf_Z.lt). Qed.

  Lemma sorted_inf_Z_strict_inc i j L n m :
    Sorted_inf_Z L → L !! i = Some n → L !! j = Some m → (n < m)%inf_Z ↔ i < j .
  Proof. apply (sorted_strict_inc inf_Z.lt _ _ L). Qed.

  Lemma sorted_inf_Z_none_in_middle idx n m k L:
    L !! idx = Some n →
    L !! (idx + 1) = Some m →
    (n < k)%inf_Z →
    (k < m)%inf_Z →
    Sorted_inf_Z L →
    k ∉ L.
  Proof. apply (sorted_none_in_middle inf_Z.lt). Qed.

  Lemma delete_inf_Z_sorted i L :
    Sorted_inf_Z L → Sorted_inf_Z (delete i L).
  Proof. apply (delete_sorted inf_Z.lt). Qed.

  Lemma take_drop_inf_Z_sorted i j L :
    i ≤ j → Sorted_inf_Z L → Sorted_inf_Z (take i L ++ drop j L).
  Proof. apply (take_drop_sorted inf_Z.lt). Qed.

  Lemma insert_middle_inf_Z_sorted i k L :
    Sorted_inf_Z L →
    (∀ (x : inf_Z), last (take i L) = Some x → (x < k)%inf_Z) →
    (∀ (x : inf_Z), (drop i L) !! 0 = Some x → (k < x)%inf_Z) →
    Sorted_inf_Z (insert_middle i k L).
  Proof. apply (insert_middle_sorted inf_Z.lt). Qed.
End sorted_list_inf_Z.

Ltac get_first H :=
  do 2 apply (f_equal (fmap fst)) in H;
  rewrite -!list_lookup_fmap in H;
  simpl in H.

Ltac get_snd H :=
  apply (f_equal (fmap fst)) in H;
  apply (f_equal (fmap snd)) in H;
  rewrite -!list_lookup_fmap in H;
  simpl in H.

Ltac get_third H :=
  apply (f_equal (fmap snd)) in H;
  rewrite -!list_lookup_fmap in H;
  simpl in H.

(* Common helpers for abstract state of Harris{-Micheal} list *)
Section harris_abs_state.
(* Generic parameter for identifier. loc for no-recl, (gname, blk) for recl. *)
Context {A : Set}.
Implicit Types
  (L : list (inf_Z * bool * A))
  (k n m z : inf_Z)
  (i j : nat)
  (b : bool)
  (p : A).

Definition prophecy_to_bool (v : list (val * val)) : bool :=
  match v with
  | (LitV (LitLoc {| Loc.tloc_oloc := _; Loc.tloc_tag := n|}), _) :: _ => bool_decide (n ≠ 0)
  | _                                                          => false
  end.

Definition insert_middle_nbl i k b p L :=
  take i L ++ [(k,b,p)] ++ drop i L.

Lemma insert_middle_nbl_insert_middle i k b p L :
  (insert_middle_nbl i k b p L).*1.*1 = insert_middle i k (L.*1.*1).
Proof. by rewrite !fmap_app !fmap_take !fmap_drop. Qed.

Definition get_abs_state L :=
  (filter (λ (kbon : inf_Z * bool * A), ¬ kbon.1.2) L).*1.*1.

Lemma get_abs_state_nil :
  get_abs_state [] = [].
Proof. unfold get_abs_state. by rewrite filter_nil. Qed.

Lemma get_abs_state_app L1 L2 :
  get_abs_state (L1 ++ L2) = get_abs_state L1 ++ get_abs_state L2.
Proof. unfold get_abs_state. by rewrite !filter_app !fmap_app. Qed.

Lemma get_abs_state_singleton k b p L :
  get_abs_state [(k,b,p)] = if b then [] else [k].
Proof. unfold get_abs_state. by destruct b. Qed.

Lemma get_abs_state_cons k b p L :
  get_abs_state ((k,b,p)::L) = if b then get_abs_state L else k :: get_abs_state L.
Proof. unfold get_abs_state. rewrite !filter_cons. by destruct b. Qed.

Lemma get_abs_state_snoc k b p L :
  get_abs_state (L ++ [(k,b,p)]) = if b then get_abs_state L else get_abs_state L ++ [k].
Proof. unfold get_abs_state. rewrite !filter_app. destruct b; simpl; by simplify_list_eq. Qed.

Lemma sorted_inf_Z_get_abs_state_sorted L :
  Sorted_inf_Z (L.*1.*1) →
  Sorted_inf_Z (get_abs_state L).
Proof.
  induction L as [|[[z b] l] L IH]; [done|]. rewrite get_abs_state_cons !fmap_cons /=.
  intros [Sorted z_LT]%(Sorted_StronglySorted inf_Z.lt)%StronglySorted_inv.
  destruct b. { by apply IH,StronglySorted_Sorted. }
  constructor. { by apply IH,StronglySorted_Sorted. }
  set (L' := get_abs_state L) in *.
  destruct L' as [|z' tlL] eqn:EQN; constructor.
  assert (z' ∈ L') as ElemOf.
  { rewrite EQN. apply elem_of_cons. by left. }
  subst L'.
  do 2 apply elem_of_list_fmap_2 in ElemOf as [[? ?] [[= <-] ElemOf]].
  apply elem_of_list_filter in ElemOf as [_ ElemOf].
  do 2 apply (elem_of_list_fmap_1 fst) in ElemOf. simpl in *.
  rewrite List.Forall_forall in z_LT.
  by apply z_LT, elem_of_list_In.
Qed.

Lemma next_not_tail_is_Some idx L k b p (p_next : option A) :
  (∃ t : A, L !! (length L - 1) = Some (∞ᵢ, false, t)) →
  L !! idx = Some (k, b, p) →
  L.*2 !! (idx + 1)%nat = p_next →
  (b = true ∨ (∃ (k' : Z), k = FinInt k') ∨ (∃ (k' : Z), (k < FinInt k')%inf_Z)) →
  is_Some p_next.
Proof.
  intros [t Ht] Hp Hp_next Cond.
  destruct p_next as [p_next|]; [done|].
  rewrite list_lookup_fmap fmap_None in Hp_next.
  apply lookup_ge_None_1 in Hp_next as GE.
  apply lookup_lt_Some in Hp as LT.
  replace idx with (length L - 1) in Hp by lia.
  rewrite Hp in Ht. injection Ht as [= -> -> ->].
  destruct Cond as [?|[?|[? H]]]; [naive_solver..|].
  inversion H.
Qed.

Lemma next_not_tail_is_Some' idx L k b p :
  (∃ t : A, L !! (length L - 1) = Some (∞ᵢ, false, t)) →
  L !! idx = Some (k, b, p) →
  (b = true ∨ (∃ (k' : Z), k = FinInt k') ∨ (∃ (k' : Z), (k < FinInt k')%inf_Z)) →
  is_Some (L.*2 !! (idx + 1)%nat).
Proof. intros. apply (next_not_tail_is_Some idx L k b p (L.*2 !! (idx + 1)%nat)); auto. Qed.


Definition lookup_post (L : list inf_Z) (b : bool) (k : Z) :=
  if b then FinInt k ∈ L else FinInt k ∉ L.

Definition insert_succ_post (L L' : list inf_Z) (k : Z) :=
  FinInt k ∉ L ∧ ∃ idx, L' = insert_middle idx (FinInt k) L.

Definition insert_fail_post (L L' : list inf_Z) (k : Z) :=
  (FinInt k) ∈ L ∧ L' = L.

Definition delete_succ_post (L L' : list inf_Z) (k : Z) :=
  ∃ idx : nat, L !! idx = Some (FinInt k) ∧ L' = delete idx L.

Definition delete_fail_post (L L' : list inf_Z) (k : Z) :=
  (FinInt k) ∉ L ∧ L' = L.

Lemma prove_lookup_post (idx : nat) (p_k c_k : inf_Z) (L : list inf_Z) b (k : Z) :
  L !! idx = Some p_k →
  L !! S idx = Some c_k →
  (p_k < FinInt k)%inf_Z →
  (if b then c_k = (FinInt k) else (FinInt k < c_k)%inf_Z) →
  Sorted_inf_Z L →
  lookup_post L b k.
Proof.
  unfold lookup_post. intros Hp Hc Hp_k Hc_k LSort.
  destruct b.
  - (* key found *)
    subst c_k. rewrite elem_of_list_lookup. eauto.
  - (* key not found *)
    apply (sorted_inf_Z_none_in_middle idx p_k c_k (FinInt k) L); auto.
    by rewrite Nat.add_1_r.
Qed.

Lemma prove_insert_succ_post (p_k c_k : inf_Z) (p c n : A) (idx : nat) (b : bool) L (k : Z)
                             (L' := insert_middle_nbl (S idx) (FinInt k) false n L) :
  L !! idx = Some (p_k, false, p) →
  L !! (idx + 1) = Some (c_k, b, c) →
  (p_k < FinInt k)%inf_Z →
  (FinInt k < c_k)%inf_Z →
  Sorted_inf_Z L.*1.*1 →
  insert_succ_post (get_abs_state L) (get_abs_state L') k.
Proof.
  intros HLp HLc Hp_k Hc_k HL. split.
  - (* k must be a element of L. But L is sorted, contradiction *)
    intros [? H_fil_L]%elem_of_list_lookup.
    do 2 (apply list_lookup_fmap_Some in H_fil_L as [[? ?] [H_fil_L [= <-]]]).
    apply elem_of_list_lookup_2,elem_of_list_filter in H_fil_L as [? [idx' Hidx']%elem_of_list_lookup].
    get_first Hidx'. get_first HLp. get_first HLc.
    apply (sorted_inf_Z_none_in_middle idx p_k c_k (FinInt k) L.*1.*1); auto.
    rewrite elem_of_list_lookup. eauto.
  - (* exists (`idx` of `p_k` in `get_abs_state L`) + 1. *)
    set (idx' := length (get_abs_state (take idx L))).
    exists (S idx').
    rewrite -(take_drop_middle L (idx + 1) (c_k,b,c)); [|done].
    rewrite Nat.add_1_r (take_S_r _ _ (p_k,false,p)); [|done].
    rewrite !get_abs_state_app /=.
    unfold insert_middle.
    repeat f_equal.
    + rewrite (take_S_r _ _ (p_k,false,p)); [|done].
      rewrite (take_S_r _ idx' p_k); last first.
      { subst idx'. simplify_list_eq. rewrite lookup_app_r; [|lia]. by rewrite Nat.sub_diag. }
      rewrite take_app3_length'; last by done.
      by rewrite get_abs_state_app.
    + rewrite drop_app_length'; last by rewrite length_app /= Nat.add_1_r.
      repeat f_equal. rewrite (drop_S L (c_k,b,c)); [done|].
      by rewrite -Nat.add_1_r.
Qed.

Lemma prove_insert_fail_post idx c_k (L : list inf_Z) (k : Z) :
  c_k = FinInt k →
  L !! idx = Some c_k →
  insert_fail_post L L k.
Proof. split; [|done]. subst c_k. rewrite elem_of_list_lookup. eauto. Qed.

Lemma prove_delete_succ_post (c : A) idx L (k : Z) (L' := <[idx:=(FinInt k, true, c)]> L) :
  L !! idx = Some (FinInt k, false, c) →
  delete_succ_post (get_abs_state L) (get_abs_state L') k.
Proof.
  intros HL2_curr.
  set (idx' := length (get_abs_state (take idx L))).
  exists idx'. split.
  - rewrite -(take_drop (S idx) L).
    rewrite get_abs_state_app lookup_app_l (take_S_r _ _(FinInt k, false, c)); try done; last first.
    { rewrite get_abs_state_app length_app /=. lia. }
    subst idx'.
    by rewrite get_abs_state_app snoc_lookup.
  - rewrite -(take_drop (S idx) L). subst L'.
    assert (idx < length L) as LT.
    { rewrite -lookup_lt_is_Some. eauto. }
    rewrite get_abs_state_app delete_take_drop insert_take_drop; [|done].
    rewrite (take_S_r L idx (FinInt k, false, c)); [|done].
    rewrite !get_abs_state_app. simplify_list_eq.
    repeat f_equal.
    rewrite cons_middle assoc drop_app_length'; [|by rewrite length_app /=; lia].
    by rewrite get_abs_state_cons.
Qed.

Lemma prove_delete_fail_post idx (p_k c_k : inf_Z) (L : list inf_Z) (k : Z) :
  L !! idx = Some p_k →
  L !! S idx = Some c_k →
  (p_k < FinInt k)%inf_Z →
  (FinInt k < c_k)%inf_Z →
  Sorted_inf_Z L →
  delete_fail_post L L k.
Proof.
  intros Hp Hc Hp_k Hc_k. split; [|done].
  apply (sorted_inf_Z_none_in_middle idx p_k c_k (FinInt k) L); auto.
  by rewrite Nat.add_1_r.
Qed.

Definition harris_list_into_set (L : list inf_Z) : gset Z :=
  list_to_set (omap (λ k_inf : inf_Z, if k_inf is (FinInt k) then Some k else None) L).

Lemma harris_list_into_set_app (L1 L2 : list inf_Z) :
  harris_list_into_set (L1 ++ L2) = harris_list_into_set L1 ∪ harris_list_into_set L2.
Proof. rewrite /insert_middle /harris_list_into_set !omap_app /= !list_to_set_app_L //. Qed.

Lemma harris_list_into_set_cons k_inf (L : list inf_Z) :
  harris_list_into_set (k_inf :: L) = if k_inf is (FinInt k) then {[k]} ∪ harris_list_into_set L else harris_list_into_set L.
Proof.
  rewrite /insert_middle /harris_list_into_set /=.
  destruct k_inf; set_solver.
Qed.

Lemma harris_list_into_set_singleton k_inf :
  harris_list_into_set [k_inf] = if k_inf is (FinInt k) then {[k]} else ∅.
Proof. destruct k_inf; set_solver. Qed.


Lemma lookup_list_post_to_set_post (L : list inf_Z) b (k : Z) :
  lookup_post L b k →
  b = bool_decide (k ∈ harris_list_into_set L).
Proof.
  intros Post.
  rewrite comm.
  destruct b; rewrite /lookup_post /= in Post.
  - apply bool_decide_eq_true,elem_of_list_to_set, elem_of_list_omap.
    eexists. split; [exact Post|]; done.
  - apply bool_decide_eq_false,not_elem_of_list_to_set.
    intros [[|k'|] [? [= <-]]]%elem_of_list_omap.
    naive_solver.
Qed.

Lemma insert_list_post_to_set_post b (L L' : list inf_Z) (k : Z) (S := harris_list_into_set L) :
  (if b then
    insert_succ_post L L' k
  else
    insert_fail_post L L' k) →
  if b then
    k ∉ S ∧ harris_list_into_set L' = {[k]} ∪ S
  else
    k ∈ S ∧ harris_list_into_set L' = S.
Proof.
  intros Post. destruct b; subst S.
  - destruct Post as [NotIn [idx ->]]. split.
    + intros [[| |] [? [= ->]]]%elem_of_list_to_set%elem_of_list_omap.
      naive_solver.
    + rewrite -{2}(take_drop idx L).
      rewrite /insert_middle !harris_list_into_set_app /=.
      set_solver.
  - destruct Post as [In ->]. split.
    + apply elem_of_list_to_set,elem_of_list_omap.
      exists (FinInt k). done.
    + done.
Qed.

Lemma delete_list_post_to_set_post b (L L' : list inf_Z) (k : Z) (S := harris_list_into_set L) :
  (if b then
    delete_succ_post L L' k
  else
    delete_fail_post L L' k) →
  Sorted_inf_Z L →
  if b then
    k ∈ S ∧ harris_list_into_set L' = S ∖ {[k]}
  else
    k ∉ S ∧ harris_list_into_set L' = S.
Proof.
  intros Post SortL. destruct b; subst S.
  - destruct Post as [idx [Hidx ->]]. split.
    + apply elem_of_list_to_set,elem_of_list_omap.
      exists (FinInt k). split; [|done].
      rewrite elem_of_list_lookup. eauto.
    + assert (k ∉ harris_list_into_set (delete idx L)) as NotIn.
      { intros [[|k'|] [[idx' Hidx']%elem_of_list_lookup [= ->]]]%elem_of_list_to_set%elem_of_list_omap.
        apply sorted_inf_Z_nodup in SortL as NoDupL.
        rewrite NoDup_alt in NoDupL.
        destruct (decide (idx' < idx)) as [LT|GE%not_lt].
        - rewrite lookup_delete_lt in Hidx'; [|lia].
          specialize (NoDupL idx idx' (FinInt k) ltac:(done) ltac:(done)).
          lia.
        - rewrite lookup_delete_ge in Hidx'; [|lia].
          specialize (NoDupL idx (S idx') (FinInt k) ltac:(done) ltac:(done)).
          lia.
      }
      rewrite delete_take_drop harris_list_into_set_app in NotIn.
      rewrite -{2}(take_drop_middle L idx (FinInt k)); [|done].
      rewrite delete_take_drop.
      rewrite !harris_list_into_set_app harris_list_into_set_cons.
      set_solver.
  - destruct Post as [NotIn ->]. split.
    + intros [[| |] [? [= ->]]]%elem_of_list_to_set%elem_of_list_omap.
      naive_solver.
    + done.
Qed.

End harris_abs_state.
