From stdpp Require Import countable list.
From iris.algebra Require Import coPset.
From iris.algebra Require Import gmap.
From iris.prelude Require Import options.

Ltac encode_agree Hγ :=
  match type of Hγ with
  | ?γ = ?e =>
      match goal with
      | H1 : ?γ = ?e, H2 : ?γ = _ |- _ =>
          rewrite H1 in H2; apply (inj encode) in H2;
          first [ injection H2 as [= <- <- <- <- <- <- <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <- <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <-]
                | injection H2 as [= <- <- <- <-]
                | injection H2 as [= <- <- <-]
                | injection H2 as [= <- <-] ]
      end
  end.

Section nats.
  Lemma neq_symm (n m : nat) : n ≠ m ↔ m ≠ n.
  Proof. lia. Qed.

  Lemma rem_mod_eq (x y : nat) : (0 < y) → (x `rem` y)%Z = x `mod` y.
  Proof.
    intros Hpos. rewrite Z.rem_mod_nonneg; [rewrite Nat2Z.inj_mod| |]; lia.
  Qed.

  Lemma lt_mult (n a b : nat) : n*a < n*b → a < b.
  Proof. induction n; lia. Qed.

  Lemma close_mod_neq a b n :
    a < b < a+n → a `mod` n ≠ b `mod` n.
  Proof.
    intros H Hmod. assert (n ≠ 0) by lia.
    assert (Ha := PeanoNat.Nat.div_mod a n).
    assert (Hb := PeanoNat.Nat.div_mod b n).
    rewrite Ha in H; auto. rewrite Hb in H; auto.
    rewrite Hmod in H.
    assert (n*a`div`n < n*b`div`n < n*a`div`n + n) as H' by lia.
    replace (n*a`div`n + n) with (n*(a`div`n + 1)) in H' by lia.
    assert (a`div`n < b`div`n < a`div`n + 1); try lia.
    destruct H' as [H1 H2].
    apply lt_mult in H1; auto. apply lt_mult in H2; auto.
  Qed.
End nats.

Section list.
Local Open Scope nat.

Context {A B : Type} (f : A → B).
Implicit Types a : A.
Implicit Types b : B.
Implicit Types l : list A.

(* fmap *)

Lemma lookup_fmap_lt_Some l i b : f <$> l !! i = Some b → i < length l.
Proof. revert i. induction l; intros [|?] ?; naive_solver auto with arith. Qed.

(* prefix *)

Lemma prefix_lookup_fmap l1 l2 i b :
  f <$> l1 !! i = Some b → l1 `prefix_of` l2 → f <$> l2 !! i = Some b.
Proof. intros ? [k ->]. rewrite lookup_app_l; eauto using lookup_fmap_lt_Some. Qed.

Lemma prefix_of_reverse_cons l x :
  reverse l `prefix_of` reverse (x::l).
Proof. by apply suffix_prefix_reverse, suffix_cons_r. Qed.

Lemma prefix_cut l1 l2 :
  l1 `prefix_of` l2 ↔ l2 = l1 ++ (drop (length l1) l2).
Proof.
  split; intros PF.
  - destruct PF as [? ->]. f_equal. by rewrite drop_app_length.
  - by exists (drop (length l1) l2).
Qed.

Lemma prefix_app_cut l1 l2 :
  l1 `prefix_of` l1 ++ l2.
Proof. by exists l2. Qed.

Lemma prefix_singleton x l :
  [x] `prefix_of` l ↔ l !! 0 = Some x.
Proof.
  rewrite prefix_cut. split; intros PF.
  - by rewrite PF lookup_app.
  - destruct l; [discriminate PF|].
    rewrite lookup_cons in PF. by injection PF as [= <-].
Qed.

Lemma prefix_forall l1 l2 :
  l1 `prefix_of` l2 ↔ ∀ i, (i < length l1 → l1 !! i = l2 !! i).
Proof.
  split.
  - intros PF i [x Hx]%lookup_lt_is_Some_2. rewrite Hx. symmetry. apply (prefix_lookup_Some l1 l2); done.
  - intros lookup. rewrite prefix_cut. apply list_eq. intro i.
    destruct (decide (i < length l1)) as [LT|GE].
    + specialize (lookup i LT). rewrite lookup_app_l; done.
    + rewrite lookup_app_r; [|lia]. rewrite lookup_drop.
      f_equal. lia.
Qed.

Lemma prefix_length_eq l1 l2 :
  length l1 = length l2 → l1 `prefix_of` l2 → l1 = l2.
Proof.
  intros LenEq [l3 ->]. assert (l3 = []) as ->; [|by rewrite app_nil_r].
  rewrite app_length in LenEq. rewrite -length_zero_iff_nil. lia.
Qed.

Lemma prefix_app_same_length l1 l1' l2 l2' :
  length l1' = length l2' →
  l1 ++ l1' `prefix_of` l2 ++ l2' → l1 `prefix_of` l2.
Proof.
  intros Hlen Hpref.
  apply prefix_length in Hpref as Hlen'. rewrite !app_length in Hlen'.
  rewrite prefix_forall in Hpref. rewrite prefix_forall. intros i LEi.
  assert (i < length (l1 ++ l1')) as LEi_app. { rewrite app_length. lia. }
  specialize (Hpref i LEi_app).
  rewrite !lookup_app_l in Hpref; [done|lia..].
Qed.

(* head & last *)

Lemma head_drop i l :
  head (drop i l) = l !! i.
Proof.
  revert i; induction l; intros.
  - by rewrite drop_nil.
  - destruct i; simpl; auto.
Qed.

Lemma take_last i l :
  is_Some (l !! i) → last (take (S i) l) = l !! i.
Proof.
  intros [x H]. rewrite (take_S_r l i x); auto.
  by rewrite last_app.
Qed.

(* reverse *)

Lemma reverse_nil_inv l :
  reverse l = [] → l = [].
Proof. intros RevNil. apply (inj reverse). done. Qed.

Lemma rev_des l :
  l = [] ∨ ∃ x l', l = l' ++ [x].
Proof. destruct l using rev_ind; [left|right]; eauto. Qed.

Lemma reverse_rev l :
  reverse l = rev l.
Proof. by rewrite rev_alt. Qed.

Lemma NoDup_reverse l :
  NoDup l ↔ NoDup (reverse l).
Proof.
  assert (∀ l', NoDup l' → NoDup (reverse l')) as NoDupRev.
  { intros. apply NoDup_ListNoDup. rewrite reverse_rev.
    by apply NoDup_rev, NoDup_ListNoDup. }
  split; auto. intros Hl%NoDupRev.
  by rewrite reverse_involutive in Hl.
Qed.

Lemma notin_reverse l x :
  x ∉ l → x ∉ reverse l.
Proof. intros NotIn In. by rewrite elem_of_reverse in In. Qed.

(* snoc *)

Lemma snoc_length x l :
  length (l ++ [x]) = S (length l).
Proof. rewrite app_length; simpl. lia. Qed.

Lemma snoc_lookup x l :
  (l ++ [x]) !! length l = Some x.
Proof.
  rewrite lookup_app_r; last lia.
  replace (length l - length l) with 0 by lia. auto.
Qed.

Lemma snoc_lookup_inv x l :
  l !! (length l - 1) = Some x →
  ∃ l', l = l' ++ [x].
Proof.
  intros Lookup. destruct l as [|h l _] using rev_ind.
  { discriminate Lookup. }
  rewrite snoc_length in Lookup.
  replace (S (length l) - 1) with (length l) in Lookup by lia.
  rewrite snoc_lookup in Lookup. injection Lookup as [= <-]. eauto.
Qed.

Lemma NoDup_snoc x l :
  (NoDup l ∧ x ∉ l) ↔ NoDup (l ++ [x]).
Proof.
  split; intro NODUP.
  - apply NoDup_reverse. rewrite reverse_snoc.
    destruct NODUP as [NODUP NotIn]. apply NoDup_reverse in NODUP. constructor; auto.
    by apply notin_reverse.
  - apply NoDup_app in NODUP as [NODUP [HElemOf_l _]]. split; auto.
    intro ElemOf. apply HElemOf_l in ElemOf. by apply ElemOf, elem_of_list_singleton.
Qed.

Lemma elem_of_snoc l x y : x ∈ l ++ [y] ↔ x = y ∨ x ∈ l.
Proof.
  by rewrite -elem_of_reverse reverse_snoc
    elem_of_cons elem_of_reverse.
Qed.

Lemma not_elem_of_snoc l x y : x ∉ l ++ [y] ↔ x ≠ y ∧ x ∉ l.
Proof.
  rewrite -elem_of_reverse reverse_snoc
     elem_of_cons elem_of_reverse.
  split.
  - intro NotElem. split; intro; destruct NotElem; [by left|by right].
  - by intros [NE NotElem] [->|Elem].
Qed.

Lemma lookup_snoc_ne l x y i :
  x ≠ y → (l ++ [y]) !! i = Some x → l !! i = Some x.
Proof.
  intros NE ElemOf.
  destruct (decide (i = length l)) as [->|NE_l].
  { rewrite snoc_lookup in ElemOf. inversion ElemOf. congruence. }
  assert (i < length l) as LE.
  { apply lookup_lt_Some in ElemOf. rewrite app_length in ElemOf.
    simpl in ElemOf. lia. }
  rewrite lookup_app_l in ElemOf; done.
Qed.

(* seq *)

Lemma seq_nil_inv n :
  seq 0 n = [] → n = 0.
Proof.
  intros Hn_nil%(f_equal length).
  by rewrite seq_length in Hn_nil.
Qed.

(* alter *)

Lemma list_alter_insert g i l x :
  l !! i = Some x →
  alter g i l = <[i:= g x]> l.
Proof.
  revert l x. induction i; intros.
  - destruct l; auto; simpl. by injection H as [= <-].
  - destruct l; auto; simpl. rewrite -IHi; auto.
Qed.

Lemma take_snoc i l :
  i < length l →
  ∃ x, take (i + 1) l = take i l ++ [x].
Proof.
  intro LE. apply lookup_lt_is_Some_2 in LE as Some. destruct Some as [x Hi].
  exists x. apply list_eq.
  intro i'. destruct (decide (i' = i)) as [->|NE].
  - rewrite lookup_take; [|lia]. rewrite Hi.
    assert (i = length (take i l)) as Len.
    { rewrite length_take_le; lia. }
    rewrite {1}Len snoc_lookup. done.
  - destruct (decide (i' < i)) as [Lt|].
    + rewrite lookup_take; last lia.
      rewrite lookup_app_l; last first.
      { rewrite length_take_le; lia. }
      by rewrite lookup_take; last lia.
    + assert (i' > i) by lia.
      rewrite lookup_take_ge; last lia.
      rewrite lookup_ge_None_2; first done.
      rewrite app_length Nat.add_1_r length_take_le; lia.
Qed.

Lemma take_prefix_le i j l :
  i ≤ j →
  take i l `prefix_of` take j l.
Proof.
  revert i j. induction l as [|x l IHl]; intros.
  - by rewrite !take_nil.
  - destruct i,j; simpl.
    all: try apply prefix_nil; try lia.
    apply prefix_cons, IHl. lia.
Qed.

Lemma take_prefix i l :
  take i l `prefix_of` l.
Proof. rewrite -{2}(take_ge l (length l `max` i)); [|lia]. apply take_prefix_le. lia. Qed.

Lemma take_app_prefix i l1 l2 :
  i ≤ length l1 →
  take i (l1 ++ l2) `prefix_of` l1.
Proof. intros. rewrite take_app_le; auto. apply take_prefix. Qed.

Lemma take_cons' x i l :
  0 < i →
  take i (x :: l) = x :: take (i - 1) l.
Proof.
  intros LT. assert (∃ j : nat, i = S j) as [j ->]. { exists (i - 1). lia. }
  rewrite firstn_cons. repeat f_equal. lia.
Qed.

End list.

(* TODO: upstream *)
Section top_lemmas.
  Context `{TopSet A C}.
  Implicit Types X : C.

  Global Instance intersection_top_l : LeftId (≡@{C}) ⊤ (∩).
  Proof using All. intros ?. set_solver. Qed.
  Global Instance intersection_top_r : RightId (≡@{C}) ⊤ (∩).
  Proof using All. intros ?. set_solver. Qed.

  Global Instance union_top_l : LeftAbsorb (≡@{C}) ⊤ (∪).
  Proof using All. intros ?. set_solver. Qed.
  Global Instance union_top_r : RightAbsorb (≡@{C}) ⊤ (∪).
  Proof using All. intros ?. set_solver. Qed.

  Lemma top_disjoint_empty X :
    ⊤ ## X → X ≡ ∅.
  Proof using All. intros ?. set_solver. Qed.

  Section leibniz.
    Context `{!LeibnizEquiv C}.

    Global Instance intersection_top_l_L : LeftId (=@{C}) ⊤ (∩).
    Proof using All. intros ?. unfold_leibniz. apply (left_id _ _). Qed.
    Global Instance intersection_top_r_L : RightId (=@{C}) ⊤ (∩).
    Proof using All. intros ?. unfold_leibniz. apply (right_id _ _). Qed.

    Global Instance union_top_l_L : LeftAbsorb (=@{C}) ⊤ (∪).
    Proof using All. intros ?. unfold_leibniz. apply (left_absorb _ _). Qed.
    Global Instance union_top_r_L : RightAbsorb (=@{C}) ⊤ (∪).
    Proof using All. intros ?. unfold_leibniz. apply (right_absorb _ _). Qed.

    Lemma top_disjoint_empty_L X :
      ⊤ ## X → X = ∅.
    Proof using All. unfold_leibniz. by apply top_disjoint_empty. Qed.
  End leibniz.

End top_lemmas.

Section gset.

Lemma set_map_difference {A B C D}
    `{Set_ B D, FinSet A C}
    (f : A → B) `{!Inj (=) (=) f} (X Y : C) :
  set_map (D:=D) f (X ∖ Y) ≡ set_map (D:=D) f X ∖ set_map (D:=D) f Y.
Proof.
  split; intro ElemOf.
  - apply elem_of_map in ElemOf as [y [-> [ElemOf NotElemOf]%elem_of_difference]].
    rewrite elem_of_difference; split.
    + apply elem_of_map. eauto.
    + by intros [? [<-%(inj _) FElemOf]]%elem_of_map.
  - apply elem_of_difference in ElemOf as [[y [-> ElemOf]]%elem_of_map NotElemOf].
    rewrite elem_of_map. exists y; split; auto.
    rewrite elem_of_difference; split; auto.
    intro ElemOf'. apply NotElemOf. rewrite elem_of_map; eauto.
  Qed.

Lemma set_map_difference_L {A B C D}
    `{Set_ B D, FinSet A C, !LeibnizEquiv D}
    (f : A → B) `{!Inj (=) (=) f}  (X Y : C) :
  set_map (D:=D) f (X ∖ Y) = set_map (D:=D) f X ∖ set_map (D:=D) f Y.
Proof. unfold_leibniz. by apply set_map_difference. Qed.

Lemma set_map_empty_iff {A B C D}
  `{SemiSet B D, FinSet A C}
    (f : A → B) (X : C) :
  set_map (D:=D) f X ≡ ∅ ↔ X ≡ ∅.
Proof.
  split.
  - rewrite !elem_of_equiv_empty.
    intros EqMap x In.
    apply (EqMap (f x)), elem_of_map_2, In.
  - intros ->. by rewrite set_map_empty.
Qed.

Lemma set_map_empty_iff_L {A B C D}
  `{SemiSet B D, FinSet A C, !LeibnizEquiv D, !LeibnizEquiv C}
    (f : A → B) (X : C) :
  set_map (D:=D) f X = ∅ ↔ X = ∅.
Proof. unfold_leibniz. by apply set_map_empty_iff. Qed.

Lemma subset_of_singleton x (X : gset nat) :
  X ⊆ {[x]} → X = ∅ ∨ X = {[x]}.
Proof.
  destruct (decide (X = ∅)) as [HX|HX]; [auto|].
  set_unfold. intros. right. intros; split; set_solver.
Qed.

Lemma gset_union_difference_L' (X Y : gset nat) :
  X ⊆ Y → Y = (Y ∖ X) ∪ X.
Proof. intros. rewrite (union_difference_L X Y); set_solver. Qed.

Lemma difference_diag `{Countable A} (X Y Z : gset A) :
  X ⊆ Z → Y ⊆ Z →
  (Z ∖ X) ∖ (Z ∖ Y) = Y ∖ X.
Proof. rewrite difference_difference_r_L. set_solver. Qed.

Lemma difference_diag_single `{Countable A} (Y Z : gset A) :
  Y ⊆ Z →
  Z ∖ (Z ∖ Y) = Y.
Proof. rewrite difference_difference_r_L. set_solver. Qed.

Lemma union_differnce_subst_difference_union `{Countable A} (X Y Z : gset A) :
  (X ∪ Y) ∖ Z ⊆ (X ∖ Z) ∪ (Y ∖ X).
Proof.
  set_unfold. intros i [[InX | InY] NotInZ]; [auto|].
  destruct (decide (i ∈ X)); auto.
Qed.

End gset.

Lemma difference_not_in_singletion `{Set_ A B} (x : A) (X : B) :
  x ∉ X → X ≡ X ∖ {[x]}.
Proof. set_solver. Qed.

Lemma difference_not_in_singletion_L `{Set_ A B, !LeibnizEquiv B} (x : A) (X : B) :
  x ∉ X → X = X ∖ {[x]}.
Proof. set_solver. Qed.

Lemma gset_to_coPset_empty :
  gset_to_coPset ∅ = ∅.
Proof. unfold_leibniz. intros ?. setoid_rewrite elem_of_gset_to_coPset. done. Qed.

Global Instance injective_gset_to_coPset :
  Inj (=) (=) gset_to_coPset.
Proof. intros ??. set_unfold. setoid_rewrite elem_of_gset_to_coPset. done. Qed.

Section gmap.

Lemma top_difference_dom_union_not_in_singleton {A} k (m: gmap positive A):
  m !! k = None →
  ⊤ ∖ ({[k]} ∪ (gset_to_coPset (dom m))) ∪ {[k]} = ⊤ ∖ gset_to_coPset (dom m).
Proof.
  intros Hk.
  rewrite comm_L singleton_union_difference_L right_absorb_L.
  rewrite difference_union_distr_l_L difference_diag_L left_id_L.
  f_equal.
  rewrite -difference_not_in_singletion_L //.
  rewrite elem_of_gset_to_coPset elem_of_dom Hk //.
Qed.

Definition range_list `{Countable K} {A: Type} (m: gmap K A) : list A :=
  snd <$> map_to_list m.

Lemma range_list_correct `{Countable K} {A: Type} (m: gmap K A) :
  ∀ x : A, x ∈ range_list m ↔ ∃ k, m !! k = Some x.
Proof.
  intros x. rewrite elem_of_list_fmap. split.
  - intros ([k a] & -> & In%elem_of_map_to_list). eauto.
  - intros [k Eqk]. exists (k,x). split; [done|].
    by rewrite elem_of_map_to_list.
Qed.

Definition range_f {E : Type} `{Countable K, Countable A} (f: E → A) (m: gmap K E) : gset A :=
  list_to_set (f <$> (range_list m)).

Lemma range_f_correct `{Countable K, Countable A} {E: Type} (f: E → A) (m: gmap K E) :
  ∀ x : A, x ∈ range_f f m ↔ ∃ k, f <$> m !! k = Some x.
Proof.
  intros x. rewrite /range_f elem_of_list_to_set elem_of_list_fmap.
  setoid_rewrite range_list_correct. split.
  - intros (e & -> & k & In). exists k. by rewrite In.
  - intros [k Eqk]. destruct (m !! k) as [e|] eqn: Eqk'; [|done].
    simpl in Eqk. simplify_eq. exists e. naive_solver.
Qed.

Definition range `{Countable K, Countable A} (m: gmap K A) := range_f id m.

Lemma range_insert `{Countable K, Countable A} (m: gmap K A) (k : K) (a : A)
  (FRESH: m !! k = None) :
  range (<[k := a]> m) = {[a]} ∪ range m.
Proof.
  rewrite -leibniz_equiv_iff => i.
  rewrite elem_of_union elem_of_singleton !range_f_correct.
  split.
  - intros [k' Eq']. case (decide (k' = k)) => ?.
    + subst k'. rewrite lookup_insert /= in Eq'. simplify_eq. by left.
    + rewrite lookup_insert_ne // in Eq'. right. by eexists.
  - intros [?|[k' Eq']].
    + subst i. exists k. by rewrite lookup_insert.
    + exists k'. rewrite lookup_insert_ne //. intros ?. subst k'.
      by rewrite FRESH in Eq'.
Qed.

Lemma range_correct `{Countable K, Countable A} (m: gmap K A) :
  ∀ x : A, x ∈ range m ↔ ∃ k, m !! k = Some x.
Proof.
  intros x. rewrite range_f_correct. split; intros [k Eq]; exists k.
  - destruct (m !! k); simpl in Eq; by simplify_eq.
  - by rewrite Eq.
Qed.

Lemma range_empty `{Countable K, Countable A} :
  range (∅ : gmap K A) = ∅.
Proof. done. Qed.

End gmap.

Section coPset.

Lemma coPset_choose (E : coPset) :
  E ≠ ∅ → ∃ x, x ∈ E.
Proof.
  intros NonEmpty. destruct (decide (set_finite E)) as [HE|HE].
  - set_unfold.
    setoid_rewrite <-elem_of_coPset_to_gset; last done.
    setoid_rewrite <-elem_of_coPset_to_gset in NonEmpty; last done.
    apply set_choose_L.
    by set_unfold.
  - exists (coPpick E). by apply coPpick_elem_of.
Qed.

Lemma top_disjoint_difference_gset_to_coPset X :
  (⊤ ## (⊤ ∖ (gset_to_coPset X))) → False.
Proof.
  intros HX%top_disjoint_empty_L.
  pose proof (empty_finite (C:=coPset)) as Hempty.
  rewrite coPset_finite_infinite -HX in Hempty.
  apply Hempty, difference_infinite; [apply top_infinite|apply gset_to_coPset_finite].
Qed.

Lemma top_disjoint_gset_to_coPset X :
  X ≠ ∅ →
  (⊤ ## (gset_to_coPset X)) → False.
Proof.
  intros ? HX%top_disjoint_empty_L. rewrite -gset_to_coPset_empty in HX.
  by apply (inj _) in HX.
Qed.

Lemma disjoint_complement (X Y : coPset) :
  X ## Y ↔ X ⊆ ⊤ ∖ Y.
Proof. set_solver. Qed.

Lemma disjoint_subset (X Y : coPset) :
  X ## ⊤ ∖ Y ↔ X ⊆ Y.
Proof.
  rewrite elem_of_disjoint elem_of_subseteq.
  split; intros; set_solver.
Qed.

Lemma union_difference_L' (X Y : coPset) :
  X ⊆ Y → Y = (Y ∖ X) ∪ X.
Proof. intros. rewrite (union_difference_L X Y); set_solver. Qed.

Lemma difference_difference_r (X Y Z : coPset) :
  Z ⊆ Y → Y ⊆ X → X ∖ Y ∪ Z = X ∖ (Y ∖ Z).
Proof. intros. rewrite difference_difference_r_L. set_solver. Qed.

Lemma top_union_difference (E : coPset) :
  ⊤ = (⊤ ∖ E) ∪ E.
Proof. by apply union_difference_L'. Qed.

Lemma top_intersection_difference (X Y : coPset) :
  X ∩ (⊤ ∖ Y) = X ∖ Y.
Proof. set_solver. Qed.

Lemma difference_union_difference (X Y Z : coPset) :
  X ∖ (Y ∪ Z) = X ∖ Y ∖ Z.
Proof. set_solver. Qed.

Lemma top_difference_diag (X Y : coPset) :
  (⊤ ∖ X) ∖ (⊤ ∖ Y) = Y ∖ X.
Proof. set_unfold. repeat (intros; split); set_solver. Qed.

Lemma elem_of_complement x (E : coPset) :
  x ∈ ⊤ ∖ E ↔ x ∉ E.
Proof. set_solver. Qed.
End coPset.

Section circular_list.
  Context {A : Type}.
  Implicit Types l : list A.

  (* mod set/get *)

  Definition mod_set l i v := <[i `mod` length l:=v]> l.

  Definition mod_get l i := l !! (i `mod` length l).

  Lemma mod_get_is_Some l i :
    length l ≠ 0 → is_Some (mod_get l i).
  Proof. intros H. by apply lookup_lt_is_Some, Nat.mod_upper_bound. Qed.

  Lemma mod_set_length l i v : length (mod_set l i v) = length l.
  Proof. by rewrite length_insert. Qed.

  Lemma mod_set_get l i j v :
    length l ≠ 0 →
    i `mod` length l = j `mod` length l →
    mod_get (mod_set l i v) j = Some v.
  Proof.
    intros H Hij. unfold mod_get, mod_set.
    rewrite length_insert Hij list_lookup_insert; auto.
    by apply Nat.mod_upper_bound.
  Qed.

  Lemma mod_set_get_ne l i j v :
    i `mod` length l ≠ j `mod` length l →
    mod_get (mod_set l i v) j = mod_get l j.
  Proof.
    intros Hij. unfold mod_get, mod_set.
    by rewrite length_insert list_lookup_insert_ne.
  Qed.

  (* slice *)

  (* circ_slice l i j = l[i%len..(j-1)%len] *)
  Fixpoint circ_slice_d l i d :=
    match d with
    | O => []
    | S d' => match mod_get l i with
      | Some v => v :: circ_slice_d l (S i) d'
      | None => []
      end
    end.
  Definition circ_slice l i j := circ_slice_d l i (j-i).

  Lemma circ_slice_nil l i j : i ≥ j → circ_slice l i j = [].
  Proof.
    unfold circ_slice. intros H. by replace (j-i) with 0 by lia.
  Qed.

  Lemma circ_slice_singleton l i :
    length l ≠ 0 →
    ∃ v, mod_get l i = Some v ∧ circ_slice l i (S i) = [v].
  Proof.
    intros Hl.
    destruct (mod_get_is_Some l i) as [v Hv]; auto.
    unfold circ_slice, circ_slice_d; simpl.
    replace (S i - i) with 1; try lia. rewrite Hv.
    by exists v.
  Qed.

  Lemma circ_slice_length l i j :
    length l ≠ 0 →
    length (circ_slice l i j) = j - i.
  Proof.
    unfold circ_slice. intros Hlen.
    remember (j-i) as ji eqn:Hji. revert ji i j Hji.
    induction ji as [|len IHji]; intros i j Hji; auto. simpl.
    destruct (mod_get_is_Some l i) as [x Hx]; auto. rewrite Hx.
    simpl. rewrite (IHji (S i) j); lia.
  Qed.

  Lemma circ_slice_split m l i j :
    length l ≠ 0 → i ≤ m ≤ j →
    circ_slice l i j = circ_slice l i m ++ circ_slice l m j.
  Proof.
    unfold circ_slice. intros Hlen Hm.
    remember (m-i) as dif eqn:Hdif. revert dif i m j Hm Hdif.
    induction dif as [|dif IHdif]; intros i m j Hm Hdif; simpl.
    { replace m with i; by try lia. }
    destruct (j-i) eqn:Eji; try lia. simpl.
    destruct (mod_get_is_Some l i) as [x Hx]; auto. rewrite Hx.
    assert (j - S i = n) as Eji' by lia.
    specialize (IHdif (S i) m j). rewrite Eji' in IHdif.
    rewrite IHdif; auto. all: lia.
  Qed.

  Lemma circ_slice_split_eq m l l' i j :
    length l ≠ 0 → length l' ≠ 0 →
    i ≤ m ≤ j →
    circ_slice l i j = circ_slice l' i j →
    circ_slice l i m = circ_slice l' i m ∧
    circ_slice l m j = circ_slice l' m j.
  Proof.
    intros Hlen Hlen' Hm Heqs.
    rewrite (circ_slice_split m l) in Heqs; auto.
    rewrite (circ_slice_split m l') in Heqs; auto.
    apply app_inj_1 in Heqs; auto.
    do 2 (rewrite circ_slice_length; auto).
  Qed.

  Lemma circ_slice_extend_right l i j v :
    length l ≠ 0 →
    i ≤ j → mod_get l j = Some v →
    circ_slice l i (S j) = circ_slice l i j ++ [v].
  Proof.
    unfold circ_slice. intros Hlen Hij Hj.
    replace (S j - i) with (S (j - i)) by lia.
    remember (j - i) as d. revert i Hij Heqd.
    induction d; intros.
    - simpl. replace i with j by lia. by rewrite Hj.
    - assert (is_Some (mod_get l i)) as [vi Vi] by by apply mod_get_is_Some.
      simpl. rewrite Vi; simpl.
      rewrite -(IHd (S i)); try lia. auto.
  Qed.

  Lemma circ_slice_update_right l i j v :
    length l ≠ 0 →
    i ≤ j < (i + length l) →
    circ_slice (mod_set l j v) i j = circ_slice l i j.
  Proof.
    unfold circ_slice. intros Hlen Hij.
    remember (j - i) as d. revert i Hij Heqd.
    induction d; intros; auto.
    assert (i < j) by lia.
    assert (is_Some (mod_get l i)) as [vi Vi] by by apply mod_get_is_Some.
    assert (mod_get (mod_set l j v) i = Some vi) as Vi'.
    { rewrite mod_set_get_ne; auto.
      assert (i < j < i + length l) as H' by lia.
      apply (close_mod_neq _ _ (length l)) in H'. lia. }
    simpl. rewrite Vi Vi'.
    rewrite -(IHd (S i)); by try lia.
  Qed.

  Lemma circ_slice_shrink_right l i j v :
    length l ≠ 0 →
    i < j → mod_get l (j - 1) = Some v →
    circ_slice l i j = circ_slice l i (j - 1) ++ [v].
  Proof.
    intros. replace j with (S (j - 1)) by lia.
    erewrite circ_slice_extend_right; eauto; try lia.
    by replace (S (j - 1)) with j by lia.
  Qed.

  Lemma circ_slice_shrink_left l i j v :
    length l ≠ 0 →
    i < j → mod_get l i = Some v →
    circ_slice l i j = v :: circ_slice l (S i) j.
  Proof.
    unfold circ_slice. intros H Hij Hi.
    replace (j - i) with (S (j - S i)) by lia. simpl.
    by rewrite Hi.
  Qed.
End circular_list.
