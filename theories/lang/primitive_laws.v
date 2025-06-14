(** This file proves the basic laws of the HeapLang program logic by applying
the Iris lifting lemmas. *)

From iris.proofmode Require Import proofmode.
From iris.algebra Require Import big_op gmap dfrac numbers.
From iris.algebra Require Import csum excl auth cmra_big_op.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_map invariants mono_nat.
From iris.base_logic.lib Require Export proph_map.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From smr.lang Require Export class_instances.
From smr.lang Require Import tactics notation.
From iris.prelude Require Import options.

Definition heap_freeableUR : ucmra :=
  gmapUR blk (prodR fracR (gmapR Z (exclR unitO))).

(* we roll our own version of inv_heap stuff, because the original one depends
on iris's [gen_heapGS]. *)
Definition inv_heap_mapUR  : ucmra := gmapUR loc $ prodR
  (optionR $ exclR $ valO)
  (agreeR (val -d> PropO)).

Class heapGS_gen hlc Σ := HeapGS {
  heapGS_invGS : invGS_gen hlc Σ;
  heap_name : gname;
  #[global] heapGS_inG :: ghost_mapG Σ loc val;
  inv_heap_name : gname;
  #[global] heapGS_inv_heapGS :: inG Σ (authR inv_heap_mapUR);
  heap_freeable_name : gname;
  #[global] heap_freeable_inG :: inG Σ (authR heap_freeableUR); (* freeable predicate to use in Alloc/Free *)
  #[global] heapGS_proph_mapGS :: proph_mapGS proph_id (val * val) Σ;
  heapGS_step_name : gname;
  heapGS_step_cnt : mono_natG Σ;
}.
Local Existing Instance heapGS_step_cnt.

Notation heapGS := (heapGS_gen HasLc).

Section steps.
  Context `{!heapGS_gen hlc Σ}.

  Local Definition steps_auth (n : nat) : iProp Σ :=
    mono_nat_auth_own heapGS_step_name 1 n.

  Definition steps_lb (n : nat) : iProp Σ :=
    mono_nat_lb_own heapGS_step_name n.

  Local Lemma steps_lb_valid n m :
    steps_auth n -∗ steps_lb m -∗ ⌜m ≤ n⌝.
  Proof.
    iIntros "Hauth Hlb".
    by iDestruct (mono_nat_lb_own_valid with "Hauth Hlb") as %[_ Hle].
  Qed.

  Local Lemma steps_lb_get n :
    steps_auth n -∗ steps_lb n.
  Proof. apply mono_nat_lb_own_get. Qed.

  Local Lemma steps_auth_update n n' :
    n ≤ n' → steps_auth n ==∗ steps_auth n' ∗ steps_lb n'.
  Proof. intros Hle. by apply mono_nat_own_update. Qed.

  Local Lemma steps_auth_update_S n :
    steps_auth n ==∗ steps_auth (S n).
  Proof.
    iIntros "Hauth".
    iMod (mono_nat_own_update with "Hauth") as "[$ _]"; [lia|done].
  Qed.

  Lemma steps_lb_le n n' :
    n' ≤ n → steps_lb n -∗ steps_lb n'.
  Proof. intros Hle. by apply mono_nat_lb_own_le. Qed.

End steps.

Definition heap_freeable_rel (m : memory) (hF : heap_freeableUR) : Prop :=
  ∀ b qs, hF !! b = Some qs →
    qs.2 ≠ ∅ ∧ ∀ i, is_Some (m !! (b, i)) ↔ is_Some (qs.2 !! i).

Section heap_definitions.
  Context `{!heapGS_gen hlc Σ}.

  Definition pointsto_st
             (l : loc) (dq : dfrac) (v: val) : iProp Σ :=
    l ↪[heap_name]{dq} v.

  Definition pointsto_def (l : loc) (d : dfrac) (v: val) : iProp Σ :=
    pointsto_st l d v.
  Definition pointsto_aux : seal (@pointsto_def). Proof. by eexists. Qed.
  Definition pointsto := unseal pointsto_aux.
  Definition pointsto_unseal : @pointsto = @pointsto_def :=
    pointsto_aux.(seal_eq).

  Definition array (l : loc) (d : dfrac) (vl : list val) : iProp Σ :=
    ([∗ list] i ↦ v ∈ vl, pointsto (l +ₗ i) d v)%I.

  Fixpoint inter (i0 : Z) (n : nat) : gmapR Z (exclR unitO) :=
    match n with O => ∅ | S n => <[i0 := Excl ()]>(inter (i0+1) n) end.

  Definition heap_freeable_def (l : loc) (q : frac) (n: nat) : iProp Σ :=
    own heap_freeable_name (◯ {[ l.1 := (q, inter (l.2) n) ]}) ∧ ⌜0 < n⌝.
  Definition heap_freeable_aux : seal (@heap_freeable_def). Proof. by eexists. Qed.
  Definition heap_freeable := unseal heap_freeable_aux.
  Definition heap_freeable_unseal : @heap_freeable = @heap_freeable_def :=
    heap_freeable_aux.(seal_eq).

  Definition heap_ctx (mem:memory) : iProp Σ :=
    (∃ hF, ghost_map_auth heap_name 1 mem
         ∗ own heap_freeable_name (● hF)
         ∗ ⌜heap_freeable_rel mem hF⌝)%I.
End heap_definitions.

Notation "l ↦ dq v" := (pointsto l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.

Notation "l ↦∗ dq vs" := (array l dq vs)
  (at level 20, dq custom dfrac at level 1, format "l  ↦∗ dq  vs") : bi_scope.

Notation "†{ q } l … n" := (heap_freeable l q n)
  (at level 20, q at level 50, format "†{ q } l … n") : bi_scope.
Notation "† l … n" := (heap_freeable l 1 n) (at level 20) : bi_scope.


Section heap.
  Context `{!heapGS_gen hlc Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : memory.
  Implicit Types E : coPset.
  Local Open Scope Z.

  (** General properties of pointsto and freeable *)
  Global Instance pointsto_timeless l d v : Timeless (pointsto l d v).
  Proof. rewrite pointsto_unseal /pointsto_def. apply _. Qed.

  Global Instance pointsto_fractional l v: Fractional (λ q, l ↦{# q} v)%I.
  Proof.
    rewrite pointsto_unseal. unfold pointsto_def. unfold pointsto_st.
    apply ghost_map_elem_fractional.
  Qed.
  Global Instance pointsto_as_fractional l q v:
    AsFractional (l ↦{# q} v) (λ q, l ↦{# q} v)%I q.
  Proof. split; first done. apply _. Qed.

  Global Instance pointsto_persistent l v : Persistent (l ↦□ v).
  Proof. rewrite pointsto_unseal. apply _. Qed.

  Global Instance frame_pointsto p l v q1 q2 q :
    FrameFractionalQp q1 q2 q →
    Frame p (l ↦{# q1} v) (l ↦{# q2} v) (l ↦{# q} v) | 5.
  Proof. apply: frame_fractional. Qed.

  Global Instance array_timeless l q vl : Timeless (l ↦∗{q} vl).
  Proof. rewrite /array. apply _. Qed.

  Global Instance array_fractional l vl: Fractional (λ q, l ↦∗{# q} vl)%I.
  Proof.
    intros p q. rewrite /array -big_sepL_sep.
    by setoid_rewrite (fractional (Φ := λ q, _ ↦{# q} _)%I).
  Qed.
  Global Instance array_as_fractional l q vl:
    AsFractional (l ↦∗{# q} vl) (λ q, l ↦∗{# q} vl)%I q.
  Proof. split; first done. apply _. Qed.

  Global Instance heap_freeable_timeless q l n : Timeless (†{q}l…n).
  Proof. rewrite heap_freeable_unseal /heap_freeable_def. apply _. Qed.

  Lemma pointsto_valid l dq v : l ↦{dq} v -∗ ⌜✓ dq⌝.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_valid. Qed.

  Lemma pointsto_valid_2 l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_valid_2. Qed.

  Lemma pointsto_agree l d1 d2 v1 v2 : l ↦{d1} v1 -∗ l ↦{d2} v2 -∗ ⌜v1 = v2⌝.
  Proof. iIntros "l↦v1 l↦v2". iDestruct (pointsto_valid_2 with "l↦v1 l↦v2") as "[_ $]". Qed.

  Lemma pointsto_combine l dq1 dq2 v1 v2 :
    l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ l ↦{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_combine. Qed.

  Lemma pointsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
    ¬ ✓(dq1 ⋅ dq2) → l1 ↦{dq1} v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_frac_ne. Qed.
  Lemma pointsto_ne l1 l2 dq2 v1 v2 : l1 ↦ v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_ne. Qed.

  (** Permanently turn any points-to predicate into a persistent
      points-to predicate. *)
  Lemma pointsto_persist l dq v : l ↦{dq} v ==∗ l ↦□ v.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_persist. Qed.

  Lemma array_nil l q : l ↦∗{q} [] ⊣⊢ True.
  Proof. by rewrite /array. Qed.

  Lemma array_app l q vl1 vl2 :
    l ↦∗{q} (vl1 ++ vl2) ⊣⊢ l ↦∗{q} vl1 ∗ (l +ₗ length vl1) ↦∗{q} vl2.
  Proof.
    rewrite /array big_sepL_app.
    do 2 f_equiv. intros k v. by rewrite Loc.add_assoc_nat.
  Qed.

  Lemma array_singleton l q v : l ↦∗{q} [v] ⊣⊢ l ↦{q} v.
  Proof. by rewrite /array /= Loc.add_0 right_id. Qed.

  Lemma array_cons l q v vl:
    l ↦∗{q} (v :: vl) ⊣⊢ l ↦{q} v ∗ (l +ₗ 1) ↦∗{q} vl.
  Proof.
    by rewrite (array_app l q [v] vl) array_singleton.
  Qed.

  Global Instance array_cons_frame l dq v vs R Q :
    Frame false R (l ↦{dq} v ∗ (l +ₗ 1) ↦∗{dq} vs) Q →
    Frame false R (l ↦∗{dq} (v :: vs)) Q | 2.
  Proof. by rewrite /Frame array_cons. Qed.

  Lemma array_agree l dq1 dq2 vs1 vs2 :
    length vs1 = length vs2 →
    l ↦∗{dq1} vs1 -∗ l ↦∗{dq2} vs2 -∗ ⌜vs1 = vs2⌝.
  Proof.
    revert l vs2. iInduction (vs1) as [|v1 vs1 IH]; iIntros (l vs2 EQ); destruct vs2; auto.
    iIntros "l↦1 l↦2". rewrite !array_cons.
    iDestruct "l↦1" as "[l↦1 l+ₗ1↦1]". iDestruct "l↦2" as "[l↦2 l+ₗ1↦2]".
    iDestruct (pointsto_agree with "l↦1 l↦2") as %[= <-].
    iDestruct ("IH" with "[] [$l+ₗ1↦1] [$l+ₗ1↦2]") as %[= <-]; last done.
    iPureIntro. rewrite !length_cons in EQ. by injection EQ.
  Qed.

  Lemma array_op l q1 q2 vl1 vl2 :
    length vl1 = length vl2 →
    l ↦∗{# q1} vl1 ∗ l ↦∗{# q2} vl2 ⊣⊢ ⌜vl1 = vl2⌝ ∧ l ↦∗{# q1+q2} vl1.
  Proof.
    intros Hlen%Forall2_same_length. apply (anti_symm (⊢)).
    - revert l. induction Hlen as [|v1 v2 vl1 vl2 _ _ IH]=> l.
      { rewrite !array_nil. iIntros "_"; auto. }
      rewrite !array_cons. iIntros "[[Hv1 Hvl1] [Hv2 Hvl2]]".
      iDestruct (IH (l +ₗ 1) with "[$Hvl1 $Hvl2]") as "[% $]"; subst.
      rewrite (inj_iff (.:: vl2)).
      iDestruct (pointsto_agree with "Hv1 Hv2") as %<-.
      iSplit; first done. iFrame.
    - by iIntros "[% [$ Hl2]]"; subst.
  Qed.

  Lemma array_combine l q vl :
    vl ≠ [] →
    l ↦∗{q} vl ⊣⊢ [∗ list] i ↦ v ∈ vl, (l +ₗ i) ↦{q} v.
  Proof.
    by rewrite /array pointsto_unseal /pointsto_def /pointsto_st=>?.
  Qed.

  Lemma array_persist l dq vs : l ↦∗{dq} vs ==∗ l ↦∗□ vs.
  Proof.
    revert l. iInduction (vs) as [|v vs' IH]; [naive_solver|].
    iIntros (l) "l↦". rewrite !array_cons. iDestruct "l↦" as "[l↦ l+ₗ1↦]".
    iMod (pointsto_persist with "l↦") as "$". iApply ("IH" with "l+ₗ1↦").
  Qed.

  Global Instance array_persistent l vs : Persistent (l ↦∗□ vs).
  Proof. destruct vs; apply _. Qed.

  Lemma inter_lookup_Some i j (n : nat):
    i ≤ j < i+n → inter i n !! j = Excl' ().
  Proof.
    revert i. induction n as [|n IH]=>/= i; first lia.
    rewrite lookup_insert_Some. destruct (decide (i = j)); naive_solver lia.
  Qed.
  Lemma inter_lookup_None i j (n : nat):
    j < i ∨ i+n ≤ j → inter i n !! j = None.
  Proof.
    revert i. induction n as [|n IH]=>/= i; first by rewrite lookup_empty.
    rewrite lookup_insert_None. naive_solver lia.
  Qed.
  Lemma inter_op i n n' : inter i n ⋅ inter (i+n) n' ≡ inter i (n+n').
  Proof.
    intros j. rewrite lookup_op.
    destruct (decide (i ≤ j < i+n)); last destruct (decide (i+n ≤ j < i+n+n')).
    - by rewrite (inter_lookup_None (i+n) j n') ?inter_lookup_Some; try lia.
    - by rewrite (inter_lookup_None i j n) ?inter_lookup_Some; try lia.
    - by rewrite !inter_lookup_None; try lia.
  Qed.
  Lemma inter_valid i n : ✓ inter i n.
  Proof. revert i. induction n as [|n IH]=>i; first done. by apply insert_valid. Qed.

  Lemma heap_freeable_valid l n n' :
    †l…n -∗ †l…n' -∗ False.
  Proof.
    rewrite heap_freeable_unseal /heap_freeable_def.
    iIntros "[†l %Hn] [†l' %Hn']".
    iCombine "†l †l'" as "†".
    rewrite own_valid.
    iDestruct "†" as "%H". iPureIntro.
    rewrite auth_frag_valid singleton_valid pair_valid in H.
    destruct H as [H _].
    rewrite frac_valid in H. done.
  Qed.

  Lemma heap_freeable_nonzero l n :
    †l…n -∗ ⌜(0 < n)%nat⌝.
  Proof.
    rewrite heap_freeable_unseal /heap_freeable_def.
    by iIntros "[_ %]".
  Qed.

  (** Properties about heap_freeable_rel and heap_freeable *)
  Lemma heap_freeable_rel_None σ (l:blk) hF :
    (∀ m : Z, σ !! (l,m) = None) → heap_freeable_rel σ hF →
    hF !! l = None.
  Proof.
    intros FRESH REL. apply eq_None_not_Some. intros [[q s] [Hsne REL']%REL].
    destruct (map_choose s) as [i []%REL'%not_eq_None_Some]; first done.
    move: (FRESH i). by rewrite /Loc.add.
  Qed.

  Lemma heap_freeable_is_Some σ hF l n i :
    heap_freeable_rel σ hF →
    hF !! l.1 = Some (1%Qp, inter (l.2) n) →
    is_Some (σ !! (l +ₗ i)) ↔ 0 ≤ i ∧ i < n.
  Proof.
    destruct l as [b j]; rewrite /Loc.add /=. intros REL Hl.
    destruct (REL b (1%Qp, inter j n)) as [_ ->]; simpl in *; auto.
    destruct (decide (0 ≤ i ∧ i < n)).
    - rewrite is_Some_alt inter_lookup_Some; lia.
    - rewrite is_Some_alt inter_lookup_None; lia.
  Qed.

  Lemma heap_freeable_rel_init_mem (l:blk) h n v σ:
    n ≠ O →
    (∀ m : Z, σ !! (l,m) = None) →
    heap_freeable_rel σ h →
    heap_freeable_rel (init_mem l n v σ)
                      (<[l := (1%Qp, inter 0%Z n)]> h).
  Proof.
    move=> Hvlnil FRESH REL b qs /lookup_insert_Some [[<- <-]|[??]].
    - split.
      { destruct n as [|n]; simpl in *; [done|]. apply: insert_non_empty. }
      intros i. destruct (decide (0 ≤ i ∧ i < n)).
      + rewrite inter_lookup_Some // lookup_init_mem; naive_solver.
      + rewrite inter_lookup_None; last lia. rewrite lookup_init_mem_ne /=; last lia.
        replace (l,i) with (l +ₗ i) by (rewrite /Loc.add; f_equal; lia).
        by rewrite FRESH !is_Some_alt.
    - destruct (REL b qs) as [? Hs]; auto.
      split; [done|]=> i. by rewrite -Hs lookup_init_mem_ne; last auto.
  Qed.

  Lemma heap_freeable_rel_free_mem σ hF n l :
    hF !! l.1 = Some (1%Qp, inter (l.2) n) →
    heap_freeable_rel σ hF →
    heap_freeable_rel (free_mem l n σ) (delete (l.1) hF).
  Proof.
    intros Hl REL b qs; rewrite lookup_delete_Some=> -[NEQ ?].
    destruct (REL b qs) as [? REL']; auto.
    split; [done|]=> i. by rewrite -REL' lookup_free_mem_ne.
  Qed.

  Lemma heap_freeable_rel_stable σ h l p :
    heap_freeable_rel σ h → is_Some (σ !! l) →
    heap_freeable_rel (<[l := p]>σ) h.
  Proof.
    intros REL Hσ b qs Hqs. destruct (REL b qs) as [? REL']; first done.
    split; [done|]=> i. rewrite -REL' lookup_insert_is_Some.
    destruct (decide (l = (b, i))); naive_solver.
  Qed.

  Lemma difference_insert' (m1 m2 : memory) i x :
    m1 !! i = None →
    m1 ∖ <[i:=x]> m2 = m1 ∖ m2.
  Proof.
    intro None.
    apply map_eq. intros i'. apply option_eq. intros x'.
    rewrite !lookup_difference_Some !lookup_insert_None.
    split.
    - intros (Hm1i' & Hm2i' & Neq). done.
    - intros (Hm1i' & Hm2i'). split_and!; [done..|].
      apply (lookup_ne m1 i i'). rewrite None Hm1i'. done.
  Qed.

  (** Weakest precondition *)
  Lemma heap_alloc_vs σ l n v :
    (∀ m : Z, σ !! (l +ₗ m) = None) →
    ghost_map_auth heap_name 1 σ
    ==∗ ghost_map_auth heap_name 1 (init_mem l n v σ)
          ∗ ([∗ list] i ↦ v ∈ (replicate n v), (l +ₗ i) ↦ v).
  Proof.
    revert l n.
    assert (∀ l n, (∀ m : Z, σ !! (l +ₗ m) = None) → σ ⊆ init_mem l n v σ) as Subσ.
    { intros l n FREE. revert l FREE. induction n as [|n IH] => l FRESH.
      { simpl. set_solver. }
      simpl. specialize IH with (l +ₗ 1). rewrite map_subseteq_spec.
      intros l' v' Hσ. destruct (decide (l' = l)) as [->|NE].
      - specialize FRESH with 0. rewrite Loc.add_0 in FRESH.
        rewrite Hσ in FRESH. inversion FRESH.
      - rewrite lookup_insert_ne; [|done]. rewrite map_subseteq_spec in IH.
        apply IH; [|done]. intro m. specialize FRESH with (1 + m).
        rewrite -Loc.add_assoc in FRESH. apply FRESH.
    }
    assert (∀ l n, (∀ m : Z, σ !! (l +ₗ m) = None) → init_mem l n v σ ∖ σ ##ₘ σ) as Disjσ.
    { intros l n FREE. by apply map_disjoint_difference_l. }
    iIntros (l n FREE) "Heap".
    iDestruct ((ghost_map_insert_big ((init_mem l n v σ) ∖ σ)) with "Heap") as "HeapCond"; [by apply Disjσ|].
    rewrite (_ :(init_mem l n v σ) ∖ σ ∪ σ = (init_mem l n v σ)); last first.
    { rewrite map_union_comm; [|by apply Disjσ]. apply map_difference_union. by apply Subσ. }
    iMod "HeapCond" as "[$ HeapCond]".
    iModIntro.
    rename FREE into FRESH.
    iInduction n as [|n IH] forall (l FRESH); [done|].
    simpl.
    iSpecialize ("IH" $! (l +ₗ 1)).
    rewrite Loc.add_0.
    iDestruct (big_sepM_delete (λ k v, (k ↪[heap_name] v)%I) (<[l:=v]> (init_mem (l +ₗ 1) n v σ) ∖ σ) l v) as "[Hl _]".
    { rewrite lookup_difference_Some. split; [simplify_map_eq|].
      - rewrite lookup_insert. done.
      - specialize FRESH with 0. by rewrite Loc.add_0 in FRESH.
    }
    iSpecialize ("Hl" with "HeapCond").
    iDestruct "Hl" as "[Hl HCons]".
    iSplitL "Hl".
    { rewrite pointsto_unseal. unfold pointsto_def. by unfold pointsto_st. }
    rewrite (_ : delete l (<[l:=v]> (init_mem (l +ₗ 1) n v σ) ∖ σ) = (init_mem (l +ₗ 1) n v σ ∖ σ)); last first.
    { rewrite (delete_difference _ _ l v).
      rewrite (difference_insert _ _ _ _ _ v).
      apply difference_insert'.
      rewrite lookup_init_mem_ne; [specialize FRESH with 0; by rewrite Loc.add_0 in FRESH|].
      right. left. destruct l. simpl. lia.
    }
    iSpecialize ("IH" with "[%] HCons").
    { intros. rewrite Loc.add_assoc. done. }
    iApply (big_sepL_mono with "IH").
    iIntros (i ? Hi) "l↦".
    rewrite Loc.add_assoc. assert (1 + i = S i) as -> by lia.
    done.
  Qed.

  Lemma heap_alloc σ (l:blk) n v :
    0 < n →
    (∀ m, σ !! (l,m) = None) →
    heap_ctx σ ==∗
      heap_ctx (init_mem l (Z.to_nat n) v σ) ∗ †l…(Z.to_nat n) ∗
      l ↦∗ replicate (Z.to_nat n) v.
  Proof.
    intros ??; iDestruct 1 as (hF) "(Hvalσ & HhF & %)".
    assert (Z.to_nat n ≠ O) as Not0 by lia.
    iMod (heap_alloc_vs _ (l,0%Z) (Z.to_nat n) with "[$Hvalσ]") as "[Hvalσ Hmapsto]"; first done.
    iMod (own_update _ (● hF) with "HhF") as "[HhF Hfreeable]".
    { apply auth_update_alloc,
        (alloc_singleton_local_update _ l (1%Qp, inter 0%Z (Z.to_nat n))).
      - eauto using heap_freeable_rel_None.
      - split; first done. apply inter_valid. }
    iModIntro. iSplitL "Hvalσ HhF".
    { iExists _. iFrame. iPureIntro.
      auto using heap_freeable_rel_init_mem. }
    rewrite heap_freeable_unseal /heap_freeable_def. iFrame.
    iPureIntro. lia.
  Qed.

  Definition heap_seq (vl : list val) (l: loc) : memory :=
    let f := λ i v, (l +ₗ i, v) in
    let heap_list := imap f vl in
    list_to_map heap_list.

  Lemma heap_free_vs σ l vl :
    ghost_map_auth heap_name 1 σ ∗ ([∗ list] i ↦ v ∈ vl, (l +ₗ i) ↦ v)
    ==∗ ghost_map_auth heap_name 1 (free_mem l (length vl) σ).
  Proof.
    iIntros "[Heap List]".
    iDestruct ((ghost_map_delete_big (heap_seq vl l)) with "Heap") as "Heap".
    assert (∀ l vl, imap ((λ (i : nat) (v : val), (l +ₗ i, v)) ∘ S) vl =
            imap (λ (i : nat) (v : val), (l +ₗ 1 +ₗ i, v)) vl) as Himap.
    { intros. apply imap_ext. intros. simpl. f_equal.
      rewrite Loc.add_assoc. f_equal. lia. }
    rewrite (_ : σ ∖ heap_seq vl l = free_mem l (length vl) σ); last first.
    { revert l. induction vl as [|v vl IH] => l.
      { by rewrite map_difference_empty. }
      unfold heap_seq. simpl. rewrite Loc.add_0.
      rewrite -delete_difference. simpl. f_equal.
      specialize IH with (l +ₗ 1). unfold heap_seq in IH.
      rewrite -IH. do 2 f_equal.
      apply Himap.
    }
    iApply "Heap".
    iInduction (vl) as [|v vl IH] forall (l); [done|].
    iSpecialize ("IH" $! (l +ₗ 1)).
    unfold heap_seq. simpl. rewrite Loc.add_0.
    rewrite big_sepM_insert_delete.
    iDestruct "List" as "[l↦ List]".
    iSplitL "l↦"; [rewrite pointsto_unseal; iFrame|].
    assert (delete l
      (list_to_map
          (imap ((λ (i : nat) (v0 : val), (l +ₗ i, v0)) ∘ S) vl)) =
       list_to_map
          (imap ((λ (i : nat) (v0 : val), (l +ₗ i, v0)) ∘ S) vl)) as ->.
    { apply delete_notin. apply not_elem_of_list_to_map_1.
      rewrite fmap_imap. intro Hl.
      apply elem_of_lookup_imap_1 in Hl.
      destruct Hl as (i & v' & Hl & _).
      destruct l. unfold Loc.add in Hl. simpl in Hl.
      inversion Hl. lia.
    }
    rewrite Himap. iApply "IH".
    iApply (big_sepL_mono with "List").
    iIntros (i v' Hi) "l↦".
    rewrite Loc.add_assoc. assert (1 + i = S i) as -> by lia.
    iFrame.
  Qed.

  Lemma heap_free σ l vl (n : Z) :
    n = length vl →
    heap_ctx σ -∗ l ↦∗ vl -∗ †l…(length vl)
    ==∗ ⌜0 < n⌝ ∗ ⌜∀ m, is_Some (σ !! (l +ₗ m)) ↔ (0 ≤ m < n)⌝ ∗
        heap_ctx (free_mem l (Z.to_nat n) σ).
  Proof.
    iDestruct 1 as (hF) "(Hvalσ & HhF & REL)"; iDestruct "REL" as %REL.
    rewrite heap_freeable_unseal /heap_freeable_def.
    iIntros "Hmt [Hf %Hn]".
    iCombine "HhF Hf" gives % [Hl Hv]%auth_both_valid_discrete.
    move: Hl=> /singleton_included_l [[q qs] [/leibniz_equiv_iff Hl Hq]].
    apply (Some_included_exclusive _ _) in Hq as [=<-<-]%leibniz_equiv; last first.
    { move: (Hv (l.1)). rewrite Hl. by intros [??]. }
    assert (vl ≠ []).
    { intros ->. by destruct (REL (l.1) (1%Qp, ∅)) as [[] ?]. }
    assert (0 < n) by (subst n; by destruct vl).
    iMod (heap_free_vs with "[Hmt Hvalσ]") as "Hvalσ".
    { rewrite array_combine //. iFrame. }
    iMod (own_update_2 with "HhF Hf") as "HhF".
    { apply auth_update_dealloc, (delete_singleton_local_update _ _ _). }
    iModIntro; subst. repeat iSplit;  eauto using heap_freeable_is_Some.
    iExists _. subst. rewrite Nat2Z.id. iFrame.
    eauto using heap_freeable_rel_free_mem.
  Qed.

  Lemma pointsto_lookup σ l q v :
    ghost_map_auth heap_name 1 σ -∗ l ↦{q} v -∗
    ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "Heap l↦".
    rewrite pointsto_unseal.
    iApply (ghost_map_lookup with "Heap l↦").
  Qed.

  Lemma pointsto_lookup_1 σ l v :
    ghost_map_auth heap_name 1 σ -∗ l ↦ v -∗
    ⌜σ !! l = Some v⌝.
  Proof.
    apply pointsto_lookup.
  Qed.

  Lemma heap_read σ l q v :
    heap_ctx σ -∗ l ↦{q} v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & REL)". iIntros "Hmt".
    iDestruct (pointsto_lookup with "Hσ Hmt") as %Hσl. done.
  Qed.

  Lemma heap_read_1 σ l v :
    heap_ctx σ -∗ l ↦ v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & REL)". iIntros "Hmt".
    iDestruct (pointsto_lookup_1 with "Hσ Hmt") as %Hσl. done.
  Qed.

  Lemma heap_write_vs σ l v v':
    σ !! l = Some v →
    ghost_map_auth heap_name 1 σ -∗ l ↦ v
    ==∗ ghost_map_auth heap_name 1 (<[l:= v']> σ)
        ∗ l ↦ v'.
  Proof.
    iIntros (Hσv) "Heap l↦".
    rewrite pointsto_unseal.
    iDestruct ((ghost_map_update v') with "Heap") as "Heap".
    iSpecialize ("Heap" with "l↦").
    iFrame.
  Qed.

  Lemma heap_write σ l v v' :
    heap_ctx σ -∗ l ↦ v ==∗ heap_ctx (<[l:=v']> σ) ∗ l ↦ v'.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & %)". iIntros "Hmt".
    iDestruct (pointsto_lookup_1 with "Hσ Hmt") as %?; auto.
    iMod (heap_write_vs with "Hσ Hmt") as "[Hσ $]"; first done.
    iModIntro. iExists _. iFrame. eauto using heap_freeable_rel_stable.
  Qed.
End heap.

#[export] Typeclasses Opaque array.

Global Program Instance heapGS_irisGS `{!heapGS_gen hlc Σ} : irisGS_gen hlc heap_lang Σ := {
  iris_invGS := heapGS_invGS;
  state_interp σ step_cnt κs _ :=
    (heap_ctx σ.(heap) ∗ proph_map_interp κs σ.(used_proph_id) ∗ steps_auth step_cnt)%I;
  fork_post _ := True%I;
  num_laters_per_step n := n;
}.
Next Obligation.
  iIntros (??? σ ns κs nt) "/= ($ & $ & H)".
  by iMod (steps_auth_update_S with "H") as "$".
Qed.


(* our version of gen_inv_heap *)
Definition inv_heapN: namespace := nroot .@ "inv_heap".

Definition to_inv_heap (h: gmap loc (val * (val -d> PropO))) : inv_heap_mapUR :=
  prod_map (λ x, Excl' x) to_agree <$> h.

Section inv_heap_definitions.
  Context `{gG: !heapGS_gen hlc Σ}.

  Definition inv_heap_inv_P : iProp Σ :=
    ∃ h : gmap loc (val * (val -d> PropO)),
       own inv_heap_name (● to_inv_heap h) ∗
       [∗ map] l ↦ p ∈ h, ⌜p.2 p.1⌝ ∗ l ↦ p.1.

  Definition inv_heap_inv : iProp Σ := inv inv_heapN inv_heap_inv_P.

  Definition inv_pointsto_own (l : loc) (v : val) (I : val → Prop) : iProp Σ :=
    own inv_heap_name (◯ {[l := (Excl' v, to_agree I) ]}).

  Definition inv_pointsto (l : loc) (I : val → Prop) : iProp Σ :=
    own inv_heap_name (◯ {[l := (None, to_agree I)]}).

End inv_heap_definitions.

Global Instance: Params (@inv_pointsto_own) 4 := {}.
Global Instance: Params (@inv_pointsto) 3 := {}.

Notation "l '↦_' I □" := (inv_pointsto l I%stdpp%type)
  (at level 20, I at level 9, format "l  '↦_' I  '□'") : bi_scope.
Notation "l ↦_ I v" := (inv_pointsto_own l v I%stdpp%type)
  (at level 20, I at level 9, format "l  ↦_ I  v") : bi_scope.

Section to_inv_heap.
  Implicit Types (h : gmap loc (val * (val -d> PropO))).

  Lemma to_inv_heap_valid h : ✓ to_inv_heap h.
  Proof. intros l. rewrite lookup_fmap. by case (h !! l). Qed.

  Lemma to_inv_heap_singleton l v I :
    to_inv_heap {[l := (v, I)]} =@{inv_heap_mapUR} {[l := (Excl' v, to_agree I)]}.
  Proof. by rewrite /to_inv_heap fmap_insert fmap_empty. Qed.

  Lemma to_inv_heap_insert l v I h :
    to_inv_heap (<[l := (v, I)]> h) = <[l := (Excl' v, to_agree I)]> (to_inv_heap h).
  Proof. by rewrite /to_inv_heap fmap_insert. Qed.

  Lemma lookup_to_inv_heap_None h l :
    h !! l = None → to_inv_heap h !! l = None.
  Proof. by rewrite /to_inv_heap lookup_fmap=> ->. Qed.

  Lemma lookup_to_inv_heap_Some h l v I :
    h !! l = Some (v, I) → to_inv_heap h !! l = Some (Excl' v, to_agree I).
  Proof. by rewrite /to_inv_heap lookup_fmap=> ->. Qed.

  Lemma lookup_to_inv_heap_Some_2 h l v' I' :
    to_inv_heap h !! l ≡ Some (v', I') →
    ∃ v I, v' = Excl' v ∧ I' ≡ to_agree I ∧ h !! l = Some (v, I).
  Proof.
    rewrite /to_inv_heap /prod_map lookup_fmap. rewrite fmap_Some_equiv.
    intros ([] & Hsome & [Heqv HeqI]); simplify_eq/=; eauto.
  Qed.
End to_inv_heap.

Section inv_heap.
  Context `{!heapGS_gen hlc Σ}.
  Implicit Types (l : loc) (v : val) (I : val → Prop).
  Implicit Types (h : gmap loc (val * (val -d> PropO))).

  (** * Helpers *)

  Lemma inv_pointsto_lookup_Some l h I :
    l ↦_I □ -∗ own inv_heap_name (● to_inv_heap h) -∗
    ⌜∃ v I', h !! l = Some (v, I') ∧ ∀ w, I w ↔ I' w ⌝.
  Proof.
    iIntros "Hl_inv H◯".
    iCombine "H◯ Hl_inv" gives %[Hincl Hvalid]%auth_both_valid_discrete.
    iPureIntro.
    move: Hincl; rewrite singleton_included_l; intros ([v' I'] & Hsome & Hincl).
    apply lookup_to_inv_heap_Some_2 in Hsome as (v'' & I'' & _ & HI & Hh).
    move: Hincl; rewrite HI Some_included_total pair_included
      to_agree_included; intros [??]; eauto.
  Qed.

  Lemma inv_pointsto_own_lookup_Some l v h I :
    l ↦_I v -∗ own inv_heap_name (● to_inv_heap h) -∗
    ⌜ ∃ I', h !! l = Some (v, I') ∧ ∀ w, I w ↔ I' w ⌝.
  Proof.
    iIntros "Hl_inv H●".
    iCombine "H● Hl_inv" gives %[Hincl Hvalid]%auth_both_valid_discrete.
    iPureIntro.
    move: Hincl; rewrite singleton_included_l; intros ([v' I'] & Hsome & Hincl).
    apply lookup_to_inv_heap_Some_2 in Hsome as (v'' & I'' & -> & HI & Hh).
    move: Hincl; rewrite HI Some_included_total pair_included
      Excl_included to_agree_included; intros [-> ?]; eauto.
  Qed.

  (** * Typeclass instances *)

  (* FIXME(Coq #6294): needs new unification
  The uses of [apply:] and [move: ..; rewrite ..] (by lack of [apply: .. in ..])
  in this file are needed because Coq's default unification algorithm fails. *)
  Global Instance inv_pointsto_own_proper l v :
    Proper (pointwise_relation _ iff ==> (≡)) (inv_pointsto_own l v).
  Proof.
    intros I1 I2 ?. rewrite /inv_pointsto_own. do 2 f_equiv.
    apply: singletonM_proper. f_equiv. by apply: to_agree_proper.
  Qed.
  Global Instance inv_pointsto_proper l :
    Proper (pointwise_relation _ iff ==> (≡)) (inv_pointsto l).
  Proof.
    intros I1 I2 ?. rewrite /inv_pointsto. do 2 f_equiv.
    apply: singletonM_proper. f_equiv. by apply: to_agree_proper.
  Qed.

  Global Instance inv_heap_inv_persistent : Persistent (inv_heap_inv).
  Proof. apply _. Qed.

  Global Instance inv_pointsto_persistent l I : Persistent (l ↦_I □).
  Proof. apply _. Qed.

  Global Instance inv_pointsto_timeless l I : Timeless (l ↦_I □).
  Proof. apply _. Qed.

  Global Instance inv_pointsto_own_timeless l v I : Timeless (l ↦_I v).
  Proof. apply _. Qed.

  (** * Public lemmas *)

  Lemma make_inv_pointsto l v I E :
    ↑inv_heapN ⊆ E →
    I v →
    inv_heap_inv -∗ l ↦ v ={E}=∗ l ↦_I v.
  Proof.
    iIntros (HN HI) "#Hinv Hl".
    iMod (inv_acc_timeless _ inv_heapN with "Hinv") as "[HP Hclose]"; first done.
    iDestruct "HP" as (h) "[H● HsepM]".
    destruct (h !! l) as [v'| ] eqn: Hlookup.
    - (* auth map contains l --> contradiction *)
      iDestruct (big_sepM_lookup with "HsepM") as "[_ Hl']"; first done.
      by iDestruct (pointsto_valid_2 with "Hl Hl'") as %[??].
    - iMod (own_update with "H●") as "[H● H◯]".
      { apply lookup_to_inv_heap_None in Hlookup.
        apply (auth_update_alloc _
          (to_inv_heap (<[l:=(v,I)]> h)) (to_inv_heap ({[l:=(v,I)]}))).
        rewrite to_inv_heap_insert to_inv_heap_singleton.
        by apply: alloc_singleton_local_update. }
      iMod ("Hclose" with "[H● HsepM Hl]").
      + iExists _.
        iDestruct (big_sepM_insert _ _ _ (_,_) with "[$HsepM $Hl]")
          as "HsepM"; auto with iFrame.
      + iModIntro. by rewrite /inv_pointsto_own to_inv_heap_singleton.
  Qed.

  Lemma inv_pointsto_own_inv l v I : l ↦_I v -∗ l ↦_I □.
  Proof.
    iApply own_mono; apply auth_frag_mono. rewrite singleton_included Some_included_total pair_included.
    split; [apply: ucmra_unit_least|done].
  Qed.

  (** An accessor to make use of [inv_pointsto_own].
    This opens the invariant *before* consuming [inv_pointsto_own] so that you can use
    this before opening an atomic update that provides [inv_pointsto_own]!. *)
  Lemma inv_pointsto_own_acc_strong' E :
    ↑inv_heapN ⊆ E →
    inv_heap_inv ={E, E ∖ ↑inv_heapN}=∗ ∀ l v I, l ↦_I v -∗
      (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦ w ==∗
        inv_pointsto_own l w I ∗ |={E ∖ ↑inv_heapN, E}=> True)).
  Proof.
    iIntros (HN) "#Hinv".
    iMod (inv_acc_timeless _ inv_heapN _ with "Hinv") as "[HP Hclose]"; first done.
    iIntros "!>" (l v I) "Hl_inv".
    iDestruct "HP" as (h) "[H● HsepM]".
    iDestruct (inv_pointsto_own_lookup_Some with "Hl_inv H●") as %(I'&?&HI').
    setoid_rewrite HI'.
    iDestruct (big_sepM_delete with "HsepM") as "[[HI Hl] HsepM]"; first done.
    iIntros "{$HI $Hl}" (w ?) "Hl".
    iMod (own_update_2 with "H● Hl_inv") as "[H● H◯]".
    { apply (auth_update _ _ (<[l := (Excl' w, to_agree I')]> (to_inv_heap h))
             {[l := (Excl' w, to_agree I)]}).
      apply: singleton_local_update.
      { by apply lookup_to_inv_heap_Some. }
      apply: prod_local_update_1. apply: option_local_update.
      apply: exclusive_local_update. done. }
    iDestruct (big_sepM_insert _ _ _ (w, I') with "[$HsepM $Hl //]") as "HsepM".
    { apply lookup_delete. }
    rewrite insert_delete_insert -to_inv_heap_insert. iIntros "!> {$H◯}".
    iApply ("Hclose" with "[H● HsepM]"). iExists _; by iFrame.
  Qed.

  (** Derive a more standard accessor. *)
  Lemma inv_pointsto_own_acc' E l v I:
    ↑inv_heapN ⊆ E →
    inv_heap_inv -∗ l ↦_I v ={E, E ∖ ↑inv_heapN}=∗
      (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦ w ={E ∖ ↑inv_heapN, E}=∗ l ↦_I w)).
  Proof.
    iIntros (?) "#Hinv Hl".
    iMod (inv_pointsto_own_acc_strong' with "Hinv") as "Hacc"; first done.
    iDestruct ("Hacc" with "Hl") as "(HI & Hl & Hclose)".
    iIntros "!> {$HI $Hl}" (w) "HI Hl".
    iMod ("Hclose" with "HI Hl") as "[$ $]".
  Qed.

  Lemma inv_pointsto_acc' l I E :
    ↑inv_heapN ⊆ E →
    inv_heap_inv -∗ l ↦_I □ ={E, E ∖ ↑inv_heapN}=∗
    ∃ v, ⌜I v⌝ ∗ l ↦ v ∗ (l ↦ v ={E ∖ ↑inv_heapN, E}=∗ ⌜True⌝).
  Proof.
    iIntros (HN) "#Hinv Hl_inv".
    iMod (inv_acc_timeless _ inv_heapN _ with "Hinv") as "[HP Hclose]"; first done.
    iModIntro.
    iDestruct "HP" as (h) "[H● HsepM]".
    iDestruct (inv_pointsto_lookup_Some with "Hl_inv H●") as %(v&I'&?&HI').
    iDestruct (big_sepM_lookup_acc with "HsepM") as "[[#HI Hl] HsepM]"; first done.
    setoid_rewrite HI'.
    iExists _. iIntros "{$HI $Hl} Hl".
    iMod ("Hclose" with "[H● HsepM Hl]"); last done.
    iExists _. iFrame "H●". iApply ("HsepM" with "[$Hl //]").
  Qed.

End inv_heap.

#[export] Typeclasses Opaque inv_heap_inv inv_pointsto inv_pointsto_own.

Section lifting.
Context `{!heapGS_gen hlc Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

Lemma wp_lb_init s E e Φ :
  TCEq (to_val e) None →
  (steps_lb 0 -∗ WP e @ s; E {{ v, Φ v }}) -∗
  WP e @ s; E {{ Φ }}.
Proof.
  (** TODO: We should try to use a generic lifting lemma (and avoid [wp_unfold])
  here, since this breaks the WP abstraction. *)
  rewrite !wp_unfold /wp_pre /=. iIntros (->) "Hwp".
  iIntros (σ1 ns κ κs m) "(Hσ & Hκ & Hsteps)".
  iDestruct (steps_lb_get with "Hsteps") as "#Hlb".
  iDestruct (steps_lb_le _ 0 with "Hlb") as "Hlb0"; [lia|].
  iSpecialize ("Hwp" with "Hlb0"). iApply ("Hwp" $! σ1 ns κ κs m). iFrame "∗#%".
Qed.

Lemma wp_lb_update s n E e Φ :
  TCEq (to_val e) None →
  steps_lb n -∗
  WP e @ s; E {{ v, steps_lb (S n) -∗ Φ v }} -∗
  WP e @ s; E {{ Φ }}.
Proof.
  (** TODO: We should try to use a generic lifting lemma (and avoid [wp_unfold])
  here, since this breaks the WP abstraction. *)
  rewrite !wp_unfold /wp_pre /=. iIntros (->) "Hlb Hwp".
  iIntros (σ1 ns κ κs m) "(Hσ & Hκ & Hsteps)".
  iDestruct (steps_lb_valid with "Hsteps Hlb") as %?.
  iMod ("Hwp" $! σ1 ns κ κs m with "[$Hσ $Hκ $Hsteps]") as "[%Hs Hwp]".
  iModIntro. iSplit; [done|].
  iIntros (e2 σ2 efs Hstep) "Hcred".
  iMod ("Hwp" with "[//] Hcred") as "Hwp".
  iIntros "!> !>". iMod "Hwp" as "Hwp". iIntros "!>".
  iApply (step_fupdN_wand with "Hwp").
  iIntros "Hwp". iMod "Hwp" as "(H & Hwp & $)".
  iDestruct "H" as "($ & $ & Hsteps)".
  iDestruct (steps_lb_get with "Hsteps") as "#HlbS".
  iDestruct (steps_lb_le _ (S n) with "HlbS") as "#HlbS'"; [lia|].
  iModIntro. iFrame "Hsteps".
  iApply (wp_wand with "Hwp"). iIntros (v) "HΦ". by iApply "HΦ".
Qed.

Lemma wp_step_fupdN_lb s n E1 E2 e P Φ :
  TCEq (to_val e) None →
  E2 ⊆ E1 →
  steps_lb n -∗
  (|={E1∖E2,∅}=> |={∅}▷=>^(S n) |={∅,E1∖E2}=> P) -∗
  WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗
  WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (He HE) "Hlb HP Hwp".
  iApply wp_step_fupdN; [done|].
  iSplit; [|by iFrame].
  iIntros (σ ns κs nt) "(? & ? & Hsteps)".
  iDestruct (steps_lb_valid with "Hsteps Hlb") as %Hle.
  iApply fupd_mask_intro; [set_solver|].
  iIntros "_". iPureIntro. rewrite /num_laters_per_step /=. lia.
Qed.

(** Recursive functions: we do not use this lemmas as it is easier to use Löb
induction directly, but this demonstrates that we can state the expected
reasoning principle for recursive functions, without any visible ▷. *)
Lemma wp_rec_löb s E f x e Φ Ψ :
  □ ( □ (∀ v, Ψ v -∗ WP (rec: f x := e)%V v @ s; E {{ Φ }}) -∗
     ∀ v, Ψ v -∗ WP (subst' x v (subst' f (rec: f x := e) e)) @ s; E {{ Φ }}) -∗
  ∀ v, Ψ v -∗ WP (rec: f x := e)%V v @ s; E {{ Φ }}.
Proof.
  iIntros "#Hrec". iLöb as "IH". iIntros (v) "HΨ".
  iApply lifting.wp_pure_step_later; first done.
  iIntros "!> _". iApply ("Hrec" with "[] HΨ"). iIntros "!>" (w) "HΨ".
  iApply ("IH" with "HΨ").
Qed.

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "He HΦ". iApply wp_lift_atomic_base_step; [done|].
  iIntros (σ1 ns κ κs nt) "(? & ? & Hsteps)".
  iModIntro. iSplit; first by eauto with base_step.
  iIntros "!>" (v2 σ2 efs Hstep) "_"; inv_base_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iFrame. by iFrame "∗#%".
Qed.

Lemma twp_fork s E e Φ :
  WP e @ s; ⊤ [{ _, True }] -∗ Φ (LitV LitUnit) -∗ WP Fork e @ s; E [{ Φ }].
Proof.
  iIntros "He HΦ". iApply twp_lift_atomic_base_step; [done|].
  iIntros (σ1 ns κs nt) "(? & ? & Hsteps)".
  iModIntro. iSplit; first by eauto with base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iFrame. done.
Qed.

(** Heap *)
Lemma inv_pointsto_own_acc_strong E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv ={E, E ∖ ↑inv_heapN}=∗ ∀ l v I, l ↦_I v -∗
    (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦ w ==∗
      inv_pointsto_own l w I ∗ |={E ∖ ↑inv_heapN, E}=> True)).
Proof.
  iIntros (?) "#Hinv".
  iMod (inv_pointsto_own_acc_strong' with "Hinv") as "Hacc"; first done.
  iIntros "!>" (l v I) "Hl". iDestruct ("Hacc" with "Hl") as "(% & Hl & Hclose)".
  iFrame "%∗".
Qed.

Lemma inv_pointsto_own_acc E l v I:
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦_I v ={E, E ∖ ↑inv_heapN}=∗
    (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦ w ={E ∖ ↑inv_heapN, E}=∗ l ↦_I w)).
Proof.
  iIntros (?) "#Hinv Hl".
  iMod (inv_pointsto_own_acc' with "Hinv Hl") as "(% & Hl & Hclose)"; first done.
  iFrame "%∗". done.
Qed.

Lemma inv_pointsto_acc l I E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦_I □ ={E, E ∖ ↑inv_heapN}=∗
    ∃ v, ⌜I v⌝ ∗ l ↦ v ∗ (l ↦ v ={E ∖ ↑inv_heapN, E}=∗ ⌜True⌝).
Proof.
  iIntros (?) "#Hinv Hl".
  iMod (inv_pointsto_acc' with "Hinv Hl") as (v) "(% & Hl & Hclose)"; [done|].
  iIntros "!>". iExists (v). iFrame "%∗".
Qed.

(** Useful rules for heap freeable predicates *)

Lemma twp_allocN s E v n :
  (0 < n)%Z →
  [[{ True }]] AllocN (Val $ LitV $ LitInt $ FinInt $ n) (Val v) @ s; E
  [[{ (l : blk), RET LitV (LitLoc l); †l…(Z.to_nat n) ∗ l ↦∗ replicate (Z.to_nat n) v }]].
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Hκs & Hsteps)". iModIntro.
  iSplit; first by destruct n; auto with lia base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (heap_alloc with "Hσ") as "[Hσ Hl]"; [try done..|].
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. do 2 (iSplit; first done). iFrame "∗#%". iApply ("HΦ" with "Hl").
Qed.

Lemma wp_allocN s E v n :
  (0 < n)%Z →
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ FinInt $ n) (Val v) @ s; E
  {{{ (l : blk), RET LitV (LitLoc l); †l…(Z.to_nat n) ∗ l ↦∗ replicate (Z.to_nat n) v }}}.
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply (twp_wp_step with "HΦ").
  iApply twp_allocN; [by auto..|]; iIntros (l) "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_alloc s E v :
  [[{ True }]] Alloc (Val v) @ s; E [[{ (l : blk), RET LitV (LitLoc l); l ↦ v ∗ †l…1}]].
Proof.
  iIntros (Φ) "_ HΦ". iApply twp_allocN; [auto with lia..|].
  iIntros (l) "/= [†l ?]". rewrite array_singleton. iApply "HΦ"; iFrame.
Qed.
Lemma wp_alloc s E v :
  {{{ True }}} Alloc (Val v) @ s; E {{{ (l : blk), RET LitV (LitLoc l); l ↦ v ∗ †l…1 }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply (twp_wp_step with "HΦ").
  iApply twp_alloc; [by auto..|]; iIntros (l) "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_free s E (n:Z) l vl :
  n = length vl →
  [[{ l ↦∗ vl ∗ †l…(length vl) }]]
    Free (Val $ LitV $ LitInt $ FinInt n) (Val $ LitV $ LitLoc l) @ s; E
  [[{ RET LitV LitUnit; True }]].
Proof.
  iIntros (? Φ) "[Hl †l] HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Hκs & Hsteps)".
  iMod (heap_free _ _ _ n with "Hσ Hl †l") as "(% & % & Hσ)"=>//.
  iModIntro. iSplit; first by eauto with base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. do 2 (iSplit; first done).
  iFrame "∗#%". by iApply "HΦ".
Qed.
Lemma wp_free s E (n:Z) l vl :
  n = length vl →
  {{{ ▷ (l ↦∗ vl ∗ †l…(length vl)) }}}
    Free (Val $ LitV $ LitInt $ FinInt n) (Val $ LitV (LitLoc l)) @ s; E
  {{{ RET LitV LitUnit; True }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_free with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_load s E l dq v :
  [[{ l ↦{dq} v }]] Load (Val $ LitV $ LitLoc l) @ s; E [[{ RET v; l ↦{dq} v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Hκs & Hsteps)". iModIntro.
  iDestruct (heap_read with "Hσ Hl") as %?.
  iSplit; first by eauto with base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iSplit; [done|]. iSplit; [done|]. iFrame.
  by iApply "HΦ".
Qed.
Lemma wp_load s E l dq v :
  {{{ ▷ l ↦{dq} v }}} Load (Val $ LitV $ LitLoc l) @ s; E {{{ RET v; l ↦{dq} v }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_load with "H"). iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_store s E l v' v :
  [[{ l ↦ v' }]] Store (Val $ LitV $ LitLoc l) (Val v) @ s; E
  [[{ RET LitV LitUnit; l ↦ v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Hκs & Hsteps)".
  iDestruct (heap_read_1 with "Hσ Hl") as %?.
  iMod (heap_write with "Hσ Hl") as "[Hσ Hl]".
  iModIntro; iSplit; first by eauto with base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iSplit; first done. iSplit; first done. iFrame.
  by iApply "HΦ".
Qed.
Lemma wp_store s E l v' v :
  {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_store with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_xchg s E l v' v :
  [[{ l ↦ v' }]] Xchg (Val $ LitV $ LitLoc l) (Val v) @ s; E
  [[{ RET v'; l ↦ v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Hκs & Hsteps)".
  iDestruct (heap_read_1 with "Hσ Hl") as %?.
  iMod (heap_write with "Hσ Hl") as "[Hσ Hl]".
  iModIntro; iSplit; first by eauto with base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iSplit; first done. iSplit; first done. iFrame.
  by iApply "HΦ".
Qed.
Lemma wp_xchg s E l v' v :
  {{{ ▷ l ↦ v' }}} Xchg (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET v'; l ↦ v }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_xchg with "H"); [by auto..|]. iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_fail s E l dq v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  [[{ l ↦{dq} v' }]] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  [[{ RET PairV v' (LitV $ LitBool false); l ↦{dq} v' }]].
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κsg nt) "(Hσ & Hκs & Hsteps)". iModIntro.
  iDestruct (heap_read with "Hσ Hl") as %?.
  iSplit; first by eauto with base_step.
  iIntros (κ v2' σ2 efs Hstep); inv_base_step.
  rewrite bool_decide_false //.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro; iSplit; first done. iSplit; first done. iFrame.
  by iApply "HΦ".
Qed.
Lemma wp_cmpxchg_fail s E l dq v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦{dq} v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{dq} v' }}}.
Proof.
  iIntros (?? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_fail with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  [[{ l ↦ v' }]] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  [[{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }]].
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Hκs & Hsteps)".
  iDestruct (heap_read_1 with "Hσ Hl") as %?.
  iMod (heap_write with "Hσ Hl") as "[Hσ Hl]".
  iModIntro; iSplit; first by eauto with base_step.
  iIntros (κ v2' σ2 efs Hstep); inv_base_step.
  rewrite bool_decide_true //.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iSplit; first done. iSplit; first done. iFrame.
  by iApply "HΦ".
Qed.
Lemma wp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦ v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }}}.
Proof.
  iIntros (?? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_suc with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_faa s E l i1 i2 :
  [[{ l ↦ LitV (LitInt $ FinInt i1) }]] FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt $ FinInt i2) @ s; E
  [[{ RET LitV (LitInt $ FinInt i1); l ↦ LitV (LitInt $ FinInt (i1 + i2)) }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Hκs & Hsteps)".
  iDestruct (heap_read_1 with "Hσ Hl") as %?.
  iMod (heap_write with "Hσ Hl") as "[Hσ Hl]".
  iModIntro; iSplit; first by eauto with base_step.
  iIntros (κ e2 σ2 efs Hstep); inv_base_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. do 2 (iSplit; first done). iFrame.
  by iApply "HΦ".
Qed.
Lemma wp_faa s E l i1 i2 :
  {{{ ▷ l ↦ LitV (LitInt $ FinInt i1) }}} FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt $ FinInt i2) @ s; E
  {{{ RET LitV (LitInt $ FinInt i1); l ↦ LitV (LitInt $ FinInt (i1 + i2)) }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_faa with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma wp_new_proph s E :
  {{{ True }}}
    NewProph @ s; E
  {{{ pvs p, RET (LitV (LitProphecy p)); proph p pvs }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κ κs nt) "(Hσ & HR & Hsteps)". iModIntro.
  iSplit; first by eauto with base_step.
  iIntros "!>" (v2 σ2 efs Hstep) "_". inv_base_step.
  rename select proph_id into p.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iMod (proph_map_new_proph p with "HR") as "[HR Hp]"; first done.
  iModIntro; iSplit; first done. iFrame.
  by iApply "HΦ".
Qed.

(* In the following, strong atomicity is required due to the fact that [e] must
be able to make a head step for [Resolve e _ _] not to be (head) stuck. *)

Lemma resolve_reducible e σ (p : proph_id) v :
  Atomic StronglyAtomic e → reducible e σ →
  reducible (Resolve e (Val (LitV (LitProphecy p))) (Val v)) σ.
Proof.
  intros A (κ & e' & σ' & efs & H).
  exists (κ ++ [(p, (default v (to_val e'), v))]), e', σ', efs.
  eapply (Ectx_step []); try done.
  assert (∃w, Val w = e') as [w <-].
  { unfold Atomic in A. apply (A σ e' κ σ' efs) in H. unfold is_Some in H.
    destruct H as [w H]. exists w. simpl in H. by apply (of_to_val _ _ H). }
  simpl. constructor. by apply prim_step_to_val_is_base_step.
Qed.

Lemma step_resolve e vp vt σ1 κ e2 σ2 efs :
  Atomic StronglyAtomic e →
  prim_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs →
  base_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs.
Proof.
  intros A [Ks e1' e2' Hfill -> step]. simpl in *.
  induction Ks as [|K Ks _] using rev_ind.
  + simpl in *. subst. inv_base_step. by constructor.
  + rewrite fill_app /= in Hfill. destruct K; inversion Hfill; subst; clear Hfill.
    - rename select ectx_item into Ki.
      assert (fill_item Ki (fill Ks e1') = fill (Ks ++ [Ki]) e1') as Eq1;
        first by rewrite fill_app.
      assert (fill_item Ki (fill Ks e2') = fill (Ks ++ [Ki]) e2') as Eq2;
        first by rewrite fill_app.
      rewrite fill_app /=. rewrite Eq1 in A.
      assert (is_Some (to_val (fill (Ks ++ [Ki]) e2'))) as H.
      { apply (A σ1 _ κ σ2 efs). eapply (Ectx_step (Ks ++ [Ki])); done. }
      destruct H as [v H]. apply to_val_fill_some in H. by destruct H, Ks.
    - rename select (of_val vp = _) into Hvp.
      assert (to_val (fill Ks e1') = Some vp) as Hfillvp by rewrite -Hvp //.
      apply to_val_fill_some in Hfillvp as [-> ->]. inv_base_step.
    - rename select (of_val vt = _) into Hvt.
      assert (to_val (fill Ks e1') = Some vt) as Hfillvt by rewrite -Hvt //.
      apply to_val_fill_some in Hfillvt as [-> ->]. inv_base_step.
Qed.

Lemma wp_resolve s E e Φ (p : proph_id) v (pvs : list (val * val)) :
  Atomic StronglyAtomic e →
  to_val e = None →
  proph p pvs -∗
  WP e @ s; E {{ r, ∀ pvs', ⌜pvs = (r, v)::pvs'⌝ -∗ proph p pvs' -∗ Φ r }} -∗
  WP Resolve e (Val $ LitV $ LitProphecy p) (Val v) @ s; E {{ Φ }}.
Proof.
  (* TODO we should try to use a generic lifting lemma (and avoid [wp_unfold])
     here, since this breaks the WP abstraction. *)
  iIntros (A He) "Hp WPe". rewrite !wp_unfold /wp_pre /= He. simpl in *.
  iIntros (σ1 ns κ κs nt) "(Hσ & Hκ & Hsteps)".
  destruct κ as [|[p' [w' v']] κ' _] using rev_ind.
  - iMod ("WPe" $! σ1 ns [] κs nt with "[$Hσ $Hκ $Hsteps]") as "[Hs WPe]".
    iModIntro. iSplit.
    { iDestruct "Hs" as "%". iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). exfalso. apply step_resolve in step; last done.
    inv_base_step. match goal with H: ?κs ++ [_] = [] |- _ => by destruct κs end.
  - rewrite -assoc.
    iMod ("WPe" $! σ1 ns _ _ nt with "[$Hσ $Hκ $Hsteps]") as "[Hs WPe]".
    iModIntro. iSplit.
    { iDestruct "Hs" as %?. iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step) "Hcred". apply step_resolve in step; last done.
    inv_base_step; simplify_list_eq.
    iMod ("WPe" $! (Val w') σ2 efs with "[%] Hcred") as "WPe".
    { by eexists [] _ _. }
    iModIntro. iNext. iMod "WPe" as "WPe". iModIntro.
    iApply (step_fupdN_wand with "WPe").
    iIntros ">[($ & Hκ & $) WPe]".
    iMod (proph_map_resolve_proph p' (w',v') κs with "[$Hκ $Hp]") as (vs' ->) "[$ HPost]".
    iModIntro. rewrite !wp_unfold /wp_pre /=. iDestruct "WPe" as "[HΦ $]".
    iMod "HΦ". iModIntro. by iApply "HΦ".
Qed.

End lifting.
