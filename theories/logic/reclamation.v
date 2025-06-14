From smr.algebra Require Import coPset.
From smr.logic Require Import token2.
From iris.base_logic.lib Require Import invariants ghost_map.
From smr.base_logic.lib Require Import coP_ghost_map ghost_vars coP_cancellable_invariants mono_list.
From smr.lang Require Import proofmode notation.
From smr Require Import helpers smr_common.

From iris.prelude Require Import options.

From smr Require Import helpers.

(* Shield id 1%positive is reserved for Managed *)
Definition gid : positive := 1.
(* Shield id from slot index, for ghost map *)
Definition ssid (s : nat) : positive := Pos.succ $ Pos.of_succ_nat s.
(* Shield id from slot index, for tokens and vars2 *)
Definition sid := Pos.of_succ_nat.

(* Shield ids of slots [0..s] (exclusive) *)
Definition sids_to (s : nat) : coPset :=
  list_to_set (sid <$> (seq 0 s)).
(* Set of shield ids of slots [s..∞]. Example: [sids_from (length slist)] *)
Definition sids_from (s : nat) : coPset :=
  ⊤ ∖ sids_to s.

Definition sids_from' (s : nat) : coPneset :=
  coPneset_complement (list_to_set (sid <$> (seq 0 s))).

(* Sets of shields ids [s1..s2] (exclusive) *)
Definition sids_range (s1 s2 : nat) : coPset :=
  list_to_set (sid <$> (seq s1 (s2 - s1))).

Section token.
Context `{!token2G Σ}.

(* tokens for pointer ids [I] and shield ids [S] *)
Definition toks γ (I S : coPset) : iProp Σ :=
  token2 γ I S.
(* a token for pointer id [i] and *slot index* [s] *)
Definition stok γ (i : positive) (s : nat) : iProp Σ :=
  toks γ {[i]} {[sid s]}.
Definition stoks γ (I : coPset) (s : nat) : iProp Σ :=
  toks γ I {[sid s]}.
(* the special token owned by [Managed] *)
Definition gtok γ (i : positive) : iProp Σ :=
  toks γ {[i]} {[gid]}.

End token.

Class reclamationG Σ := ReclamationG {
  #[export] recl_tokenG :: token2G Σ;
  (* id ↪□ (allocation, cinv gname) *)
  #[export] recl_infoG :: ghost_mapG Σ positive (alloc * gname); (* γinfo *)
  #[export] recl_dataG :: ghost_mapG Σ positive gname; (* γdata *)
  (* allocation status *)
  #[export] recl_ptrsG :: coP_ghost_mapG Σ blk positive; (* γptrs *)
  #[export] recl_cinvG :: coP_cinvG Σ; (* γtok *)
  #[export] recl_varsG :: ghost_varsG Σ bool; (* γU *)
  #[export] recl_vars2G :: ghost_vars2G Σ bool; (* γV, γR *)
}.

Definition reclamationΣ : gFunctors :=
  #[ token2Σ;
     ghost_mapΣ positive (alloc * gname);
     ghost_mapΣ positive gname;
     (* mono_listΣ positive (blk * gname * gname); *)
     coP_ghost_mapΣ blk positive;
     coP_cinvΣ;
     ghost_varsΣ bool;
     ghost_vars2Σ bool ].

Global Instance subG_reclamationΣ Σ :
  subG reclamationΣ Σ → reclamationG Σ.
Proof. solve_inG. Qed.

Section defs.
Context `{!reclamationG Σ, !heapGS Σ}.

Context (base_mgmtN base_ptrsN : namespace) (DISJ : base_mgmtN ## base_ptrsN).
(* Managed ghost names. Add to reclamationG? *)
Context (γtok γinfo γdata γptrs γU γR γV : gname).

Implicit Types
  (γc : gname) (R : resource Σ).

(* Hack: we have @ "base" so that namespaces used by rcu_base.v have "base"
  after the namespace given by rcu_{simple,traversal} *)
Definition exchN (p : blk) (i : positive) := base_mgmtN .@ "base" .@ "exch" .@ p .@ i.
Definition resN (p : blk) (i : positive) := base_ptrsN .@ p .@ "base" .@ i.

(* Exchanges a token for pointer ownership *)
Definition Exchanges' (p : blk) (i : positive) (γc_i : gname) : iProp Σ :=
  ( (* exchange cancelled; holds all the tokens *)
    toks γtok {[i]} ⊤
  ) ∨
  ( (* holds a finite set of tokens *)
    ∃ (ss : gset nat),
    p ↪c[γptrs]{coPneset_complement (set_map ssid ss ∪ {[gid]})} i ∗
    coP_cinv_own γc_i (coPneset_complement (set_map ssid ss ∪ {[gid]})) ∗
    toks γtok {[i]} (gset_to_coPset (set_map sid ss))
  ) ∨
  ( (* holds a cofinite set, but not ⊤, of tokens *)
    ∃ (ssc : gset nat) (cossc : coPneset),
    ⌜coPneset_coPset cossc = gset_to_coPset (set_map ssid ssc)⌝ ∗
    p ↪c[γptrs]{cossc} i ∗
    coP_cinv_own γc_i cossc ∗
    toks γtok {[i]} (⊤ ∖ gset_to_coPset (set_map sid ssc))
  ).

Definition Exchanges (p : blk) (i : positive) (γc_i : gname) : iProp Σ :=
  inv (exchN p i) (Exchanges' p i γc_i).

Definition ResourceCInv p i γc_i size_i R :=
  coP_cinv (resN p i) γc_i (∃ vl, ⌜length vl = size_i⌝ ∗ R p vl i ∗ p ↦∗ vl).

(* Transforms block resource on logical name to block resource on the pointer id. *)
Definition wrap_resource R data_i : resource Σ :=
  (λ p vl i, i ↪[γdata]□ data_i ∗ R p vl data_i)%I.

Definition NodeInfoBase (p : blk) (i : positive) (size_i : nat) R : iProp Σ :=
  ∃ γc_i,
    i ↪[γinfo]□ ({| addr := p; len := size_i |}, γc_i) ∗
    Exchanges p i γc_i ∗
    ResourceCInv p i γc_i size_i R.

(* NOTE: To avoid laters, separate out [Exchanges] and [ResourceCInv] as [NodeInfo]. *)
Definition ManagedBase (p : blk) (i : positive) (size_i : nat) R : iProp Σ :=
  ∃ γc_i,
    coP_cinv_own γc_i {[gid]} ∗
    i ↪[γinfo]□ ({| addr := p; len := size_i |}, γc_i) ∗
    p ↪c[γptrs]{{[gid]}} i ∗
    Exchanges p i γc_i ∗
    ResourceCInv p i γc_i size_i R ∗
    (* TODO: Why need space? Might be do to cghost_map above *)
    i ↦p[γU] {# 1/2 } false ∗
    ({[i]},⊤) ↦P2[γR] {# 1/2 } false.

Definition RetiredBase (p : blk) (i : positive) (size_i : nat) R : iProp Σ :=
  ∃ γc_i,
    coP_cinv_own γc_i {[gid]} ∗
    i ↪[γinfo]□ ({| addr := p; len := size_i |}, γc_i) ∗
    p ↪c[γptrs]{{[gid]}} i ∗
    Exchanges p i γc_i ∗
    ResourceCInv p i γc_i size_i R ∗
    i ↦p[γU]□ true ∗
    ({[i]},⊤) ↦P2[γR] {# 1/2 } false.

Definition Retired (p : blk) (i : positive) (size_i : nat) R : iProp Σ :=
  ∃ data_i, RetiredBase p i size_i (wrap_resource R data_i).

Definition ReclaimingBase (p : blk) (i : positive) (size_i : nat) R : iProp Σ :=
  ∃ γc_i,
    coP_cinv_own γc_i {[gid]} ∗
    i ↪[γinfo]□ ({| addr := p; len := size_i |}, γc_i) ∗
    p ↪c[γptrs]{{[gid]}} i ∗
    Exchanges p i γc_i ∗
    ResourceCInv p i γc_i size_i R ∗
    i ↦p[γU]□ true.

Definition Reclaiming (p : blk) (i : positive) (size_i : nat) R : iProp Σ :=
  ∃ data_i, ReclaimingBase p i size_i (wrap_resource R data_i).

(* [Retired] becomes [Reclaimed]. *)
Definition Reclaimed (i : positive) : iProp Σ :=
  i ↦p[γU]□ true ∗
  ({[i]},⊤) ↦P2[γR]□ true.

Definition ProtectedBase (s : nat) (i : positive) (p : blk) R size_i : iProp Σ :=
  ∃ γc_i,
    i ↪[γinfo]□ ({| addr := p; len := size_i |}, γc_i) ∗
    p ↪c[γptrs]{{[ssid s]}} i ∗
    coP_cinv_own γc_i {[ssid s]} ∗
    Exchanges p i γc_i ∗
    ResourceCInv p i γc_i size_i R ∗
    (i, sid s) ↦p2[γV] {# 1/2 } true.

End defs.

Section lemmas.
Context `{!reclamationG Σ, !heapGS Σ}.

(* sid, ssid, gid *)

Lemma ssid_neq_gid n : ssid n ≠ gid.
Proof. unfold ssid, gid. lia. Qed.

Global Instance sid_injective : Inj (=) (=) sid.
Proof. unfold sid. apply _. Qed.

Global Instance ssid_injective : Inj (=) (=) ssid.
Proof. unfold ssid. intro. lia. Qed.

Lemma sid_to_idx (s : positive) : ∃ n, s = sid n.
Proof. unfold sid. exists (Nat.pred (Pos.to_nat s)). lia. Qed.

(* sids_to *)

Lemma sids_to_0 : sids_to 0 = ∅.
Proof. done. Qed.

Lemma sids_from_0 : sids_from 0 = ⊤.
Proof. rewrite /sids_from sids_to_0. set_solver. Qed.

Lemma sids_from'_0 : sids_from' 0 = ⊤.
Proof. rewrite /sids_from' coPneset_eq. set_solver. Qed.

Lemma sids_to_S n : sids_to (S n) = sids_to n ∪ {[sid n]}.
Proof. unfold sids_to. rewrite seq_S. set_solver. Qed.

Lemma sids_to_gset n :
  gset_to_coPset (list_to_set (sid <$> seq 0 n)) = sids_to n.
Proof.
  unfold sids_to. induction n as [|n IH]. { set_solver. }
  rewrite -Nat.add_1_r seq_app fmap_app !list_to_set_app_L.
  rewrite gset_to_coPset_union. rewrite IH. f_equal.
  rewrite Nat.add_0_l.
  assert (list_to_set (sid <$> seq n 1) = ({[sid n]} : gset positive)) as ->.
  { simpl. set_solver. } rewrite gset_to_coPset_singleton. set_solver.
Qed.

Lemma sids_range_fold s1 s :
  list_to_set (sid <$> (seq s1 s)) = sids_range s1 (s1+s).
Proof. unfold sids_range. replace (s1+s-s1) with s by lia. done. Qed.

Lemma sids_to_sids_range n : sids_range 0 n = sids_to n.
Proof. unfold sids_range. replace (n-0) with n by lia. done. Qed.

Lemma NoDup_sids_to_inner n :
  NoDup (sid <$> seq 0 n).
Proof.
  rewrite NoDup_fmap.
  induction n as [|n IH]; [by apply NoDup_nil|].
  rewrite -Nat.add_1_r seq_app NoDup_app.
  split_and!; [done| |by apply NoDup_singleton].
  intros m ElemOf. simpl. rewrite elem_of_seq in ElemOf.
  rewrite elem_of_list_singleton. lia.
Qed.

Lemma sids_to_sid_disjoint m n :
  m ≤ n →
  sids_to m ## {[sid n]}.
Proof.
  induction m; intros; first set_solver.
  rewrite sids_to_S. apply disjoint_union_l. split.
  - apply IHm. lia.
  - apply disjoint_singleton_r, not_elem_of_singleton.
    unfold sid. lia.
Qed.

Lemma sids_to_not_elem_of m n :
  m ≤ n →
  sid n ∉ sids_to m.
Proof. rewrite -disjoint_singleton_r. apply sids_to_sid_disjoint. Qed.

Lemma sids_from_not_elem_of m n :
  n < m →
  sid n ∉ sids_from m.
Proof.
  intros. assert (sid n ∈ sids_to m); last first.
  { rewrite not_elem_of_difference. by right. }
  rewrite elem_of_list_to_set.
  apply elem_of_list_fmap_1, elem_of_seq. lia.
Qed.

Lemma sids_from_sid_disjoint m n :
  n < m →
  sids_from m ## {[sid n]}.
Proof. intros. apply disjoint_singleton_r, sids_from_not_elem_of. lia. Qed.

Lemma sids_from'_sid_disjoint m n :
  n < m →
  sids_from' m ## {[sid n]}.
Proof.
  intros. unfold sids_from'.
  rewrite coPneset_disj_iff. simpl.
  rewrite !sids_to_gset. fold (sids_from m).
  apply sids_from_sid_disjoint. done.
Qed.

Lemma sids_from_S n :
  sids_from n = sids_from (S n) ∪ {[sid n]}.
Proof.
  unfold sids_from. rewrite sids_to_S difference_union_distr_r_L.
  rewrite top_intersection_difference.
  rewrite -(union_difference_L' {[sid n]} (⊤ ∖ sids_to n)); auto.
  rewrite -disjoint_complement.
  symmetry. by apply sids_to_sid_disjoint.
Qed.

Lemma sids_from'_S n :
  sids_from' n = sids_from' (S n) ∪ {[sid n]}.
Proof.
  unfold sids_from'.
  rewrite coPneset_eq coPneset_union_eq -Nat.add_1_r /=.
  rewrite !sids_to_gset Nat.add_1_r.
  fold (sids_from n) (sids_from (S n)).
  apply sids_from_S.
Qed.

Lemma sids_to_sids_from_union n :
  sids_to n ∪ sids_from n = ⊤.
Proof. rewrite /sids_from (comm_L union) -top_union_difference //. Qed.

Lemma sids_to_sids_from_complement n :
  sids_to n = ⊤ ∖ sids_from n.
Proof. unfold sids_from. rewrite difference_difference_r_L; set_solver. Qed.

Lemma sids_range_split (s1 s2 s3 : nat) :
  s1 ≤ s2 ≤ s3 →
  sids_range s1 s3 = sids_range s1 s2 ∪ sids_range s2 s3.
Proof.
  intros. unfold sids_range. rewrite -list_to_set_app_L -fmap_app.
  rewrite (_ : s3 - s1 = (s2 - s1) + (s3 - s2)); last lia.
  have Hs2 : s2 = s1 + (s2 - s1) by lia.
  rewrite [in seq s2 _]Hs2. rewrite -seq_app. rewrite -Hs2. done.
Qed.

Lemma sids_range_empty (s : nat) :
  sids_range s s = ∅.
Proof. unfold sids_range. rewrite Nat.sub_diag //. Qed.

Lemma sids_range_singleton (s : nat) :
  sids_range s (s + 1) = {[sid s]}.
Proof. unfold sids_range. have -> : s + 1 - s = 1 by lia. simpl. set_solver. Qed.

Lemma sids_range_cons (s1 s2 : nat) :
  s1 < s2 →
  sids_range s1 s2 = {[sid s1]} ∪ sids_range (s1 + 1) s2.
Proof. intros. rewrite -sids_range_singleton -sids_range_split //. lia. Qed.

Lemma sids_to_sids_from_disjoint n :
  sids_to n ## sids_from n.
Proof. rewrite sids_to_sids_from_complement. set_solver. Qed.

Lemma sids_range_disjoint s1 s2 s3 s4 :
  s2 ≤ s3 →
  sids_range s1 s2 ## sids_range s3 s4.
Proof.
  intros. unfold sids_range. intro.
  do 2 rewrite elem_of_list_to_set.
  do 2 rewrite elem_of_list_fmap.
  intros [y0 [H0x H0in]] [y1 [H1x H1in]]; subst.
  apply sid_injective in H1x; subst.
  rewrite elem_of_seq in H0in.
  rewrite elem_of_seq in H1in.
  lia.
Qed.

Lemma sids_from_prefix (s1 s2 : nat) :
  s1 ≤ s2 →
  sids_from s1 = sids_range s1 s2 ∪ sids_from s2.
Proof.
  intros. unfold sids_from,sids_to,sids_range.
  rewrite (comm_L union).
  have [s Hs2] : ∃ s, s2 = s1 + s by exists (s2 - s1); lia.
  rewrite Hs2. replace (s1 + s - s1) with s by lia.
  rewrite seq_app fmap_app list_to_set_app_L. rewrite Nat.add_0_l.
  rewrite -difference_difference_l_L.
  rewrite -union_difference_L'; first done.
  rewrite -disjoint_complement.
  do 2 rewrite sids_range_fold.
  symmetry. by apply sids_range_disjoint.
Qed.

(* NOTE: disjoint lemmas are not fully general, but good enough? *)
Lemma sids_range_sids_from_disjoint (s1 s2 : nat) :
  s1 ≤ s2 →
  sids_range s1 s2 ## sids_from s2.
Proof.
  intros. unfold sids_range, sids_from, sids_to. intro.
  rewrite elem_of_list_to_set elem_of_difference.
  rewrite not_elem_of_list_to_set.
  do 2 rewrite elem_of_list_fmap.
  intros [y [-> Hy1]] [_ Hy2]. apply Hy2.
  exists y. split; auto.
  rewrite elem_of_seq. rewrite elem_of_seq in Hy1. lia.
Qed.

Lemma sid_sids_range_disjoint_cons (s1 s2 : nat) :
  {[sid s1]} ## sids_range (s1 + 1) s2.
Proof. rewrite -sids_range_singleton. by apply sids_range_disjoint. Qed.

Lemma sids_range_0_sids_to (s : nat) :
  sids_range 0 s = sids_to s.
Proof. unfold sids_range, sids_to. rewrite Nat.sub_0_r //. Qed.

Lemma sids_from_infinite n :
  set_infinite (sids_from n).
Proof.
  unfold sids_from, sids_to. apply difference_infinite.
  - apply top_infinite.
  - apply list_to_set_finite.
Qed.

Lemma sids_from_nonempty n :
  sids_from n ≠ ∅.
Proof.
  intro. eapply set_not_infinite_finite.
  - apply sids_from_infinite.
  - erewrite H. exists []. set_solver.
Qed.

Lemma big_sepL_sids_range_1 {PROP : bi} (Φ : coPset → PROP) `{!∀ x, Affine (Φ x)} {A}
    (s1 s2 : nat) (slist12 : list A) :
  (∀ E1 E2, E1 ## E2 → Φ E1 ∗ Φ E2 ⊣⊢ Φ (E1 ∪ E2)) →
  length slist12 = s2 - s1 →
  Φ (sids_range s1 s2) -∗ [∗ list] k ↦ _ ∈ slist12, Φ {[sid (s1 + k)]}.
Proof.
  iIntros (Hhomo Hlen) "range12".
  iInduction slist12 as [|? ? IH] forall (s1 s2 Hlen).
  { rewrite big_sepL_nil //. }
  rewrite length_cons in Hlen.
  have LE12 : s1 < s2 by lia.
  have {}Hlen : length slist12 = s2 - (s1 + 1) by lia.
  rewrite big_sepL_cons. rewrite Nat.add_0_r.
  rewrite (sids_range_cons _ _ LE12).
  rewrite -Hhomo; last apply sid_sids_range_disjoint_cons.
  iDestruct "range12" as "[$ range1'2]".
  iSpecialize ("IH" $! (s1+1) s2 with "[%] range1'2"); first done.
  iEval (setoid_rewrite <-(assoc Nat.add)) in "IH". done.
Qed.

Lemma big_sepL_sids_range_2 {PROP : bi} (Φ : coPset → PROP)
    `{!∀ x, Affine (Φ x), !∀ x, Absorbing (Φ x)} {A}
    (s1 s2 : nat) (slist12 : list A) :
  (∀ E1 E2, E1 ## E2 → Φ E1 ∗ Φ E2 ⊣⊢ Φ (E1 ∪ E2)) →
  length slist12 = s2 - s1 →
  slist12 ≠ [] →
  ([∗ list] k ↦ _ ∈ slist12, Φ {[sid (s1 + k)]}) -∗ Φ (sids_range s1 s2).
Proof.
  intros Hhomo Hlen.
  have HH : ([∗ list] k ↦ _ ∈ slist12, Φ {[sid (s1 + k)]}) -∗
            ⌜slist12 = []⌝ ∨ Φ (sids_range s1 s2); last first.
  { iIntros (NE) "X". iDestruct (HH with "X") as "[%|?]"; done. }
  iIntros "range12".
  iInduction slist12 as [|? ? IH] forall (s1 s2 Hlen).
  { rewrite big_sepL_nil //. by iLeft. }
  iRight.
  rewrite length_cons in Hlen.
  have LE12 : s1 < s2 by lia.
  have {}Hlen : length slist12 = s2 - (s1 + 1) by lia.
  rewrite big_sepL_cons. rewrite Nat.add_0_r.
  rewrite (sids_range_cons _ _ LE12).
  rewrite -Hhomo; last apply sid_sids_range_disjoint_cons.
  iDestruct "range12" as "[? range1'2]". (* Should not frame s1 here. *)
  iSpecialize ("IH" $! (s1+1) s2 with "[%] [range1'2]"); first lia.
  { iEval (setoid_rewrite <-(assoc Nat.add)). done. }
  iDestruct "IH" as "[%|$]"; last by iFrame.
  subst slist12. simpl in *. assert (s2 = s1 + 1) as -> by lia.
  replace (sids_range (s1 + 1) (s1 + 1)) with (∅ : coPset); last first.
  { unfold sids_range. rewrite Nat.sub_diag //. }
  rewrite Hhomo; last set_solver. rewrite right_id_L //.
Qed.

(* toks *)

Lemma toks_valid_1 γ E1A E1B E2 :
  E2 ≠ ∅ →
  toks γ E1A E2 -∗ toks γ E1B E2 -∗ ⌜E1A ## E1B⌝.
Proof.
  iIntros (H) "T1 T2".
  iDestruct (token2_valid_1 with "T1 T2") as "%"; auto.
Qed.

Lemma toks_valid_2 γ E1 E2A E2B :
  E1 ≠ ∅ →
  toks γ E1 E2A -∗ toks γ E1 E2B -∗ ⌜E2A ## E2B⌝.
Proof.
  iIntros (H) "T1 T2".
  iDestruct (token2_valid_2 with "T1 T2") as "%"; auto.
Qed.

Lemma toks_union_1 γ E1A E1B E2 :
  E1A ## E1B →
  toks γ E1A E2 ∗ toks γ E1B E2 ⊣⊢ toks γ (E1A ∪ E1B) E2.
Proof.
  intros. iIntros. iSplit.
  - iIntros "[T1 T2]".
    iApply token2_union_1; auto. iFrame.
  - iIntros "T".
    iDestruct (token2_union_1 with "T") as "[T1 T2]"; auto. iFrame.
Qed.

Lemma toks_union_2 γ E1 E2A E2B :
  E2A ## E2B →
  toks γ E1 E2A ∗ toks γ E1 E2B ⊣⊢ toks γ E1 (E2A ∪ E2B).
Proof.
  intros. iIntros. iSplit.
  - iIntros "[T1 T2]".
    iApply token2_union_2; auto. iFrame.
  - iIntros "T".
    iDestruct (token2_union_2 with "T") as "[T1 T2]"; auto. iFrame.
Qed.

Lemma toks_delete_1 γ E1 E2 X :
  X ⊆ E1 →
  toks γ E1 E2 ⊣⊢ toks γ (E1 ∖ X) E2 ∗ toks γ X E2.
Proof. intros. rewrite toks_union_1; last set_solver. by rewrite -union_difference_L'. Qed.

Lemma toks_delete_2 γ E1 E2 X :
  X ⊆ E2 →
  toks γ E1 E2 ⊣⊢ toks γ E1 (E2 ∖ X) ∗ toks γ E1 X.
Proof. intros. rewrite toks_union_2; last set_solver. by rewrite -union_difference_L'. Qed.

Lemma toks_get_empty_1 γ E :
  ⊢ |==> toks γ ∅ E.
Proof. unfold toks. iApply token2_get_empty_1. Qed.

Lemma toks_get_empty_2 γ E :
  ⊢ |==> toks γ E ∅.
Proof. unfold toks. iApply token2_get_empty_2. Qed.

(* exchanges *)

Lemma exchange_toks_give_all γtok γptrs γc_i
    (N : namespace) E (p : blk) (i : positive) :
  ↑exchN N p i ⊆ E →
  Exchanges N γtok γptrs p i γc_i -∗
  toks γtok {[i]} ⊤
  ={E}=∗
  p ↪c[γptrs]{coPneset_complement {[gid]}} i ∗
  coP_cinv_own γc_i (coPneset_complement {[gid]}).
Proof.
  iIntros (?) "#Ex TII".
  iInv "Ex" as ">[Ex'|[Ex'|Ex']]".
  - (* ⊤: contradiction since I have all tokens *)
    iDestruct ((toks_valid_2 _ _ _ ⊤) with "TII Ex'") as "%"; set_solver.
  - (* finite: should be empty, give all, get all *)
    iDestruct "Ex'" as (ss) "(pi & cinv & TIS)".
    iDestruct (toks_valid_2 with "TII TIS") as "%NotIn"; [set_solver|].
    assert (gset_to_coPset (set_map sid ss) = ∅) by set_solver.
    apply gset_to_coPset_empty_inv in H0.
    assert (ss = ∅) by set_solver. subst.
    rewrite set_map_empty union_empty_l_L.
    iSplitR "pi cinv"; iFrame; auto.
  - (* cofinite: contradiction since I have all tokens *)
    iDestruct "Ex'" as (ssc cossc Hco) "(pi & cinv & TIE)".
    iDestruct (toks_valid_2 with "TII TIE") as "%NotIn"; [set_solver|].
    by apply top_disjoint_difference_gset_to_coPset in NotIn.
Qed.

Lemma exchange_stok_give_token_set (ssc : gset nat) (idx : nat) :
  idx ∈ ssc →
  ⊤ ∖ gset_to_coPset (set_map sid ssc) ∪ {[sid idx]} =
  ⊤ ∖ gset_to_coPset (set_map sid (ssc ∖ {[idx]})).
Proof.
  intros.
  rewrite set_map_difference_L gset_to_coPset_difference.
  rewrite set_map_singleton_L gset_to_coPset_singleton.
  rewrite difference_difference_r; auto.
  rewrite singleton_subseteq_l.
  rewrite elem_of_gset_to_coPset elem_of_map. eauto.
Qed.

Lemma exchange_stok_give γtok γptrs γc_i
    (N : namespace) E (p : blk) (i : positive) (idx : nat) :
  ↑exchN N p i ⊆ E →
  Exchanges N γtok γptrs p i γc_i -∗
  stok γtok i idx -∗
  |={E}=> (
    p ↪c[γptrs]{{[ssid idx]}} i ∗
    coP_cinv_own γc_i {[ssid idx]}
  ).
Proof.
  iIntros (?) "#Ex TII".
  iInv "Ex" as ">[Ex'|[Ex'|Ex']]".
  - (* ⊤: contradiction since I have a token *)
    iDestruct ((toks_valid_2 _ _ _ ⊤) with "TII Ex'") as "%"; set_solver.

  - (* finite: add idx to ss *)
    iDestruct "Ex'" as (ss) "(pi & cinv & TIS)".
    iDestruct (toks_valid_2 with "TII TIS") as "%NotIn"; [set_solver|].
    (* give token *)
    iCombine "TIS TII" as "TISi".
    rewrite toks_union_2; auto.
    iModIntro.
    rewrite -(gset_to_coPset_singleton (sid idx)) -gset_to_coPset_union.
    assert (set_map sid ss ∪ {[sid idx]} = set_map sid (ss ∪ {[idx]})) as ->.
    { rewrite set_map_union_L. set_solver. }
    rewrite disjoint_singleton_l in NotIn.
    (* separate pi and cinv *)
    rewrite elem_of_gset_to_coPset in NotIn.
    rewrite (complement_insert (set_map ssid ss ∪ {[gid]}) (ssid idx)); last first.
    { apply not_elem_of_union. split; intro In.
      - apply elem_of_map in In.
        destruct In as [x [IdEQ In]]. apply ssid_injective in IdEQ.
        subst. apply NotIn, elem_of_map; eauto.
      - apply elem_of_singleton in In. by apply ssid_neq_gid in In. }
    rewrite coP_ghost_map_elem_fractional; last first.
      { apply coPneset_disj_elem_of. set_solver. }
    iDestruct "pi" as "[pi spi]".
    rewrite coP_cinv_own_fractional; last first.
      { apply coPneset_disj_elem_of. set_solver. }
    iDestruct "cinv" as "[cinv scinv]".
    (* close *)
    iSplitR "pi cinv"; iFrame; auto.
    iNext. iRight; iLeft. iExists _. iFrame "∗#%".
    rewrite set_map_union_L set_map_singleton_L.
    assert (∀ (X Y Z : gset positive), X ∪ Y ∪ Z = X ∪ Z ∪ Y) as EQ by set_solver.
    rewrite EQ. iFrame.

  - (* cofinite: remove idx from ssc *)
    iDestruct "Ex'" as (ssc cossc Hco) "(pi & cinv & TIE)".
    iDestruct (toks_valid_2 with "TII TIE") as "%NotIn"; [set_solver|].
    assert (idx ∈ ssc) as Hin.
    { destruct (decide (idx ∈ ssc)); auto.
      rewrite disjoint_singleton_l elem_of_complement in NotIn.
      exfalso. apply NotIn.
      rewrite elem_of_gset_to_coPset elem_of_map.
      intro. destruct H0 as [x [Hsid Hx]].
      apply sid_injective in Hsid. set_solver. }

    (* prove non-empty *)
    assert (ssc ≠ ∅) as Hne.
    { intro. subst.
      rewrite set_map_empty gset_to_coPset_empty in Hco.
      exfalso. by eapply coPneset_nonempty. }

    (* give token *)
    iCombine "TIE TII" as "TIEi". rewrite toks_union_2; auto.
    rewrite exchange_stok_give_token_set; auto.
    iModIntro.
    (* close if ssc = {[idx]} *)
    destruct (decide (ssc = {[idx]})).
    { subst.
      rewrite difference_diag_L set_map_empty.
      rewrite gset_to_coPset_empty difference_empty_L.
      rewrite set_map_singleton_L gset_to_coPset_singleton in Hco.
      apply coPneset_is_singleton in Hco. subst.
      iSplitL "TIEi"; iFrame. done. }

    (* get ↪c and cinv *)
    assert (idx ∈ ssc) as Hi.
    { apply disjoint_subset in NotIn as Hsub.
      apply elem_of_subseteq_singleton in Hsub.
      apply elem_of_gset_to_coPset, elem_of_map in Hsub.
      destruct Hsub as [x [Hsidx Hssc]].
      apply sid_injective in Hsidx. by subst. }
    assert (ssc ∖ {[idx]} ≠ ∅) as Hine.
    { intro. apply empty_difference_subseteq_L in H0.
      by apply subset_of_singleton in H0 as [H0|H0]. }
    remember (gset_to_coPset (set_map ssid (ssc ∖ {[idx]}))) as co1.
    assert (co1 ≠ ∅) as co1ne.
    { intro. subst.
      apply gset_to_coPset_empty_inv in H0. set_solver. }
    apply coPneset_construct in co1ne as [co1E Hco1E].
    assert (cossc = co1E ∪ {[ssid idx]}).
    { apply coPneset_eq. simpl.
      rewrite Hco Hco1E Heqco1.
      rewrite -gset_to_coPset_singleton -gset_to_coPset_union.
      assert (set_map ssid (ssc ∖ {[idx]}) ∪ {[ssid idx]} =
        set_map ssid (ssc ∖ {[idx]} ∪ {[idx]})) as ->.
      { rewrite set_map_union_L. set_solver. }
      rewrite -gset_union_difference_L'; set_solver. }
    subst.
    assert (co1E ## {[ssid idx]}).
    { unfold disjoint, coPneset_disjoint. simpl.
      rewrite Hco1E disjoint_singleton_r. intro.
      rewrite elem_of_gset_to_coPset in H0. set_solver. }
    iDestruct (coP_ghost_map_elem_fractional with "pi") as "[pi pis]"; auto.
    iDestruct (coP_cinv_own_fractional with "cinv") as "[cinv cis]"; auto.

    (* close *)
    iSplitL "TIEi pi cinv".
    + iRight; iRight. repeat iExists _. iFrame "∗#%".
    + by iFrame.
Qed.

Lemma exchange_stok_get_token_set (ssc : gset nat) idx :
  idx ∉ ssc →
  ⊤ ∖ gset_to_coPset (set_map sid ssc) =
  ⊤ ∖ gset_to_coPset (set_map sid (ssc ∪ {[idx]})) ∪ {[sid idx]}.
Proof.
  intros.
  rewrite set_map_union_L gset_to_coPset_union.
  rewrite set_map_singleton_L gset_to_coPset_singleton.
  rewrite difference_union_difference.
  rewrite -union_difference_L'; auto.
  rewrite singleton_subseteq_l elem_of_difference. split; [set_solver|].
  rewrite elem_of_gset_to_coPset elem_of_map.
  intro. destruct H0 as [x [Hsid Hx]].
  apply sid_injective in Hsid. set_solver.
Qed.

Lemma exchange_stok_get γtok γptrs γc_i
    (N : namespace) E p i idx :
  ↑exchN N p i ⊆ E →
  Exchanges N γtok γptrs p i γc_i -∗
  p ↪c[γptrs]{{[ssid idx]}} i -∗
  coP_cinv_own γc_i {[ssid idx]} -∗
  |={E}=> stok γtok i idx.
Proof.
  iIntros (?) "#Ex pi cinv".
  iInv "Ex" as ">[Ex'|[Ex'|Ex']]".
  - (* ⊤: remove idx from ⊤ *)
    rewrite (top_union_difference {[sid idx]}).
    iDestruct (toks_union_2 with "Ex'") as "[TIE TII]"; [set_solver|].
    iModIntro. iSplitR "TII"; auto.
    iRight; iRight. iExists {[idx]}, _. iFrame.
    do 2 rewrite set_map_singleton_L.
    do 2 rewrite gset_to_coPset_singleton. auto.
  - (* finite: remove idx from ss *)
    iDestruct "Ex'" as (ss) "(Expi & Excinv & TIS)".
    iDestruct (coP_ghost_map.coP_ghost_map_elem_valid_2
      with "pi Expi") as "%".
    destruct H0 as [H0 _].
    apply coPneset_disj_elem_of in H0 as H0'.

    (* give p↪, cinv *)
    iCombine "pi Expi" as "Expi".
    iCombine "cinv Excinv" as "Excinv".

    (* separate token *)
    apply coPneset_disj_elem_of in H0.
    apply elem_of_union in H0; destruct H0; last first.
    { by apply elem_of_singleton, ssid_neq_gid in H0. }
    rewrite (union_difference_L {[sid idx]} (set_map sid ss)); last first.
    { rewrite elem_of_map in H0.
      destruct H0 as [x [H0 H1]]. apply ssid_injective in H0.
      subst. rewrite singleton_subseteq_l elem_of_map; eauto. }
    rewrite gset_to_coPset_union -toks_union_2; last first.
      { rewrite gset_to_coPset_difference gset_to_coPset_singleton.
        set_solver. }
    rewrite gset_to_coPset_singleton.
    iDestruct "TIS" as "[TII TISx]".

    (* close *)
    iModIntro. iSplitR "TII"; auto.
    rewrite -complement_delete; last set_solver.
    rewrite difference_union_distr_l_L.
    rewrite (difference_disjoint_L {[gid]}); last first.
    { apply disjoint_singleton_r. intro.
      by apply elem_of_singleton, ssid_neq_gid in H1. }
    assert (set_map ssid ss ∖ {[ssid idx]} = set_map ssid (ss ∖ {[idx]})) as ->.
    { rewrite set_map_difference_L. set_solver. }
    assert (set_map sid ss ∖ {[sid idx]} = set_map sid (ss ∖ {[idx]})) as ->.
    { rewrite set_map_difference_L. set_solver. }
    iRight; iLeft. iExists _. iFrame "∗#%".
  - (* cofinite: add idx to ss *)
    iDestruct "Ex'" as (ssc cossc Hco) "(Expi & Excinv & TIE)".
    iDestruct (coP_ghost_map_elem_valid_2 with "Expi pi") as %[D _].
    assert (idx ∉ ssc) as Hnotin.
    { revert D.
      unfold disjoint, coPneset_disjoint; simpl.
      rewrite Hco disjoint_singleton_r.
      rewrite elem_of_gset_to_coPset elem_of_map.
      intros. intro. apply D. eauto. }

    (* give p↪, cinv *)
    iCombine "Expi pi" as "pi".
    iCombine "Excinv cinv" as "cinv".

    (* separate token *)
    rewrite (exchange_stok_get_token_set _ idx); auto.
    rewrite -toks_union_2; last first.
    { symmetry. apply disjoint_subset.
      rewrite set_map_union_L gset_to_coPset_union.
      rewrite set_map_singleton_L gset_to_coPset_singleton.
      set_solver. }
    iDestruct "TIE" as "[TIE T]".

    (* close *)
    iModIntro.
    iSplitL "TIE pi cinv".
    + iRight; iRight. iExists _,_. iFrame "∗#%". iPureIntro.
      simpl. rewrite Hco set_map_union_L set_map_singleton_L.
      rewrite gset_to_coPset_union gset_to_coPset_singleton. auto.
    + by iFrame.
Qed.

(* Managed *)

Lemma managed_base_exclusive base_mgmtN base_ptrsN γtok γinfo γptrs γU γR p i i' size_i size_i' R R' :
  ManagedBase base_mgmtN base_ptrsN γtok γinfo γptrs γU γR p i size_i R -∗
  ManagedBase base_mgmtN base_ptrsN γtok γinfo γptrs γU γR p i' size_i' R' -∗
  False.
Proof.
  iIntros "M M'".
  iDestruct "M" as (γc_i) "(cinv & i↪ & pc & Ex & CInv & U & γR)".
  iDestruct "M'" as (γc_i') "(cinv' & i'↪ & pc' & Ex' & CInv' & U' & γR')".
  iDestruct (coP_ghost_map_elem_agree with "pc' pc") as %->.
  iDestruct (ghost_map_elem_agree with "i'↪ i↪") as %[= -> ->].
  iDestruct (coP_cinv_own_valid with "cinv' cinv") as %DISJ.
  iPureIntro. rewrite coPneset_disj_iff /= in DISJ.
  set_solver.
Qed.

End lemmas.
