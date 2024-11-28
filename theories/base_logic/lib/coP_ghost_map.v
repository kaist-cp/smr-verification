From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From smr.algebra Require Import coPset coP_gmap_view.
From iris.algebra Require Export dfrac.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

(** like ghost_map, but using coP_gmap_view instead of gmap_view *)

Class coP_ghost_mapG Σ (K V : Type) `{Countable K} := CoPGhostMapG {
  #[local] coP_ghost_map_inG :: inG Σ (coP_gmap_viewR K (leibnizO V));
}.

Definition coP_ghost_mapΣ (K V : Type) `{Countable K} : gFunctors :=
  #[ GFunctor (coP_gmap_viewR K (leibnizO V)) ].

Global Instance subG_coP_ghost_mapΣ Σ (K V : Type) `{Countable K} :
  subG (coP_ghost_mapΣ K V) Σ → coP_ghost_mapG Σ K V.
Proof. solve_inG. Qed.

Section definitions.
  Context `{coP_ghost_mapG Σ K V}.

  Definition coP_ghost_map_auth_def (γ : gname) (q : Qp) (m : gmap K V) : iProp Σ :=
    own γ (coP_gmap_view_auth (V:=leibnizO V) (DfracOwn q) m).
  Definition coP_ghost_map_auth_aux : seal (@coP_ghost_map_auth_def). Proof. by eexists. Qed.
  Definition coP_ghost_map_auth := coP_ghost_map_auth_aux.(unseal).
  Definition coP_ghost_map_auth_unseal : @coP_ghost_map_auth = @coP_ghost_map_auth_def := coP_ghost_map_auth_aux.(seal_eq).

  Definition coP_ghost_map_elem_def (γ : gname) (k : K) (E : coPneset) (v : V) : iProp Σ :=
    own γ (coP_gmap_view_frag (V:=leibnizO V) k (CoPNESetDisj E) v).
  Definition coP_ghost_map_elem_aux : seal (@coP_ghost_map_elem_def). Proof. by eexists. Qed.
  Definition coP_ghost_map_elem := coP_ghost_map_elem_aux.(unseal).
  Definition coP_ghost_map_elem_unseal : @coP_ghost_map_elem = @coP_ghost_map_elem_def := coP_ghost_map_elem_aux.(seal_eq).
End definitions.

Notation "k ↪c[ γ ]{ E } v" := (coP_ghost_map_elem γ k E v)
  (at level 20, γ at level 50, E at level 50, format "k  ↪c[ γ ]{ E }  v") : bi_scope.
Notation "k ↪c[ γ ] v" := (k ↪c[γ]{⊤} v)%I
  (at level 20, γ at level 50, format "k  ↪c[ γ ]  v") : bi_scope.

Local Ltac unseal := rewrite
  ?coP_ghost_map_auth_unseal /coP_ghost_map_auth_def
  ?coP_ghost_map_elem_unseal /coP_ghost_map_elem_def.

Section lemmas.
  Context `{coP_ghost_mapG Σ K V}.
  Implicit Types (k : K) (v : V) (dq : dfrac) (E : coPneset) (q : Qp) (m : gmap K V).

  (** * Lemmas about the map elements *)
  Global Instance coP_ghost_map_elem_timeless k γ E v : Timeless (k ↪c[γ]{E} v).
  Proof. unseal. apply _. Qed.
  Lemma coP_ghost_map_elem_fractional k γ E1 E2 v :
    E1 ## E2 →
    k ↪c[γ]{E1 ∪ E2} v ⊣⊢ k ↪c[γ]{E1} v ∗ k ↪c[γ]{E2} v.
  Proof. intros. unseal. rewrite -coPneset_disj_union // coP_gmap_view_frag_op own_op //. Qed.

  Local Lemma coP_ghost_map_elems_unseal γ m E :
    ([∗ map] k ↦ v ∈ m, k ↪c[γ]{E} v) ==∗
    own γ ([^op map] k↦v ∈ m, coP_gmap_view_frag (V:=leibnizO V) k (CoPNESetDisj E) v).
  Proof.
    unseal. destruct (decide (m = ∅)) as [->|Hne].
    - rewrite !big_opM_empty. iIntros "_". iApply own_unit.
    - rewrite big_opM_own //. iIntros "?". done.
  Qed.

  Lemma coP_ghost_map_elem_valid_2 k γ E1 E2 v1 v2 :
    k ↪c[γ]{E1} v1 -∗ k ↪c[γ]{E2} v2 -∗ ⌜E1 ## E2 ∧ v1 = v2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    by iCombine "H1 H2" gives
      %[?%coPneset_disj_valid_op ?]%coP_gmap_view_frag_op_valid_L.
  Qed.
  Lemma coP_ghost_map_elem_agree k γ E1 E2 v1 v2 :
    k ↪c[γ]{E1} v1 -∗ k ↪c[γ]{E2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Helem1 Helem2".
    iDestruct (coP_ghost_map_elem_valid_2 with "Helem1 Helem2") as %[_ ?].
    done.
  Qed.

  Lemma coP_ghost_map_elem_combine k γ E1 E2 v1 v2 :
    k ↪c[γ]{E1} v1 -∗ k ↪c[γ]{E2} v2 -∗ k ↪c[γ]{E1 ∪ E2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (coP_ghost_map_elem_valid_2 with "Hl1 Hl2") as %[? ->].
    unseal. iCombine "Hl1 Hl2" as "Hl".
    rewrite coPneset_disj_union //. auto with iFrame.
  Qed.

  Lemma coP_ghost_map_elem_frac_ne γ k1 k2 E1 E2 v1 v2 :
    ¬ E1 ## E2 →
    k1 ↪c[γ]{E1} v1 -∗ k2 ↪c[γ]{E2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof.
    iIntros (?) "H1 H2"; iIntros (->).
    by iDestruct (coP_ghost_map_elem_valid_2 with "H1 H2") as %[??].
  Qed.
  Lemma coP_ghost_map_elem_ne γ k1 k2 E2 v1 v2 :
    k1 ↪c[γ] v1 -∗ k2 ↪c[γ]{E2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof. apply coP_ghost_map_elem_frac_ne => ?. by apply: coPneset_top_disjoint. Qed.

  (** * Lemmas about [ghost_map_auth] *)
  Lemma coP_ghost_map_alloc_strong P m :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ coP_ghost_map_auth γ 1 m ∗ [∗ map] k ↦ v ∈ m, k ↪c[γ] v.
  Proof.
    unseal. intros.
    iMod (own_alloc_strong (coP_gmap_view_auth (V:=leibnizO V) (DfracOwn 1) ∅) P)
      as (γ) "[% Hauth]"; first done.
    { apply coP_gmap_view_auth_valid. }
    iExists γ. iSplitR; first done.
    rewrite -big_opM_own_1 -own_op. iApply (own_update with "Hauth").
    etrans; first apply: (coP_gmap_view_alloc_big (V:=leibnizO V) _ m (CoPNESetDisj ⊤)).
    - apply map_disjoint_empty_r.
    - done.
    - rewrite right_id. done.
  Qed.
  Lemma coP_ghost_map_alloc_strong_empty P :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ coP_ghost_map_auth γ 1 (∅ : gmap K V).
  Proof.
    intros. iMod (coP_ghost_map_alloc_strong P ∅) as (γ) "(% & Hauth & _)"; eauto.
  Qed.
  Lemma coP_ghost_map_alloc m :
    ⊢ |==> ∃ γ, coP_ghost_map_auth γ 1 m ∗ [∗ map] k ↦ v ∈ m, k ↪c[γ] v.
  Proof.
    iMod (coP_ghost_map_alloc_strong (λ _, True) m) as (γ) "[_ Hmap]".
    - by apply pred_infinite_True.
    - eauto.
  Qed.
  Lemma coP_ghost_map_alloc_empty :
    ⊢ |==> ∃ γ, coP_ghost_map_auth γ 1 (∅ : gmap K V).
  Proof.
    intros. iMod (coP_ghost_map_alloc ∅) as (γ) "(Hauth & _)"; eauto.
  Qed.

  Global Instance coP_ghost_map_auth_timeless γ q m : Timeless (coP_ghost_map_auth γ q m).
  Proof. unseal. apply _. Qed.
  Global Instance coP_ghost_map_auth_fractional γ m : Fractional (λ q, coP_ghost_map_auth γ q m)%I.
  Proof. intros p q. unseal. rewrite -own_op -coP_gmap_view_auth_dfrac_op //. Qed.
  Global Instance coP_ghost_map_auth_as_fractional γ q m :
    AsFractional (coP_ghost_map_auth γ q m) (λ q, coP_ghost_map_auth γ q m)%I q.
  Proof. split; first done. apply _. Qed.

  Lemma coP_ghost_map_auth_valid γ q m : coP_ghost_map_auth γ q m -∗ ⌜q ≤ 1⌝%Qp.
  Proof.
    unseal. iIntros "Hauth".
    iDestruct (own_valid with "Hauth") as %?%coP_gmap_view_auth_dfrac_valid.
    done.
  Qed.
  Lemma coP_ghost_map_auth_valid_2 γ q1 q2 m1 m2 :
    coP_ghost_map_auth γ q1 m1 -∗ coP_ghost_map_auth γ q2 m2 -∗ ⌜(q1 + q2 ≤ 1)%Qp ∧ m1 = m2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    by iCombine "H1 H2" gives %[??]%coP_gmap_view_auth_dfrac_op_valid_L.
  Qed.
  Lemma coP_ghost_map_auth_agree γ q1 q2 m1 m2 :
    coP_ghost_map_auth γ q1 m1 -∗ coP_ghost_map_auth γ q2 m2 -∗ ⌜m1 = m2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (coP_ghost_map_auth_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.

  (** * Lemmas about the interaction of [ghost_map_auth] with the elements *)
  Lemma coP_ghost_map_lookup {γ q m k E v} :
    coP_ghost_map_auth γ q m -∗ k ↪c[γ]{E} v -∗ ⌜m !! k = Some v⌝.
  Proof.
    unseal. iIntros "Hauth Hel".
    by iCombine "Hauth Hel" gives %[? [??] ]%coP_gmap_view_both_dfrac_valid_L.
  Qed.

  Lemma coP_ghost_map_insert {γ m} k v :
    m !! k = None →
    coP_ghost_map_auth γ 1 m ==∗ coP_ghost_map_auth γ 1 (<[k := v]> m) ∗ k ↪c[γ] v.
  Proof.
    unseal. intros ?. rewrite -own_op.
    iApply own_update. apply: coP_gmap_view_alloc; done.
  Qed.

  Lemma coP_ghost_map_delete {γ m k v} :
    coP_ghost_map_auth γ 1 m -∗ k ↪c[γ] v ==∗ coP_ghost_map_auth γ 1 (delete k m).
  Proof.
    unseal. iApply bi.wand_intro_r. rewrite -own_op.
    iApply own_update. apply: coP_gmap_view_delete.
  Qed.

  Lemma coP_ghost_map_update {γ m k v} w :
    coP_ghost_map_auth γ 1 m -∗ k ↪c[γ] v ==∗ coP_ghost_map_auth γ 1 (<[k := w]> m) ∗ k ↪c[γ] w.
  Proof.
    unseal. iApply bi.wand_intro_r. rewrite -!own_op.
    iApply own_update. apply: coP_gmap_view_update.
  Qed.

  (** Big-op versions of above lemmas *)
  Lemma coP_ghost_map_lookup_big {γ q m} m0 :
    coP_ghost_map_auth γ q m -∗
    ([∗ map] k↦v ∈ m0, k ↪c[γ] v) -∗
    ⌜m0 ⊆ m⌝.
  Proof.
    iIntros "Hauth Hfrag". rewrite map_subseteq_spec. iIntros (k v Hm0).
    iDestruct (coP_ghost_map_lookup with "Hauth [Hfrag]") as %->.
    { rewrite big_sepM_lookup; done. }
    done.
  Qed.

  Lemma coP_ghost_map_insert_big {γ m} m' :
    m' ##ₘ m →
    coP_ghost_map_auth γ 1 m ==∗
    coP_ghost_map_auth γ 1 (m' ∪ m) ∗ ([∗ map] k ↦ v ∈ m', k ↪c[γ] v).
  Proof.
    unseal. intros ?. rewrite -big_opM_own_1 -own_op.
    iApply own_update. apply: coP_gmap_view_alloc_big; done.
  Qed.

  Lemma coP_ghost_map_delete_big {γ m} m0 :
    coP_ghost_map_auth γ 1 m -∗
    ([∗ map] k↦v ∈ m0, k ↪c[γ] v) ==∗
    coP_ghost_map_auth γ 1 (m ∖ m0).
  Proof.
    iIntros "Hauth Hfrag". iMod (coP_ghost_map_elems_unseal with "Hfrag") as "Hfrag".
    unseal. iApply (own_update_2 with "Hauth Hfrag").
    apply: coP_gmap_view_delete_big.
  Qed.

  Theorem coP_ghost_map_update_big {γ m} m0 m1 :
    dom m0 = dom m1 →
    coP_ghost_map_auth γ 1 m -∗
    ([∗ map] k↦v ∈ m0, k ↪c[γ] v) ==∗
    coP_ghost_map_auth γ 1 (m1 ∪ m) ∗
        [∗ map] k↦v ∈ m1, k ↪c[γ] v.
  Proof.
    iIntros (?) "Hauth Hfrag". iMod (coP_ghost_map_elems_unseal with "Hfrag") as "Hfrag".
    unseal. rewrite -big_opM_own_1 -own_op.
    iApply (own_update_2 with "Hauth Hfrag").
    apply: coP_gmap_view_update_big. done.
  Qed.

End lemmas.
