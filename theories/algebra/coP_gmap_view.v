From iris.algebra Require Export view gmap.
From iris.algebra Require Import local_updates proofmode_classes big_op.
From smr.algebra Require Import coPset.
From iris.prelude Require Import options.

(** * like gmap_view, but using coPneset_disj instead of dfrac *)

Local Definition coP_gmap_view_fragUR (K : Type) `{Countable K} (V : ofe) : ucmra :=
  gmapUR K (prodR coPneset_disjR (agreeR V)).

(** View relation. *)
Section rel.
  Context (K : Type) `{Countable K} (V : ofe).
  Implicit Types (m : gmap K V) (k : K) (v : V) (n : nat).
  Implicit Types (f : gmap K (coPneset_disj * agree V)).

  Local Definition coP_gmap_view_rel_raw n m f : Prop :=
    map_Forall (λ k dv, ∃ v, dv.2 ≡{n}≡ to_agree v ∧ ✓ dv.1 ∧ m !! k = Some v) f.

  Local Lemma coP_gmap_view_rel_raw_mono n1 n2 m1 m2 f1 f2 :
    coP_gmap_view_rel_raw n1 m1 f1 →
    m1 ≡{n2}≡ m2 →
    f2 ≼{n2} f1 →
    n2 ≤ n1 →
    coP_gmap_view_rel_raw n2 m2 f2.
  Proof.
    intros Hrel Hm Hf Hn k [q va] Hk.
    (* For some reason applying the lemma in [Hf] does not work... *)
    destruct (lookup_includedN n2 f2 f1) as [Hf' _]. specialize (Hf' Hf). clear Hf.
    specialize (Hf' k). rewrite Hk in Hf'.
    apply option_includedN in Hf'.
    destruct Hf' as [[=]|(? & [q' va'] & [= <-] & Hf1 & Hincl)].
    specialize (Hrel _ _ Hf1) as (v & Hagree & Hdval & Hm1). simpl in *.
    specialize (Hm k).
    edestruct (dist_Some_inv_l _ _ _ _ Hm Hm1) as (v' & Hm2 & Hv).
    exists v'. rewrite assoc. split; last done.
    rewrite -Hv.
    destruct Hincl as [[Heqq Heqva]|[Hinclq Hinclva]%pair_includedN].
    - simpl in *. split.
      + rewrite Heqva. eapply dist_le; last eassumption. done.
      + rewrite <-discrete_iff in Heqq; last by apply _.
        fold_leibniz. subst q'. done.
    - split.
      + etrans; last first.
        { eapply dist_le; last eassumption. done. }
        eapply agree_valid_includedN; last done.
        eapply cmra_validN_le; last eassumption.
        rewrite Hagree. done.
      + rewrite <-cmra_discrete_included_iff in Hinclq.
        eapply cmra_valid_included; done.
  Qed.

  Local Lemma coP_gmap_view_rel_raw_valid n m f :
    coP_gmap_view_rel_raw n m f → ✓{n} f.
  Proof.
    intros Hrel k. destruct (f !! k) as [[q va]|] eqn:Hf; rewrite Hf; last done.
    specialize (Hrel _ _ Hf) as (v & Hagree & Hdval & Hm1). simpl in *.
    split; simpl.
    - apply cmra_discrete_valid_iff. done.
    - rewrite Hagree. done.
  Qed.

  Local Lemma coP_gmap_view_rel_raw_unit n :
    ∃ m, coP_gmap_view_rel_raw n m ε.
  Proof. exists ∅. apply: map_Forall_empty. Qed.

  Local Canonical Structure coP_gmap_view_rel : view_rel (gmapO K V) (coP_gmap_view_fragUR K V) :=
    ViewRel coP_gmap_view_rel_raw coP_gmap_view_rel_raw_mono
            coP_gmap_view_rel_raw_valid coP_gmap_view_rel_raw_unit.

  Local Lemma coP_gmap_view_rel_exists n (f : gmap K (coPneset_disj * agreeR V)) :
    (∃ m, coP_gmap_view_rel n m f) ↔ ✓{n} f.
  Proof.
    split.
    { intros [m Hrel]. eapply coP_gmap_view_rel_raw_valid, Hrel. }
    intros Hf.
    cut (∃ m, coP_gmap_view_rel n m f ∧ ∀ k, f !! k = None → m !! k = None).
    { naive_solver. }
    induction f as [|k [dq ag] f Hk' IH] using map_ind.
    { exists ∅. split; [|done]. apply: map_Forall_empty. }
    move: (Hf k). rewrite lookup_insert=> -[/= ??].
    destruct (to_agree_uninjN n ag) as [v ?]; [done|].
    destruct IH as (m & Hm & Hdom).
    { intros k'. destruct (decide (k = k')) as [->|?]; [by rewrite Hk'|].
      move: (Hf k'). by rewrite lookup_insert_ne. }
    exists (<[k:=v]> m).
    rewrite /coP_gmap_view_rel /= /coP_gmap_view_rel_raw map_Forall_insert //=. split_and!.
    - exists v. by rewrite lookup_insert.
    - eapply map_Forall_impl; [apply Hm|]; simpl.
      intros k' [dq' ag'] (v'&?&?&?). exists v'.
      rewrite lookup_insert_ne; naive_solver.
    - intros k'. rewrite !lookup_insert_None. naive_solver.
  Qed.

  Local Lemma coP_gmap_view_rel_unit n m : coP_gmap_view_rel n m ε.
  Proof. apply: map_Forall_empty. Qed.

  Local Lemma coP_gmap_view_rel_discrete :
    OfeDiscrete V → ViewRelDiscrete coP_gmap_view_rel.
  Proof.
    intros ? n m f Hrel k [df va] Hk.
    destruct (Hrel _ _ Hk) as (v & Hagree & Hdval & Hm).
    exists v. split; last by auto.
    eapply discrete_iff; first by apply _.
    eapply discrete_iff; first by apply _.
    done.
  Qed.
End rel.

Local Existing Instance coP_gmap_view_rel_discrete.

(** [gmap_view] is a notation to give canonical structure search the chance
to infer the right instances (see [auth]). *)
Notation coP_gmap_view K V := (view (@coP_gmap_view_rel_raw K _ _ V)).
Definition coP_gmap_viewO (K : Type) `{Countable K} (V : ofe) : ofe :=
  viewO (coP_gmap_view_rel K V).
Definition coP_gmap_viewR (K : Type) `{Countable K} (V : ofe) : cmra :=
  viewR (coP_gmap_view_rel K V).
Definition coP_gmap_viewUR (K : Type) `{Countable K} (V : ofe) : ucmra :=
  viewUR (coP_gmap_view_rel K V).

Section definitions.
  Context {K : Type} `{Countable K} {V : ofe}.

  Definition coP_gmap_view_auth (dq : dfrac) (m : gmap K V) : coP_gmap_viewR K V :=
    ●V{dq} m.
  Definition coP_gmap_view_frag (k : K) (E : coPneset_disj) (v : V) : coP_gmap_viewR K V :=
    ◯V {[k := (E, to_agree v)]}.
End definitions.

Section lemmas.
  Context {K : Type} `{Countable K} {V : ofe}.
  Implicit Types (m : gmap K V) (k : K) (q : Qp) (dq : dfrac) (E : coPneset_disj) (v : V).

  Global Instance : Params (@coP_gmap_view_auth) 5 := {}.
  Global Instance gmap_view_auth_ne dq : NonExpansive (coP_gmap_view_auth (K:=K) (V:=V) dq).
  Proof. solve_proper. Qed.
  Global Instance gmap_view_auth_proper dq : Proper ((≡) ==> (≡)) (coP_gmap_view_auth (K:=K) (V:=V) dq).
  Proof. apply ne_proper, _. Qed.

  Global Instance : Params (@coP_gmap_view_frag) 6 := {}.
  Global Instance gmap_view_frag_ne k oq : NonExpansive (coP_gmap_view_frag (V:=V) k oq).
  Proof. solve_proper. Qed.
  Global Instance gmap_view_frag_proper k oq : Proper ((≡) ==> (≡)) (coP_gmap_view_frag (V:=V) k oq).
  Proof. apply ne_proper, _. Qed.

  (* Helper lemmas *)
  Local Lemma coP_gmap_view_rel_lookup n m k E v :
    coP_gmap_view_rel K V n m {[k := (E, to_agree v)]} ↔ ✓ E ∧ m !! k ≡{n}≡ Some v.
  Proof.
    split.
    - intros Hrel.
      edestruct (Hrel k) as (v' & Hagree & Hval & ->).
      { rewrite lookup_singleton. done. }
      simpl in *. apply (inj _) in Hagree. rewrite Hagree.
      done.
    - intros [Hval (v' & Hm & Hv')%dist_Some_inv_r'] j [df va].
      destruct (decide (k = j)) as [<-|Hne]; last by rewrite lookup_singleton_ne.
      rewrite lookup_singleton. intros [= <- <-]. simpl.
      exists v'. split_and!; by rewrite ?Hv'.
  Qed.

  (** Composition and validity *)
  Lemma coP_gmap_view_auth_dfrac_op dp dq m :
    coP_gmap_view_auth (dp ⋅ dq) m ≡
    coP_gmap_view_auth dp m ⋅ coP_gmap_view_auth dq m.
  Proof. by rewrite /coP_gmap_view_auth view_auth_dfrac_op. Qed.
  Global Instance coP_gmap_view_auth_dfrac_is_op dq dq1 dq2 m :
    IsOp dq dq1 dq2 → IsOp' (coP_gmap_view_auth dq m) (coP_gmap_view_auth dq1 m) (coP_gmap_view_auth dq2 m).
  Proof. rewrite /coP_gmap_view_auth. apply _. Qed.

  Lemma coP_gmap_view_auth_dfrac_op_invN n dp m1 dq m2 :
    ✓{n} (coP_gmap_view_auth dp m1 ⋅ coP_gmap_view_auth dq m2) → m1 ≡{n}≡ m2.
  Proof. apply view_auth_dfrac_op_invN. Qed.
  Lemma coP_gmap_view_auth_dfrac_op_inv dp m1 dq m2 :
    ✓ (coP_gmap_view_auth dp m1 ⋅ coP_gmap_view_auth dq m2) → m1 ≡ m2.
  Proof. apply view_auth_dfrac_op_inv. Qed.
  Lemma coP_gmap_view_auth_dfrac_op_inv_L `{!LeibnizEquiv V} dq m1 dp m2 :
    ✓ (coP_gmap_view_auth dp m1 ⋅ coP_gmap_view_auth dq m2) → m1 = m2.
  Proof. apply view_auth_dfrac_op_inv_L, _. Qed.

  Lemma coP_gmap_view_auth_dfrac_validN m n dq : ✓{n} coP_gmap_view_auth dq m ↔ ✓ dq.
  Proof.
    rewrite view_auth_dfrac_validN. intuition eauto using coP_gmap_view_rel_unit.
  Qed.
  Lemma coP_gmap_view_auth_dfrac_valid m dq : ✓ coP_gmap_view_auth dq m ↔ ✓ dq.
  Proof.
    rewrite view_auth_dfrac_valid. intuition eauto using coP_gmap_view_rel_unit.
  Qed.
  Lemma coP_gmap_view_auth_valid m : ✓ coP_gmap_view_auth (DfracOwn 1) m.
  Proof. rewrite coP_gmap_view_auth_dfrac_valid. done. Qed.

  Lemma coP_gmap_view_auth_dfrac_op_validN n dq1 dq2 m1 m2 :
    ✓{n} (coP_gmap_view_auth dq1 m1 ⋅ coP_gmap_view_auth dq2 m2) ↔ ✓ (dq1 ⋅ dq2) ∧ m1 ≡{n}≡ m2.
  Proof.
    rewrite view_auth_dfrac_op_validN. intuition eauto using coP_gmap_view_rel_unit.
  Qed.
  Lemma coP_gmap_view_auth_dfrac_op_valid dq1 dq2 m1 m2 :
    ✓ (coP_gmap_view_auth dq1 m1 ⋅ coP_gmap_view_auth dq2 m2) ↔ ✓ (dq1 ⋅ dq2) ∧ m1 ≡ m2.
  Proof.
    rewrite view_auth_dfrac_op_valid. intuition eauto using coP_gmap_view_rel_unit.
  Qed.
  Lemma coP_gmap_view_auth_dfrac_op_valid_L `{!LeibnizEquiv V} dq1 dq2 m1 m2 :
    ✓ (coP_gmap_view_auth dq1 m1 ⋅ coP_gmap_view_auth dq2 m2) ↔ ✓ (dq1 ⋅ dq2) ∧ m1 = m2.
  Proof. unfold_leibniz. apply coP_gmap_view_auth_dfrac_op_valid. Qed.

  Lemma coP_gmap_view_auth_op_validN n m1 m2 :
    ✓{n} (coP_gmap_view_auth (DfracOwn 1) m1 ⋅ coP_gmap_view_auth (DfracOwn 1) m2) ↔ False.
  Proof. apply view_auth_op_validN. Qed.
  Lemma coP_gmap_view_auth_op_valid m1 m2 :
    ✓ (coP_gmap_view_auth (DfracOwn 1) m1 ⋅ coP_gmap_view_auth (DfracOwn 1) m2) ↔ False.
  Proof. apply view_auth_op_valid. Qed.

  Lemma coP_gmap_view_frag_validN n k E v : ✓{n} coP_gmap_view_frag k E v ↔ ✓ E.
  Proof.
    rewrite view_frag_validN coP_gmap_view_rel_exists singleton_validN pair_validN.
    naive_solver.
  Qed.
  Lemma coP_gmap_view_frag_valid k E v : ✓ coP_gmap_view_frag k E v ↔ ✓ E.
  Proof.
    rewrite cmra_valid_validN. setoid_rewrite coP_gmap_view_frag_validN.
    naive_solver eauto using O.
  Qed.

  Lemma coP_gmap_view_frag_op k E1 E2 v :
  coP_gmap_view_frag k (E1 ⋅ E2) v ≡ coP_gmap_view_frag k E1 v ⋅ coP_gmap_view_frag k E2 v.
  Proof. rewrite -view_frag_op singleton_op -pair_op agree_idemp //. Qed.

  Lemma coP_gmap_view_frag_op_validN n k E1 E2 v1 v2 :
    ✓{n} (coP_gmap_view_frag k E1 v1 ⋅ coP_gmap_view_frag k E2 v2) ↔
      ✓ (E1 ⋅ E2) ∧ v1 ≡{n}≡ v2.
  Proof.
    rewrite view_frag_validN coP_gmap_view_rel_exists singleton_op singleton_validN.
    by rewrite -pair_op pair_validN to_agree_op_validN.
  Qed.
  Lemma coP_gmap_view_frag_op_valid k E1 E2 v1 v2 :
    ✓ (coP_gmap_view_frag k E1 v1 ⋅ coP_gmap_view_frag k E2 v2) ↔ ✓ (E1 ⋅ E2) ∧ v1 ≡ v2.
  Proof.
    rewrite view_frag_valid. setoid_rewrite coP_gmap_view_rel_exists.
    rewrite -cmra_valid_validN singleton_op singleton_valid.
    by rewrite -pair_op pair_valid to_agree_op_valid.
  Qed.
  (* FIXME: Having a [valid_L] lemma is not consistent with [auth] and [view]; they
     have [inv_L] lemmas instead that just have an equality on the RHS. *)
  Lemma coP_gmap_view_frag_op_valid_L `{!LeibnizEquiv V} k E1 E2 v1 v2 :
    ✓ (coP_gmap_view_frag k E1 v1 ⋅ coP_gmap_view_frag k E2 v2) ↔ ✓ (E1 ⋅ E2) ∧ v1 = v2.
  Proof. unfold_leibniz. apply coP_gmap_view_frag_op_valid. Qed.

  Lemma coP_gmap_view_both_dfrac_validN n dp m k E v :
    ✓{n} (coP_gmap_view_auth dp m ⋅ coP_gmap_view_frag k E v) ↔
      ✓ dp ∧ ✓ E ∧ m !! k ≡{n}≡ Some v.
  Proof.
    rewrite /coP_gmap_view_auth /coP_gmap_view_frag.
    rewrite view_both_dfrac_validN coP_gmap_view_rel_lookup.
    naive_solver.
  Qed.
  Lemma coP_gmap_view_both_validN n m k E v :
    ✓{n} (coP_gmap_view_auth (DfracOwn 1) m ⋅ coP_gmap_view_frag k E v) ↔
      ✓ E ∧ m !! k ≡{n}≡ Some v.
  Proof. rewrite coP_gmap_view_both_dfrac_validN. naive_solver done. Qed.
  Lemma coP_gmap_view_both_dfrac_valid dp m k E v :
    ✓ (coP_gmap_view_auth dp m ⋅ coP_gmap_view_frag k E v) ↔
    ✓ dp ∧ ✓ E ∧ m !! k ≡ Some v.
  Proof.
    rewrite /coP_gmap_view_auth /coP_gmap_view_frag.
    rewrite view_both_dfrac_valid. setoid_rewrite coP_gmap_view_rel_lookup.
    split=>[[Hq Hm]|[Hq Hm]].
    - split; first done. split.
      + apply (Hm 0%nat).
      + apply equiv_dist=>n. apply Hm.
    - split; first done. intros n. split.
      + apply Hm.
      + revert n. apply equiv_dist. apply Hm.
  Qed.
  Lemma coP_gmap_view_both_dfrac_valid_L `{!LeibnizEquiv V} dp m k E v :
    ✓ (coP_gmap_view_auth dp m ⋅ coP_gmap_view_frag k E v) ↔
    ✓ dp ∧ ✓ E ∧ m !! k = Some v.
  Proof. unfold_leibniz. apply coP_gmap_view_both_dfrac_valid. Qed.
  Lemma coP_gmap_view_both_valid m k E v :
    ✓ (coP_gmap_view_auth (DfracOwn 1) m ⋅ coP_gmap_view_frag k E v) ↔
    ✓ E ∧ m !! k ≡ Some v.
  Proof. rewrite coP_gmap_view_both_dfrac_valid. naive_solver done. Qed.
  (* FIXME: Having a [valid_L] lemma is not consistent with [auth] and [view]; they
     have [inv_L] lemmas instead that just have an equality on the RHS. *)
  Lemma coP_gmap_view_both_valid_L `{!LeibnizEquiv V} m k E v :
    ✓ (coP_gmap_view_auth (DfracOwn 1) m ⋅ coP_gmap_view_frag k E v) ↔
    ✓ E ∧ m !! k = Some v.
  Proof. unfold_leibniz. apply coP_gmap_view_both_valid. Qed.

  (** Frame-preserving updates *)
  Lemma coP_gmap_view_alloc m k E v :
    m !! k = None →
    ✓ E →
    coP_gmap_view_auth (DfracOwn 1) m ~~> coP_gmap_view_auth (DfracOwn 1) (<[k := v]> m) ⋅ coP_gmap_view_frag k E v.
  Proof.
    intros Hfresh Hdq. apply view_update_alloc=>n bf Hrel j [df va] /=.
    rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
    - assert (bf !! k = None) as Hbf.
      { destruct (bf !! k) as [[df' va']|] eqn:Hbf; last done.
        specialize (Hrel _ _ Hbf). destruct Hrel as (v' & _ & _ & Hm).
        exfalso. rewrite Hm in Hfresh. done. }
      rewrite lookup_singleton Hbf right_id.
      intros [= <- <-]. eexists. do 2 (split; first done).
      rewrite lookup_insert. done.
    - rewrite lookup_singleton_ne; last done.
      rewrite left_id=>Hbf.
      specialize (Hrel _ _ Hbf). destruct Hrel as (v' & ? & ? & Hm).
      eexists. do 2 (split; first done).
      rewrite lookup_insert_ne //.
  Qed.

  Lemma coP_gmap_view_alloc_big m m' E :
    m' ##ₘ m →
    ✓ E →
    coP_gmap_view_auth (DfracOwn 1) m ~~>
      coP_gmap_view_auth (DfracOwn 1) (m' ∪ m) ⋅ ([^op map] k↦v ∈ m', coP_gmap_view_frag k E v).
  Proof.
    intros. induction m' as [|k v m' ? IH] using map_ind; decompose_map_disjoint.
    { rewrite big_opM_empty left_id_L right_id. done. }
    rewrite IH //.
    rewrite big_opM_insert // assoc.
    apply cmra_update_op; last done.
    rewrite -insert_union_l. apply (coP_gmap_view_alloc _ k E); last done.
    by apply lookup_union_None.
  Qed.

  Lemma coP_gmap_view_delete m k v :
    coP_gmap_view_auth (DfracOwn 1) m ⋅ coP_gmap_view_frag k (CoPNESetDisj ⊤) v ~~>
    coP_gmap_view_auth (DfracOwn 1) (delete k m).
  Proof.
    apply view_update_dealloc=>n bf Hrel j [df va] Hbf /=.
    destruct (decide (j = k)) as [->|Hne].
    - edestruct (Hrel k) as (v' & _ & Hdf & _).
      { rewrite lookup_op Hbf lookup_singleton -Some_op. done. }
      exfalso. eapply coPneset_disj_top_exclusive. apply Hdf.
    - edestruct (Hrel j) as (v' & ? & ? & Hm).
      { rewrite lookup_op lookup_singleton_ne // Hbf. done. }
      exists v'. do 2 (split; first done).
      rewrite lookup_delete_ne //.
  Qed.

  Lemma coP_gmap_view_delete_big m m' :
    coP_gmap_view_auth (DfracOwn 1) m ⋅ ([^op map] k↦v ∈ m', coP_gmap_view_frag k (CoPNESetDisj ⊤) v) ~~>
    coP_gmap_view_auth (DfracOwn 1) (m ∖ m').
  Proof.
    induction m' as [|k v m' ? IH] using map_ind.
    { rewrite right_id_L big_opM_empty right_id //. }
    rewrite big_opM_insert //.
    rewrite [coP_gmap_view_frag _ _ _ ⋅ _]comm assoc IH coP_gmap_view_delete.
    rewrite -delete_difference. done.
  Qed.

  Lemma coP_gmap_view_update m k v v' :
    coP_gmap_view_auth (DfracOwn 1) m ⋅ coP_gmap_view_frag k (CoPNESetDisj ⊤) v ~~>
      coP_gmap_view_auth (DfracOwn 1) (<[k := v']> m) ⋅ coP_gmap_view_frag k (CoPNESetDisj ⊤) v'.
  Proof.
    rewrite coP_gmap_view_delete.
    rewrite (coP_gmap_view_alloc _ k (CoPNESetDisj ⊤) v') //; last by rewrite lookup_delete.
    rewrite insert_delete_insert //.
  Qed.

  Lemma coP_gmap_view_update_big m m0 m1 :
    dom m0 = dom m1 →
    coP_gmap_view_auth (DfracOwn 1) m ⋅ ([^op map] k↦v ∈ m0, coP_gmap_view_frag k (CoPNESetDisj ⊤) v) ~~>
      coP_gmap_view_auth (DfracOwn 1) (m1 ∪ m) ⋅ ([^op map] k↦v ∈ m1, coP_gmap_view_frag k (CoPNESetDisj ⊤) v).
  Proof.
    intros Hdom%eq_sym. revert m1 Hdom.
    induction m0 as [|k v m0 Hnotdom IH] using map_ind; intros m1 Hdom.
    { rewrite dom_empty_L in Hdom.
      apply dom_empty_iff_L in Hdom as ->.
      rewrite left_id_L big_opM_empty. done. }
    rewrite dom_insert_L in Hdom.
    assert (k ∈ dom m1) as Hindom by set_solver.
    apply elem_of_dom in Hindom as [v' Hlookup].
    rewrite big_opM_insert //.
    rewrite [coP_gmap_view_frag _ _ _ ⋅ _]comm assoc.
    rewrite (IH (delete k m1)); last first.
    { rewrite dom_delete_L Hdom.
      apply not_elem_of_dom in Hnotdom. set_solver -Hdom. }
    rewrite -assoc [_ ⋅ coP_gmap_view_frag _ _ _]comm assoc.
    rewrite (coP_gmap_view_update _ _ _ v').
    rewrite (big_opM_delete _ m1 k v') // -assoc.
    rewrite insert_union_r; last by rewrite lookup_delete.
    rewrite union_delete_insert //.
  Qed.

  Lemma coP_gmap_view_auth_persist dq m :
    coP_gmap_view_auth dq m ~~> coP_gmap_view_auth DfracDiscarded m.
  Proof. apply view_update_auth_persist. Qed.

  (** Typeclass instances *)
  Global Instance coP_gmap_view_frag_core_id k E v : CoreId E → CoreId (coP_gmap_view_frag k E v).
  Proof. apply _. Qed.

  Global Instance coP_gmap_view_cmra_discrete : OfeDiscrete V → CmraDiscrete (coP_gmap_viewR K V).
  Proof. apply _. Qed.

  Global Instance coP_gmap_view_frag_mut_is_op E E1 E2 k v :
    IsOp E E1 E2 →
    IsOp' (coP_gmap_view_frag k E v) (coP_gmap_view_frag k E1 v) (coP_gmap_view_frag k E2 v).
  Proof. rewrite /IsOp' /IsOp => ->. apply coP_gmap_view_frag_op. Qed.
End lemmas.

(** Functor *)
Program Definition coP_gmap_viewURF (K : Type) `{Countable K} (F : oFunctor) : urFunctor := {|
  urFunctor_car A _ B _ := coP_gmap_viewUR K (oFunctor_car F A B);
  urFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (rel:=coP_gmap_view_rel K (oFunctor_car F A1 B1))
              (rel':=coP_gmap_view_rel K (oFunctor_car F A2 B2))
              (gmapO_map (K:=K) (oFunctor_map F fg))
              (gmapO_map (K:=K) (prodO_map cid (agreeO_map (oFunctor_map F fg))))
|}.
Next Obligation.
  intros K ?? F A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  apply viewO_map_ne.
  - apply gmapO_map_ne, oFunctor_map_ne. done.
  - apply gmapO_map_ne. apply prodO_map_ne; first done.
    apply agreeO_map_ne, oFunctor_map_ne. done.
Qed.
Next Obligation.
  intros K ?? F A ? B ? x; simpl in *. rewrite -{2}(view_map_id x).
  apply (view_map_ext _ _ _ _)=> y.
  - rewrite /= -{2}(map_fmap_id y).
    apply map_fmap_equiv_ext=>k ??.
    apply oFunctor_map_id.
  - rewrite /= -{2}(map_fmap_id y).
    apply map_fmap_equiv_ext=>k [df va] ?.
    split; first done. simpl.
    rewrite -{2}(agree_map_id va).
    eapply agree_map_ext; first by apply _.
    apply oFunctor_map_id.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl in *.
  rewrite -view_map_compose.
  apply (view_map_ext _ _ _ _)=> y.
  - rewrite /= -map_fmap_compose.
    apply map_fmap_equiv_ext=>k ??.
    apply oFunctor_map_compose.
  - rewrite /= -map_fmap_compose.
    apply map_fmap_equiv_ext=>k [df va] ?.
    split; first done. simpl.
    rewrite -agree_map_compose.
    eapply agree_map_ext; first by apply _.
    apply oFunctor_map_compose.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? B1 ? B2 ? fg; simpl.
  (* [apply] does not work, probably the usual unification probem (Coq #6294) *)
  apply: view_map_cmra_morphism; [apply _..|]=> n m f.
  intros Hrel k [df va] Hf. move: Hf.
  rewrite !lookup_fmap.
  destruct (f !! k) as [[df' va']|] eqn:Hfk; rewrite Hfk; last done.
  simpl=>[= <- <-].
  specialize (Hrel _ _ Hfk). simpl in Hrel. destruct Hrel as (v & Hagree & Hdval & Hm).
  exists (oFunctor_map F fg v).
  rewrite Hm. split; last by auto.
  rewrite Hagree. rewrite agree_map_to_agree. done.
Qed.

Global Instance coP_gmap_viewURF_contractive (K : Type) `{Countable K} F :
  oFunctorContractive F → urFunctorContractive (coP_gmap_viewURF K F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  apply viewO_map_ne.
  - apply gmapO_map_ne. apply oFunctor_map_contractive. done.
  - apply gmapO_map_ne. apply prodO_map_ne; first done.
    apply agreeO_map_ne, oFunctor_map_contractive. done.
Qed.

Program Definition coP_gmap_viewRF (K : Type) `{Countable K} (F : oFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := coP_gmap_viewR K (oFunctor_car F A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (rel:=coP_gmap_view_rel K (oFunctor_car F A1 B1))
              (rel':=coP_gmap_view_rel K (oFunctor_car F A2 B2))
              (gmapO_map (K:=K) (oFunctor_map F fg))
              (gmapO_map (K:=K) (prodO_map cid (agreeO_map (oFunctor_map F fg))))
|}.
Solve Obligations with apply coP_gmap_viewURF.

Global Instance coP_gmap_viewRF_contractive (K : Type) `{Countable K} F :
  oFunctorContractive F → rFunctorContractive (coP_gmap_viewRF K F).
Proof. apply coP_gmap_viewURF_contractive. Qed.

#[export] Typeclasses Opaque coP_gmap_view_auth coP_gmap_view_frag.
