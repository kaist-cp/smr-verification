(** This file extends the HeapLang program logic with some derived laws (not
using the lifting lemmas) about arrays and prophecies. *)

From stdpp Require Import fin_maps.
From iris.bi Require Import lib.fractional.
From iris.proofmode Require Import proofmode.
From smr.lang Require Export primitive_laws.
From smr.lang Require Import tactics notation.
From iris.prelude Require Import options.

(* extra array rules that don't have counterpart in lambda-rust *)
Section lifting.
Context `{!heapGS_gen hlc Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types l : loc.
Implicit Types sz off : nat.

Lemma update_array l dq vs off v :
  vs !! off = Some v →
  ⊢ l ↦∗{dq} vs -∗ ((l +ₗ off) ↦{dq} v ∗ ∀ v', (l +ₗ off) ↦{dq} v' -∗ l ↦∗{dq} <[off:=v']>vs).
Proof.
  iIntros (Hlookup) "Hl".
  rewrite -[X in (l ↦∗{_} X)%I](take_drop_middle _ off v); last done.
  iDestruct (array_app with "Hl") as "[Hl1 Hl]".
  iDestruct (array_cons with "Hl") as "[Hl2 Hl3]".
  assert (off < length vs) as H by (apply lookup_lt_is_Some; by eexists).
  rewrite length_take min_l; last by lia. iFrame "Hl2".
  iIntros (w) "Hl2".
  clear Hlookup. assert (<[off:=w]> vs !! off = Some w) as Hlookup.
  { apply list_lookup_insert. lia. }
  rewrite -[in (l ↦∗{_} <[off:=w]> vs)%I](take_drop_middle (<[off:=w]> vs) off w Hlookup).
  iApply array_app. rewrite take_insert; last by lia. iFrame.
  iApply array_cons. rewrite length_take min_l; last by lia. iFrame.
  rewrite drop_insert_gt; last by lia. done.
Qed.

(** * Rules for accessing array elements *)
Lemma twp_load_offset s E l dq off vs v :
  vs !! off = Some v →
  [[{ l ↦∗{dq} vs }]] ! #(l +ₗ off) @ s; E [[{ RET v; l ↦∗{dq} vs }]].
Proof.
  iIntros (Hlookup Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (twp_load with "Hl1"). iIntros "Hl1". iApply "HΦ".
  iDestruct ("Hl2" $! v) as "Hl2". rewrite list_insert_id; last done.
  iApply "Hl2". iApply "Hl1".
Qed.
Lemma wp_load_offset s E l dq off vs v :
  vs !! off = Some v →
  {{{ ▷ l ↦∗{dq} vs }}} ! #(l +ₗ off) @ s; E {{{ RET v; l ↦∗{dq} vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_load_offset with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma twp_persistent_load_offset s E l (off : nat) vs v :
  vs !! off = Some v →
  [[{ l ↦∗□ vs }]] ! #(l +ₗ off) @ s; E [[{ RET v; True }]].
Proof.
  iIntros (Hlookup Φ) "#Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (twp_load with "Hl1"). iIntros "_". by iApply "HΦ".
Qed.
Lemma wp_persistent_load_offset s E l (off : nat) vs v :
  vs !! off = Some v →
  {{{ l ↦∗□ vs }}} ! #(l +ₗ off) @ s; E {{{ RET v; True }}}.
Proof.
  iIntros (? Φ) "#H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_persistent_load_offset with "H"); [by eauto..|].
  iIntros "_ HΦ". by iApply "HΦ".
Qed.

Lemma twp_load_offset_vec s E l dq sz (off : fin sz) (vs : vec val sz) :
  [[{ l ↦∗{dq} vs }]] ! #(l +ₗ off) @ s; E [[{ RET vs !!! off; l ↦∗{dq} vs }]].
Proof. apply twp_load_offset. by apply vlookup_lookup. Qed.
Lemma wp_load_offset_vec s E l dq sz (off : fin sz) (vs : vec val sz) :
  {{{ ▷ l ↦∗{dq} vs }}} ! #(l +ₗ off) @ s; E {{{ RET vs !!! off; l ↦∗{dq} vs }}}.
Proof. apply wp_load_offset. by apply vlookup_lookup. Qed.

Lemma twp_store_offset s E l off vs v :
  is_Some (vs !! off) →
  [[{ l ↦∗ vs }]] #(l +ₗ off) <- v @ s; E [[{ RET #(); l ↦∗ <[off:=v]> vs }]].
Proof.
  iIntros ([w Hlookup] Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (twp_store with "Hl1"). iIntros "Hl1".
  iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.
Lemma wp_store_offset s E l off vs v :
  is_Some (vs !! off) →
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #(); l ↦∗ <[off:=v]> vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_store_offset with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma twp_store_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v :
  [[{ l ↦∗ vs }]] #(l +ₗ off) <- v @ s; E [[{ RET #(); l ↦∗ vinsert off v vs }]].
Proof.
  setoid_rewrite vec_to_list_insert. apply twp_store_offset.
  eexists. by apply vlookup_lookup.
Qed.
Lemma wp_store_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v :
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #(); l ↦∗ vinsert off v vs }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_store_offset_vec with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma twp_xchg_offset s E l off vs v v' :
  vs !! off = Some v →
  [[{ l ↦∗ vs }]] Xchg #(l +ₗ off) v' @ s; E [[{ RET v; l ↦∗ <[off:=v']> vs }]].
Proof.
  iIntros (Hlookup Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (twp_xchg with "Hl1"). iIntros "Hl1".
  iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.
Lemma wp_xchg_offset s E l off vs v v' :
  vs !! off = Some v →
  {{{ ▷ l ↦∗ vs }}} Xchg #(l +ₗ off) v' @ s; E {{{ RET v; l ↦∗ <[off:=v']> vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_xchg_offset with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma twp_xchg_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v :
  [[{ l ↦∗ vs }]] Xchg #(l +ₗ off) v @ s; E [[{ RET (vs !!! off); l ↦∗ vinsert off v vs }]].
Proof.
  setoid_rewrite vec_to_list_insert. apply twp_xchg_offset.
  by apply vlookup_lookup.
Qed.
Lemma wp_xchg_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v :
   {{{ ▷ l ↦∗ vs }}} Xchg #(l +ₗ off) v @ s; E {{{ RET (vs !!! off); l ↦∗ vinsert off v vs }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_xchg_offset_vec with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_suc_offset s E l off vs v' v1 v2 :
  vs !! off = Some v' →
  v' = v1 →
  vals_compare_safe v' v1 →
  [[{ l ↦∗ vs }]]
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  [[{ RET (v', #true); l ↦∗ <[off:=v2]> vs }]].
Proof.
  iIntros (Hlookup ?? Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (twp_cmpxchg_suc with "Hl1"); [done..|].
  iIntros "Hl1". iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.
Lemma wp_cmpxchg_suc_offset s E l off vs v' v1 v2 :
  vs !! off = Some v' →
  v' = v1 →
  vals_compare_safe v' v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (v', #true); l ↦∗ <[off:=v2]> vs }}}.
Proof.
  iIntros (??? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_suc_offset with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_suc_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off = v1 →
  vals_compare_safe (vs !!! off) v1 →
  [[{ l ↦∗ vs }]]
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  [[{ RET (vs !!! off, #true); l ↦∗ vinsert off v2 vs }]].
Proof.
  intros. setoid_rewrite vec_to_list_insert.
  apply twp_cmpxchg_suc_offset; [|done..].
  by apply vlookup_lookup.
Qed.
Lemma wp_cmpxchg_suc_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off = v1 →
  vals_compare_safe (vs !!! off) v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (vs !!! off, #true); l ↦∗ vinsert off v2 vs }}}.
Proof.
  iIntros (?? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_suc_offset_vec with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_fail_offset s E l dq off vs v0 v1 v2 :
  vs !! off = Some v0 →
  v0 ≠ v1 →
  vals_compare_safe v0 v1 →
  [[{ l ↦∗{dq} vs }]]
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  [[{ RET (v0, #false); l ↦∗{dq} vs }]].
Proof.
  iIntros (Hlookup HNEq Hcmp Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (twp_cmpxchg_fail with "Hl1"); first done.
  { destruct Hcmp; by [ left | right ]. }
  iIntros "Hl1". iApply "HΦ". iDestruct ("Hl2" $! v0) as "Hl2".
  rewrite list_insert_id; last done. iApply "Hl2". iApply "Hl1".
Qed.
Lemma wp_cmpxchg_fail_offset s E l dq off vs v0 v1 v2 :
  vs !! off = Some v0 →
  v0 ≠ v1 →
  vals_compare_safe v0 v1 →
  {{{ ▷ l ↦∗{dq} vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (v0, #false); l ↦∗{dq} vs }}}.
Proof.
  iIntros (??? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_fail_offset with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_fail_offset_vec s E l dq sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off ≠ v1 →
  vals_compare_safe (vs !!! off) v1 →
  [[{ l ↦∗{dq} vs }]]
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  [[{ RET (vs !!! off, #false); l ↦∗{dq} vs }]].
Proof.
  intros. apply twp_cmpxchg_fail_offset; [|done..].
  by apply vlookup_lookup.
Qed.
Lemma wp_cmpxchg_fail_offset_vec s E l dq sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off ≠ v1 →
  vals_compare_safe (vs !!! off) v1 →
  {{{ ▷ l ↦∗{dq} vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (vs !!! off, #false); l ↦∗{dq} vs }}}.
Proof.
  intros. eapply wp_cmpxchg_fail_offset; [|done..].
  by apply vlookup_lookup.
Qed.

Lemma twp_faa_offset s E l off vs (i1 i2 : Z) :
  vs !! off = Some #i1 →
  [[{ l ↦∗ vs }]] FAA #(l +ₗ off) #i2 @ s; E
  [[{ RET LitV (LitInt i1); l ↦∗ <[off:=#(i1 + i2)]> vs }]].
Proof.
  iIntros (Hlookup Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (twp_faa with "Hl1").
  iIntros "Hl1". iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.
Lemma wp_faa_offset s E l off vs (i1 i2 : Z) :
  vs !! off = Some #i1 →
  {{{ ▷ l ↦∗ vs }}} FAA #(l +ₗ off) #i2 @ s; E
  {{{ RET LitV (LitInt i1); l ↦∗ <[off:=#(i1 + i2)]> vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_faa_offset with "H"); [by eauto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_faa_offset_vec s E l sz (off : fin sz) (vs : vec val sz) (i1 i2 : Z) :
  vs !!! off = #i1 →
  [[{ l ↦∗ vs }]] FAA #(l +ₗ off) #i2 @ s; E
  [[{ RET LitV (LitInt i1); l ↦∗ vinsert off #(i1 + i2) vs }]].
Proof.
  intros. setoid_rewrite vec_to_list_insert. apply twp_faa_offset.
  by apply vlookup_lookup.
Qed.
Lemma wp_faa_offset_vec s E l sz (off : fin sz) (vs : vec val sz) (i1 i2 : Z) :
  vs !!! off = #i1 →
  {{{ ▷ l ↦∗ vs }}} FAA #(l +ₗ off) #i2 @ s; E
  {{{ RET LitV (LitInt i1); l ↦∗ vinsert off #(i1 + i2) vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_faa_offset_vec with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

(** Derived prophecy laws *)

(** Lemmas for some particular expression inside the [Resolve]. *)
Lemma wp_resolve_proph s E (p : proph_id) (pvs : list (val * val)) v :
  {{{ proph p pvs }}}
    ResolveProph (Val $ LitV $ LitProphecy p) (Val v) @ s; E
  {{{ pvs', RET (LitV LitUnit); ⌜pvs = (LitV LitUnit, v)::pvs'⌝ ∗ proph p pvs' }}}.
Proof.
  iIntros (Φ) "Hp HΦ". iApply (wp_resolve with "Hp"); first done.
  iApply lifting.wp_pure_step_later; first done.
  iIntros "!> _". iApply wp_value. iIntros (vs') "HEq Hp". iApply "HΦ". iFrame.
Qed.

Lemma wp_resolve_load s E l (p : proph_id) (pvs : list (val * val)) dq v v':
  {{{ proph p pvs ∗ ▷ l ↦{dq} v }}}
    Resolve !#l #p v' @ s; E
  {{{ pvs', RET v; ⌜pvs = (v, v')::pvs'⌝ ∗ proph p pvs' ∗ l ↦{dq} v }}}.
Proof.
  iIntros (Φ) "[Hp Hl] HΦ". iApply (wp_resolve with "Hp"); first done.
  iApply (wp_load with "Hl"). iIntros "!> Hl".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.

Lemma wp_resolve_load_offset s E l (p : proph_id) (pvs : list (val * val)) dq off vs v v':
  vs !! off = Some v →
  {{{ proph p pvs ∗ ▷ l ↦∗{dq} vs }}}
    Resolve !#(l +ₗ off) #p v' @ s; E
  {{{ pvs', RET v; ⌜pvs = (v, v')::pvs'⌝ ∗ proph p pvs' ∗ l ↦∗{dq} vs }}}.
Proof.
  iIntros (Hlookup Φ) "[Hp Hl] HΦ".
  iApply (wp_resolve with "Hp"); first done.
  iApply (wp_load_offset with "Hl"); [done|]. iIntros "!> Hl".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.

Lemma wp_resolve_cmpxchg_suc s E l (p : proph_id) (pvs : list (val * val)) v1 v2 v :
  vals_compare_safe v1 v1 →
  {{{ proph p pvs ∗ ▷ l ↦ v1 }}}
    Resolve (CmpXchg #l v1 v2) #p v @ s; E
  {{{ RET (v1, #true) ; ∃ pvs', ⌜pvs = ((v1, #true)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦ v2 }}}.
Proof.
  iIntros (Hcmp Φ) "[Hp Hl] HΦ".
  iApply (wp_resolve with "Hp"); first done.
  assert (val_is_unboxed v1) as Hv1; first by destruct Hcmp.
  iApply (wp_cmpxchg_suc with "Hl"); [done..|]. iIntros "!> Hl".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.

Lemma wp_resolve_cmpxchg_fail s E l (p : proph_id) (pvs : list (val * val)) dq v' v1 v2 v :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ proph p pvs ∗ ▷ l ↦{dq} v' }}}
    Resolve (CmpXchg #l v1 v2) #p v @ s; E
  {{{ RET (v', #false) ; ∃ pvs', ⌜pvs = ((v', #false)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦{dq} v' }}}.
Proof.
  iIntros (NEq Hcmp Φ) "[Hp Hl] HΦ".
  iApply (wp_resolve with "Hp"); first done.
  iApply (wp_cmpxchg_fail with "Hl"); [done..|]. iIntros "!> Hl".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.

End lifting.
