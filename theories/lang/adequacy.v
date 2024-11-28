From iris.algebra Require Import auth gmap.
From iris.base_logic.lib Require Import mono_nat ghost_map invariants mono_nat.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre adequacy.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

Class heapGpreS Σ := HeapGpreS {
  #[global] heapGpreS_iris :: invGpreS Σ;
  #[global] heapGpreS_heap :: ghost_mapG Σ loc val;
  #[global] heapGpreS_inv_heap :: inG Σ (authR inv_heap_mapUR);
  #[global] heapGS_freeable :: inG Σ (authR heap_freeableUR);
  #[global] heapGpreS_proph :: proph_mapGpreS proph_id (val * val) Σ;
  #[global] heapGS_step_cnt :: mono_natG Σ;
}.

Definition heapΣ : gFunctors :=
  #[invΣ; ghost_mapΣ loc val; GFunctor (constRF (authR inv_heap_mapUR));
    GFunctor (constRF (authR heap_freeableUR));
    proph_mapΣ proph_id (val * val); mono_natΣ].
Global Instance subG_heapGpreS {Σ} : subG heapΣ Σ → heapGpreS Σ.
Proof. solve_inG. Qed.

(* TODO: The [wp_adequacy] lemma is insufficient for a state interpretation
with a non-constant step index function. We thus use the more general
[wp_strong_adequacy] lemma. The proof below replicates part of the proof of
[wp_adequacy], and it hence would make sense to see if we can prove a version
of [wp_adequacy] for a non-constant step version. *)
Definition heap_adequacy Σ `{!heapGpreS Σ} s e σ φ :
  (∀ `{!heapGS Σ}, ⊢ inv_heap_inv -∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp.
  apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done].
  iIntros (Hinv).
  iMod (ghost_map_alloc σ.(heap)) as (vγ) "[Hvγ ?]".
  iMod (own_alloc (● (to_inv_heap ∅))) as (iγ) "H●".
  { rewrite auth_auth_valid. exact: to_inv_heap_valid. }
  iMod (own_alloc (● (∅ : heap_freeableUR))) as (fγ) "Hfγ";
    first by apply auth_auth_valid.
  iMod (proph_map_init κs σ.(used_proph_id)) as (?) "Hp".
  iMod (mono_nat_own_alloc) as (nγ) "[Hsteps _]".
  set (Hheap := HeapGS _ _ _ vγ _ iγ _ fγ _ _ nγ _).
  iAssert (inv_heap_inv_P (gG:=Hheap)) with "[H●]" as "P".
  { iExists _. iFrame. done. }
  iMod (inv_alloc inv_heapN ⊤ inv_heap_inv_P with "P") as "Hi".
  iDestruct (Hwp Hheap with "Hi") as "Hwp".
  iModIntro.
  iExists (λ σ ns κs nt, (heap_ctx σ.(heap) ∗
                          proph_map_interp κs σ.(used_proph_id) ∗
                          mono_nat_auth_own nγ 1 ns))%I.
  iExists [(λ v, ⌜φ v⌝%I)], (λ _, True)%I, _ => /=.
  iFrame. iSplit. { by iFrame. }
  iIntros (es' t2' -> ? ?) " _ H _".
  iApply fupd_mask_intro_discard; [done|]. iSplit; [|done].
  iDestruct (big_sepL2_cons_inv_r with "H") as (e' ? ->) "[Hwp H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed.
