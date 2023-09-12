From iris.algebra Require Import agree.
From iris.base_logic.lib Require Import invariants ghost_var.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr Require Import helpers no_recl.spec_counter no_recl.code_counter.

Set Printing Projections.

Local Open Scope Z.

Class counterG Σ := CounterG {
  counter_ghost_varG :> ghost_varG Σ Z;
}.

Definition counterΣ : gFunctors := #[ghost_varΣ Z].

Global Instance subG_counterΣ {Σ} :
  subG counterΣ Σ → counterG Σ.
Proof. solve_inG. Qed.

Section counter.
Context `{!heapGS Σ, !counterG Σ}.
Notation iProp := (iProp Σ).
Context (counterN : namespace).

Definition Counter (γ : gname) (x : Z) : iProp :=
  ghost_var γ (1/2)%Qp x.

Global Instance Counter_Timeless γ xs: Timeless (Counter γ xs).
  Proof. apply _. Qed.

Definition CounterInternalInv (c : loc) (γc : gname) : iProp :=
  ∃ (p  : loc) (x : Z), p ↦□ #x ∗
    ghost_var γc (1/2)%Qp x ∗ c ↦ #p.

(* NOTE: ignoring reclamation of the hazard domain for convenience *)
Definition IsCounter (γ : gname) (c : loc) : iProp :=
  inv counterN (CounterInternalInv c γ).

Global Instance IsCounter_Persistent γ c : Persistent (IsCounter γ c).
Proof. apply _. Qed.

Lemma counter_new_spec :
  counter_new_spec' counterN counter_new Counter IsCounter.
Proof.
  iIntros (Φ _) "HΦ".
  wp_lam. wp_alloc c as "c↦" "†c". wp_let.
  simpl. rewrite array_cons. iDestruct "c↦" as "[c.n↦ _]".
  wp_alloc p as "p↦" "†p". rewrite array_singleton.
  wp_let. wp_store. wp_op. rewrite loc_add_0. wp_store.

  iMod (ghost_var_alloc 0) as (γc) "[Hγc Hγc']".
  iMod (mapsto_persist with "p↦") as "#p↦".
  iAssert (Counter γc 0) with "[Hγc]" as "C".
  { repeat iExists _. by iFrame. }
  iMod (inv_alloc counterN _ (CounterInternalInv c γc) with "[-HΦ C]") as "#Inv".
  { iNext. repeat iExists _. iFrame "∗%#". }
  iModIntro. iApply "HΦ". iSplit.
  - repeat iExists _. by iFrame "∗#%".
  - iFrame.
Qed.

Lemma counter_inc_spec :
  counter_inc_spec' counterN counter_inc Counter IsCounter.
Proof using All.
  iIntros (γ c).
  iDestruct 1 as "#Inv".
  iIntros (Φ) "AU".

  wp_lam.
  wp_alloc n as "n↦" "†n". rewrite array_singleton.
  wp_let. wp_op. rewrite loc_add_0.

  (* start counter loop *)
  move: #0 => vn.
  wp_bind (counter_inc_loop _). iLöb as "IH" forall (vn).
  wp_rec. wp_pures.

  (* deref *)
  wp_bind (! _)%E.
  iInv "Inv" as (p1 x1) ">(#p↦ & Hγc & c.n↦)".
  wp_load.
  iModIntro. iSplitL "Hγc c.n↦".
  { repeat iExists _. iFrame "∗#%". }

  wp_pures. wp_load. wp_store.

  (* CAS *)
  wp_bind (CmpXchg _ _ _).
  iInv "Inv" as (p3 x3) ">(#p'↦ & Hγc & c.n↦)".
  case (decide (p3 = p1)) as [->|NE].
  - (* success *) iClear "IH".
    wp_cmpxchg_suc.
    iMod (mapsto_persist with "n↦") as "n↦".
    iDestruct (mapsto_agree with "p↦ p'↦") as %[= <-].

    iMod "AU" as (x2') "[C [_ Commit]]".
    iDestruct "C" as "Hγc'".
    iDestruct (ghost_var_agree with "Hγc Hγc'") as %<-.
    iMod (ghost_var_update_halves (x1 + 1) with "Hγc Hγc'") as "[Hγc Hγc']".
    iMod ("Commit" with "[Hγc']") as "HΦ"; last iModIntro.
    { by iFrame. }
    (* close inv*) iSplitL "c.n↦ n↦ Hγc".
    { repeat iExists _. iFrame "∗#%". }
    wp_pures.

    wp_bind (! _)%E.
    wp_load.
    wp_pures.

    by iApply "HΦ".
  - (* fail *)
    wp_cmpxchg_fail.
    (* close inv*) iModIntro. iSplitL "c.n↦ Hγc".
    { repeat iExists _. iFrame "∗#%". }
    wp_pure. wp_if.
    wp_apply ("IH" with "AU n↦ †n").
Qed.

#[export] Typeclasses Opaque Counter IsCounter.

End counter.
