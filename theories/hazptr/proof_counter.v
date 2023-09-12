From iris.algebra Require Import agree.
From iris.base_logic.lib Require Import invariants ghost_var.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr Require Import helpers hazptr.spec_hazptr hazptr.spec_counter hazptr.code_counter.

Set Printing Projections.

Local Open Scope Z.

Class counterG Σ := CounterG {
  counter_inG :> inG Σ (agreeR ZO);
  counter_ghost_varG :> ghost_varG Σ Z;
}.

Definition counterΣ : gFunctors := #[ghost_varΣ Z; GFunctor (agreeR ZO)].

Global Instance subG_counterΣ {Σ} :
  subG counterΣ Σ → counterG Σ.
Proof. solve_inG. Qed.

Section counter.
Context `{!heapGS Σ, !counterG Σ}.
Notation iProp := (iProp Σ).
Context (counterN hazptrN : namespace) (DISJN : hazptrN ## counterN).

Variable (hazptr : hazard_pointer_spec Σ hazptrN).

Definition node (p : loc) lv γ_p : iProp :=
  ∃ x : Z, ⌜lv = [ #x ]⌝ ∗ own γ_p (to_agree x).

Definition Counter (γ : gname) (x : Z) : iProp :=
    ∃ (γz γc : gname), ⌜γ = encode(γz, γc)⌝ ∗ ghost_var γc (1/2)%Qp x.

Global Instance Counter_Timeless γ xs: Timeless (Counter γ xs).
  Proof. apply _. Qed.

Definition CounterInternalInv (c : loc) (γz γc : gname) : iProp :=
  ∃ (p : blk) (x : Z) (γ_p : gname), hazptr.(Managed) γz p γ_p 1%nat node ∗
    ghost_var γc (1/2)%Qp x ∗ c ↦ #p ∗ own γ_p (to_agree x).

(* NOTE: ignoring reclamation of the hazard domain for convenience *)
Definition IsCounter (γ : gname) (c : loc) : iProp :=
  ∃ (d : loc) (γz γc: gname), ⌜γ = encode(γz, γc)⌝ ∗
    (c +ₗ 1) ↦□ #d ∗ hazptr.(IsHazardDomain) γz d ∗
    inv counterN (CounterInternalInv c γz γc).

Global Instance IsCounter_Persistent γ c : Persistent (IsCounter γ c).
Proof. apply _. Qed.

Lemma counter_new_spec :
  counter_new_spec' counterN hazptrN counter_new hazptr Counter IsCounter.
Proof.
  iIntros (γz d Φ) "!> #IHD HΦ".
  wp_lam. wp_alloc c as "c↦" "†c". wp_let.
  simpl. rewrite array_cons array_singleton. iDestruct "c↦" as "[c.n↦ c.d↦]".
  wp_alloc p as "p↦" "†p". rewrite array_singleton.
  wp_let. wp_store. wp_op. rewrite loc_add_0. wp_store.

  wp_op.
  wp_store.
  iMod (mapsto_persist with "c.d↦") as "#c.d↦".
  iMod (own_alloc (to_agree 0)) as (γ_p) "#Hγ_p"; [done|].
  iMod (ghost_var_alloc 0) as (γc) "[Hγc Hγc']".
  remember (encode (γz, γc)) as γ eqn:Hγ.
  iEval (rewrite -array_singleton) in "p↦".
  iMod (hazptr.(hazard_domain_register) node with "IHD [$p↦ $†p]") as "G_p"; [solve_ndisj| |].
  { iExists _. by iFrame "#". }
  iAssert (Counter γ 0) with "[Hγc]" as "C".
  { repeat iExists _. by iFrame. }
  iMod (inv_alloc counterN _ (CounterInternalInv c γz γc) with "[-HΦ C]") as "#Inv".
  { iNext. repeat iExists _. iFrame "∗%#". }
  iModIntro. iApply "HΦ". iSplit.
  - repeat iExists _. by iFrame "∗#%".
  - iFrame.
Qed.

Lemma counter_inc_spec :
  counter_inc_spec' counterN hazptrN (counter_inc hazptr) Counter IsCounter.
Proof using All.
  iIntros (γ c).
  iDestruct 1 as (??? Hγ) "#(c.d↦ & IHD & Inv)".
  iIntros (Φ) "AU".

  wp_lam. wp_op. wp_load. wp_let.
  wp_apply (hazptr.(shield_new_spec) with "IHD [//]") as (s) "S"; [solve_ndisj|].
  wp_let.
  wp_alloc n as "n↦" "†n". rewrite array_singleton.
  wp_let. wp_op. rewrite loc_add_0.

  (* start counter loop *)
  move: Deactivated {1}#0 => s_st vn.
  wp_bind ((counter_inc_loop hazptr) _). iLöb as "IH" forall (s_st vn).
  wp_rec. wp_pures.

  (* protect *)
  awp_apply (hazptr.(shield_protect_spec) with "IHD S"); [solve_ndisj|].
  iInv "Inv" as (p1 x1 γ_p1) "[G_p >(Hγc & c.n↦ & #Hγ_p1)]".
  iAaccIntro with "[c.n↦ G_p]".
  1: instantiate (1 := [tele_arg (Some _); _; _; _]).
  all: simpl.
  { iFrame. }
  { iIntros "(c.n↦ & G_p) !>". iSplitL "c.n↦ G_p Hγc"; [iExists _,_,_; by iFrame|iFrame]. }
  iIntros "(c.n↦ & G_p & S) !>". iSplitL "c.n↦ G_p Hγc"; [iExists _,_,_; by iFrame|].
  iIntros "_". wp_pures.

  (* deref *)
  wp_apply (shield_read with "S") as (??) "(S & #Hγ_p1' & %EQ)"; [solve_ndisj|lia|].
  iDestruct "Hγ_p1'" as (x2') "[-> Hγ_p1']". injection EQ as [= <-].
  iCombine "Hγ_p1 Hγ_p1'" gives %<-%to_agree_op_inv_L. iClear "Hγ_p1'".

  wp_op. wp_store.

  (* CAS *)
  wp_bind (CmpXchg _ _ _).
  iInv "Inv" as (p3 x3 γ_p3) "[G_p >(Hγc & c.n↦ & #Hγ_p3)]".
  case (decide (p3 = p1)) as [->|NE].
  - (* success *) iClear "IH".
    wp_cmpxchg_suc. { naive_solver. }
    iDestruct (hazptr.(shield_managed_agree) with "S G_p") as %<-.
    iCombine "Hγ_p1 Hγ_p3" gives %<-%to_agree_op_inv_L. iClear "Hγ_p3".
    iMod (own_alloc (to_agree (x1+1))) as (γ_n) "#Hγ_n"; [done|].
    iEval (rewrite -array_singleton) in "n↦".
    iMod (hazptr.(hazard_domain_register) node with "IHD [$n↦ $†n]") as "G_n"; [solve_ndisj| |].
    { iExists _. by iFrame "∗#". }

    iMod "AU" as (x2') "[C [_ Commit]]".
    iDestruct "C" as (???) "Hγc'".
    encode_agree Hγ.
    iDestruct (ghost_var_agree with "Hγc Hγc'") as %<-.
    iMod (ghost_var_update_halves (x1 + 1) with "Hγc Hγc'") as "[Hγc Hγc']".
    iMod ("Commit" with "[Hγc']") as "HΦ"; last iModIntro.
    { iExists _,_. by iFrame. }
    (* close inv*) iSplitL "c.n↦ G_n Hγc".
    { repeat iExists _. iFrame "∗#%". }
    wp_pures.

    wp_apply (shield_read with "S") as (??) "(S & #Hγ_p1' & %EQ)"; [solve_ndisj|lia|]. wp_pures.
    iDestruct "Hγ_p1'" as (x2') "[-> Hγ_p1']". injection EQ as [= <-].
    iCombine "Hγ_p1 Hγ_p1'" gives %<-%to_agree_op_inv_L. iClear "Hγ_p1'".

    wp_apply (hazptr.(hazard_domain_retire_spec) with "IHD G_p") as "_"; [solve_ndisj|].
    wp_seq.
    wp_apply (hazptr.(shield_drop_spec) with "IHD S") as "_"; [solve_ndisj|].
    wp_seq. by iApply "HΦ".
  - (* fail *)
    wp_cmpxchg_fail.
    (* close inv*) iModIntro. iSplitL "c.n↦ G_p Hγc".
    { repeat iExists _. iFrame "∗#%". }
    wp_pure. wp_if.
    wp_apply ("IH" with "AU S n↦ †n").
Qed.

#[export] Typeclasses Opaque Counter IsCounter.

End counter.
