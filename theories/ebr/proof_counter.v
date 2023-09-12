From iris.algebra Require Import agree.
From iris.base_logic.lib Require Import invariants ghost_var.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr Require Import helpers ebr.spec_rcu_simple ebr.spec_counter ebr.code_counter.

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
Context (counterN rcuN : namespace) (DISJN : rcuN ## counterN).

Variable (rcu : rcu_simple_spec Σ rcuN).

Definition node (p : loc) lv γ_p : iProp :=
  ∃ x : Z, ⌜lv = [ #x ]⌝ ∗ own γ_p (to_agree x).

Definition Counter (γc : gname) (x : Z) : iProp :=
  ghost_var γc (1/2)%Qp x.

Global Instance Counter_Timeless γc xs: Timeless (Counter γc xs).
Proof. apply _. Qed.

Definition CounterInternalInv (c : loc) (γe γc : gname) : iProp :=
  ∃ (p : blk) (x : Z) (γ_p : gname), rcu.(Managed) γe p γ_p 1%nat node ∗
    ghost_var γc (1/2)%Qp x ∗ c ↦ #p ∗ own γ_p (to_agree x).

(* NOTE: ignoring reclamation of the rcu domain for convenience *)
Definition IsCounter (γe : gname) (γc : gname) (c : loc) : iProp :=
  ∃ (d : loc), (c +ₗ 1) ↦□ #d ∗ rcu.(IsRCUDomain) γe d ∗
    inv counterN (CounterInternalInv c γe γc).

Global Instance IsCounter_Persistent γe γc c : Persistent (IsCounter γe γc c).
Proof. apply _. Qed.

Lemma counter_new_spec :
  counter_new_spec' counterN rcuN counter_new rcu Counter IsCounter.
Proof.
  iIntros (γe d Φ) "!> #IED HΦ".
  wp_lam. wp_alloc c as "c↦" "†c". wp_let.
  simpl. rewrite array_cons array_singleton. iDestruct "c↦" as "[c.n↦ c.d↦]".
  wp_alloc p as "p↦" "†p". rewrite array_singleton.
  wp_let. wp_store. wp_op. rewrite loc_add_0. wp_store.

  wp_op.
  wp_store.
  iMod (mapsto_persist with "c.d↦") as "#c.d↦".
  iMod (own_alloc (to_agree 0)) as (γ_p) "#Hγ_p"; [done|].
  iMod (ghost_var_alloc 0) as (γc) "[Hγc Hγc']".
  iEval (rewrite -array_singleton) in "p↦".
  iMod (rcu.(rcu_domain_register) node with "IED [$p↦ $†p]") as "G_p"; [solve_ndisj| |].
  { iExists _. by iFrame "∗#". }
  iAssert (Counter γc 0) with "[Hγc]" as "C".
  { repeat iExists _. by iFrame. }
  iMod (inv_alloc counterN _ (CounterInternalInv c γe γc) with "[-HΦ C]") as "#Inv".
  { iNext. repeat iExists _. iFrame "∗%#". }
  iModIntro. iApply "HΦ". iSplit.
  - repeat iExists _. iFrame "∗#%".
  - iFrame.
Qed.

Lemma counter_inc_spec :
  counter_inc_spec' counterN rcuN (counter_inc rcu) rcu Counter IsCounter.
Proof using All.
  iDestruct 1 as (?) "#(c.d↦ & IED & Inv)".
  iIntros "G" (Φ) "AU".

  wp_lam. wp_pures. wp_load. wp_let.
  wp_alloc n as "n↦" "†n". rewrite array_singleton. wp_let.
  wp_apply (rcu.(guard_activate_spec) with "IED G") as (?) "G"; [solve_ndisj|].
  wp_seq. wp_op. rewrite loc_add_0.

  (* start counter loop *)
  move: {1}#0=> vn.
  wp_bind (counter_inc_loop _). iLöb as "IH" forall (vn).
  wp_rec. wp_pures.

  (* register *)
  wp_bind (! _)%E.
  iInv "Inv" as (p1 x1 γ_p1) "[G_p >(Hγc & c.n↦ & #Hγ_p1)]".
  wp_load.
  iMod (rcu.(guard_protect) with "IED G_p G") as "(G_p & G & #Info)"; [solve_ndisj|].
  iModIntro. iSplitL "c.n↦ G_p Hγc".
  { repeat iExists _. iFrame "∗#". }

  wp_pures.

  (* deref *)
  wp_apply (guard_read node 0%nat with "[$Info $G]") as (??) "(G & Hγ_p1' & %EQ)"; [solve_ndisj|lia|].
  iDestruct "Hγ_p1'" as (x2') "#[-> Hγ_p1']". injection EQ as [= <-].
  iCombine "Hγ_p1 Hγ_p1'" gives %<-%to_agree_op_inv_L. iClear "Hγ_p1'".

  wp_op. wp_store.

  (* CAS *)
  wp_bind (CmpXchg _ _ _).
  iInv "Inv" as (p3 x3 γ_p3) "[G_p >(Hγc & c.n↦ & #Hγ_p3)]".
  case (decide (p3 = p1)) as [->|NE].
  - (* success *) iClear "IH".
    wp_cmpxchg_suc.
    iDestruct (rcu.(guard_managed_agree) with "Info G G_p") as %<-.
    iCombine "Hγ_p1 Hγ_p3" gives %<-%to_agree_op_inv_L. iClear "Hγ_p3".
    iMod (own_alloc (to_agree (x1+1))) as (γ_n) "#Hγ_n"; [done|].
    iEval (rewrite -array_singleton) in "n↦".
    iMod (rcu.(rcu_domain_register) node with "IED [$n↦ $†n]") as "G_n"; [solve_ndisj|..].
    { iExists _. by iFrame "∗#". }
    iMod "AU" as (x2') "[Hγc' [_ Commit]]".

    iDestruct (ghost_var_agree with "Hγc Hγc'") as %<-.
    iMod (ghost_var_update_halves (x1 + 1) with "Hγc Hγc'") as "[Hγc Hγc']".
    iMod ("Commit" with "[Hγc']") as "HΦ"; last iModIntro.
    { by iFrame. }
    (* close inv*) iSplitL "c.n↦ G_n Hγc".
    { repeat iExists _. iFrame "∗#%". }
    wp_pures.

    wp_apply (guard_read node 0%nat with "[$Info $G]") as (??) "(G & Hγ_p1' & %EQ)"; [solve_ndisj|lia|].
    iDestruct "Hγ_p1'" as (x2') "#[-> Hγ_p1']". injection EQ as [= <-].
    iCombine "Hγ_p1 Hγ_p1'" gives %<-%to_agree_op_inv_L. iClear "Hγ_p1'".
    wp_pures.

    wp_apply (rcu.(rcu_domain_retire_spec) with "IED G_p") as "_"; [solve_ndisj|].
    wp_seq.
    wp_apply (rcu.(guard_deactivate_spec) with "IED G") as "G"; [solve_ndisj|].
    wp_seq. by iApply "HΦ".
  - (* fail *)
    wp_cmpxchg_fail.
    (* close inv*) iModIntro. iSplitL "c.n↦ G_p Hγc".
    { repeat iExists _. iFrame "∗#%". }
    wp_pure. wp_if.
    wp_apply ("IH" with "AU n↦ †n G").
Qed.

#[export] Typeclasses Opaque Counter IsCounter.

End counter.
