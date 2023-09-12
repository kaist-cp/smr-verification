From iris.algebra Require Import agree.
From iris.base_logic.lib Require Import invariants ghost_var.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr Require Import helpers ebr.spec_rcu_simple ebr.spec_stack ebr.code_treiber.

Class treiberG Σ := TreiberG {
  treiber_ghost_varG :> ghost_varG Σ (list val);
  treiber_inG :> inG Σ (agreeR (prodO valO (optionO blkO)));
}.

Definition treiberΣ : gFunctors := #[ghost_varΣ (list val); GFunctor (agreeR (prodO valO (optionO blkO)))].

Global Instance subG_treiberΣ {Σ} :
  subG treiberΣ Σ → treiberG Σ.
Proof. solve_inG. Qed.

Section treiber_stack.
Context `{!heapGS Σ, !treiberG Σ}.
Notation iProp := (iProp Σ).
Context (treiberN rcuN : namespace) (DISJN : treiberN ## rcuN).

(* iExists + iFrame *)
Ltac exfr := repeat (repeat iExists _; iFrame "∗#%").

Variable (rcu : rcu_simple_spec Σ rcuN).

Definition node_info γ_p (x : val) (n : option blk) :=
  own γ_p (to_agree (x, n)).

Definition node (p : blk) lv γ_p : iProp :=
  ∃ x n, ⌜lv = [ x; #(oblk_to_lit n) ]⌝ ∗ node_info γ_p x n.

Fixpoint phys_list γe (lopt : option blk) (xs : list val) : iProp :=
  match (lopt, xs) with
  | (None  , []     ) => True
  | (None  , _ :: _ ) => False
  | (Some _, []     ) => False
  | (Some l, x :: xs) => ∃ γ_l n,
      rcu.(Managed) γe l γ_l nodeSize node ∗ node_info γ_l x n ∗
      phys_list γe n xs
  end.

(* Ownership of the stack *)
Definition TStack (γ : gname) (xs : list val) : iProp :=
  ghost_var γ (1/2)%Qp xs.

Global Instance TStack_Timeless γ xs: Timeless (TStack γ xs).
Proof. apply _. Qed.

Definition TStackInternalInv (st : loc) (γe γs : gname) : iProp :=
  ∃ (h : option blk) (xs : list val),
    phys_list γe h xs ∗ (st +ₗ head) ↦ #(oblk_to_lit h) ∗ ghost_var γs (1/2)%Qp xs.

(* Persistent assertions about the stack *)
Definition IsTStack (γe : gname) (γs : gname) (st : loc) : iProp :=
  ∃ (d : loc),
    (st +ₗ domain) ↦□ #d ∗ rcu.(IsRCUDomain) γe d ∗
    inv treiberN (TStackInternalInv st γe γs).

Global Instance IsTStack_Persistent γe γs st : Persistent (IsTStack γe γs st).
Proof. apply _. Qed.

(** * Automation hints for [eauto] ******************************************)
Local Hint Extern 0 (environments.envs_entails _
  (node _ _ _)) => iExists _,_ : core.

Local Hint Extern 0 (environments.envs_entails _
  (TStack _ _ [])) => iExists None : core.

Local Hint Extern 0 (environments.envs_entails _
  (TStack _ _ (_ :: _))) => iExists (Some _) : core.

Local Hint Extern 10 (environments.envs_entails _
  (TStack _ _ _)) => unfold TStack : core.

Local Hint Extern 0 (environments.envs_entails _
  (phys_list _ None [])) => simpl : core.

Local Hint Extern 0 (environments.envs_entails _
  (phys_list _ (Some _) (_ :: _))) => simpl : core.

Local Hint Extern 0 (environments.envs_entails _
  (IsTStack _ _)) => iExists _ : core.

Lemma tstack_new_spec :
  stack_new_spec' treiberN rcuN tstack_new rcu TStack IsTStack.
Proof.
  iIntros (γe d Φ) "!> #IED HΦ".
  wp_lam. wp_alloc st as "st↦" "†st". wp_pures.
  do 2 (wp_apply (wp_store_offset with "st↦") as "st↦"; [by simplify_list_eq|]; wp_pures).
  rewrite /= array_cons array_singleton.
  iDestruct "st↦" as "[st.h↦ st.d↦]".
  iMod (mapsto_persist with "st.d↦") as "#st.d↦".
  iMod (ghost_var_alloc []) as (γs) "[γs γs_I]".
  iAssert (TStack γs []) with "[γs_I]" as "S"; first by iFrame.
  iMod (inv_alloc treiberN _ (TStackInternalInv _ _ _) with "[-HΦ S]") as "#Inv".
  { iNext. iExists None, []. rewrite loc_add_0. iFrame "∗#". }
  iModIntro. iApply "HΦ". iFrame "∗#%". exfr.
Qed.

Lemma tstack_push_spec :
  stack_push_spec' treiberN rcuN tstack_push rcu TStack IsTStack.
Proof using All.
  iIntros (γe γs st g x).
  iDestruct 1 as (?) "#(st.d↦ & IED & Inv)".
  iIntros "G" (Φ) "AU".

  wp_lam. wp_alloc new as "new↦" "†new". wp_pures.
  wp_apply (wp_store_offset with "new↦") as "new↦"; [by simplify_list_eq|]; wp_pures.
  move: #0 => next.

  iLöb as "IH" forall (next).
  wp_rec. wp_pures. wp_bind (! _)%E.

  (* Open inv to load head from st. *)
  iInv "Inv" as (h1 xs1) "[Nodes >(st.h↦ & γs)]".
  wp_load.
  (* close inv *)
  iModIntro. iSplitL "Nodes st.h↦ γs"; first by exfr.

  wp_pures.
  wp_apply (wp_store_offset with "new↦") as "new↦"; [by simplify_list_eq|]; wp_pures.

  wp_bind (CmpXchg _ _ _).
  iInv "Inv" as (h2 xs2) "[Nodes >(st.h↦ & γs)]".
  case (decide (h2 = h1)) as [->|NE].
  - (* successful CAS; commit push *) iClear "IH".
    iMod (own_alloc (to_agree (x, h1))) as (γ_n) "#Info_new"; [done|].
    iAssert (node new _ γ_n) with "[Info_new]" as "N_new"; [eauto|].

    iMod (rcu.(rcu_domain_register) node with "IED [$new↦ $†new $N_new]") as "G_new"; [solve_ndisj|].

    wp_cmpxchg_suc.
    iAssert (phys_list γe (Some new) (x::xs2)) with "[Info_new G_new Nodes]" as "Nodes'"; first by exfr.

    iMod "AU" as (?) "[γs' [_ Commit]]".

    iDestruct (ghost_var_agree with "γs γs'") as %<-.
    iMod (ghost_var_update_halves (x :: xs2) with "γs γs'") as "[γs γs']".

    iMod ("Commit" with "γs'") as "HΦ".
    (* close inv *)
    iModIntro. iSplitL "Nodes' st.h↦ γs"; first by exfr.
    wp_pures. by iApply "HΦ".

  - (* failed CAS; restore AU *)
    wp_cmpxchg_fail.
    (* close inv *)
    iModIntro. iSplitL "Nodes st.h↦ γs"; first by exfr.
    wp_pure. wp_if. iApply ("IH" with "G AU †new new↦").
Qed.

Lemma tstack_pop_spec :
  stack_pop_spec' treiberN rcuN (tstack_pop rcu) rcu TStack IsTStack.
Proof using All.
  iIntros (γe γs st g).
  iDestruct 1 as (?) "#(st.d↦ & IED & Inv)".
  iIntros "G" (Φ) "AU".

  wp_lam. wp_pures.

  wp_apply (rcu.(guard_activate_spec) with "IED G") as (?) "G"; [solve_ndisj|..].
  wp_seq.

  wp_bind ((tstack_pop_loop rcu) _). iLöb as "IH".
  wp_rec. wp_pures. wp_bind (! _)%E.

  (* If the value read is null, commit empty pop. Otherwise, register and restore AU. *)
  iInv "Inv" as (h1 xs1) "[Nodes >(st.h↦ & γs)]".
  wp_load.
  destruct h1 as [h1|], xs1 as [|x1 xs1']; simpl; try done; last first.
  { iClear "IH".
    iMod "AU" as (xs1') "[γs' [_ Commit]]".
    iDestruct (ghost_var_agree with "γs γs'") as %<-.
    iMod ("Commit" with "γs'") as "HΦ".
    (* close inv *)
    iModIntro. iSplitL "Nodes st.h↦ γs"; first by iExists None; exfr.
    wp_pures.
    wp_apply (rcu.(guard_deactivate_spec) with "IED G") as "G"; [solve_ndisj|].
    wp_seq.
    iApply "HΦ". by iFrame. }

  (* prove for non-empty stack case and restore AU *)
  iDestruct "Nodes" as (γ_h1 n1) "(G_h1 & #Info_h1 & Nodes)".
  iMod (rcu.(guard_protect) with "IED G_h1 G") as "(G_h1 & G & #h1Info)"; [solve_ndisj|].
  (* close inv *)
  iModIntro. iSplitL "Nodes st.h↦ γs G_h1"; first by iExists (Some _); exfr.

  wp_pures.

  wp_apply (guard_read node with "[$h1Info $G]") as (??) "(G & #Info_h1' & %EQ)"; [solve_ndisj|lia|].
  iDestruct "Info_h1'" as (x2 n2) "[-> Info_h1']".
  iCombine "Info_h1 Info_h1'" gives %[= <- <-]%to_agree_op_inv_L.
  iClear "Info_h1'". injection EQ as [= <-].

  wp_pures. wp_bind (CmpXchg _ _ _).
  iInv "Inv" as (h2 xs2) "[Nodes >(st.h↦ & γs)]".
  case (decide (h2 = Some h1)) as [->|NE].
  - (* successful CAS; commit pop *) iClear "IH".
    destruct xs2 as [|x2 xs2']; [iMod "Nodes"; done|]. simpl.
    iDestruct "Nodes" as (γ_h2 n2) "(G_h2 & #Info_h2 & Nodes')".
    wp_cmpxchg_suc.
    iDestruct (rcu.(guard_managed_agree) with "h1Info G G_h2") as %<-.
    iCombine "Info_h1 Info_h2" gives %[= <- <-]%to_agree_op_inv_L.
    iMod "AU" as (xs2) "[γs' [_ Commit]]".

    iDestruct (ghost_var_agree with "γs γs'") as %<-.
    iMod (ghost_var_update_halves (xs2') with "γs γs'") as "[γs γs']".
    iMod ("Commit" with "γs'") as "HΦ".

    iModIntro. iSplitL "Nodes' st.h↦ γs"; first by exfr. wp_pures.

    wp_apply (guard_read node with "[$h1Info $G]") as (??) "(G & #Info_h1' & %EQ)"; [solve_ndisj|lia|].
    iDestruct "Info_h1'" as (x2 n2) "[-> Info_h1']".
    iCombine "Info_h1 Info_h1'" gives %[= <- <-]%to_agree_op_inv_L.
    iClear "Info_h1'". injection EQ as [= <-].

    wp_pures. wp_load. wp_pures.
    wp_apply (rcu.(rcu_domain_retire_spec) with "IED G_h2") as "_"; [solve_ndisj|].
    wp_pures.

    wp_apply (rcu.(guard_deactivate_spec) with "IED G") as "G"; [solve_ndisj|]; wp_pures.
    iApply "HΦ". by iFrame.

  - (* failed CAS; restore AU *)
    wp_cmpxchg_fail.
    iModIntro. iSplitL "Nodes st.h↦ γs"; first by exfr.
    wp_pure. wp_if. wp_apply ("IH" with "AU G").
Qed.

#[export] Typeclasses Opaque TStack IsTStack.

End treiber_stack.
