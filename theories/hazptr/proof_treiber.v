From iris.algebra Require Import agree.
From iris.base_logic.lib Require Import invariants ghost_var.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr Require Import helpers hazptr.spec_hazptr hazptr.spec_stack hazptr.code_treiber.

Class treiberG Σ := TreiberG {
  #[local] treiber_ghost_varG :: ghost_varG Σ (list val);
  #[local] treiber_inG :: inG Σ (agreeR (prodO valO (optionO blkO)));
}.

Definition treiberΣ : gFunctors := #[ghost_varΣ (list val); GFunctor (agreeR (prodO valO (optionO blkO)))].

Global Instance subG_treiberΣ {Σ} :
  subG treiberΣ Σ → treiberG Σ.
Proof. solve_inG. Qed.

Section treiber_stack.
Context `{!heapGS Σ, !treiberG Σ}.
Notation iProp := (iProp Σ).
Context (treiberN hazptrN : namespace) (DISJN : hazptrN ## treiberN).

(* iExists + iFrame *)
Ltac exfr := repeat (repeat iExists _; iFrame "∗#%").

Variable (hazptr : hazard_pointer_spec Σ hazptrN).

Definition node_info γ_p (x : val) (n : option blk) :=
  own γ_p (to_agree (x, n)).

Definition node (p : blk) lv γ_p : iProp :=
  ∃ x n, ⌜lv = [ x; #(oblk_to_lit n) ]⌝ ∗ node_info γ_p x n.

Fixpoint phys_list γz (lopt : option blk) (xs : list val) : iProp :=
  match (lopt, xs) with
  | (None  , []     ) => True
  | (None  , _ :: _ ) => False
  | (Some _, []     ) => False
  | (Some l, x :: xs) => ∃ γ_l n,
      hazptr.(Managed) γz l γ_l nodeSize node ∗ node_info γ_l x n ∗
      phys_list γz n xs
  end.

(* Ownership of the stack *)
Definition TStack (γ : gname) (xs : list val) : iProp :=
  ∃ (γz γs : gname), ⌜γ = encode(γz, γs)⌝ ∗ ghost_var γs (1/2)%Qp xs.

Global Instance TStack_Timeless γ xs: Timeless (TStack γ xs).
Proof. apply _. Qed.

Definition TStackInternalInv (st : loc) (γz γs : gname) : iProp :=
  ∃ (h : option blk) (xs : list val),
    phys_list γz h xs ∗ (st +ₗ head) ↦ #(oblk_to_lit h) ∗ ghost_var γs (1/2)%Qp xs.

(* Persistent assertions about the stack *)
Definition IsTStack (γ : gname) (st : loc) : iProp :=
  ∃ (d : loc) (γz γs : gname), ⌜γ = encode(γz, γs)⌝ ∗
    (st +ₗ domain) ↦□ #d ∗ hazptr.(IsHazardDomain) γz d ∗
    inv treiberN (TStackInternalInv st γz γs).

Global Instance IsTStack_Persistent γ l : Persistent (IsTStack γ l).
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
  stack_new_spec' treiberN hazptrN tstack_new hazptr TStack IsTStack.
Proof.
  iIntros (γz dom Φ) "!> #IHD HΦ".
  wp_lam. wp_alloc st as "st↦" "†st". wp_pures.
  do 2 (wp_apply (wp_store_offset with "st↦") as "st↦"; [by simplify_list_eq|]; wp_pures).
  rewrite /= array_cons array_singleton.
  iDestruct "st↦" as "[st.h↦ st.d↦]".
  iMod (pointsto_persist with "st.d↦") as "#st.d↦".
  iMod (ghost_var_alloc []) as (γs) "[γs γs_I]".
  remember (encode (γz, γs)) as γ eqn:Hγ.
  iAssert (TStack γ []) with "[γs_I]" as "S"; first by exfr.
  iMod (inv_alloc treiberN _ (TStackInternalInv _ _ _) with "[-HΦ S]") as "#Inv".
  { iNext. iExists None, []. rewrite Loc.add_0. iFrame "∗#". }
  iModIntro. iApply "HΦ". iFrame "∗". exfr.
Qed.

Lemma tstack_push_spec :
  stack_push_spec' treiberN hazptrN tstack_push TStack IsTStack.
Proof using All.
  iIntros (γ st x).
  iDestruct 1 as (??? Hγ) "#(st.d↦ & IHD & Inv)".
  iIntros (Φ) "AU".

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

    iMod (hazptr.(hazard_domain_register) node with "IHD [$new↦ $†new $N_new]") as "G_new"; [solve_ndisj|].

    wp_cmpxchg_suc.
    iAssert (phys_list γz (Some new) (x::xs2)) with "[Info_new G_new Nodes]" as "Nodes'"; first by exfr.

    iMod "AU" as (?) "[S [_ Commit]]".
    iDestruct "S" as (??) "(% & γs')". encode_agree Hγ.

    iDestruct (ghost_var_agree with "γs γs'") as %<-.
    iMod (ghost_var_update_halves (x :: xs2) with "γs γs'") as "[γs γs']".

    iMod ("Commit" with "[γs']") as "HΦ"; first by exfr.
    (* close inv *)
    iModIntro. iSplitL "Nodes' st.h↦ γs"; first by exfr.
    wp_pures. by iApply "HΦ".

  - (* failed CAS; restore AU *)
    wp_cmpxchg_fail.
    (* close inv *)
    iModIntro. iSplitL "Nodes st.h↦ γs"; first by exfr.
    wp_pure. wp_if. wp_apply ("IH" with "AU †new new↦").
Qed.

Lemma tstack_pop_spec :
  stack_pop_spec' treiberN hazptrN (tstack_pop hazptr) TStack IsTStack.
Proof using All.
  iIntros (γ st).
  iDestruct 1 as (??? Hγ) "#(st.d↦ & IHD & Inv)".
  iIntros (Φ) "AU".

  wp_lam. wp_pures. wp_load. wp_pures.
  wp_apply (hazptr.(shield_new_spec) with "IHD [//]") as (s) "S"; [solve_ndisj|].
  wp_let.
  move: Deactivated => s_st.

  wp_bind ((tstack_pop_loop hazptr) _). iLöb as "IH" forall (s_st).
  wp_rec. wp_pures.

  (* If the validation read is null, commit empty pop. Otherwise, restore AU. *)
  awp_apply (hazptr.(shield_protect_spec) with "IHD S"); [solve_ndisj|].
  iInv "Inv" as (h1 xs1) "[Nodes >(st.h↦ & γs)]".
  destruct h1 as [h1|], xs1 as [|x1 xs1']; simpl; try (iMod "Nodes"; done); last first.
  { (* prove AACC of [protect] for empty stack case and commit empty pop *)
    iClear "IH".
    iAaccIntro with "[st.h↦]".
    1: instantiate (1 := [tele_arg None; inhabitant; 0; node]); iFrame. all: simpl.
    { iIntros "[st.h↦ _] !>". iSplitL "Nodes st.h↦ γs"; eauto with iFrame.
      iExists None, []. by iFrame. }
    iMod "AU" as (xs1') "[TStack [_ Commit]]".
    iDestruct "TStack" as (??) "(% & γs')". encode_agree Hγ.
    iDestruct (ghost_var_agree with "γs γs'") as %<-.
    iMod ("Commit" with "[γs]") as "HΦ"; first by exfr.
    iIntros "[st.h↦ S]".
    (* close inv *)
    iModIntro. iSplitL "Nodes st.h↦ γs'"; first by (iExists None; exfr).
    wp_pures.
    wp_apply (hazptr.(shield_drop_spec) with "IHD S") as "_"; [solve_ndisj|].
    wp_pures.
    iApply "HΦ". }

  (* prove AACC of [protect] for non-empty stack case and restore AU *)
  iDestruct "Nodes" as (γ_h1 n1) "(G_h1 & #Info_h1 & Nodes)".
  iAaccIntro with "[st.h↦ G_h1]".
  1: instantiate (1 := [tele_arg (Some h1); _; _; _]); iFrame. all: simpl.
  { iIntros "[st.h↦ G_h1] !>". iSplitR "AU".
    - iExists (Some h1),_. iFrame. simpl. repeat iExists _. iFrame "∗#".
    - iFrame. }
  iIntros "(st.h↦ & G_h1 & S) !>".
  iSplitL "Nodes st.h↦ γs G_h1"; first by (iExists (Some _); exfr).

  wp_pures. wp_bind (! _)%E.
  wp_apply (shield_read with "S") as (??) "(S & #Info_h1' & %EQ)"; [solve_ndisj|lia|].
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
    iDestruct (hazptr.(shield_managed_agree) with "S G_h2") as %<-.
    iCombine "Info_h1 Info_h2" gives %[= <- <-]%to_agree_op_inv_L.
    iMod "AU" as (xs2) "[TStack [_ Commit]]".
    iDestruct "TStack" as (??) "(% & γs')". encode_agree Hγ.

    iDestruct (ghost_var_agree with "γs γs'") as %<-.
    iMod (ghost_var_update_halves (xs2') with "γs γs'") as "[γs γs']".
    iMod ("Commit" with "[γs']") as "HΦ"; first by exfr.

    iModIntro. iSplitL "Nodes' st.h↦ γs"; first by exfr. wp_pures.

    wp_apply (shield_read with "S") as (??) "(S & #Info_h1' & %EQ)"; [solve_ndisj|lia|].
    iDestruct "Info_h1'" as (x2 n2) "[-> Info_h1']".

    iCombine "Info_h1 Info_h1'" gives %[= <- <-]%to_agree_op_inv_L.
    iClear "Info_h1'". injection EQ as [= <-].

    wp_pures. wp_load. wp_pures.
    wp_apply (hazptr.(hazard_domain_retire_spec) with "IHD G_h2") as "_"; [solve_ndisj|].
    wp_pures.

    wp_apply (hazptr.(shield_drop_spec) with "IHD S") as "_"; [solve_ndisj|].
    wp_pures. iApply "HΦ".

  - (* failed CAS; restore AU *)
    wp_cmpxchg_fail.
    iModIntro. iSplitL "Nodes st.h↦ γs"; first by exfr.
    wp_pure. wp_if. wp_apply ("IH" with "AU S").
Qed.

#[export] Typeclasses Opaque TStack IsTStack.

End treiber_stack.
