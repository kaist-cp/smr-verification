From iris.algebra Require Import agree.
From iris.base_logic.lib Require Import invariants ghost_var.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr.diaframe.lang Require Import proof_automation wp_auto_lob atomic_specs atom_spec_notation.
From smr.diaframe.hints Require Import ghost_var_hints array_hints hazptr_hints.

From smr Require Import helpers hazptr.spec_hazptr hazptr.spec_stack hazptr.code_treiber.

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
Context (treiberN hazptrN : namespace) (DISJN : hazptrN ## treiberN).

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
  (st +ₗ head) ↦ #(oblk_to_lit h) ∗ phys_list γz h xs ∗ ghost_var γs (1/2)%Qp xs ∗ emp%I.

(* Persistent assertions about the stack *)
Definition IsTStack (γ : gname) (st : loc) : iProp :=
  ∃ (d : loc) (γz γs : gname),
    (st +ₗ domain) ↦□ #d ∗ hazptr.(IsHazardDomain) γz d ∗
    inv treiberN (TStackInternalInv st γz γs) ∗ ⌜γ = encode(γz, γs)⌝.

Global Instance IsTStack_Persistent γ l : Persistent (IsTStack γ l).
Proof. apply _. Qed.

Local Instance biabd_phys_list_none γz xs :
  HINT ε₁ ✱ [- ; ⌜xs = []⌝] ⊫ [id]; phys_list γz None xs ✱ [⌜xs = []⌝].
Proof. iSteps. Qed.

Local Instance biabd_phys_list_some_later (l : blk) γz:
  HINT ε₁ ✱ [γ_l x n xs';
    ▷ hazptr.(Managed) γz l γ_l nodeSize node ∗ ▷ node_info γ_l x n ∗
      ▷ phys_list γz n xs'  ] ⊫
    [ id ] xs; ▷ phys_list γz (Some l) xs ✱ [ ▷ ⌜xs = x :: xs'⌝ ].
Proof. iSteps. iExists (x0 :: x2). unseal_diaframe; simpl. iSplit; [|done]. iSteps. Qed.

Local Instance biabd_destruct_TStack (γz γs: gname) (xs: list val) :
  HINT TStack (encode (γz, γs)) xs ✱ [-; True] ⊫
    [id]; ghost_var γs (1/2)%Qp xs ✱ [ True ].
Proof. iSteps. Qed.

Local Instance no_lob_on_namespace_1 : do_lob.NoLobGen treiberN := I.
Local Instance no_lob_on_namespace_2 : do_lob.NoLobGen hazptrN := I.

Lemma tstack_new_spec :
  stack_new_spec' treiberN hazptrN tstack_new hazptr TStack IsTStack.
Proof. iSteps. Qed.

Global Instance tstack_push_loop_spec γs st (new : blk) v next :
  SPEC ⟨⊤, ↑treiberN ∪ ↑ptrsN hazptrN, ↑mgmtN hazptrN⟩ xs,
  << IsTStack γs st ∗ †new…2 ∗ (new +ₗ 0) ↦ v ∗ (new +ₗ 1) ↦∗ [next] ¦ TStack γs xs > >
    tstack_push_loop #st #new
  << RET #(); TStack γs (v :: xs) > >.
Proof using DISJN. iSteps. Qed.

Lemma tstack_push_spec :
  stack_push_spec' treiberN hazptrN tstack_push TStack IsTStack.
Proof using DISJN. iSteps. Qed.

Lemma tstack_pop_spec :
  stack_pop_spec' treiberN hazptrN (tstack_pop hazptr) TStack IsTStack.
Proof using DISJN.
  iSteps as (st d γz γs Φ s) "IHD Inv st.d↦□ AU Sh". iModIntro. move: Deactivated => s_st.
  (* Since diaframe refuses to generalize over instance of (shield Σ), we have to do induction manually *)
  wp_bind ((tstack_pop_loop hazptr) _). iLöb as "IH" forall (s_st). wp_lam.
  iSteps as (h xs) "Close Nodes γs".
  destruct h as [h|], xs as [|x xs]; simpl; iDecompose "Nodes" as (γ_h1 n1) "Info_h1 M_h1 Nodes".
  - (* Non-empty case *)
    iSteps as (xs') "Info_h1 AU Sh γs Nodes". destruct xs'; iDecompose "Nodes" as (γ_h1) "Info_h1 M_h1 Sh γs Nodes". iSteps as "st.d↦□ Info_h1 HΦ Sh". unseal_diaframe. by iFrame.
  - (* Empty pop. Commit immediately. *)
    iStep; [exact 0 | exact node |]. iStep 3 as "st.h↦"|"st.h↦ Sh"; first iSteps.
    iMod "AU" as "AbCom". iDecompose "AbCom" as (γz γs) "Inv IHD IH Sh Close γs AbCom". iDestruct (diaframe_close_right with "AbCom") as "Commit". iSteps.
Qed.

#[export] Typeclasses Opaque TStack IsTStack.

End treiber_stack.
