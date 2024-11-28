From iris.algebra Require Import agree.
From iris.base_logic.lib Require Import invariants ghost_var.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr.diaframe.lang Require Import proof_automation atomic_specs wp_auto_lob.
From smr.diaframe.hints Require Import ghost_var_hints array_hints.

From smr Require Import helpers no_recl.spec_stack no_recl.code_treiber.

Class treiberG Σ := TreiberG {
  #[local] treiber_ghost_varG :: ghost_varG Σ (list val);
}.

Definition treiberΣ : gFunctors := #[ghost_varΣ (list val)].

Global Instance subG_treiberΣ {Σ} :
  subG treiberΣ Σ → treiberG Σ.
Proof. solve_inG. Qed.

Section treiber_stack.
Context `{!heapGS Σ, !treiberG Σ}.
Notation iProp := (iProp Σ).
Context (treiberN : namespace).

Fixpoint phys_list (lopt : option loc) (xs : list val) : iProp :=
  match (lopt, xs) with
  | (None  , []     ) => True
  | (None  , _ :: _ ) => False
  | (Some _, []     ) => False
  | (Some l, x :: xs) => ∃ n,
      (l +ₗ 0) ↦□  x ∗ (l +ₗ 1) ↦□  #(oloc_to_lit n)  ∗
      phys_list n xs
  end.

Global Instance phys_list_timeless l xs: Timeless (phys_list l xs).
Proof. revert l. induction xs as [| x xs]; tc_solve. Qed.

(* Ownership of the stack *)
Definition TStack (γ : gname) (xs : list val) : iProp :=
  ghost_var γ (1/2)%Qp xs.

Global Instance TStack_Timeless γ xs: Timeless (TStack γ xs).
Proof. apply _. Qed.

Definition TStackInternalInv (st : loc) (γs : gname) : iProp :=
  ∃ (h : option loc) (xs : list val),
  (st +ₗ head) ↦ #(oloc_to_lit h) ∗ phys_list h xs ∗ ghost_var γs (1/2)%Qp xs ∗ emp%I.
(* (∗ emp) is essential for Diframe to open additional invariants/atomic updates for getting the ghost_var *)

(* Persistent assertions about the stack *)
Definition IsTStack (γ : gname) (st : loc) : iProp :=
    inv treiberN (TStackInternalInv st γ).

Global Instance IsTStack_Persistent γ l : Persistent (IsTStack γ l).
Proof. apply _. Qed.

Global Instance biabd_phys_list_none xs :
  HINT ε₀ ✱ [- ; ⌜xs = []⌝] ⊫ [id]; phys_list None xs ✱ [⌜xs = []⌝].
Proof. iSteps. Qed.

Global Instance biabd_phys_list_some (l : loc) xs :
    HINT ε₁ ✱ [x n xs' ;  (l +ₗ 0) ↦□  x ∗ (l +ₗ 1) ↦□ #(oloc_to_lit n) ∗ phys_list n xs' ∗  ⌜xs = x :: xs'⌝ ] ⊫
      [id]; phys_list (Some l) xs ✱ [ ⌜xs = x :: xs'⌝  ] | 120.
Proof. iSteps. Qed.

Lemma tstack_new_spec :
  stack_new_spec' treiberN tstack_new TStack IsTStack.
Proof. iSteps. Qed.

Local Instance no_lob_on_namespace : do_lob.NoLobGen treiberN := I.

Global Instance tstack_push_loop γs st new v next :
  SPEC ⟨↑treiberN⟩ xs,
  << IsTStack γs st ∗ (new +ₗ 0) ↦ v ∗ (new +ₗ 1) ↦∗ [next] ¦ TStack γs xs >>
    tstack_push_loop #st #new
  << RET #(); TStack γs (v :: xs) >>.
Proof. iSteps. Qed.

Lemma tstack_push_spec :
  stack_push_spec' treiberN tstack_push TStack IsTStack.
Proof. iSteps. Qed.

Lemma tstack_pop_spec :
  stack_pop_spec' treiberN tstack_pop TStack IsTStack.
Proof.
  iStep 28 as (a b c st Φ γs IH h xs|a b c st Φ γs IH h xs) "Inv IH AU InvCl Nodes γs st↦" | "Inv IH AU InvCl Nodes γs st↦"; first iSteps.
  (* If the validation read is null, commit empty pop. Otherwise, restore AU. *)
  destruct h as [h|], xs as [|x xs]; simpl; try done.
  - (* non-empty case *)
    iSteps as (n xs') "h.v↦□ h.n↦□ AU γs Nodes". destruct xs'; [done|]. iDecompose "Nodes" as "h.v↦□ h.n↦□ γs Nodes". iSteps.
  - (* empty pop case *)
    iMod "AU" as "AbCom". iDecompose "AbCom" as "γs AbCom". iDestruct (diaframe_close_right with "AbCom") as "Commit". iSteps.
Qed.

#[export] Typeclasses Opaque TStack IsTStack.

End treiber_stack.
