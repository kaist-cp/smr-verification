From iris.algebra Require Import agree.
From iris.base_logic.lib Require Import invariants ghost_var.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr.diaframe.lang Require Import proof_automation atomic_specs wp_auto_lob atom_spec_notation.
From smr.diaframe.hints Require Import ghost_var_hints array_hints rcu_hints.
From diaframe Require Import own_hints.

From smr Require Import helpers ebr.spec_rcu_simple ebr.spec_stack ebr.code_treiber.

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
  (st +ₗ head) ↦ #(oblk_to_lit h) ∗ phys_list γe h xs ∗ ghost_var γs (1/2)%Qp xs ∗ emp%I.

(* Persistent assertions about the stack *)
Definition IsTStack (γe : gname) (γs : gname) (st : loc) : iProp :=
  ∃ (d : loc),
    (st +ₗ domain) ↦□ #d ∗ rcu.(IsRCUDomain) γe d ∗
    inv treiberN (TStackInternalInv st γe γs).

Global Instance IsTStack_Persistent γe γs st : Persistent (IsTStack γe γs st).
Proof. apply _. Qed.

Local Instance biabd_phys_list_none γ xs :
  HINT ε₁ ✱ [- ; ⌜xs = []⌝] ⊫ [id]; phys_list γ None xs ✱ [⌜xs = []⌝].
Proof. iSteps. Qed.

Local Instance biabd_phys_list_some_later (l : blk) γ:
  HINT ε₁ ✱ [γ_l x n xs';
    ▷ rcu.(Managed) γ l γ_l nodeSize node ∗ ▷ node_info γ_l x n ∗
      ▷ phys_list γ n xs'  ] ⊫
    [id] xs; ▷ phys_list γ (Some l) xs ✱ [ ▷ ⌜ xs = x :: xs' ⌝ ].
Proof. iSteps. iExists (x0 :: x2). unseal_diaframe; simpl. iSplit; [| done]. iSteps. Qed.

Lemma tstack_new_spec :
  stack_new_spec' treiberN rcuN tstack_new rcu TStack IsTStack.
Proof. iSteps. Qed.

Local Instance no_lob_on_namespace_1 : do_lob.NoLobGen treiberN := I.
Local Instance no_lob_on_namespace_2 : do_lob.NoLobGen rcuN := I.

Global Instance tstack_push_loop_spec γe γs st (new : blk) v next :
  SPEC ⟨⊤, ↑treiberN ∪ ↑ptrsN rcuN, ↑mgmtN rcuN⟩ xs,
  << IsTStack γe γs st ∗ †new…2 ∗ (new +ₗ 0) ↦ v ∗ (new +ₗ 1) ↦∗ [next] ¦ TStack γs xs > >
    tstack_push_loop #st #new
  << RET #(); TStack γs (v :: xs) > >.
Proof using DISJN. iSteps. Qed.

Lemma tstack_push_spec :
  stack_push_spec' treiberN rcuN tstack_push rcu TStack IsTStack.
Proof using DISJN. iSteps. Qed.

Lemma tstack_pop_spec :
  stack_pop_spec' treiberN rcuN (tstack_pop rcu) rcu TStack IsTStack.
Proof using DISJN.
  iSteps as (γr γs st g d Φ γg) "st.d↦□ IRD Inv AU G". iModIntro.
  wp_bind (tstack_pop_loop rcu _).
  iLöb as "IH". wp_lam. wp_pure credit: "Lc".
  iStep 9 as (h xs | h xs) "Close Nodes γs st.n↦" | "Close Nodes γs st.n↦"; first iSteps.
  iMod (lc_fupd_elim_later with "Lc Nodes") as "Nodes".
  destruct h as [h|], xs as [|x xs]; try done.
  - (* Non-empty case *)
    iDecompose "Nodes" as (γ_h1 n1) "Info_h1 GetInfo Nodes".
    iStep 41 as (n1' xs' | n1' xs') "h1Info Info_h1 AU G Close Nodes γs st.n↦" | "h1Info Info_h1 AU G Close Nodes γs"; first by iSteps. iStep as (|NE) "Nodes st.n↦" | "st.n↦".
    + iSteps. destruct xs'; iDecompose "Nodes" as (γ_h1) "h1Info Info_h1 M_h1 G γs Nodes". iSteps. unseal_diaframe. simpl. iFrame. naive_solver.
    + iStep 15 as (res) "WP". iFrame. done.
  - (* Empty pop. Commit immediately. *)
    iMod "AU" as "AbCom". iDecompose "AbCom" as "γs AbCom". iPoseProof (diaframe_close_right with "AbCom") as "Commit". iSteps.
Qed.

#[export] Typeclasses Opaque TStack IsTStack.

End treiber_stack.
