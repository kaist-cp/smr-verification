From iris.program_logic Require Export language.
From smr.lang Require Export lang.
From smr.lang Require Import tactics notation.
From iris.prelude Require Import options.

Global Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
Global Instance as_val_val v : AsVal (Val v).
Proof. by eexists. Qed.

(** * Instances of the [Atomic] class *)
Section atomic.
  Local Ltac solve_atomic :=
    apply strongly_atomic_atomic, ectx_language_atomic;
      [inversion 1; naive_solver
      |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

  Global Instance rec_atomic s f x e : Atomic s (Rec f x e).
  Proof. solve_atomic. Qed.
  Global Instance pair_atomic s v1 v2 : Atomic s (Pair (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance injl_atomic s v : Atomic s (InjL (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance injr_atomic s v : Atomic s (InjR (Val v)).
  Proof. solve_atomic. Qed.
  (** The instance below is a more general version of [Skip] *)
  Global Instance beta_atomic s f x v1 v2 : Atomic s (App (RecV f x (Val v1)) (Val v2)).
  Proof. destruct f, x; solve_atomic. Qed.
  Global Instance unop_atomic s op v : Atomic s (UnOp op (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance binop_atomic s op v1 v2 : Atomic s (BinOp op (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance if_true_atomic s v1 e2 :
    Atomic s (If (Val $ LitV $ LitBool true) (Val v1) e2).
  Proof. solve_atomic. Qed.
  Global Instance if_false_atomic s e1 v2 :
    Atomic s (If (Val $ LitV $ LitBool false) e1 (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance fst_atomic s v : Atomic s (Fst (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance snd_atomic s v : Atomic s (Snd (Val v)).
  Proof. solve_atomic. Qed.

  Global Instance fork_atomic s e : Atomic s (Fork e).
  Proof. solve_atomic. Qed.

  Global Instance alloc_atomic s v w : Atomic s (AllocN (Val v) (Val w)).
  Proof. solve_atomic. Qed.
  Global Instance free_atomic s v w : Atomic s (Free (Val v) (Val w)).
  Proof. solve_atomic. Qed.
  Global Instance load_atomic s v : Atomic s (Load (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance xchg_atomic s v1 v2 : Atomic s (Xchg (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance store_atomic s v1 v2 : Atomic s (Store (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance cmpxchg_atomic s v0 v1 v2 : Atomic s (CmpXchg (Val v0) (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance faa_atomic s v1 v2 : Atomic s (FAA (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.

  Global Instance new_proph_atomic s : Atomic s NewProph.
  Proof. solve_atomic. Qed.
  Global Instance resolve_atomic s e v1 v2 :
    Atomic s e → Atomic s (Resolve e (Val v1) (Val v2)).
  Proof.
    rename e into e1. intros H σ1 e2 κ σ2 efs [Ks e1' e2' Hfill -> step].
    simpl in *. induction Ks as [|K Ks _] using rev_ind; simpl in Hfill.
    - subst. inversion_clear step. by eapply (H σ1 (Val _) _ σ2 efs), head_prim_step.
    - rewrite fill_app. rewrite fill_app in Hfill.
      assert (∀ v, Val v = fill Ks e1' → False) as fill_absurd.
      { intros v Hv. assert (to_val (fill Ks e1') = Some v) as Htv by by rewrite -Hv.
        apply to_val_fill_some in Htv. destruct Htv as [-> ->]. inversion step. }
      destruct K; (inversion Hfill; clear Hfill; subst; try
        match goal with | H : Val ?v = fill Ks e1' |- _ => by apply fill_absurd in H end).
      refine (_ (H σ1 (fill (Ks ++ [_]) e2') _ σ2 efs _)).
      + destruct s; intro Hs; simpl in *.
        * destruct Hs as [v Hs]. apply to_val_fill_some in Hs. by destruct Hs, Ks.
        * apply irreducible_resolve. by rewrite fill_app in Hs.
      + econstructor; try done. simpl. by rewrite fill_app.
  Qed.
End atomic.

(** * Instances of the [PureExec] class *)
(** The behavior of the various [wp_] tactics with regard to lambda differs in
the following way:

- [wp_pures] does *not* reduce lambdas/recs that are hidden behind a definition.
- [wp_rec] and [wp_lam] reduce lambdas/recs that are hidden behind a definition.

To realize this behavior, we define the class [AsRecV v f x erec], which takes a
value [v] as its input, and turns it into a [RecV f x erec] via the instance
[AsRecV_recv : AsRecV (RecV f x e) f x e]. We register this instance via
[Hint Extern] so that it is only used if [v] is syntactically a lambda/rec, and
not if [v] contains a lambda/rec that is hidden behind a definition.

To make sure that [wp_rec] and [wp_lam] do reduce lambdas/recs that are hidden
behind a definition, we activate [AsRecV_recv] by hand in these tactics. *)
Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Global Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Global Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Section pure_exec.
  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; inv_head_step; try (done||lia).
  Local Ltac solve_pure_exec :=
    (try subst); intros ?; apply nsteps_once, pure_head_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].

  Global Instance pure_recc f x (erec : expr) :
    PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_pairc (v1 v2 : val) :
    PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_injlc (v : val) :
    PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_injrc (v : val) :
    PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
    PureExec True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
  Proof. unfold AsRecV in *. solve_pure_exec. Qed.

  Global Instance pure_unop op v v' :
    PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
  Proof. solve_pure_exec. Qed.

  Global Instance pure_binop op v1 v2 v' :
    PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v') | 10.
  Proof. solve_pure_exec. Qed.
  (* Lower-cost instance for [EqOp]. *)
  Global Instance pure_eqop v1 v2 :
    PureExec (vals_compare_safe v1 v2) 1
      (BinOp EqOp (Val v1) (Val v2))
      (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
  Proof.
    intros Hcompare.
    cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
    { intros. revert Hcompare. solve_pure_exec. }
    rewrite /bin_op_eval /= decide_True //.
  Qed.

  Global Instance pure_if_true e1 e2 :
    PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
  Proof. solve_pure_exec. Qed.
  Global Instance pure_if_false e1 e2 :
    PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_fst v1 v2 :
    PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_snd v1 v2 :
    PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inl v e1 e2 :
    PureExec True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_case_inr v e1 e2 :
    PureExec True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_eq_oloc l1 l2:
    PureExec True 1 (BinOp EqOp (LitV (oloc_to_lit l1)) (LitV (oloc_to_lit l2))) (LitV (bool_decide (l1 = l2))).
  Proof.
    destruct l1,l2; simpl; solve_pure_exec.
    all: split_and!; try done; unfold bin_op_eval in *; simpl in *; try naive_solver.
    repeat case_bool_decide; naive_solver.
  Qed.

  Global Instance pure_eq_oblk l1 l2:
    PureExec True 1 (BinOp EqOp (LitV (oblk_to_lit l1)) (LitV (oblk_to_lit l2))) (LitV (bool_decide (l1 = l2))).
  Proof.
    destruct l1,l2; simpl; solve_pure_exec.
    all: split_and!; try done; unfold bin_op_eval in *; simpl in *; try naive_solver.
    repeat case_bool_decide; naive_solver.
  Qed.

  Global Instance pure_eq_onat n1 n2:
    PureExec True 1 (BinOp EqOp (LitV (onat_to_lit n1)) (LitV (onat_to_lit n2))) (LitV (bool_decide (n1 = n2))).
  Proof.
    destruct n1,n2; simpl; solve_pure_exec.
    all: split_and!; try done; unfold bin_op_eval in *; simpl in *; try naive_solver.
    all: repeat case_bool_decide; try naive_solver.
    all: select (#_ = #_) (fun H => inversion H; lia).
  Qed.

  Global Instance pure_lt_inf_Z (z1 z2 : inf_Z) :
    PureExec True 1 (BinOp LtOp (LitV z1) (LitV z2)) (LitV (bool_decide (z1 < z2)%inf_Z)).
  Proof. solve_pure_exec.
    split_and!; [done..| |done]. unfold bin_op_eval in *; simpl in *.
    by select (Some _ = Some _) (fun H => injection H as [= <-]).
  Qed.

  Global Instance pure_le_inf_Z (z1 z2 : inf_Z) :
    PureExec True 1 (BinOp LeOp (LitV z1) (LitV z2)) (LitV (bool_decide (z1 ≤ z2)%inf_Z)).
  Proof. solve_pure_exec.
    split_and!; [done..| |done]. unfold bin_op_eval in *; simpl in *.
    by select (Some _ = Some _) (fun H => injection H as [= <-]).
  Qed.

  Global Instance pure_eq_inf_Z (z1 z2 : inf_Z) :
    PureExec True 1 (BinOp EqOp (LitV z1) (LitV z2)) (LitV (bool_decide (z1 = z2))).
  Proof. solve_pure_exec.
    split_and!; [done..| |done]. unfold bin_op_eval in *; simpl in *.
    select (Some _ = Some _) (fun H => injection H as [= <-]).
    repeat case_bool_decide; auto.
    - select (#_ = #_) ltac:(fun H => injection H as [= ->]). done.
    - exfalso. select (#_ ≠ #_) ltac:(fun H => apply H). naive_solver.
  Qed.

  Global Instance pure_lt_inf_Z_Z (z1 z2 : Z) :
    PureExec True 0 (Val (LitV (bool_decide (z1 < z2)%inf_Z))) (LitV (bool_decide (z1 < z2)%Z)).
  Proof.
    intros ?. assert ((bool_decide (z1 < z2)%inf_Z) = (bool_decide (z1 < z2)%Z)) as ->; [|constructor].
    case_bool_decide as EQ_inf_Z; case_bool_decide as EQ_Z; naive_solver.
  Qed.

  Global Instance pure_le_inf_Z_Z (z1 z2 : Z) :
    PureExec True 0 (Val (LitV (bool_decide (z1 ≤ z2)%inf_Z))) (LitV (bool_decide (z1 ≤ z2)%Z)).
  Proof.
    intros ?. assert ((bool_decide (z1 ≤ z2)%inf_Z) = (bool_decide (z1 ≤ z2)%Z)) as ->; [|constructor].
    case_bool_decide as EQ_inf_Z; case_bool_decide as EQ_Z; naive_solver.
  Qed.

  Global Instance pure_tag on t1 t2:
    PureExec True 1 (BinOp TagOp (LitV (on &ₜ t1)) (LitV (FinInt t2))) (LitV (on &ₜ t2)).
  Proof. destruct on; solve_pure_exec.
    all: split_and!; try done; unfold bin_op_eval in *; simpl in *; try naive_solver.
  Qed.

End pure_exec.
