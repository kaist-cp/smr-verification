From smr.diaframe.lang Require Import proof_automation.
From diaframe.lib Require Import do_lob.

From iris.prelude Require Import options.


(* This file, when imported, allows Diaframe to automatically perform Löb induction in
   the verification of recursive functions. Leverages the [do_lob] library.
   The main extra machinery that needs to be provided is detecting the arguments of the expression,
   and properly unfolding them *)

Set Universe Polymorphism.
Unset Universe Minimization ToSet. (* hilarious *)

Class AsRecFunOn (e : expr) (TT : tele) (args : TT)
        (shape : TT -t> Prop) (e' : TT -t> expr) := BuildRecFunOn {
  rec_fun_expr_eq : e = tele_app e' args;
  rec_fun_shape : tele_app shape args;
}.

Set Universe Minimization ToSet.
Unset Universe Polymorphism.

Fixpoint rec_apply (vr : val) (args : list val) : expr :=
  match args with
  | [] => vr
  | arg :: args' => (rec_apply vr args') arg
  end.

Class AsRecApply (e : expr) (vr : val) (args : list val) :=
  as_rec_apply : e = rec_apply vr args.

Global Instance as_rec_apply_base v f x eb :
  ((∀ f' x' v', SolveSepSideCondition (is_recursive_fun (RecV f' x' v') = true) →
      AsRecV (RecV f' x' v') f' x' v') → AsRecV v f x eb) →
  AsRecApply v v nil.
Proof. move => -> //. Qed.

Global Instance as_rec_apply_cons el (v2 vr : val) args :
  AsRecApply el vr args →
  AsRecApply (App el v2) vr (v2 :: args).
Proof. rewrite /AsRecApply => -> //. Qed.

Fixpoint list_to_tele {A : Type} (l : list A) : tele :=
  match l with
  | [] => TeleO
  | _ :: l' => TeleS (λ _ : A, list_to_tele l')
  end.

Fixpoint list_to_tele_arg {A : Type} (l : list A) : list_to_tele l :=
  match l return tele_arg $ list_to_tele l with
  | [] => TargO
  | a :: l' => TargS' (λ _ : A, list_to_tele l') a (list_to_tele_arg l')
  end.

Fixpoint tele_arg_to_list {A : Type} (l : list A) : list_to_tele l → list A :=
  match l return list_to_tele l → list A with
  | [] => λ _, []
  | _ :: l' => λ arg, arg.t1 :: tele_arg_to_list l' (arg.t2)
  end.

Lemma tele_arg_to_list_back {A : Type} (l : list A) :
  tele_arg_to_list l (list_to_tele_arg l) = l.
Proof.
  elim: l => //=.
  move => a l -> //.
Qed.

Definition has_löbbed (vr : val) : Prop := True.

Lemma has_löbbed_witness e : has_löbbed e.
Proof. exact I. Qed.

Global Opaque has_löbbed.

Class HasNotLöbbed (vr : val) := has_not_löbbed : True.

Global Hint Extern 4 (HasNotLöbbed ?e) =>
  lazymatch goal with
  | has_indeed : has_löbbed e |- _ => fail
  | |- _ => exact I
  end : typeclass_instances.

Global Instance make_as_rec_fun e vr args (TT2 : tele) (tt2 : TT2) l' :
  AsRecApply e vr args →
  HasNotLöbbed vr →
  AsFunOfAmongOthers args (list_to_tele_arg args) tt2 l' →
  AsRecFunOn e (TeleConcatType (list_to_tele args) (tele_bind (λ _ : list_to_tele args, TT2)))
      (tele_pair_arg (list_to_tele_arg args) tt2)
      (tele_curry $ tele_dep_bind (λ a, as_dependent_fun _ _ (
          tele_bind (λ tt2, fold_right and True $ zip_with eq (tele_app (tele_app l' tt2) a) (tele_arg_to_list _ a)
          )) a))
      (tele_curry $ tele_dep_bind (λ a : list_to_tele args,
      tele_bind (λ _ : ((λ.. _, TT2) a), rec_apply vr $ tele_arg_to_list args a))).
Proof.
  rewrite /AsRecApply /AsFunOfAmongOthers => -> _ Hargs.
  split.
  - rewrite tele_curry_uncurry_relation.
    rewrite -!tele_uncurry_curry_compose.
    rewrite !tele_dep_appd_bind.
    rewrite tele_app_bind. f_equal.
    rewrite tele_arg_to_list_back //.
  - rewrite tele_curry_uncurry_relation.
    rewrite -!tele_uncurry_curry_compose.
    rewrite !tele_dep_appd_bind.
    rewrite -dependent_fun_eq.
    rewrite tele_app_bind.
    rewrite Hargs. rewrite tele_arg_to_list_back //.
    clear. induction args => //=.
Qed.

Section hints.
  Context `{!heapGS Σ}.

  Set Universe Polymorphism.
  Unset Universe Minimization ToSet. (* hilarious *)

  Lemma rec_abduct e Φ TT args shape e' Φ' :
    AsRecFunOn e TT args shape e' →
    AsFunOfOnly Φ args Φ' →
    HINT1 ε₁ ✱
        [do_löb TT args (tele_map bi_pure shape) (tele_bind (λ tt, WP (tele_app e' tt) {{ (tele_app Φ' tt) }}))]
        ⊫ [id]; WP e {{ Φ }}.
  Proof.
    case => -> Hshape <-.
    rewrite /Abduct.
    iIntros "[_ H]".
    rewrite do_löb_eq /do_löb_def tele_app_bind.
    iSimpl. iApply "H". rewrite tele_map_app. done.
  Qed.

  Global Instance rec_abduct_2 e (Φ : val → iProp Σ) TT args shape e' (TT2 : tele) (args2 : TT2) eΦ' :
    AsRecFunOn e TT args shape e' →
    AsFunOfAmongOthers (e', Φ) args args2 eΦ' →
    HINT1 ε₁ ✱
        [do_löb (TelePairType TT TT2) (tele_pair_arg args args2)
            (tele_curry $ tele_dep_bind (λ tt1, tele_bind (λ _, ⌜tele_app shape tt1⌝)))
            (tele_curry $ tele_dep_bind (λ tt1, as_dependent_fun _ _  (
                tele_bind (λ tt2,
                  WP (tele_app (fst $ tele_app (tele_app eΦ' tt2) tt1) tt1) {{ (snd $ tele_app (tele_app eΦ' tt2) tt1) }}
                )
                ) tt1))
            (*(tele_bind (λ tt, WP (tele_app e' tt) {{ (tele_app Φ tt) }})) *)]
        ⊫ [id]; WP e {{ Φ }}.
  Proof.
    case => -> Hshape HeΦ.
    rewrite /Abduct.
    iIntros "[_ H]".
    rewrite do_löb_eq /do_löb_def.
    rewrite /tele_pair_arg.
    rewrite !tele_curry_uncurry_relation.
    rewrite -!tele_uncurry_curry_compose.
    rewrite !tele_dep_appd_bind.
    rewrite -!dependent_fun_eq.
    rewrite !tele_app_bind.
    rewrite HeΦ /=.
    iApply "H". done.
  Qed.

  Set Universe Minimization ToSet.
  Unset Universe Polymorphism.

  Global Instance post_löb_open_acquire e vr args f x eb Φ fa :
    AsRecApply e vr args →
    ((∀ f' x' v', AsRecV (RecV f' x' v') f' x' v') → AsRecV vr f x eb) →
    TCEq (last args) (Some fa) →
    HINT1 ε₁ ✱
        [▷ (⌜has_löbbed vr⌝ -∗ WP
          (fold_right (λ (ar : val) r, App r ar) (subst' x fa (subst' f vr eb)) (reverse (tl (reverse args))))
        {{ Φ }}) ]
        ⊫ [id]; post_löb (WP e {{ Φ }}).
  Proof.
    rewrite /AsRecApply => Hvr1 Hvr2 /TCEq_eq /last_Some [l' Hl]. subst.
    iStep. iSpecialize ("H1" with "[%//]").
    rewrite post_löb_eq /post_löb_def. simpl.
    iApply (lifting.wp_pure_step_fupd _ _ ⊤ _ (fold_right (λ (ar : val) r, App r ar) (subst' x fa (subst' f vr eb)) (reverse (tl (reverse (l' ++ [fa]))))) True 1).
    - rewrite reverse_snoc. simpl. rewrite reverse_involutive.
      induction l'; first tc_solve.
      eapply (pure_exec_ctx (fill_item (AppLCtx a))). apply IHl'.
    - done.
    - iIntros "!> !> !>". iSteps.
  Qed.

End hints.
