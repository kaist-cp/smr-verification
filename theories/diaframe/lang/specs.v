

From iris.bi Require Export bi telescopes derived_laws.
From iris.proofmode Require Import proofmode.
From diaframe.symb_exec Require Import defs weakestpre.
From diaframe Require Export spec_notation.
From diaframe Require Import proofmode_base.
From diaframe.lib Require Import iris_hints.
From smr.lang Require Import proofmode notation.
From smr.diaframe Require Import base_hints.

From iris.prelude Require Import options.

Import bi.

(* This file registers the specifications of heap_langs native (atomic) instructions, like
   CmpXchg, load, store and FAA instructions. These are written as SPEC, just like the specifications
   we prove in the examples. The main difference here is that to prove these specifications, we use
   lemma's provided by Iris's heap_lang. These are proven using the semantics of the language.

   We can use Diaframe's automation here, to partially 'bootstrap' ourselves. This is because
   Diaframe's automation will just stop when it does not know how to proceed.
 *)

Class PureExecNoRec φ n e1 e2 :=
  is_pure_exec : PureExec (Λ := heap_lang) φ n e1 e2.

Set Universe Polymorphism.

Section heap_lang_instances.
  Context `{!heapGS Σ}.

  Local Open Scope expr_scope.

  Global Instance pure_wp_step_exec_inst1 `(e : expr) φ n e' E s:
    PureExecNoRec φ n e e' → (* TODO: prevent unfolding explicit recs *)
    ReductionTemplateStep wp_red_cond (TeleO*TeleO) (ε₀)%I [tele_arg3 E;s] e
      (λ pr, tele_app (TT := [tele]) (tele_app (TT := [tele]) e' pr.1) pr.2)
      (template_M n id id TeleO TeleO ⌜φ⌝%I emp%I) | 80.
      (* used when φ is an equality on a new evar: this will cause SolveSepSideCondition to fail *)
      (* this is a ReductionTemplateStep: if it were a ReductionStep, the priority of as_template_step would be considered, not that of this instance *)
  Proof.
    intros.
    refine (pure_wp_step_exec _ _ _ _ _ _ _ _ _). exact H.
  Qed.

  Global Instance pure_wp_step_exec_inst2 (e : expr) φ n e' E s:
    PureExecNoRec φ n e e' →
    SolveSepSideCondition φ →
    ReductionTemplateStep wp_red_cond [tele] (ε₀)%I [tele_arg3 E; s] e (tele_app (TT := [tele]) e') (template_I n (fupd E E))%I | 8.
  Proof.
    intros. eapply pure_wp_step_exec2 => //. tc_solve.
  Qed.

  Global Instance load_step_wp (l : loc) E1 E2 s :
    SPEC ⟨E1, E2⟩ v q, {{ ▷ l ↦{q} v }} ! #l @ s {{ RET v; l ↦{q} v }}.
  Proof.
    iStepsS.
    iApply (wp_load with "H1").
    iStepsS.
  Qed.

  Global Instance allocN_step_wp e v E1 E2 (n : Z) s:
    IntoVal e v →
    SPEC ⟨E1, E2⟩ {{ ⌜0 < n⌝%Z }} AllocN #n e @ s
       {{ (l : blk)(sz : nat), RET #l; ⌜ n = sz ⌝ ∗ l ↦∗ replicate sz v ∗ †l … sz }} | 30.
  Proof.
    move => <- /=.
    iSteps.
    iApply wp_allocN => //. iSteps.
  Qed.

  Global Instance store_step_wp (l : loc) (v' : val) E1 E2 s :
    SPEC ⟨E1, E2⟩ v, {{ ▷ l ↦ v }} #l <- v' @ s {{ RET #(); l ↦ v' }}.
  Proof.
    iStepsS.
    iApply (wp_store with "H1").
    iStepsS.
  Qed.

  (* Global Instance free_step_wp (l : loc) e (n: nat)  E1 E2 s :
    IntoVal e () →
    SPEC ⟨E1, E2⟩ vs, {{ ▷ l ↦∗ vs ∗ †l … (length vs)}} Free e #n @ s {{ RET #(); True }}.
  Proof.
    iStepsS. wp_free.
    iApply (wp_free with "[H1]").
    iStepsS.
  Qed. *)

  Global Instance new_proph_step s :
    SPEC {{ True }} NewProph @ s {{ pvs (p : proph_id), RET #p; proph p pvs }}.
  Proof.
    iStepsS.
    iApply wp_new_proph; iStepsS.
  Qed.

  Global Instance abduct_resolve_atomic_spec K (e e_in : expr) (p : proph_id) (v : val) s Φ pre n E1 E2 (TT1 TT2 : tele)
      L e' v' U M1 M2 :
    ReshapeExprAnd expr e_in K (Resolve e #p v) (TCAnd (LanguageCtx K) $
                                                 TCAnd (Atomic StronglyAtomic e) $
                                                 TCAnd (Atomic WeaklyAtomic e) $ (SolveSepSideCondition (to_val e = None))) →
    ReductionStep' wp_red_cond pre n M1 M2 TT1 TT2 L U e e' [tele_arg3 E2; s] → (* does not work for pure since that is a ReductionTemplateStep *)
    IntroducableModality M1 → IntroducableModality M2 →
    (TC∀.. ttl, TC∀.. ttr, IntoVal (tele_app (tele_app e' ttl) ttr) (tele_app (tele_app v' ttl) ttr)) →
    HINT1 pre ✱ [|={E1, E2}=> ∃ pvs, proph p pvs ∗ ∃.. ttl, tele_app L ttl ∗
      ▷^n (∀ pvs', ∀.. ttr, ⌜pvs = (pair (tele_app (tele_app v' ttl) ttr) v)::pvs'⌝ ∗ proph p pvs' ∗ tele_app (tele_app U ttl) ttr ={E2,E1}=∗
            WP K $ tele_app (tele_app e' ttl) ttr @ s ; E1 {{ Φ }} ) ]
          ⊫ [id]; WP e_in @ s ; E1 {{ Φ }} | 45.
  Proof.
    case => -> [HK [He1 [He3 He2]]] HLU HM1 HM2 Hev'.
    iStepS. iApply wp_bind. iMod "H2" as (pvs) "[Hp Hwp]".
    { apply resolve_atomic. destruct s; try tc_solve. }
    iApply (wp_resolve with "Hp"); first apply He2. simpl.
    iDestruct "Hwp" as (ttl) "[Hl HΦ]".
    rewrite /ReductionStep' /ReductionTemplateStep in HLU.
    iPoseProof (HLU with "H1") as "HWP". simpl.
    iApply "HWP". iApply HM1 => /=.
    iExists ttl. iFrame. iIntros "!>" (tt2) "HU". iApply HM2 => /=.
    revert Hev'. rewrite /TCTForall /IntoVal => /(dep_eval_tele ttl) /(dep_eval_tele tt2) => Hev'.
    rewrite -Hev'.
    iApply wp_value. iIntros (pvs').
    iStepS.
    iStepS. iSpecialize ("H8" $! pvs' tt2). rewrite -Hev'. iApply "H8".
    iStepsS.
  Qed.

  Global Instance abduct_resolve_skip K (e_in : expr) (p : proph_id) (v : val) s E1 E2 Φ :
    ReshapeExprAnd expr e_in K (Resolve Skip #p v) (LanguageCtx K) →
    HINT1 ε₀ ✱ [|={E1, E2}=> ∃ pvs, proph p pvs ∗
      ▷ (∀ pvs', ⌜pvs = (pair (#()) v)::pvs'⌝ ∗ proph p pvs' ={E2,E1}=∗
            WP K $ #() @ s ; E1 {{ Φ }} ) ]
          ⊫ [id]; WP e_in @ s ; E1 {{ Φ }} | 45.
  Proof.
    case => -> HK.
    iStep as "Upd". iApply wp_bind. iMod "Upd". iDecompose "Upd" as (pvs) "pv Upd".
    iApply (wp_resolve with "pv"); [done | ].
    wp_pures. iStep 3 as (pvs) "Upd pv". iMod ("Upd" with "[$pv]"); done.
  Qed.

  Global Opaque vals_compare_safe.

  Global Instance cmpxchg_step_wp_stronger (l : loc) (v1 v2 : val) E1 E2 s :
    SPEC ⟨E1, E2⟩ (v : val) (q : dfrac),
      {{ ▷ l ↦{q} v ∗ ⌜vals_compare_safe v v1⌝ ∗ ⌜q = DfracOwn 1 ∨ v1 ≠ v⌝ }}
        CmpXchg #l v1 v2 @ s
      {{ (b : bool), RET (v, #b)%V;
          ⌜b = true⌝ ∗ ⌜v = v1⌝ ∗ l ↦{q} v2   ∨
          ⌜b = false⌝ ∗ ⌜v ≠ v1⌝ ∗ l ↦{q} v }}.
  Proof.
    iSteps as (v Hv | v q Hv Hneq) "l↦" | "l↦".
    - destruct (decide (v = v1)) as [->|Hneq].
      * iApply (wp_cmpxchg_suc with "l↦") => //.
        iSteps.
      * iApply (wp_cmpxchg_fail with "l↦") => //.
        iSteps.
    - iApply (wp_cmpxchg_fail with "l↦") => //.
      iSteps.
  Qed.

  Global Instance xchg_step_wp (l : loc) (v : val) E1 E2 s :
    SPEC ⟨E1, E2⟩ (v' : val), {{ ▷ l ↦ v' }}
      Xchg #l v @ s
    {{ RET v'; l ↦ v }}.
  Proof.
    iSteps as (v') "l↦".
    iApply (wp_xchg with "l↦").
    iSteps.
  Qed.

  Global Instance faa_step_wp (l : loc) (i : Z) E1 E2 s :
    SPEC ⟨E1, E2⟩ (z : Z), {{ ▷ l ↦ #z }} FAA #l #i @ s {{ RET #z; l ↦ #(z + i) }}.
  Proof.
    iSteps as (z) "l↦".
    iApply (wp_faa with "l↦").
    iSteps.
  Qed.

  (* There is no PureExec for an If statement with an abstract boolean. We create a reduction step for
      the case where this boolean is a bool_decide. *)

  Global Instance if_step_bool_decide P `{Decision P} e1 e2 E s :
    ReductionStep (wp_red_cond, [tele_arg3 E; s]) if: #(bool_decide P) then e1 else e2 ⊣ ⟨id⟩ emp; ε₀ =[▷^1]=>
      ∃ b : bool, ⟨id⟩ (if b then e1 else e2)%V ⊣ ⌜b = true⌝ ∗ ⌜P⌝ ∨ ⌜b = false⌝ ∗ ⌜¬P⌝| 50.
  Proof.
    (* texan_to_red_cond does not work here, since (if b then e1 else e2) is not a value! *)
    rewrite /ReductionStep' /=.
    apply forall_intro => Φ.
    iIntros "_ [_ H]".
    case_bool_decide; wp_pures => /=.
    - iApply ("H" $! true). eauto.
    - iApply ("H" $! false). eauto.
  Qed.

  Global Instance if_step_bool_decide_neg P `{Decision P} e1 e2 E s :
    ReductionStep (wp_red_cond, [tele_arg3 E; s]) if: #(bool_decide (¬P)) then e1 else e2 ⊣ ⟨id⟩ emp; ε₀ =[▷^1]=>
      ∃ b : bool, ⟨id⟩ (if b then e1 else e2)%V ⊣ ⌜b = true⌝ ∗ ⌜¬P⌝ ∨ ⌜b = false⌝ ∗ ⌜P⌝ | 49.
  Proof.
    rewrite /ReductionStep' /=.
    apply forall_intro => Φ.
    iIntros "_ [_ H]".
    case_bool_decide => /=.
    - wp_pures.
      iApply ("H" $! true). eauto.
    - wp_pures.
      iApply ("H" $! false). eauto.
  Qed.

End heap_lang_instances.

Section unfold_functions.
  Context `{!heapGS Σ}.

  Fixpoint occurs_in (s : string) (body : expr) : bool :=
    match body with
    | Val _ => false
    | Var s' => if decide (s = s') then true else false
    | Rec b x e => if decide (BNamed s ≠ b ∧ BNamed s ≠ x) then occurs_in s e else false
    | App f a => (occurs_in s f) || (occurs_in s a)
    | UnOp _ e => occurs_in s e
    | BinOp _ l r => (occurs_in s l) || (occurs_in s r)
    | If c t e => (occurs_in s c) || (occurs_in s t) || (occurs_in s e)
    | Pair l r => (occurs_in s l) || (occurs_in s r)
    | Fst e => (occurs_in s e)
    | Snd e => (occurs_in s e)
    | InjL e => (occurs_in s e)
    | InjR e => (occurs_in s e)
    | Case c l r => (occurs_in s c) || (occurs_in s l) || (occurs_in s r)
    | Fork e => (occurs_in s e)
    | AllocN n e => (occurs_in s n) || (occurs_in s e)
    | Free e1 e2 => (occurs_in s e1) || (occurs_in s e2)
    | Load e => (occurs_in s e)
    | Store l e => (occurs_in s l) || (occurs_in s e)
    | CmpXchg l e1 e2 => (occurs_in s l) || (occurs_in s e1) || (occurs_in s e2)
    | Xchg l e1 => (occurs_in s l) || (occurs_in s e1)
    | FAA l n => (occurs_in s l) || (occurs_in s n)
    | NewProph => false
    | Resolve a1 a2 a3 => (occurs_in s a1) || (occurs_in s a2) || (occurs_in s a3)
    end.

  Definition is_recursive_fun (v : val) :=
    match v with
    | RecV (BNamed f) x e => occurs_in f e
    | _ => false
    end.

  Global Instance pure_wp_step_exec_inst_last `(e : expr) φ n e' E s :
    ((∀ f x e, SolveSepSideCondition (is_recursive_fun (RecV f x e) = false) →
                AsRecV (RecV f x e) f x e) →
      PureExec φ n e e') →
    SolveSepSideCondition φ →
    ReductionTemplateStep wp_red_cond [tele] (ε₁)%I [tele_arg3 E; s] e (tele_app (TT := [tele]) e') (template_I n (fupd E E)).
  Proof.
    intros. eapply pure_wp_step_exec2 => //; first tc_solve.
    apply H. intros. exact eq_refl.
  Qed.

End unfold_functions.

Ltac find_reshape e K e' TC :=
  lazymatch e with
  | fill ?Kabs ?e_inner =>
    reshape_expr e_inner ltac:(fun K' e'' =>
      unify K (fill Kabs ∘ fill K'); unify e' e'';
      notypeclasses refine (ConstructReshape e (fill Kabs ∘ fill K') e'' _ (eq_refl) _); tc_solve )
  | _ =>
    reshape_expr e ltac:(fun K' e'' =>
      unify K (fill K'); unify e' e'';
      notypeclasses refine (ConstructReshape e (fill K') e'' _ (eq_refl) _); tc_solve )
  end.

Global Hint Extern 4 (ReshapeExprAnd expr ?e ?K ?e' ?TC) =>
  find_reshape e K e' TC : typeclass_instances.

Global Hint Extern 4 (ReshapeExprAnd (language.expr ?L) ?e ?K ?e' ?TC) =>
  unify L heap_lang;
  find_reshape e K e' TC : typeclass_instances.

Global Arguments heap_lang : simpl never.
  (* If not, cbn unfolds heap_lang, and this term is quite large, causing slowdowns in various places *)

Unset Universe Polymorphism.

Global Hint Extern 4 (PureExecNoRec _ _ ?e1 _) =>
  lazymatch e1 with
  | (App (Val ?v1) (Val ?v2)) =>
    assert_fails (assert (∃ f x erec,
      TCAnd (AsRecV v1 f x erec) $
      TCAnd (TCIf (TCEq f BAnon) False TCTrue)
            (SolveSepSideCondition (is_recursive_fun (RecV f x erec) = true))) by (do 3 eexists; tc_solve));
    unfold PureExecNoRec; tc_solve
  | _ => unfold PureExecNoRec; tc_solve
  end : typeclass_instances.
