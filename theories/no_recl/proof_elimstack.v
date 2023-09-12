From iris.algebra Require Import excl agree gset auth.
From iris.base_logic.lib Require Import invariants ghost_var ghost_map.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr Require Import helpers no_recl.spec_stack no_recl.code_elimstack.

Class elimstackG Σ := ElimstackG {
  elimstack_ghost_varG :> ghost_varG Σ (list val);
  elimstack_tokG :> inG Σ (exclR unitO);
}.

Definition elimstackΣ : gFunctors := #[ghost_varΣ (list val); GFunctor (exclR unitO)].

Global Instance subG_elimstackΣ {Σ} :
  subG elimstackΣ Σ → elimstackG Σ.
Proof. solve_inG. Qed.

Section elim_stack.
Context `{!heapGS Σ, !elimstackG Σ}.
Notation iProp := (iProp Σ).
Context (elimN : namespace).
Let stackN := elimN .@ "stack".
Let offerN := elimN .@ "offer".

(* iExists + iFrame *)
Ltac exfr := repeat (repeat iExists _; iFrame "∗#%").

Fixpoint phys_list (lopt : option loc) (xs : list val) : iProp :=
  match (lopt, xs) with
  | (None  , []     ) => True
  | (None  , _ :: _ ) => False
  | (Some _, []     ) => False
  | (Some l, x :: xs) => ∃ n,
      l ↦∗□ [ x; #(oloc_to_lit n) ] ∗
      phys_list n xs
  end.

Inductive offer_state := OfferPending | OfferRevoked | OfferAccepted | OfferAcked.

Local Instance offer_state_eq_dec : EqDecision offer_state.
Proof. solve_decision. Qed.

Local Instance: Inhabited offer_state := populate OfferPending.

Definition offer_state_rep (st : offer_state) : Z :=
  match st with
  | OfferPending => 0
  | OfferRevoked => 2
  | OfferAccepted => 1
  | OfferAcked => 1
  end.

(* NOTE: If we put everything inside `offer_inv` into Managed, then
   the existential quantifier of `P` and `Q` makes everything difficult
   since we lose the information of `P` and `Q` in the second opening of the invariant.
   (--> thus, we cannot apply laterable AU in last step of `OfferPending` case in the proof of `push`)
   But, by maintaining small invariant of `offer_inv` in the iris context,
   we can avoid second bound of `P` and `Q`, which resolves the problem. *)
Definition offer_inv (offer_loc : loc) (γo : gname) (P Q : iProp) : iProp :=
  ∃ (st : offer_state), (offer_loc +ₗ state) ↦ #(offer_state_rep st) ∗
    match st with
    | OfferPending => P
    | OfferAccepted => Q
    | _ => own γo (Excl ())
    end.

(* Ownership of the stack *)
Definition EStack (γ : gname) (xs : list val) : iProp :=
  ∃ (γs γof : gname), ⌜γ = encode(γs, γof)⌝ ∗ ghost_var γs (1/2)%Qp xs.

Global Instance EStack_Timeless γ xs: Timeless (EStack γ xs).
Proof. apply _. Qed.

Definition stack_push_au γ v Q : iProp :=
  AU << ∃∃ l, EStack γ l>> @ ⊤∖↑elimN,∅ << EStack γ (v :: l), COMM Q >>.

Definition IsOffer (γ : gname) (offer_rep : option loc) : iProp :=
  match offer_rep with
  | None => True
  | Some (offer_loc) =>
    ∃ Q v (γs γo γof : gname),
      ⌜γ = encode (γs, γof)⌝ ∗
      inv offerN (offer_inv offer_loc γo (stack_push_au γ v Q) Q) ∗
      offer_loc ↦□ v
  end.

Definition OfferInternalInv (st : loc) (γ γs γof : gname) : iProp :=
  ∃ offer_rep,
    (st +ₗ offer) ↦ #(oloc_to_lit offer_rep) ∗
    IsOffer γ offer_rep.

Definition EStackInternalInv (st : loc) (γ γs γof : gname) : iProp :=
  ∃ (h : option loc) (xs : list val),
    phys_list h xs ∗ (st +ₗ head) ↦ #(oloc_to_lit h) ∗ ghost_var γs (1/2)%Qp xs ∗
    OfferInternalInv st γ γs γof.

(* Persistent assertions about the stack *)
Definition IsEStack (γ : gname) (st : loc) : iProp :=
  ∃ (γs γof : gname),
    ⌜γ = encode(γs, γof)⌝ ∗
    inv stackN (EStackInternalInv st γ γs γof).

Global Instance IsEStack_Persistent γ l : Persistent (IsEStack γ l).
Proof. apply _. Qed.

Lemma estack_new_spec :
  stack_new_spec' elimN estack_new EStack IsEStack.
Proof.
  iIntros (Φ _) "!> HΦ".
  wp_lam. wp_alloc st as "st↦" "†st". wp_pures.
  do 2 (wp_apply (wp_store_offset with "st↦") as "st↦"; [by simplify_list_eq|]; wp_pures).
  rewrite array_cons array_singleton. iDestruct "st↦" as "[st.h↦ st.of↦]".
  iMod (ghost_var_alloc []) as (γs) "[Hγs Hγs']".
  iMod (ghost_map_alloc_empty) as (γof) "Hγof".
  remember (encode (γs, γof)) as γ eqn:Hγ.
  iMod (inv_alloc stackN _ (EStackInternalInv st γ γs γof) with "[st.h↦ st.of↦ Hγs Hγof]") as "#Hinv_stack".
  { iNext. iExists None, []. rewrite /= loc_add_0. iFrame. iExists None. by iFrame. }
  iApply "HΦ". iSplitR "Hγs'"; by exfr.
Qed.

Lemma estack_push_spec :
  stack_push_spec' elimN estack_push EStack IsEStack.
Proof using All.
  iIntros (γ st x) "#Hst".
  iIntros (Φ) "AU".
  iDestruct "Hst" as (γs γof) "(%Hγ & #Hinv_stack)".
  iLöb as "IH".
  wp_rec. wp_pures. wp_bind (! _)%E.
  iInv "Hinv_stack" as (h1 xs1) "(Hplist & >st.h↦ & >Hγs & Hoffer)" "Hclose".
  wp_load.
  iMod ("Hclose" with "[Hplist st.h↦ Hγs Hoffer]") as "_"; first by exfr.
  iModIntro. wp_let. wp_alloc n as "n↦" "†n".
  wp_let. wp_op.
  do 2 (wp_apply (wp_store_offset with "n↦") as "n↦"; [by simplify_list_eq|]; wp_pures).
  wp_bind (CmpXchg _ _ _).
  iInv "Hinv_stack" as (h2 xs2) "(Hplist & >st.h↦ & >Hγs & Hoffer)" "Hclose".
  destruct (decide (h1 = h2)) as [->|NEQ].
  - (* CAS success --> similar proof as treiber stack *)
    clear xs1. wp_cmpxchg_suc.
    iMod "AU" as (xs) "[Hst [_ Commit]]".
    iDestruct "Hst" as (γs' γof') "[%Hγ' Hγs']". encode_agree Hγ.
    iDestruct (ghost_var_agree with "Hγs Hγs'") as %<-.
    iMod (ghost_var_update_halves (x :: xs2) with "Hγs Hγs'") as "[Hγs Hγs']".
    iMod ("Commit" with "[Hγs']") as "HΦ"; first by exfr.
    iMod (array_persist with "n↦") as "#n↦".
    iMod ("Hclose" with "[st.h↦ Hplist Hγs Hoffer]") as "_".
    { iExists (Some (blk_to_loc n)), (x :: xs2). simpl. exfr. }
    iModIntro. wp_pures. by iApply "HΦ".
  - (* CAS failed --> make an offer *)
    wp_cmpxchg_fail; [destruct h1, h2; simpl; naive_solver..|].
    iMod ("Hclose" with "[Hplist st.h↦ Hγs Hoffer]") as "_"; first by exfr.
    iModIntro. wp_pures.
    wp_apply (wp_store_offset with "n↦") as "n↦"; [by simplify_list_eq|]; wp_pures.
    rewrite array_cons array_singleton. iDestruct "n↦" as "[n.x↦ n.st↦]".
    (* make an offer *)
    iMod (own_alloc (Excl ())) as (γo) "Htok"; [done|].
    wp_bind (_ <- _)%E. clear NEQ h2 xs2.
    iInv "Hinv_stack" as (h2 xs2) "(Hplist & >st.h↦ & >Hγs & (%offer_rep & st.of↦ & _))".
    wp_store.
    iMod (mapsto_persist with "n.x↦") as "#n.x↦".
    iMod (inv_alloc offerN _ (offer_inv n γo (stack_push_au _ _ _) _) with "[AU n.st↦]") as "#Hinv_noffer".
    { iExists OfferPending. iFrame. }

    iModIntro. iSplitL "Hplist st.h↦ Hγs st.of↦".
    { repeat iExists _. iFrame "∗#%". iExists (Some _). iFrame "∗#%". exfr. }
    (* Retract the offer *)
    wp_pures. wp_bind (_ <- _)%E. clear h2 xs2.
    iInv "Hinv_stack" as (h2 xs2) "(Hplist & >st.h↦ & >Hγs & (%offer_rep' & st.of↦ & _))".
    wp_store.
    (* Obtain the managed pointer again *)
    iModIntro. iSplitL "Hplist st.h↦ Hγs st.of↦".
    { repeat iExists _. iFrame "∗#%". iExists None. iFrame "∗#%". }
    (* See if someone took it *)
    wp_pure credit:"Hlc". wp_pures.
    wp_bind (CmpXchg _ _ _). clear offer_rep h2 xs2.
    iInv "Hinv_stack" as (h2 xs2) "(Hplist & >st.h↦ & >Hγs & (%offer_rep & st.of↦ & Hio))".
    (* iDestruct (ghost_map_lookup with "γof key") as %res. *)
    iInv "Hinv_noffer" as (stat) "[>n.st↦ Hstat]".
    destruct stat.
    + (* OfferPending *)
      wp_cmpxchg_suc; first done.
      iModIntro. iSplitL "n.st↦ Htok". { iExists OfferRevoked. iFrame "∗". }
      iModIntro. iSplitL "Hplist st.h↦ Hγs Hio st.of↦"; [exfr|].
      wp_pure. wp_if. wp_apply ("IH" with "Hstat").
    + (* OfferRevoked --> impossible case *)
      by iDestruct (own_valid_2 with "Htok Hstat") as ">%".
    + (* OfferAccepted *)
      wp_cmpxchg_fail.
      iModIntro. iSplitL "n.st↦ Htok". { iExists OfferAcked. iFrame "∗". }
      iModIntro. iSplitL "Hplist st.h↦ Hγs Hio st.of↦"; [exfr|].
      wp_pures. by iApply "Hstat".
    + (* OfferAcked --> impossible case *)
      by iDestruct (own_valid_2 with "Htok Hstat") as ">%".
Qed.

Lemma estack_pop_spec :
  stack_pop_spec' elimN estack_pop EStack IsEStack.
Proof using All.
  iIntros (γ st) "#Hstack".
  iDestruct "Hstack" as (γs γof) "(%Hγ & Hinv_stack)".
  iIntros (Φ) "AU".
  iLöb as "IH".
  wp_rec. wp_pures. wp_bind (! _)%E.
  iInv "Hinv_stack" as (h1 xs1) "(Hplist & >st.h↦ & >Hγs & Hoffer)".
  destruct h1 as [h1|]; destruct xs1 as [|x1 xs1]; simpl;
  try (iMod "Hplist"; done); last first.
  { (* empty stack case *)
    wp_load.
    iMod "AU" as (xs) "[EStack [_ Commit]]".
    iDestruct "EStack" as (γs' γof') "[%Hγ' Hγs']". encode_agree Hγ.
    iDestruct (ghost_var_agree with "Hγs Hγs'") as %<-.
    iMod ("Commit" with "[Hγs']") as "HΦ"; first by exfr.
    iModIntro. iSplitL "st.h↦ Hγs Hoffer".
    { iExists None, []. iFrame. }
    wp_pures.
    iApply "HΦ". done. }
  (* nonempty stack case *)
  iDestruct "Hplist" as (n1) "[#h1↦ Hplist]".
  wp_load. iModIntro. iSplitR "AU".
  { iExists (Some h1), (x1 :: xs1). exfr. }
  wp_pures. wp_apply (wp_load_offset with "h1↦") as "_"; [by simplify_list_eq|].
  wp_pures. wp_bind (CmpXchg _ _ _).
  iInv "Hinv_stack" as (h2 xs2) "(Hplist & >st.h↦ & >Hγs & Hoffer)".
  destruct (decide (h2 = Some h1)) as [->|NE].
  - (* CAS success *)
    simpl. wp_cmpxchg_suc.
    iMod "AU" as (xs) "[EStack [_ Commit]]".
    iDestruct "EStack" as (γs' γof') "[%Hγ' Hγs']". encode_agree Hγ.
    iDestruct (ghost_var_agree with "Hγs Hγs'") as %<-.
    destruct xs2 as [|x2 xs2]; [iDestruct "Hplist" as %[]|].
    iMod (ghost_var_update_halves xs2 with "Hγs Hγs'") as "[Hγs Hγs']".
    iMod ("Commit" with "[Hγs']") as "HΦ"; first by exfr.
    simpl. iDestruct "Hplist" as (n2) "(#h1'↦ & Hplist)".
    iDestruct (array_agree with "h1↦ h1'↦") as %[= <- <-]; [done|].
    iModIntro. iSplitL "Hplist st.h↦ Hγs Hoffer"; first by exfr.
    wp_pures. wp_apply (wp_load_offset with "h1↦") as "_"; [by simplify_list_eq|].
    wp_pures. iApply "HΦ". done.
  - (* CAS failed --> take an offer *)
    wp_cmpxchg_fail.
    iModIntro. iSplitL "Hγs st.h↦ Hplist Hoffer"; first by exfr.
    wp_pures. wp_bind (! _)%E. clear NE h2 xs2.
    iInv "Hinv_stack" as (h2 xs2) "(Hplist & >st.h↦ & >Hγs & (%offer_rep & st.of↦ & Hio))".
    destruct offer_rep as [n|]; last first.
    { (* no offer *)
      wp_load.
      iModIntro. iSplitL "Hplist st.h↦ Hγs st.of↦"; first by exfr.
      wp_pures. wp_apply ("IH" with "AU"). }
    (* offer exists *)
    iDestruct "Hio" as (Q v ???) "(>% & #Hinv_noffer & #>n.x↦)". wp_load. encode_agree Hγ.
    iModIntro. iSplitL "Hplist st.h↦ Hγs st.of↦"; first by exfr.
    wp_pure credit:"Hlc". wp_pures. wp_bind (CmpXchg _ _ _).
    clear h2 xs2.
    iInv "Hinv_noffer" as (stat) "[n.st↦ Hstat]".

    destruct (decide (stat = OfferPending)) as [->|]; last first.
    { (* CAS at state position failed *)
      wp_cmpxchg_fail; first by destruct stat.
      iModIntro. iSplitL "n.st↦ Hstat"; [exfr|].
      wp_pures. wp_apply ("IH" with "AU"). }
    (* CAS at state position succeeded *)
    wp_cmpxchg_suc; first done.
    iInv "Hinv_stack" as (h2 xs2) "(Hplist & >st.h↦ & >Hγs & (%offer_rep & st.of↦ & Hio))".

    iMod "Hstat" as (l) "[Hstack [_ Commit]]".
    iDestruct "Hstack" as (γs' γof') "[%Hγ' Hγs']". encode_agree Hγ.
    iDestruct (ghost_var_agree with "Hγs Hγs'") as %<-.
    iMod (ghost_var_update_halves (v :: xs2) with "Hγs Hγs'") as "[Hγs Hγs']".
    iMod ("Commit" with "[Hγs']") as "HQ"; first by exfr.
    iMod "AU" as (xs) "[Hstack [_ Commit]]".
    iDestruct "Hstack" as (γs' γof') "[%Hγ' Hγs']". encode_agree Hγ.
    iDestruct (ghost_var_agree with "Hγs Hγs'") as %<-.
    iMod (ghost_var_update_halves xs2 with "Hγs Hγs'") as "[Hγs Hγs']".
    iMod ("Commit" with "[Hγs']") as "HΦ"; first by exfr.
    iModIntro. iSplitL "Hplist st.h↦ st.of↦ Hio Hγs".
    { exfr. }
    iModIntro. iSplitL "n.st↦ HQ".
    { iExists OfferAccepted. iFrame "∗". }
    wp_pures. rewrite loc_add_0. wp_load. wp_pures.
    iApply "HΦ". done.
Qed.

#[export] Typeclasses Opaque EStack IsEStack.

End elim_stack.
