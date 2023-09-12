From iris.algebra Require Import excl agree gset auth.
From iris.base_logic.lib Require Import invariants ghost_var ghost_map.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr Require Import helpers ebr.spec_rcu_simple ebr.spec_stack ebr.code_elimstack.

Inductive offer_state := OfferPending | OfferRevoked | OfferAccepted | OfferAcked.

Local Instance offer_state_eq_dec : EqDecision offer_state.
Proof. solve_decision. Qed.

Class elimstackG Σ := ElimstackG {
  elimstack_ghost_varG :> ghost_varG Σ (list val);
  elimstack_inG :> inG Σ (agreeR (prodO valO (optionO blkO)));
  elimstack_tokG :> inG Σ (exclR unitO);
  elimstack_ghost_var2G :> ghost_varG Σ offer_state;
  elimstack_offer_gmapG :> ghost_mapG Σ blk gname;
  elimstack_var_tokG :> inG Σ (agreeR valO);
}.

Definition elimstackΣ : gFunctors := #[ghost_varΣ (list val); GFunctor (agreeR (prodO valO (optionO blkO))); GFunctor (exclR unitO); ghost_varΣ offer_state; ghost_mapΣ blk gname; GFunctor (agreeR valO)].

Global Instance subG_elimstackΣ {Σ} :
  subG elimstackΣ Σ → elimstackG Σ.
Proof. solve_inG. Qed.

Section elim_stack.
Context `{!heapGS Σ, !elimstackG Σ}.
Notation iProp := (iProp Σ).
Context (elimN rcuN : namespace) (DISJN : elimN ## rcuN).
Let stackN := elimN .@ "stack".
Let offerN := elimN .@ "offer".

(* iExists + iFrame *)
Ltac exfr := repeat (repeat iExists _; iFrame "∗#%").

Variable (rcu : rcu_simple_spec Σ rcuN).

Definition node_info γ_p (x : val) (n : option blk) :=
  own γ_p (to_agree (x, n)).

Definition node (p : loc) lv γ_p : iProp :=
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

Local Instance: Inhabited offer_state := populate OfferPending.

Definition offer_state_rep (st : offer_state) : Z :=
  match st with
  | OfferPending => 0
  | OfferRevoked => 2
  | OfferAccepted => 1
  | OfferAcked => 1
  end.

Definition offer_info γ_p (v : val) (st : offer_state) : iProp :=
  ∃ (γ_pv γ_po : gname), ⌜γ_p = encode (γ_pv, γ_po)⌝ ∗ ghost_var γ_pv (1/2)%Qp st ∗ own γ_po (to_agree v).

Definition offer_data (p : loc) lv γ_p : iProp :=
  ∃ x st, ⌜lv = [ x; #(offer_state_rep st) ]⌝ ∗ offer_info γ_p x st.

(* NOTE: If we put everything inside `offer_inv` into Managed, then
   the existential quantifier of `P` and `Q` makes everything difficult
   since we lose the information of `P` and `Q` in the second opening of the invariant.
   (--> thus, we cannot apply laterable AU in last step of `OfferPending` case in the proof of `push`)
   But, by maintaining small invariant of `offer_inv` in the iris context,
   we can avoid second bound of `P` and `Q`, which resolves the problem. *)
Definition offer_inv (offer_loc : blk) (v : val) (γn γo : gname) (P Q : iProp) : iProp :=
  ∃ (st : offer_state), offer_info γn v st ∗
    match st with
    | OfferPending => P
    | OfferAccepted => Q
    | _ => own γo (Excl ())
    end.

(* Ownership of the stack *)
Definition EStack (γ : gname) (xs : list val) : iProp :=
  ∃ (γs γof : gname), ⌜γ = encode(γs, γof)⌝ ∗ ghost_var γs (1/2)%Qp xs.

Global Instance EStack_Timeless γs xs: Timeless (EStack γs xs).
Proof. apply _. Qed.

Definition stack_push_au γ v Q : iProp :=
  AU << ∃∃ l, EStack γ l>> @ ⊤∖(↑elimN ∪ ↑ptrsN rcuN),↑mgmtN rcuN << EStack γ (v :: l), COMM Q >>.

Definition IsOffer (γe γ : gname) (offer_rep : option blk) (offers : gmap blk gname) : iProp :=
  match offer_rep with
  | None => True
  | Some (offer_loc) =>
    ∃ Q v (γs γn γo γof : gname),
      ⌜γ = encode (γs, γof)⌝ ∗
      inv offerN (offer_inv offer_loc v γn γo (stack_push_au γ v Q) Q) ∗
      ⌜offers !! offer_loc = Some γn⌝
  end.

Definition OfferInternalInv (st : loc) (γe γ γs γof : gname) : iProp :=
  ∃ offer_rep (offers : gmap blk gname),
    (st +ₗ offer) ↦ #(oblk_to_lit offer_rep) ∗
    IsOffer γe γ offer_rep offers ∗
    ghost_map_auth γof 1 offers ∗
    [∗ map] off ↦ γn ∈ offers, rcu.(Managed) γe off γn nodeSize offer_data.

Definition EStackInternalInv (st : loc) (γe γ γs γof : gname) : iProp :=
  ∃ (h : option blk) (xs : list val),
    phys_list γe h xs ∗ (st +ₗ head) ↦ #(oblk_to_lit h) ∗ ghost_var γs (1/2)%Qp xs ∗
    OfferInternalInv st γe γ γs γof.

(* Persistent assertions about the stack *)
Definition IsEStack (γe γ : gname) (st : loc) : iProp :=
  ∃ (d : loc) (γs γof : gname),
    ⌜γ = encode(γs, γof)⌝ ∗
    (st +ₗ domain) ↦□ #d ∗ rcu.(IsRCUDomain) γe d ∗
    inv stackN (EStackInternalInv st γe γ γs γof).

Global Instance IsEStack_Persistent γe γ l : Persistent (IsEStack γe γ l).
Proof. apply _. Qed.

Lemma estack_new_spec :
  stack_new_spec' elimN rcuN estack_new rcu EStack IsEStack.
Proof.
  iIntros (γe d Φ) "!> #IED HΦ".
  wp_lam. wp_alloc st as "st↦" "†st". wp_pures.
  repeat (wp_apply (wp_store_offset with "st↦") as "st↦"; [by simplify_list_eq|]; wp_pures).
  rewrite !array_cons !loc_add_assoc.
  iDestruct "st↦" as "(st.h↦ & st.of↦ & st.d↦ & _)".
  iMod (ghost_var_alloc []) as (γs) "[Hγs Hγs']".
  iMod (ghost_map_alloc_empty) as (γof) "Hγof".
  remember (encode (γs, γof)) as γ eqn:Hγ.
  iMod (mapsto_persist with "st.d↦") as "#st.d↦".
  iMod (inv_alloc stackN _ (EStackInternalInv st γe γ γs γof) with "[st.h↦ Hγs st.of↦ Hγof]") as "#Hinv_stack".
  { iNext. iExists None, []. rewrite loc_add_0. iFrame. iExists None, ∅. by iFrame. }
  iApply ("HΦ" $! γ). iSplitR "Hγs'"; by exfr.
Qed.

Lemma estack_push_spec :
  stack_push_spec' elimN rcuN (estack_push rcu) rcu EStack IsEStack.
Proof using All.
  iIntros (γe γ st g x) "Hstack G".
  iIntros (Φ) "AU".
  iDestruct "Hstack" as (d γs γof) "(%Hγ & st.d↦ & #IED & #Hinv_stack)".
  iLöb as "IH".
  wp_rec. wp_pures. wp_bind (! _)%E.
  iInv "Hinv_stack" as (h1 xs1) "(Hplist & >st.h↦ & >Hγs & Hoffer)".
  wp_load. iSplitL "Hplist st.h↦ Hγs Hoffer"; first by exfr.
  iModIntro. wp_let. wp_alloc n as "n↦" "†n". wp_let. wp_op.
  do 2 (wp_apply (wp_store_offset with "n↦") as "n↦"; [by simplify_list_eq|]; wp_pures).
  wp_bind (CmpXchg _ _ _).
  iInv "Hinv_stack" as (h2 xs2) "(Hplist & >st.h↦ & >Hγs & Hoffer)".
  destruct (decide (h1 = h2)) as [->|NEQ].
  - (* CAS success --> similar proof as treiber stack *)
    clear xs1. wp_cmpxchg_suc.
    iMod (own_alloc (to_agree (x, h2))) as (γn) "#Hγn"; [done|].
    iMod (rcu.(rcu_domain_register) node with "IED [$n↦ $†n]") as "G_new"; [solve_ndisj|by exfr|].
    iMod "AU" as (xs) "[Hst [_ Commit]]".
    iDestruct "Hst" as (γs' γof') "[%Hγ' Hγs']". encode_agree Hγ.
    iDestruct (ghost_var_agree with "Hγs Hγs'") as %<-.
    iMod (ghost_var_update_halves (x :: xs2) with "Hγs Hγs'") as "[Hγs Hγs']".
    iMod ("Commit" with "[Hγs']") as "HΦ"; first by exfr.
    iModIntro. iSplitL "st.h↦ Hplist Hγs Hγn G_new Hoffer".
    { iExists (Some n), _. by exfr. }
    wp_pures. by iApply "HΦ".
  - (* CAS failed --> make an offer *)
    wp_cmpxchg_fail; [destruct h1, h2; simpl; naive_solver..|].
    iSplitL "Hplist st.h↦ Hγs Hoffer"; first by exfr.
    iModIntro. wp_pures.
    wp_apply (wp_store_offset with "n↦") as "n↦"; [by simplify_list_eq|]; wp_pures.
    (* make an offer *)
    iMod (own_alloc (Excl ())) as (γo) "Htok"; [done|].
    iMod (ghost_var_alloc OfferPending) as (γn_v) "[Hγn_v Hγn_v']".
    iMod (own_alloc (to_agree x)) as (γn_o) "#Hγn_o"; [done|].
    remember (encode (γn_v, γn_o)) as γn eqn:Hγn.
    iMod (rcu.(rcu_domain_register) offer_data with "IED [$n↦ $†n Hγn_o Hγn_v]") as "G_new"; [solve_ndisj|..].
    { iExists _, OfferPending. iSplitR; by exfr. }
    iMod (inv_alloc offerN _ (offer_inv n x γn γo (stack_push_au _ _ _) _) with "[AU Hγn_v']") as "#Hinv_noffer".
    { iExists OfferPending. exfr. }
    wp_bind (_ <- _)%E. clear NEQ h2 xs2.
    iInv "Hinv_stack" as (h2 xs2) "(Hplist & >st.h↦ & >Hγs & (%offer_rep & %offers & st.of↦ & _ & >γof & Hoffers))".
    wp_store.
    destruct (offers !! n) eqn:Hn.
    { rewrite big_sepM_lookup_acc; [|apply Hn].
      iDestruct "Hoffers" as "[G_new' _]".
      iDestruct (rcu.(managed_exclusive) with "G_new G_new'") as %[]. }
    iMod (ghost_map_insert _ γn with "γof") as "[γof key]"; [apply Hn|].
    iDestruct (big_sepM_insert with "[$Hoffers $G_new]") as "Hoffers"; [done|].
    iModIntro. iSplitL "Hplist st.h↦ Hγs st.of↦ γof Hoffers".
    { repeat iExists _. iFrame "∗#%". iExists (Some n), _. iFrame "∗#%". exfr. by simplify_map_eq. }
    (* Retract the offer *)
    wp_pures. wp_bind (_ <- _)%E. clear h2 xs2.
    iInv "Hinv_stack" as (h2 xs2) "(Hplist & >st.h↦ & >Hγs & (%offer_rep' & %offers' & st.of↦ & _ & >γof & Hoffers))".
    wp_store.
    (* Obtain the managed pointer again *)
    iDestruct (ghost_map_lookup with "γof key") as %res.
    rewrite big_sepM_delete; [|apply res]. clear res.
    iDestruct "Hoffers" as "[G_new Hoffers]".
    iMod (ghost_map_delete with "γof key") as "γof".
    iModIntro. iSplitL "Hplist st.h↦ Hγs st.of↦ γof Hoffers".
    { repeat iExists _. iFrame "∗#%". iExists None. exfr. }
    (* See if someone took it *)
    wp_pure credit:"Hlc". wp_pures.
    wp_bind (CmpXchg _ _ _). clear offer_rep Hn offers h2 xs2.
    iInv "G_new" as (lv) "(_ & n↦ & >Hod & G_new)".
    iDestruct "Hod" as (v stat) "[-> (%γn_v' & %γn_o' & %Hγn' & Hγn_v & #Hγn_o')]". encode_agree Hγn.
    iCombine "Hγn_o Hγn_o'" gives %<-%to_agree_op_inv_L. iClear "Hγn_o'".
    iInv "Hinv_noffer" as (stat') "[>(%γn_v' & %γn_o' & %Hγn' & Hγn_v' & _) Hstat']" "Hclose". encode_agree Hγn.
    destruct stat; simpl.
    + (* OfferPending *)
      wp_apply (wp_cmpxchg_suc_offset with "n↦") as "n↦"; [by simplify_list_eq|done|by constructor|].
      iDestruct (ghost_var_agree with "Hγn_v Hγn_v'") as %<-.
      iMod (ghost_var_update_halves OfferRevoked with "Hγn_v Hγn_v'") as "[Hγn_v Hγn_v']".
      iMod ("Hclose" with "[Hγn_v' Htok]") as "_".
      { iExists OfferRevoked. exfr. }
      do 2 iModIntro. iSplitL "n↦ Hγn_v".
      { iExists _. iFrame "n↦". iSplitR; first done. iExists _, OfferRevoked. iSplit; first done. exfr. }
      iMod (lc_fupd_elim_later with "Hlc Hstat'") as "AU".
      wp_pures. wp_load. wp_let.
      wp_apply (rcu.(rcu_domain_retire_spec) with "IED G_new") as "_"; [solve_ndisj|].
      wp_seq. wp_apply ("IH" with "st.d↦ G AU").
    + (* OfferRevoked --> impossible case *)
      iDestruct (ghost_var_agree with "Hγn_v Hγn_v'") as %<-.
      iDestruct "Hstat'" as ">Htok'".
      iCombine "Htok Htok'" gives %[].
    + (* OfferAccepted *)
      wp_apply (wp_cmpxchg_fail_offset with "n↦") as "n↦"; [by simplify_list_eq|done|by constructor|].
      iDestruct (ghost_var_agree with "Hγn_v Hγn_v'") as %<-.
      iMod (ghost_var_update_halves OfferAcked with "Hγn_v Hγn_v'") as "[Hγn_v Hγn_v']".
      iMod ("Hclose" with "[Hγn_v' Htok]") as "_". { iExists OfferAcked. exfr. }
      do 2 iModIntro. iSplitL "n↦ Hγn_v".
      { iExists _. iFrame "n↦". iSplit; [done|]. iExists _, OfferAcked. iSplit; [done|]. exfr. }
      wp_pures. wp_load. wp_let.
      wp_apply (rcu.(rcu_domain_retire_spec) with "IED G_new") as "_"; [solve_ndisj|].
      wp_pures. by iApply "Hstat'".
    + (* OfferAcked --> impossible case *)
      iDestruct (ghost_var_agree with "Hγn_v Hγn_v'") as %<-.
      iMod "Hstat'". iCombine "Htok Hstat'" gives %[].
Qed.

Lemma estack_pop_spec :
  stack_pop_spec' elimN rcuN (estack_pop rcu) rcu EStack IsEStack.
Proof using All.
  iIntros (γe γ st g) "Hstack G".
  iDestruct "Hstack" as (d γs γof) "(%Hγ & #st.d↦ & #IED & #Hinv_stack)".
  iIntros (Φ) "AU".
  wp_lam. wp_pures.
  wp_apply (rcu.(guard_activate_spec) with "IED G") as (?) "G"; [solve_ndisj|].
  wp_seq. wp_bind (estack_pop_loop _ _).
  iLöb as "IH".
  wp_rec. wp_pures. wp_bind (! _)%E.
  iInv "Hinv_stack" as (h1 xs1) "(Hplist & >st.h↦ & >Hγs & Hoffer)" "Hclose".
  wp_load.
  destruct h1 as [h1|]; destruct xs1 as [|x1 xs1]; simpl;
  try (iDestruct "Hplist" as %[]); last first.
  { (* empty stack case *)
    iMod "AU" as (xs) "[EStack [_ Commit]]".
    iDestruct "EStack" as (γs' γof') "[%Hγ' Hγs']". encode_agree Hγ.
    iDestruct (ghost_var_agree with "Hγs Hγs'") as %<-.
    iMod ("Commit" with "[Hγs']") as "HΦ"; first by exfr.
    iMod ("Hclose" with "[st.h↦ Hγs Hoffer]") as "_".
    { iExists None, []. exfr. }
    iModIntro. wp_pures.
    wp_apply (rcu.(guard_deactivate_spec) with "IED G") as "G"; [solve_ndisj|].
    wp_pures. iApply "HΦ". by iFrame. }
  (* nonempty stack case *)
  iDestruct "Hplist" as (γ_h1 n1) "(G_h1 & #Info_h1 & Hplist)".
  iMod (rcu.(guard_protect) with "IED G_h1 G") as "(G_h1 & G & #h1Info)"; [solve_ndisj|].
  iMod ("Hclose" with "[- G AU]") as "_".
  { iExists (Some h1), (x1 :: xs1). iFrame. simpl. iExists γ_h1, n1. iFrame "∗#%". }
  iModIntro. wp_pures. wp_bind (! _)%E.
  wp_apply (guard_read node with "[$h1Info $G]") as (??) "(G & #Info_h1' & %EQ)"; [solve_ndisj|lia|].
  iDestruct "Info_h1'" as (x1' n1') "[-> Info_h1']". injection EQ as [= <-].
  iCombine "Info_h1 Info_h1'" gives %[= <- <-]%to_agree_op_inv_L.
  iClear "Info_h1'".
  wp_let. wp_op. wp_bind (CmpXchg _ _ _).
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
    simpl. iDestruct "Hplist" as (γ_h2 n2) "(G_h2 & #Info_h2 & Hplist)".
    iDestruct (rcu.(guard_managed_agree) with "h1Info G G_h2") as %<-.
    iCombine "Info_h1 Info_h2" gives %[= <- <-]%to_agree_op_inv_L.
    iClear "Info_h2".
    iModIntro. iSplitL "Hplist st.h↦ Hγs Hoffer"; first by exfr.
    wp_pures. wp_apply (guard_read node with "[$h1Info $G]") as (??) "(G & #Info_h1' & %EQ)"; [solve_ndisj|lia|].
    iDestruct "Info_h1'" as (x1' n1') "[-> Info_h1']". injection EQ as [= <-].
    iCombine "Info_h1 Info_h1'" gives %[= <- <-]%to_agree_op_inv_L.
    iClear "Info_h1'". wp_pures. wp_load. wp_let.
    wp_apply (rcu.(rcu_domain_retire_spec) with "IED G_h2") as "_"; [solve_ndisj|].
    wp_pures.
    wp_apply (rcu.(guard_deactivate_spec) with "IED G") as "G"; [solve_ndisj|].
    wp_pures. iApply "HΦ". done.
  - (* CAS failed --> take an offer *)
    wp_cmpxchg_fail.
    iSplitL "Hγs st.h↦ Hplist Hoffer"; first by exfr.
    iModIntro. wp_pures. wp_bind (! _)%E. clear NE h2 xs2.
    iInv "Hinv_stack" as (h2 xs2) "(Hplist & >st.h↦ & >Hγs & (%offer_rep & %offers & >st.of↦ & Hio & >γof & Hoffers))".
    destruct offer_rep as [n|]; last first.
    { (* no offer *)
      wp_load. iModIntro. iSplitL "st.of↦ γof Hoffers Hplist st.h↦ Hγs"; first by exfr.
      wp_pures. wp_apply ("IH" with "AU G"). }
    (* offer exists *)
    simpl. iDestruct "Hio" as (Q v ????) "(>%Hγ' & #Hinv_noffer & >%res)". encode_agree Hγ.
    rewrite big_sepM_lookup_acc; [|apply res].
    iDestruct "Hoffers" as "[G_γn Hoffers]".
    wp_load.
    iMod (rcu.(guard_protect) with "IED G_γn G") as "(G_γn & G & #oInfo)"; [solve_ndisj|].
    iModIntro. iSplitR "AU G".
    { repeat iExists _. iFrame "∗#%". iExists (Some _). exfr.
      iSplitR; first by exfr. by iApply "Hoffers". }
    wp_pure credit:"Hlc". wp_pures. wp_bind (CmpXchg _ _ _).
    iInv "oInfo" as (lv) "(_ & n↦ & >Hod & G)".
    iDestruct "Hod" as (x stat ->) "(%γn_v & %γn_o & %Hγn & Hγn_v & #Hγn_o)".
    destruct (decide (stat = OfferPending)) as [->|NE]; last first.
    { (* CAS at state position failed *)
      wp_apply (wp_cmpxchg_fail_offset with "n↦") as "n↦"; [by simplify_list_eq|by destruct stat|by constructor|].
      iModIntro. iSplitL "n↦ Hγn_v". { iExists _. iFrame "n↦". iSplit; [done|]. iExists x, stat. iSplit; [done|]. exfr. }
      wp_pures. wp_apply ("IH" with "AU G"). }
    (* CAS at state position succeeded *)
    wp_apply (wp_cmpxchg_suc_offset with "n↦") as "n↦"; [by simplify_list_eq|done|by constructor|].
    iInv "Hinv_noffer" as (stat') "[>(%γn_v' & %γn_o' & %Hγn' & Hγn_v' & #Hγn_o') Hstat']". encode_agree Hγn.
    iCombine "Hγn_o Hγn_o'" gives %<-%to_agree_op_inv_L. iClear "Hγn_o'".
    iDestruct (ghost_var_agree with "Hγn_v Hγn_v'") as %<-.
    iMod (lc_fupd_elim_later with "Hlc Hstat'") as "AU_off". clear h2 xs2.
    iInv "Hinv_stack" as (h2 xs2) "(Hplist & >st.h↦ & >Hγs & (%offer_rep' & %offers' & >st.of↦ & Hio & >γof & Hoffers))".
    iMod "AU_off" as (l) "[Hstack [_ Commit]]"; [solve [eauto 13 with ndisj]|].
    iDestruct "Hstack" as (γs' γof') "[%Hγ' Hγs']". encode_agree Hγ.
    iDestruct (ghost_var_agree with "Hγs Hγs'") as %<-.
    iMod (ghost_var_update_halves (x :: xs2) with "Hγs Hγs'") as "[Hγs Hγs']".
    iMod ("Commit" with "[Hγs']") as "HQ"; first by exfr.
    iMod "AU" as (xs) "[Hstack [_ Commit]]"; [solve [eauto 13 with ndisj]|].
    iDestruct "Hstack" as (γs' γof') "[%Hγ' Hγs']". encode_agree Hγ.
    iDestruct (ghost_var_agree with "Hγs Hγs'") as %<-.
    iMod (ghost_var_update_halves xs2 with "Hγs Hγs'") as "[Hγs Hγs']".
    iMod ("Commit" with "[Hγs']") as "HΦ"; first by exfr.
    iModIntro. iSplitL "Hplist st.h↦ Hγs st.of↦ Hoffers Hio γof"; first by exfr.
    iMod (ghost_var_update_halves OfferAccepted with "Hγn_v Hγn_v'") as "[Hγn_v Hγn_v']".
    iModIntro. iSplitL "Hγn_v' HQ". { iExists OfferAccepted. exfr. }
    iModIntro. iSplitL "n↦ Hγn_v".
    { iExists _. iFrame "n↦". iSplit; [done|]. iExists x, OfferAccepted. iSplit; [done|]. repeat iExists _. iFrame "∗#%". }
    wp_pures. wp_bind (! _)%E.
    iInv "oInfo" as (lv) "(_ & n↦ & >Hod & G)".
    iDestruct "Hod" as (x' stat' ->) "(%γn_v' & %γn_o' & %Hγn' & Hγn_v & #Hγn_o')". encode_agree Hγn.
    iCombine "Hγn_o Hγn_o'" gives %<-%to_agree_op_inv_L. iClear "Hγn_o'".
    wp_apply (wp_load_offset with "n↦") as "n↦"; [by simplify_list_eq|].
    iModIntro. iSplitL "n↦ Hγn_v".
    { iExists _. iFrame "n↦". iSplit; [done|]. repeat iExists _. iSplit; [done|]. repeat iExists _. iFrame "∗#%". }
    wp_pures.
    wp_apply (rcu.(guard_deactivate_spec) with "IED G") as "G"; [solve_ndisj|].
    wp_pures. iApply "HΦ". by iFrame.
Qed.

#[export] Typeclasses Opaque EStack IsEStack.

End elim_stack.
