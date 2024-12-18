From iris.bi Require Import lib.fractional.
From iris.algebra Require Import agree csum frac mono_list.
From iris.base_logic.lib Require Import mono_nat invariants ghost_var.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr.base_logic Require Import lib.mono_list.
From smr Require Import helpers ebr.spec_rcu_simple ebr.spec_hybrid_counter ebr.code_hybrid_counter.

Set Printing Projections.

Local Open Scope Z.

Definition oneshotR := csumR fracR (agreeR unitO).

Class hcounterG Σ := HCounterG {
  #[local] hcounter_inG :: inG Σ oneshotR;
  #[local] hcounter_ghost_varG :: ghost_varG Σ nat;
  #[local] hcounter_mono_listG:: mono_listG (gname * loc) Σ;
  #[local] hcounter_mono_natG :: mono_natG Σ;
}.

Definition hcounterΣ : gFunctors := #[GFunctor oneshotR; ghost_varΣ nat; mono_listΣ (gname * loc); mono_natΣ].

Global Instance subG_hcounterΣ {Σ} :
  subG hcounterΣ Σ → hcounterG Σ.
Proof. solve_inG. Qed.

Section hcounter.
Context `{!heapGS Σ, !hcounterG Σ}.
Notation iProp := (iProp Σ).
Context (hcounterN rcuN : namespace) (DISJN : hcounterN ## rcuN).

Variable (rcu : rcu_simple_spec Σ rcuN).

Definition nodeT : Type := gname * loc.
Implicit Types (nodes olds : list nodeT).

(** * Ghosts
- [γi]: The current logical id of physical node [l ↪ γ_l].
- [γ_l]: per-node oneshot
- [γn]: node number (x mod 2) ↔ node logical id (as [mono_list (gname * loc)])
  - Logical ids are unique ([NoDup]).
- [γm]: Node number increases monotonically. *)
Notation token γ f := (own γ (Cinl f%Qp : oneshotR)).
Notation shot γ := (own γ (Cinr (to_agree ()) : oneshotR)).

Local Instance token_Fractional γ : Fractional (λ f, token γ f).
Proof. intros ??. rewrite -frac_op -own_op -Cinl_op //. Qed.
Local Instance token_AsFractional γ f :
  AsFractional (token γ f) (λ f, token γ f) f.
Proof. split; [done|]. apply _. Qed.

Lemma token_alloc (names : list gname) :
 ⊢ |==> ∃ γ, ⌜γ ∉ names⌝ ∗ token γ 1.
Proof.
  iMod (own_alloc_cofinite _ (list_to_set names)) as "?"; last first.
  { setoid_rewrite not_elem_of_list_to_set. done. } done.
Qed.

Lemma token_shot γ : token γ 1 ==∗ shot γ.
Proof. by iApply own_update; apply cmra_update_exclusive. Qed.

(** * Main assertions *)
Definition node_info γn γ_l l i_l : iProp :=
  ∃ nodes,
    mono_list_lb_own γn nodes ∗
    ⌜nodes !! i_l = Some (γ_l, l) ∧ NoDup nodes.*1⌝.

Definition node_status γ_l x i_l : iProp :=
  (* pending *)
  ( ⌜(x = i_l * 2)%nat⌝ ∗ token γ_l (1/2) ) ∨
  (* shot *)
  ( ⌜(x = i_l * 2 + 1)%nat⌝ ∗ shot γ_l )
  .

Definition node γn l lv γ_l : iProp :=
  ∃ (x : nat) i_l,
    ⌜lv = [ #x ]⌝ ∗
    node_info γn γ_l l i_l ∗
    node_status γ_l x i_l.

Definition HCounterInternalInv (γe γn γm γx : gname) (c : loc) : iProp :=
  ∃ (γ_l : gname) (l : blk) (x : nat) i_l olds,
    rcu.(Managed) γe l γ_l 1%nat (node γn) ∗
    c ↦ #l ∗
    node_info γn γ_l l i_l ∗
    ghost_var γx (1/2)%Qp x ∗
    node_status γ_l x i_l ∗
    ([∗ list] i_old ↦ old ∈ olds,
      node_info γn old.1 old.2 i_old ∗ shot old.1) ∗
    mono_list_auth_own γn 1 (olds ++ [(γ_l, Loc.blk_to_loc l)]) ∗
    mono_nat_auth_own γm 1 i_l ∗
    ⌜ (length olds = i_l)%nat ∧
      NoDup (olds.*1 ++ [γ_l]) ⌝
    .

Definition HCounter (γc : gname) (x : nat) : iProp :=
  ∃ (γn γm γx : gname), ⌜γc = encode (γn, γm, γx)⌝ ∗ ghost_var γx (1/2)%Qp x.

Global Instance HCounter_Timeless γc xs: Timeless (HCounter γc xs).
Proof. apply _. Qed.

(** Persistent assertion. *)
Definition IsHCounter (γe : gname) (γc : gname) (c : loc) : iProp :=
  ∃ (γn γm γx : gname) (d : loc), ⌜γc = encode (γn, γm, γx)⌝ ∗
    (c +ₗ 1) ↦□ #d ∗ rcu.(IsRCUDomain) γe d ∗
    inv hcounterN (HCounterInternalInv γe γn γm γx c)
    .

Global Instance IsHCounter_Persistent γe γc c : Persistent (IsHCounter γe γc c).
Proof. apply _. Qed.

(** * Helpers *)
Local Hint Extern 1 (environments.envs_entails _
  (node_info _ _ _ _)) => iExists _ : core.
Local Hint Extern 1 (environments.envs_entails _
  (node _ _ _)) => rewrite -?Nat2Z.inj_mul -?Nat2Z.inj_add; iExists _,_ : core.
Local Hint Extern 1 (environments.envs_entails _
  (HCounter _ _)) => iExists _,_,_: core.
Local Hint Extern 1 (environments.envs_entails _
  (IsHCounter _ _ _)) => iExists _,_,_,_ : core.
Local Hint Extern 1 (NoDup _) => simpl || rewrite fmap_app : core.
Local Hint Constructors NoDup : core.
Local Hint Immediate not_elem_of_nil : core.



Lemma node_info_agree γn γ_l1 γ_l2 l1 l2 i_l1 i_l2 :
  γ_l1 = γ_l2 ∨ i_l1 = i_l2 →
  node_info γn γ_l1 l1 i_l1 -∗ node_info γn γ_l2 l2 i_l2 -∗
  ⌜γ_l1 = γ_l2 ∧ l1 = l2 ∧ i_l1 = i_l2⌝.
Proof.
  intros EQ.
  iDestruct 1 as (nodes1) "[◯n1 [%Hi_l1 %Hn1]]".
  iDestruct 1 as (nodes2) "[◯n2 [%Hi_l2 %Hn2]]".
  iDestruct (mono_list_lb_valid with "◯n1 ◯n2") as %CASE.
  iPureIntro.
  wlog: γ_l1 γ_l2 l1 l2 i_l1 i_l2 nodes1 nodes2 EQ Hi_l1 Hi_l2 Hn1 Hn2 CASE
      / nodes1 `prefix_of` nodes2.
  { intros X. destruct CASE.
    - eapply (X γ_l1 γ_l2); eauto.
    - suff [? []]: γ_l2 = γ_l1 ∧ l2 = l1 ∧ i_l2 = i_l1 by done.
      eapply (X γ_l2 γ_l1); eauto. clear -EQ. naive_solver. }
  intros Hn12. clear CASE Hn1.
  have {}Hi_l1 := prefix_lookup_Some _ _ _ _ Hi_l1 Hn12.
  suff ? : i_l1 = i_l2.
  { subst. rewrite Hi_l2 in Hi_l1. by simplify_eq. }
  destruct EQ; subst; [|done].
  apply (f_equal (fmap fst)) in Hi_l1, Hi_l2.
  simpl in Hi_l1, Hi_l2. rewrite <-list_lookup_fmap in Hi_l1, Hi_l2.
  eapply NoDup_lookup; eauto.
Qed.

Lemma node_info_agree_γ γn γ_l l1 l2 i_l1 i_l2 :
  node_info γn γ_l l1 i_l1 -∗ node_info γn γ_l l2 i_l2 -∗
  ⌜l1 = l2 ∧ i_l1 = i_l2⌝.
Proof.
  iIntros "Info1 Info2".
  iDestruct (node_info_agree with "Info1 Info2") as %(?&?&?); [by left|done].
Qed.

Lemma node_info_agree_i γn γ_l1 γ_l2 l1 l2 i_l :
  node_info γn γ_l1 l1 i_l -∗ node_info γn γ_l2 l2 i_l -∗
  ⌜γ_l1 = γ_l2 ∧ l1 = l2⌝.
Proof.
  iIntros "Info1 Info2".
  iDestruct (node_info_agree with "Info1 Info2") as %(?&?&?); [by right|done].
Qed.

Lemma node_info_disagree γn γ_l1 γ_l2 l1 l2 i_l1 i_l2 :
  l1 ≠ l2 →
  node_info γn γ_l1 l1 i_l1 -∗ node_info γn γ_l2 l2 i_l2 -∗
  ⌜γ_l1 ≠ γ_l2 ∧ i_l1 ≠ i_l2⌝.
Proof.
  intros NE_l.
  iDestruct 1 as (nodes1) "[◯n1 [%Hi_l1 %Hn1]]".
  iDestruct 1 as (nodes2) "[◯n2 [%Hi_l2 %Hn2]]".
  iDestruct (mono_list_lb_valid with "◯n1 ◯n2") as %CASE.
  iPureIntro.
  wlog: γ_l1 γ_l2 l1 l2 i_l1 i_l2 nodes1 nodes2 NE_l Hi_l1 Hi_l2 Hn1 Hn2 CASE
      / nodes1 `prefix_of` nodes2.
  { intros X. destruct CASE.
    - eapply (X γ_l1 γ_l2); eauto.
    - suff []: γ_l2 ≠ γ_l1 ∧ i_l2 ≠ i_l1 by done.
      eapply (X γ_l2 γ_l1 l2 l1); eauto. }
  intros Hn12. clear CASE Hn1.
  have {}Hi_l1 := prefix_lookup_Some _ _ _ _ Hi_l1 Hn12.
  assert (nodes2 !! i_l1 ≠ nodes2 !! i_l2) as NE_i_l%lookup_ne.
  { rewrite Hi_l1 Hi_l2. intros ?. simplify_eq. }
  split; [|done]. intros ->.
  apply (f_equal (fmap fst)) in Hi_l1, Hi_l2. simpl in Hi_l1, Hi_l2.
  rewrite <-list_lookup_fmap in Hi_l1, Hi_l2.
  eauto using NoDup_lookup.
Qed.

Lemma node_status_case γ_l x1 x2 i_l :
  node_status γ_l x1 i_l -∗ node_status γ_l x2 i_l -∗
  ⌜x1 = x2⌝ ∗
  ( (* pending *)
    ( ⌜(x1 = i_l * 2)%nat⌝ ∗ token γ_l 1 )
  ∨ (* shot *)
    ( ⌜(x1 = i_l * 2 + 1)%nat⌝ ∗ shot γ_l ) ).
Proof.
  iDestruct 1 as "[[-> Tok1]|[-> #Shot1]]"; iDestruct 1 as "[[-> Tok2]|[-> #Shot2]]".
  - iSplit; [done|]. iLeft. iSplit; [done|]. by iSplitL "Tok1".
  - by iCombine "Tok1 Shot2" gives %?.
  - by iCombine "Tok2 Shot1" gives %?.
  - iSplit; [done|]. iRight. by iSplit.
Qed.

(** * Spec proofs  *)
Lemma hcounter_new_spec :
  hcounter_new_spec' hcounterN rcuN hcounter_new rcu HCounter IsHCounter.
Proof.
  iIntros (γe Φ d) "!> #IED HΦ".
  wp_lam.
  wp_alloc c as "c↦" "†c".
  rewrite array_cons array_singleton. iDestruct "c↦" as "[c.n↦ c.d↦]".
  wp_let.
  wp_alloc l as "l↦" "†l". rewrite array_singleton. wp_let. wp_store.
  wp_op. rewrite Loc.add_0. wp_store.
  iMod (mono_list_own_alloc []) as (γn) "[●n _]".
  wp_op. wp_store.
  iMod (pointsto_persist with "c.d↦") as "#c.d↦".
  iMod (own_alloc (Cinl 1%Qp)) as (γ_l) "Tok_l"; [done|].
  iMod (mono_list_auth_own_update_app [(γ_l,Loc.blk_to_loc l)] with "●n") as "[●n #◯n]". simpl.
  iAssert (node_status γ_l 0 0 ∗ node_status γ_l 0 0)%I with "[Tok_l]" as "[St_l_C St_l_P]".
  { iDestruct "Tok_l" as "[Tok_l_C Tok_l_P]". iSplitL "Tok_l_C"; iLeft; by iFrame. }
  iAssert (node_info γn γ_l l 0) as "Info_l"; first by eauto 10 with iFrame.
  iEval (rewrite -array_singleton) in "l↦".
  iMod (rcu.(rcu_domain_register) (node γn) with "IED [$l↦ $†l St_l_P]") as "G_l"; [solve_ndisj|..].
  { iExists _, _. by iFrame "∗#". }
  iAssert (([∗ list] i_old ↦ old ∈ ([] : list nodeT),
      node_info γn old.1 old.2 i_old ∗ shot old.1))%I as "Shots"; [done|].
  iMod (mono_nat_own_alloc 0) as (γm) "[●m _]".
  iMod (ghost_var_alloc 0%nat) as (γx) "[Hγx Hγx']".
  remember (encode (γn,γm,γx)) as γc eqn:Hγc.
  iAssert (HCounter γc 0) with "[Hγx']" as "C".
  { repeat iExists _. by iFrame. }
  iMod (inv_alloc hcounterN _ (HCounterInternalInv γe γn γm γx c) with "[-HΦ C]") as "#Inv".
  { repeat iExists _. iFrame "∗#%". iNext. simpl. iFrame. iPureIntro.
    split; [done|apply NoDup_singleton]. }
  iModIntro. iApply "HΦ". iFrame.
  repeat iExists _. iFrame "∗#%".
Qed.

Lemma hcounter_inc_spec :
  hcounter_inc_spec' hcounterN rcuN (hcounter_inc rcu) rcu HCounter IsHCounter.
Proof using All.
  iIntros (γe γc c g).
  iDestruct 1 as (???? Hγc) "#(c.d↦ & IED & Inv)".
  iIntros "G" (Φ) "AU".

  wp_lam. wp_pures. wp_load. wp_let.
  wp_apply (rcu.(guard_activate_spec) with "IED G") as (?) "G"; [solve_ndisj|].
  wp_seq. wp_op. rewrite Loc.add_0.

  (* start hcounter loop *)
  wp_bind ((hcounter_inc_loop rcu) _). iLöb as "IH".
  wp_rec. wp_pures.

  (* obtain node from Inv *)
  wp_bind (! _)%E.

  iInv "Inv" as (γ_l l x i_l olds)
                "[G_l >(c.n↦ & #Info_l & Hγx & St_l_C & Shots & ●n & ●m & %Holds1 & %Holds2)]".
  wp_load.

  iMod (rcu.(guard_protect) with "IED G_l G") as "(G_l & G & #lInfo)"; [solve_ndisj|].

  (* snapshots used for failing even → odd CAS *)
  iDestruct (mono_nat_lb_own_get with "●m") as "#◯m".
  iDestruct (mono_list_lb_own_get with "●n") as "#◯n".

  iModIntro. iSplitR "AU G".
  { repeat iExists _. iFrame "∗%#". iPureIntro. rewrite fmap_app. simpl. rewrite -Holds1 snoc_lookup. done. }
  clear x.
  wp_let.

  (* read *)
  wp_bind (! _)%E.
  iInv "lInfo" as (?) "(_ & l↦ & >N_l & G)".
  iDestruct "N_l" as (x ? ->) "(#Info_l' & St_l_P)".
  iDestruct (node_info_agree_γ with "Info_l Info_l'") as %[_ <-]. iClear "Info_l'".
  iEval (rewrite array_singleton) in "l↦".
  wp_load.
  iEval (rewrite -array_singleton) in "l↦".

  (* case analysis on the status of current node *)
  iDestruct "St_l_P" as "[[-> Tok_l_P]|[-> #Shot_l]]".
  - (* even: try even→odd value CAS *)
    iModIntro. iSplitL "l↦ Tok_l_P".
    { iExists _. iFrame "l↦". iSplit; [done|]. iNext. iExists _,i_l.
      iFrame "Info_l". iSplit; [done|]. iLeft. by iFrame. }
    wp_pures.
    rewrite Nat2Z.inj_mul. rewrite Z.rem_mul; [|done].
    wp_pures.

    (* prepare CAS *)
    wp_bind (CmpXchg _ _ _).
    (* access the node *)
    iInv "lInfo" as (?) "(_ & l↦ & >N_l & G)".
    iDestruct "N_l" as (x ? ->) "(#Info_l' & St_l_P)".
    iDestruct (node_info_agree_γ with "Info_l Info_l'") as %[_ <-]. iClear "Info_l'".
    iEval (rewrite array_singleton) in "l↦".
    (* inspect the current state *)
    iInv "Inv" as (γ_l' l' x' i_l' olds')
                "[G_l' >(c.n↦ & #Info_l' & Hγx & St_l'_C & Shots & ●n & ●m & %Holds'1 & %Holds'2)]".

    (* Has the current node changed? *)
    case (decide (l = l')) as [<-|NE_l].
    + (* node didn't change *)
      iDestruct (rcu.(guard_managed_agree) with "lInfo G G_l'") as "#><-".
      iDestruct (node_info_agree_γ with "Info_l Info_l'") as %[_ <-]. iClear "Info_l'".

      (* Has the node's value changed? *)
      iDestruct (node_status_case with "St_l_P St_l'_C") as "[<- [[-> Tok_l]|[-> #Shot_l]]]".
      * (* not yet shot; CAS succeeds; commit *)
        wp_cmpxchg_suc; [repeat f_equal;lia|].
        iMod (token_shot with "Tok_l") as "#Shot_l".
        iAssert (□ node_status γ_l (i_l * 2 + 1)%nat i_l)%I as "#St_l".
        { iModIntro. iRight. by iSplit. }
        iMod "AU" as (?) "[C [_ Commit]]".
        iDestruct "C" as (????) "Hγx'".
        encode_agree Hγc.
        iDestruct (ghost_var_agree with "Hγx Hγx'") as %<-.
        iMod (ghost_var_update_halves (i_l * 2 + 1)%nat with "Hγx Hγx'") as "[Hγx Hγx']".
        iMod ("Commit" with "[Hγx]") as "HΦ".
        { repeat iExists _. by iFrame "∗#". }
        iModIntro. iSplitR "HΦ l↦ G".
        { repeat iExists _. iFrame "∗#%". iPureIntro. rewrite fmap_app. simpl. rewrite -Holds1 snoc_lookup. repeat (split; try (done||lia)). }
        iEval (rewrite -array_singleton) in "l↦".
        iModIntro. iSplitL "l↦".
        { iExists _. iFrame. iSplit; [done|]. iNext. iFrame "#".
          iPureIntro. rewrite fmap_app. simpl. rewrite -Holds1 snoc_lookup.
          repeat (split; repeat f_equal; try (done||lia)). }
        wp_pures.
        wp_apply (rcu.(guard_deactivate_spec) with "IED G") as "G"; [solve_ndisj|].
        wp_seq. iModIntro.
        rewrite Nat2Z.inj_mul. by iApply "HΦ".

      * (* already shot; CAS fails; loop *)
        wp_cmpxchg_fail.
        { injection. lia. }
        iAssert (□ node_status γ_l (i_l * 2 + 1)%nat i_l)%I as "#St_l".
        { iModIntro. iRight. by iSplit. }
        iModIntro. iSplitR "AU l↦ G".
        { iFrame "∗#%". iPureIntro.
          repeat (split; repeat f_equal; try (done||lia)).
          all: try rewrite fmap_app; simpl; try rewrite -Holds1 snoc_lookup.
          all: done.
        }
        iEval (rewrite -array_singleton) in "l↦".
        iModIntro. iSplitL "l↦".
        { iExists _. iFrame. iSplit; [done|]. iNext. iFrame "#". iPureIntro.
          rewrite fmap_app. simpl. rewrite -Holds1 snoc_lookup.
          repeat (split; repeat f_equal; try (done||lia)).
        }
        wp_pure. wp_if.
        wp_apply ("IH" with "AU G").

    + (* node changed → the old node's value must've changed too → CAS fails → loop *)

      (* The node number must've changed, and it must be higher since it
      increases monotonically. *)
      iDestruct (node_info_disagree with "Info_l Info_l'") as %[NE_γ_l NE_i_l].
      { unfold not. intros H. by inversion H. }
      iDestruct (mono_list_auth_lb_valid with "●n ◯n") as %[_ PF_olds].
      apply prefix_app_same_length in PF_olds; auto.
      iDestruct (mono_nat_lb_own_valid with "●m ◯m") as %[_ LE_i_l]. iClear "◯m".
      have {LE_i_l}LT_i_l : (i_l < i_l')%nat by lia.

      (* There should be a [shot] of the old node. *)
      have [old Hold] : is_Some (olds' !! i_l).
      { apply lookup_lt_is_Some_2. lia. }
      iDestruct (big_sepL_lookup _ _ _ _ Hold with "Shots") as "#[Info_l'' Shot_l]".
      iDestruct (node_info_agree_i with "Info_l Info_l''") as %[<- <-].
      clear dependent old.

      (* So the value must've changed. *)
      iDestruct "St_l_P" as "[[-> Tok_l]|[-> _]]".
      { by iCombine "Tok_l Shot_l" gives %?. }
      iAssert (node_status γ_l _ i_l) as "St_n_P".
      { iRight. by iFrame "Shot_l". }

      (* CAS fails. *)
      wp_cmpxchg_fail.
      { injection. lia. }
      iModIntro. iSplitR "AU l↦ G".
      { repeat iExists _. by iFrame "∗#%". }
      iEval (rewrite -array_singleton) in "l↦".
      iModIntro. iSplitL "l↦".
      { iExists _. iFrame. iSplit; [done|]. iNext. iFrame "#". done. }
      wp_pure. wp_if.
      wp_apply ("IH" with "AU G").

  - (* odd *)
    iClear "◯m ◯n". clear dependent olds.
    iModIntro. iSplitL "l↦".
    { iExists _. iFrame. iSplit; [done|]. iNext. iExists _,_. iFrame "∗#%".
      iSplit; [iPureIntro; done|]. by iRight. }
    wp_pures.
    rewrite (_ : ((i_l * 2 + 1)%nat `rem` 2) = 1); last first.
    { rewrite (_ : i_l * 2 + 1 = 1 + i_l * 2)%nat; [|lia].
      rewrite Nat2Z.inj_add Nat2Z.inj_mul.
      rewrite Z.rem_add; [done|lia..]. }
    wp_if. wp_alloc n as "n↦" "†n". rewrite array_singleton.
    wp_pures. wp_store.

    wp_bind (CmpXchg _ _ _).
    iInv "Inv" as (γ_l' l' x' i_l' olds')
                "[G_l' >(c.n↦ & #Info_l' & Hγx & St_l'_C & Shots & ●n & ●m & %Holds'1 & %Holds'2)]".

    (* Has the current node changed? *)
    case (decide (l = l')) as [<-|NE_l].
    + (* node didn't change; CAS success; commit *)
      iClear "IH".
      iDestruct (rcu.(guard_managed_agree) with "lInfo G G_l'") as "#><-".
      iDestruct (node_info_agree_γ with "Info_l Info_l'") as %[_ <-]. iClear "Info_l'".

      (* We know that the node is in the odd state. *)
      iDestruct "St_l'_C" as "[[-> Tok_l']|[-> _]]".
      { by iCombine "Shot_l Tok_l'" gives %?. }

      wp_cmpxchg_suc.
      (* update ghosts *)
      set olds'' := olds' ++ [(γ_l, Loc.blk_to_loc l)].
      iMod (token_alloc olds''.*1) as (γ_n Hγ_l) "Tok_n".
      rewrite fmap_app /= in Hγ_l.
      iMod (mono_list_auth_own_update_app [(γ_n,Loc.blk_to_loc n)] with "●n") as "[●n #◯n]".
      iMod (mono_nat_own_update (i_l + 1) with "●m") as "[●m _]"; [lia|].
      iAssert (node_status γ_n _ _ ∗ node_status γ_n _ _)%I with "[Tok_n]" as "[St_n_C St_n_P]".
      { iDestruct "Tok_n" as "[Tok_n_C ?]". iSplitL "Tok_n_C"; iLeft; by iFrame. }
      have ? : length olds'' = (length olds' + 1)%nat.
      { rewrite length_app //. }
      have ? : (olds'' ++ [(γ_n, Loc.blk_to_loc n)]) !! (length olds' + 1)%nat = Some (γ_n, Loc.blk_to_loc n).
      { by apply list_lookup_middle. }
      have ? : NoDup (olds''.*1 ++ [γ_n]).
      { unfold olds''. rewrite fmap_app /=.
        eapply NoDup_app. split_and!; [done|set_solver|auto]. }
      iAssert (node_info γn γ_n n (i_l+1)) as "Info_n"; first by eauto 10 with iFrame subst.
      iDestruct (big_sepL_snoc _ _ (γ_l, Loc.blk_to_loc l) with "[$Shots $Shot_l]") as "Shots"; eauto with iFrame subst.
      iEval (rewrite -array_singleton) in "n↦".
      iMod (rcu.(rcu_domain_register) (node γn) with "IED [$n↦ $†n St_n_P]") as "G_n"; [solve_ndisj|..].
      { iExists _,_. iFrame "∗#". iPureIntro. repeat f_equal. lia. }
      iMod "AU" as (?) "[C [_ Commit]]".
      iDestruct "C" as (????) "Hγx'".
      encode_agree Hγc.
      iDestruct (ghost_var_agree with "Hγx Hγx'") as %<-.
      iMod (ghost_var_update_halves (i_l * 2 + 1 + 1)%nat with "Hγx Hγx'") as "[Hγx Hγx']".
      iMod ("Commit" with "[Hγx']") as "HΦ".
      { repeat iExists _. by iFrame. }
      iModIntro.
      iSplitR "HΦ G G_l'".
      { repeat iExists _. iFrame "∗#%".
        rewrite (_ : i_l * 2 + 1 + 1 = (i_l + 1) * 2)%nat; [|lia].
        iFrame. iPureIntro. split.
        - rewrite length_app. simpl. rewrite Holds'1. done.
        - subst olds''. done.
      }
      wp_pures.
      wp_apply (rcu.(rcu_domain_retire_spec) with "IED G_l'") as "_"; [solve_ndisj|].
      wp_pures.
      wp_apply (rcu.(guard_deactivate_spec) with "IED G") as "G"; [solve_ndisj|].
      wp_pures.
      by iApply "HΦ".

    + (* node changed → CAS fails; loop *)
      wp_cmpxchg_fail.
      iModIntro.
      iSplitR "AU G n↦ †n".
      { repeat iExists _. by iFrame "∗#%". }
      wp_pures.
      iEval (rewrite -array_singleton) in "n↦".
      wp_free; [done|]. wp_pures.
      wp_apply ("IH" with "AU G").
Qed.

#[export] Typeclasses Opaque HCounter IsHCounter.

End hcounter.
