From iris.base_logic.lib Require Import invariants ghost_map.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.

From smr.ebr Require Import spec_rcu_base spec_rcu_traversal.
From smr.logic Require Import reclamation node_link_history.
From smr Require Import helpers.

From iris.prelude Require Import options.

Set Printing Projections.

Class rcu_traversalG Σ := RCUTraversalG {
  #[local] rcu_traversal_nlhG :: node_link_historyG Σ;
  #[local] rcu_traversal_gmapG :: ghost_mapG Σ blk positive;
}.

Definition rcu_traversalΣ: gFunctors := #[node_link_historyΣ; ghost_mapΣ blk positive].

Global Instance subG_rcu_traversalΣ Σ :
  subG rcu_traversalΣ Σ → rcu_traversalG Σ.
Proof. solve_inG. Qed.

Section rcu_traversal.
Context `{!heapGS Σ, !rcu_traversalG Σ}.
Context (N : namespace) (base : spec_rcu_base.rcu_base_spec Σ (mgmtN N) (ptrsN N)).

Implicit Types
  (γd γb γh γg γrg γbg : gname)
  (Im : gmap positive alloc) (Rs : gset positive) (h : list event)
  (G : gmap blk positive)
  (Syn : gset positive) (Det : gset positive)
  .

Record RCUInvConsistent {Im : gmap positive alloc} {Rs : gset positive} {h : list event} : Prop := {
  ric_dom i : i ∈ dom Im ↔ i ∈ event_id <$> h;
  ric_live_unretired i : LiveAt h i → i ∉ Rs;
}.
Global Arguments RCUInvConsistent : clear implicits.

Definition RCUInv γb γh Im Rs h : iProp Σ :=
  base.(RCUAuth) γb Im Rs ∗
  HistAuth γh h ∗
  ⌜ RCUInvConsistent Im Rs h ⌝
  .

Definition IsRCUDomain γd d : iProp Σ :=
  ∃ γb γh,
    ⌜γd = encode (γb, γh)⌝ ∗
    base.(spec_rcu_base.IsRCUDomain) γb d ∗
    inv ((mgmtN N).@"traversal") (∃ Im Rs h, RCUInv γb γh Im Rs h) .

Definition Inactive γd g : iProp Σ :=
  ∃ γb γh,
    ⌜γd = encode (γb, γh)⌝ ∗
    base.(BaseInactive) γb g .

Record GuardConsistent {Det Syn h} : Prop := {
  gc_det_syn : Syn ⊆ Det;
  gc_live_not_detached i : LiveAt h i ↔ i ∉ Det;
}.
Global Arguments GuardConsistent : clear implicits.

Definition Guard γd γg g : iProp Σ :=
  ∃ γb γh γrg γbg Det Syn G h,
    ⌜γd = encode (γb, γh)⌝ ∗
    ⌜γg = encode (γbg,γrg)⌝ ∗
    base.(BaseGuard) γb γbg g Syn G ∗
    HistSnap γh h ∗
    (* TODO: this is already in the base spec. Should be possible to just add more lemmas to the base spec without this. *)
    ghost_map_auth γrg 1 G ∗
    ([∗ map] p ↦ i ∈ G, p ↪[γrg]□ i) ∗
    ⌜ Det ## range G ⌝ ∗
    ⌜ GuardConsistent Det Syn h ⌝
  .

Definition Managed γd (p : blk) (i : positive) (ty : type Σ) (B : gmultiset positive) : iProp Σ :=
  ∃ γb γh,
    ⌜γd = encode (γb, γh)⌝ ∗
    base.(BaseManaged) γb p i ty.(ty_sz) ty.(ty_res) ∗
    HistPointedBy γh i B.

Definition Deleted γd (p : blk) (i : positive) (ty : type Σ) : iProp Σ :=
  ∃ γb γh,
    ⌜γd = encode (γb, γh)⌝ ∗
    base.(BaseManaged) γb p i ty.(ty_sz) ty.(ty_res) ∗
    HistDeleted γh i.

Definition RCUPointsTo γd (p : blk) (i : positive) (o : nat) (to : option (blk * positive * type Σ)) : iProp Σ :=
  ∃ γb γh,
    ⌜γd = encode (γb, γh)⌝ ∗
    HistPointsToLast γh i o (snd ∘ fst <$> to) ∗
    if to is Some (q, j, ty) then
      base.(BaseNodeInfo) γb q j ty.(ty_sz) ty.(ty_res)
    else True
  .

Definition RCUNodeInfo γd γg (p : blk) (i : positive) (ty : type Σ) : iProp Σ :=
  ∃ γb γh γrg γbg,
    ⌜γd = encode (γb, γh)⌝ ∗
    ⌜γg = encode (γbg,γrg)⌝ ∗
    p ↪[γrg]□ i ∗
    base.(BaseGuardedNodeInfo) γb γbg p i ty.(ty_sz) ty.(ty_res).

Global Instance IsRCUDomain_Persistent γd d : Persistent (IsRCUDomain γd d).
Proof. apply _. Qed.

Global Instance RCUPointsTo_Some_Contractive γd p1 i1 o1 p2 i2 n : Proper (type_dist2 n ==> dist n) (λ ty2, RCUPointsTo γd p1 i1 o1 (Some (p2,i2,ty2))).
Proof.
  intros ty1 ty2 Hty.
  apply bi.exist_ne => γb. apply bi.exist_ne => γh.
  repeat apply bi.sep_ne; try done.
  destruct Hty as [-> Hres].
  apply base.(BaseNodeInfo_contractive). rewrite dist_later_fin_iff.
  destruct n; [done|]. simpl in *.
  intros ???. apply Hres. lia.
Qed.

Global Instance RCUNodeInfo_Persistent γd γg p i ty : Persistent (RCUNodeInfo γd γg p i ty).
Proof. apply _. Qed.

Lemma rcu_domain_new_spec :
  rcu_domain_new_spec' N base.(rcu_domain_new) IsRCUDomain.
Proof.
  iIntros (???) "HΦ".
  iApply wp_fupd.

  wp_apply (spec_rcu_base.rcu_domain_new_spec) as (γb ?) "[#BRID BRA]"; [done|].

  iMod (hist_alloc) as (γh) "HA".
  remember (encode (γb, γh)) as γ.
  iApply "HΦ". iFrame "∗#%".

  iMod (inv_alloc (mgmtN N.@"traversal") _  (∃ Im Rs h, RCUInv γb γh Im Rs h)
    with "[BRA HA]") as "$"; [| done].
  iModIntro. iExists ∅, ∅, []. iFrame. iPureIntro. split; set_solver.
Qed.


Lemma rcu_domain_register :
  rcu_domain_register' N IsRCUDomain Managed RCUPointsTo.
Proof.
  intros I ty succs R ?????? ?? ? Hsz Hsuccs. iIntros "IRD p↦ †p SM Reg".
  iDestruct (heap_freeable_nonzero with "†p") as %Hsz_nz.
  rewrite -Hsz in Hsz_nz.
  iDestruct "IRD" as (??) "(%Hγ & #BIRD & #RI)".
  iInv "RI" as (?? h) ">(BRA & HA & %RIC)".


  iMod (spec_rcu_base.rcu_domain_register base ty.(ty_res)
        (I ∪ dom Im)
        (λ i, HistAuth γh ((h ++ ((λ o, link i o None) <$> (seq 0 ty.(ty_sz))))
          ++ (imap (λ o s, link i o ((λ '(_, p, _, _), p) <$> s)) succs) )
            ∗ HistPointedBy γh i ∅
            ∗ RCUNodeSuccManageds N Managed γd (succs_add_pred succs i)
            ∗ R i)%I
      with "BIRD BRA p↦ †p [SM Reg HA]") as "OUT"; [solve_ndisj..| |].
  { iIntros (i Hi). iSpecialize ("Reg" $! i with "[%]"); [set_solver +Hi|].
    iMod (hist_create_node _ _ ty.(ty_sz) i with "HA") as "(HA & $ & HPT)"; [done|..].
    { move => /RIC.(ric_dom). set_solver +Hi. }
    set h' := h ++ _.
    set h'' := h' ++ _.
    iAssert (
      HistAuth γh h''
      ∗ RCUNodeSuccManageds N Managed γd (succs_add_pred succs i)
      ∗ ([∗ list] o↦field ∈ succs, RCUPointsTo γd p i o (fst <$> field)))%I
    with "[> HA SM HPT]" as "(HA & SM & HPT)".
    {
      clear lv Hsz. rewrite Hsuccs in Hsz_nz. rewrite Hsuccs. clear Hsuccs Hsz_nz.
      iInduction succs as [| a succs' IH] using rev_ind.
      - subst h''. simpl. rewrite app_nil_r. iFrame. done.
      - iEval (unfold RCUNodeSuccManageds; rewrite big_sepL_snoc) in "SM".
        iDestruct "SM" as "[SM' last_M]". fold (RCUNodeSuccManageds N Managed γd succs').
        iEval (rewrite length_app seq_app Nat.add_0_l big_sepL_snoc) in "HPT".
        iDestruct "HPT" as "[HPT' last_HP]".


        iDestruct ("IH" with "HA SM' HPT'") as ">(HistAuth' & SM' & RPTs)". iClear "#".

        set h_prev := h' ++ _.
        assert (h'' = h_prev ++ [link i (length succs') ( (λ '(_, p, _, _), p) <$> a)]) as ->.
        { subst h'' h_prev. rewrite imap_app app_assoc /= Nat.add_0_r //. }
        destruct a as [[[[? p'] ?] ?]| ]; simpl.
        + iAssert (base.(BaseNodeInfo) γb b p' t.(ty_sz) t.(ty_res)) with "[last_M]" as "#last_node_info". {
            iDestruct "last_M" as (???) "[BM _]". encode_agree Hγ. iDestruct (spec_rcu_base.managed_get_node_info with "BM") as "$".
          }
          iAssert (
            HistAuth γh (h_prev ++ [link i (length succs') (Some p')])
            ∗ HistPointsToLast γh i (length succs') (Some p')
            ∗ Managed γd b p' t (g ⊎ {[+ i +]}))%I
          with "[> HistAuth' last_HP last_M]" as "($ & last_HP' & last_M')". {
            iDestruct "last_M" as (???) "[BM HPB]". encode_agree Hγ.
            iMod (hist_points_to_link with "HistAuth' last_HP HPB")as "($ & $ & HPB')". iFrame "∗#%". done.
          }
          iAssert (RCUNodeSuccManageds _ _ _ _)%I with "[SM' last_M']" as "$".
          { rewrite /succs_add_pred fmap_app. iFrame "∗#%". auto. }
          iFrame "∗#%". simpl. rewrite Nat.add_0_r. by iFrame.
        + iMod (hist_points_to_unlink_simple with "HistAuth' last_HP") as "[$ last_HP]".
          iAssert (RCUNodeSuccManageds N Managed γd (succs_add_pred (succs' ++ [None]) i)) with "[SM']" as "$".
          { iClear "#". unfold RCUNodeSuccManageds, succs_add_pred. rewrite fmap_app. simpl. rewrite big_sepL_snoc. iFrame.
          }
          rewrite big_sepL_snoc. iFrame "∗#%". done.
    }

    iMod (fupd_mask_subseteq E') as "Close"; [solve_ndisj|].
    iMod ("Reg" with "HPT") as "[Res R]".
    iMod "Close".
    iFrame. done.
  }
  iDestruct "OUT" as (i Hi) "(BRA & BM & HA & HPB & SM & R)".

  (* close inv *)
  iModIntro. iSplitL "BRA HA".
  { iClear "#". clear -RIC Hi Hsz_nz Hsuccs. iFrame "∗#%". iPureIntro. destruct RIC as [ric1 ric2].
    assert (∃ sz', ty.(ty_sz) = S sz') as [sz' ->]. { exists (ty.(ty_sz) - 1). lia. }
    split.
    - intros. unfold event_id. rewrite !fmap_app dom_insert.
      rewrite !elem_of_app elem_of_union. split; [intros [?|?]| intros [[?|?]|?]]; [set_solver.. | ].
      left. clear -H. induction succs using rev_ind; try rewrite imap_app in H; set_solver.
    - intros. unfold LiveAt in *. set_solver +ric2 H.
  }

  (* Managed *)
  iModIntro. iExists i. iSplit. { iPureIntro. set_solver +Hi. } iFrame.
  iExists _. rewrite Hsz. iFrame (Hγ) "∗".
Qed.

Lemma guard_new_spec :
  guard_new_spec' N base.(guard_new) IsRCUDomain Inactive.
Proof.
  intros ????. iIntros "#IRD" (Φ) "!> _ HΦ".
  iDestruct "IRD" as (??) "(%Hγ & #BIRD & #RI)".
  wp_apply (spec_rcu_base.guard_new_spec with "BIRD [//]") as (g) "BG"; [solve_ndisj|].
  iApply "HΦ". iFrame "∗#%".
Qed.

Lemma guard_activate_spec :
  guard_activate_spec' N base.(guard_activate) IsRCUDomain Inactive Guard.
Proof.
  intros ?????. iIntros "#IRD" (Φ) "!> I HΦ".
  iDestruct "IRD" as (??) "(%Hγ & #BIRD & #RI)".
  iDestruct "I" as (???) "BI". encode_agree Hγ.
  iApply wp_fupd.
  wp_apply (spec_rcu_base.guard_activate_spec with "BIRD BI") as (γbg Syn) "BG"; [solve_ndisj|].
  iInv "RI" as (???) ">(BRA & HA & %RIC)".
  iDestruct (hist_take_snapshot with "HA") as "#HS".
  iMod (rcu_auth_guard_subset with "BIRD BRA BG") as "(BRA & BG & %HSyn)"; [solve_ndisj|].
  iModIntro. iSplitL "BRA HA". { iFrame "∗#%". }
  iMod ghost_map_alloc_empty as (γrg) "I".
  remember (encode (γbg, γrg)) as γg.
  iModIntro.

  iApply ("HΦ" $! γg).
  iExists _,_,_,_,
          (list_to_set (omap (λ ev,
                        match ev with
                        | link _ _ _ => None
                        | del i => Some i
                        end) h)),
          Syn,∅,h.
  iFrame "∗#%". rewrite big_sepM_empty.
  iPureIntro. repeat split.
  - done.
  - set_unfold. move => i /HSyn /RIC.(ric_live_unretired) Del.
    rewrite elem_of_list_omap. exists (del i). split; [|done]. set_solver.
  - move => NotIn In. apply NotIn.
    rewrite elem_of_list_to_set elem_of_list_omap in In.
    destruct In as [[?|?] [In [= ->]]].
    done.
  - move => NotIn In. apply NotIn.
    rewrite elem_of_list_to_set elem_of_list_omap.
    exists (del i). done.
Qed.

Lemma guard_deactivate_spec :
  guard_deactivate_spec' N base.(guard_deactivate) IsRCUDomain Inactive Guard.
Proof.
  iIntros (??????). iIntros "#IRD" (Φ) "!> G HΦ".
  iDestruct "IRD" as (?? Hγ) "[BRD _]".
  iDestruct "G" as (??????????) "(BG & HS & I & Prot & %DISJ & %GC)". encode_agree Hγ.
  wp_apply (spec_rcu_base.guard_deactivate_spec with "BRD BG") as "BI"; [solve_ndisj| ].
  iApply "HΦ". iFrame "∗#%".
Qed.

Lemma guard_drop_spec :
  guard_drop_spec' N base.(guard_drop) IsRCUDomain Guard.
Proof.
  iIntros (??????). iIntros "#IRD" (Φ) "!> G HΦ".
  iDestruct "IRD" as (?? Hγ) "[BRD _]".
  iDestruct "G" as (??????????) "[BG _]". encode_agree Hγ.

  wp_apply (spec_rcu_base.guard_drop_spec with "BRD BG"); [solve_ndisj|]. done.
Qed.

Lemma guard_drop_inactive_spec :
  guard_drop_inactive_spec' N base.(guard_drop) IsRCUDomain Inactive.
Proof.
  iIntros (?????). iIntros "#IRD" (Φ) "!> I HΦ".
  iDestruct "IRD" as (?? Hγd) "[BIRD _]".
  iDestruct "I" as (?? ?) "BI". encode_agree Hγd.

  wp_apply (spec_rcu_base.guard_drop_inactive_spec with "BIRD BI"); [solve_ndisj|]. done.
Qed.

Local Lemma guard_protect_collect_guard_and_node_info
  G d γd γb γh γg γrg γbg g Syn Det hg p i ty E :
  ↑(mgmtN N) ⊆ E →
  γd = prod_countable.(encode) (γb, γh) →
  γg = prod_countable.(encode) (γbg, γrg) →
  i ∉ Syn →
  Det ## range G ∧ Det ## {[i]} →
  GuardConsistent Det Syn hg →
  base.(spec_rcu_base.IsRCUDomain) γb d -∗
  ([∗ map] p ↦ i ∈ G, p ↪[γrg]□ i) -∗
  base.(BaseNodeInfo) γb p i ty.(ty_sz) ty.(ty_res) -∗
  HistSnap γh hg -∗
  ghost_map_auth γrg 1 G -∗
  base.(BaseGuard) γb γbg g Syn G -∗
  |={E}=> Guard γd γg g ∗ RCUNodeInfo γd γg p i ty.
Proof.
  iIntros (? Hγd Hγg Hi_Syn [DISJ_G DISJ_i] GC) "#BRD #Prot #BInfo HS I BG".

  iMod (spec_rcu_base.guard_protect_node_info with "BRD BInfo BG") as "(BG & #BGInfo & %Lookup_p)"; [solve_ndisj|done|].

  iAssert (Guard γd γg g ∗ p ↪[γrg]□ i)%I with "[> BG HS I]" as "[$ #p]"; last first.
  { by iFrame (Hγd Hγg) "#". }

  destruct (G !! p) as [i'|] eqn:InG.
  - specialize (Lookup_p ltac:(done)) as [= ->].
    rewrite insert_id //.
    iDestruct (big_sepM_lookup with "Prot") as "#$"; [exact InG|].
    iModIntro. iFrame "∗#%".
  - iMod (ghost_map_insert_persist p i with "I") as "[I #$]"; [done|].
    iModIntro. iFrame "∗#%". iSplit.
    { rewrite big_sepM_insert //. iFrame "#". }
    iPureIntro. rewrite range_insert // disjoint_union_r //.
Qed.

Lemma guard_protect_managed :
  guard_protect_managed' N IsRCUDomain Guard Managed RCUNodeInfo.
Proof.
  iIntros (??????????) "#IRD M G".
  iDestruct "IRD" as (?? Hγ) "[BRD Inv]".
  iInv "Inv" as (???) ">(BRA & HA & %RIC)".
  iDestruct "G" as (??????? hg ??) "(BG & HS & I & #Prot & %DISJ & %GC)".
  iDestruct "M" as (???) "[BM HPB]". do 2 encode_agree Hγ.

  iDestruct (hist_auth_snap_valid with "HA HS") as %hg_pf_h%prefix_cut.
  iDestruct (hist_pointedby_is_alive with "HA HPB") as %LiveAt_i.

  iDestruct (spec_rcu_base.managed_get_node_info with "BM") as "#BInfo".
  iDestruct (spec_rcu_base.guard_managed_notin_syn with "BM BG") as %NotSyn_i.
  iModIntro. iSplitL "BRA HA".
  { iFrame "∗#%". }

  iAssert (Managed γd p i ty B) with "[$BM $HPB]" as "$"; first done.

  iApply (guard_protect_collect_guard_and_node_info G with "[#] [#] [#] HS I BG"); try done.
  rewrite hg_pf_h /LiveAt not_elem_of_app in LiveAt_i.
  destruct GC. set_solver.
Qed.

Lemma guard_protect_rcu_points_to :
  guard_protect_rcu_points_to' N IsRCUDomain Guard RCUPointsTo RCUNodeInfo.
Proof.
  intros ??? p1 i1 ????????. iIntros "#IRD #RGI1 RPT G".
  iDestruct "IRD" as (?? Hγd) "(#BIRD & #RI)".
  iDestruct "RGI1" as (????? Hγg) "[#p1 BGI1]".
  iDestruct "RPT" as (???) "[HPT #BNI2]". simpl.
  iDestruct "G" as (??????????) "(BG & HS & I & #Prot & %DISJ & %GC)".
  do 3 encode_agree Hγd. encode_agree Hγg.
  iDestruct (ghost_map_lookup with "I p1") as %?.
  assert (i1 ∉ Det) as Hguarded1.
  { assert (i1 ∈ range G); [|set_solver]. apply range_correct. eauto. }
  iInv "RI" as (???) ">(BRA & HA & %RIC)".
  iDestruct (hist_optimistic_traversal with "HA HS HPT") as %Hlive2%(GC.(gc_live_not_detached)).
  { by apply GC.(gc_live_not_detached) in Hguarded1. }
  iModIntro. iSplitL "BRA HA". { iFrame. done. }
  assert (i2 ∉ Syn).
  { destruct GC. set_solver. }
  iSplitL "HPT". { iFrame "∗#%". done. }

  iApply (guard_protect_collect_guard_and_node_info G with "[#] [#] [#] HS I BG"); try done.
  set_solver.
Qed.

Lemma guard_acc :
  guard_acc' N Guard RCUNodeInfo.
Proof.
  intros ????????. iIntros "#Info_p G".
  iDestruct "Info_p" as (???? Hγd Hγg) "[#p BInfo_p]".
  iDestruct "G" as (??????????) "(BG & HS & I & #Prot & %DISJ & %GC)".
  encode_agree Hγd. encode_agree Hγg.
  iMod (spec_rcu_base.guard_acc with "BInfo_p BG") as (lv) "(% & p↦ & R & RG & Close1)"; [solve_ndisj|].

  iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Close2".
  iExists lv. iFrame.

  iSplit.
  { iFrame "∗#%". }

  iIntros (lv') "[p↦ R]".
  iDestruct (ty_sz_eq with "R") as "#>%".
  iMod "Close2".
  iDestruct ("Close1" $! lv' with "[$p↦ $R]") as "$".
  iPureIntro. lia.
Qed.

Lemma managed_acc :
  managed_acc' N Managed.
Proof.
  iIntros (???????) "M".
  iDestruct "M" as (???) "[BM HPB]".
  iMod (spec_rcu_base.managed_acc with "BM") as (lv) "(% & p↦ & R & BM & Close1)"; [solve_ndisj|].

  iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Close2".
  iExists lv. iFrame.

  iSplit. { iFrame "∗#%". }

  iIntros (lv') "[p↦ R]".
  iDestruct (ty_sz_eq with "R") as "#>%".
  iMod "Close2".
  iDestruct ("Close1" $! lv' with "[$p↦ $R]") as "$".
  iPureIntro. lia.
Qed.

Lemma deleted_acc :
  deleted_acc' N Deleted.
Proof.
  iIntros (??????) "D".
  iDestruct "D" as (???) "[BM #HD]".
  iMod (spec_rcu_base.managed_acc with "BM") as (lv) "(% & p↦ & R & BM & Close1)"; [solve_ndisj|].

  iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Close2".
  iExists lv. iFrame.

  iSplit. { iFrame "∗#". done. }

  iIntros (lv') "[p↦ R]".
  iDestruct (ty_sz_eq with "R") as "#>%".
  iMod "Close2".
  iDestruct ("Close1" $! lv' with "[$p↦ $R]") as "$".
  iPureIntro. lia.
Qed.

Lemma managed_exclusive :
  managed_exclusive' N Managed.
Proof.
  intros ????????.
  iDestruct 1 as (?? Hγd) "[BM1 _]".
  iDestruct 1 as (?? ?) "[BM2 _]".
  encode_agree Hγd.
  iApply (spec_rcu_base.managed_exclusive with "BM1 BM2").
Qed.

Lemma guard_managed_agree :
  guard_managed_agree' N Guard Managed RCUNodeInfo.
Proof.
  intros ?????????.
  iIntros "#Info_p G M".
  iDestruct "Info_p" as (???? Hγd Hγg) "[#p BGInfo_p]".
  iDestruct "G" as (??????????) "(BG & HS & I & #Prot & %DISJ & %GC)".
  iDestruct "M" as (???) "[BM HPB]". do 2 encode_agree Hγd. encode_agree Hγg.
  by iDestruct (spec_rcu_base.guard_managed_agree with "BGInfo_p BG BM") as %->.
Qed.

Lemma rcu_points_to_link :
  rcu_points_to_link' N IsRCUDomain Managed RCUPointsTo.
Proof.
  iIntros (???????????) "IRD RPT M".
  iDestruct "IRD" as (?? Hγ) "[#BIRD #RI]".
  iDestruct "RPT" as (???) "[HPT _]".
  iDestruct "M" as (???) "[BM HPB]". do 2 encode_agree Hγ.

  iInv "RI" as (???) ">(BRA & HA & %RIC)".

  iDestruct (hist_pointsto_is_registered with "HA HPT") as %InHist_i.

  iMod (hist_points_to_link with "HA HPT HPB") as "(HA & HPT & HPB)".

  iModIntro.
  iSplitL "HA BRA". { iFrame "∗#%". iPureIntro. destruct RIC. split; unfold LiveAt in *; set_solver. }

  iModIntro.
  iDestruct (spec_rcu_base.managed_get_node_info with "BM") as "#Info_i2".

  iSplitL "HPT"; by iFrame "∗#%".
Qed.

Lemma rcu_points_to_unlink :
  rcu_points_to_unlink' N IsRCUDomain Managed RCUPointsTo.
Proof.
  iIntros (???????????) "IRD RPT M".
  iDestruct "IRD" as (?? Hγ) "[#BIRD #RI]".
  iDestruct "RPT" as (???) "[HPT _]".
  iDestruct "M" as (???) "[BM HPB]". do 2 encode_agree Hγ.

  iInv "RI" as (???) ">(BRA & HA & %RIC)".

  iDestruct (hist_pointsto_is_registered with "HA HPT") as %InHist_i.

  iMod (hist_points_to_unlink with "HA HPT HPB") as "(HA & HPT & HPB)".

  iModIntro.
  iSplitL "HA BRA". { iFrame "∗#%". iPureIntro. destruct RIC. split; unfold LiveAt in *; set_solver. }
  iModIntro.

  iSplitL "HPT"; by iFrame "∗#%".
Qed.

Lemma rcu_points_to_update :
  rcu_points_to_update' N IsRCUDomain Managed RCUPointsTo.
Proof.
  iIntros (???????????????) "IRD RPT fM tM".
  iDestruct "IRD" as (?? Hγ) "[#BIRD #RI]".
  iDestruct "RPT" as (???) "[HPT _]".
  iDestruct "fM" as (???) "[fBM fHPB]".
  iDestruct "tM" as (???) "[tBM tHPB]". do 3 encode_agree Hγ.

  iInv "RI" as (???) ">(BRA & HA & %RIC)".

  iDestruct (hist_pointsto_is_registered with "HA HPT") as %InHist_i.

  iMod (hist_points_to_update with "HA HPT fHPB tHPB") as "(HA & HPT & fHPB & tHPB)".

  iModIntro.
  iSplitL "HA BRA". { iFrame "∗#%". iPureIntro. destruct RIC. split; unfold LiveAt in *; set_solver. }
  iModIntro.

  iDestruct (spec_rcu_base.managed_get_node_info with "tBM") as "#tBInfo".
  iSplitL "HPT". { iFrame "∗#%". }
  iSplitL "fBM fHPB"; by iFrame "∗#%".
Qed.

Lemma managed_delete :
  managed_delete' N IsRCUDomain Managed Deleted.
Proof.
  iIntros (???????) "IRD M".
  iDestruct "IRD" as (?? Hγ) "[#BIRD #RI]".
  iDestruct "M" as (???) "[BM HPB]". encode_agree Hγ.

  iInv "RI" as (???) ">(BRA & HA & %RIC)".

  iDestruct (hist_pointedby_is_registered with "HA HPB") as %InHist_i.

  iMod (hist_delete_node with "HA HPB") as "[HA #HD]".

  iModIntro.
  iSplitL "HA BRA". { iFrame. iPureIntro. destruct RIC. split; unfold LiveAt in *; set_solver. }
  iModIntro.

  iFrame "∗#%".
Qed.

Lemma deleted_clean :
  deleted_clean' N IsRCUDomain Managed Deleted.
Proof.
  iIntros (???????????) "#IRD D M".
  iDestruct "IRD" as (?? Hγ) "[#BIRD #RI]".
  iDestruct "D" as (???) "[BMD #HD]".
  iDestruct "M" as (???) "[BM HPB]". do 2 encode_agree Hγ.

  iInv "RI" as (???) ">(BRA & HA & %RIC)".

  iMod (hist_pointedby_remove_deleted with "HA HD HPB") as "[HA HPB]".

  iModIntro.
  iSplitL "HA BRA". { iFrame "∗#%". }
  iModIntro.

  iSplitL "BMD HD"; by iFrame "∗#%".
Qed.

Lemma rcu_domain_retire_spec :
  rcu_domain_retire_spec' N base.(rcu_domain_retire) IsRCUDomain Deleted.
Proof.
  intros ??? p i ty sz ? Hsz. iIntros "#IRD" (Φ) "!> D HΦ".
  (* remove ▷ of HΦ *)
  iApply (wp_step_fupd _ E E _ (_ -∗ _)%I with "[$HΦ]"); [done..|].
  iDestruct "IRD" as (??) "(%Hγ & #BIRD & #RI)".
  iDestruct "D" as (???) "[BM #HD]". encode_agree Hγ.

  rewrite -Hsz.
  awp_apply (spec_rcu_base.rcu_domain_retire_spec with "BIRD BM"); [solve_ndisj..|].
  iInv "RI" as (???) ">(BRA & HA & %RIC)".
  iAaccIntro with "BRA".
  { iIntros. iModIntro. iFrame. done. }
  iIntros "BRA".

  iDestruct (hist_deleted_is_not_alive with "HA HD") as %Hdel.

  iModIntro. iSplitL "BRA HA".
  { iFrame. iPureIntro. split.
    - apply RIC.(ric_dom).
    - intros i' Hi'. case (decide (i' = i)) as [->|NE].
      + clear -Hdel Hi'. by exfalso.
      + set_unfold. move => [//|]. by apply RIC.(ric_live_unretired). }

  iIntros "HΦ". iApply "HΦ". done.
Qed.

Lemma rcu_domain_do_reclamation_spec :
  rcu_domain_do_reclamation_spec' N base.(rcu_domain_do_reclamation) IsRCUDomain.
Proof.
  intros ????. iIntros "#IRD" (Φ) "!> _ HΦ".
  iDestruct "IRD" as (??) "(%Hγ & #BIRD & #RI)".
  wp_apply (spec_rcu_base.rcu_domain_do_reclamation_spec with "BIRD [//]"); [solve_ndisj|].
  iFrame "HΦ".
Qed.

End rcu_traversal.

#[export] Typeclasses Opaque IsRCUDomain Inactive Guard Managed Deleted RCUPointsTo.
