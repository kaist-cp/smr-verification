From iris.base_logic.lib Require Import invariants ghost_map.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.

From smr Require Import ebr.spec_rcu_base ebr.spec_rcu_simple helpers logic.reclamation.

From iris.prelude Require Import options.

Set Printing Projections.

Section ebr.
Context `{!heapGS Σ, !reclamationG Σ}.
Context (N : namespace).

Context (base : spec_rcu_base.rcu_base_spec Σ (mgmtN N) (ptrsN N)).

Implicit Types
  (γd γb γdata γ_p : gname)
  (i : positive)
  (R : resource Σ).

Definition Managed γd (p : blk) (γ_p : gname) (sz : nat) R : iProp Σ :=
  ∃ γb γdata i,
    ⌜γd = encode (γb, γdata)⌝ ∗
    i ↪[γdata]□ γ_p ∗
    base.(BaseManaged) γb p i sz (wrap_resource γdata R γ_p).

Definition Guard γd (g : loc) (st : guard_state) : iProp Σ :=
  ∃ γb γdata,
    ⌜γd = encode (γb, γdata)⌝ ∗
    match st with
    | Deactivated => base.(BaseInactive) γb g
    | Activated γg => ∃ Syn G Gb,
        base.(BaseGuard) γb γg g Syn Gb ∗
        [∗ map] p ↦ γ_p; i ∈ G; Gb,
          i ↪[γdata]□ γ_p
    end.

Definition RCUInv γb γdata Im Dm Rs : iProp Σ :=
  ghost_map_auth γdata 1 Dm ∗
  base.(RCUAuth) γb Im Rs ∗
  ⌜dom Im = dom Dm⌝.

Definition IsRCUDomain γd d : iProp Σ :=
  ∃ γb γdata,
    ⌜γd = encode (γb, γdata)⌝ ∗
    base.(spec_rcu_base.IsRCUDomain) γb d ∗
    inv ((mgmtN N).@"simpl") (∃ Im Dm Rs, RCUInv γb γdata Im Dm Rs).

Definition NodeInfo γd γg p γ_p size_i R : iProp Σ :=
  ∃ γb γdata i,
    ⌜γd = encode (γb, γdata)⌝ ∗
    i ↪[γdata]□ γ_p ∗
    base.(BaseGuardedNodeInfo) γb γg p i size_i (wrap_resource γdata R γ_p).

Global Instance IsRCUDomain_Persistent γd d : Persistent (IsRCUDomain γd d).
Proof. apply _. Qed.

Global Instance NodeInfo_Persistent γd γg p γ_p size_i R : Persistent (NodeInfo γd γg p γ_p size_i R).
Proof. apply _. Qed.

Lemma rcu_domain_new_spec :
  rcu_domain_new_spec' N base.(rcu_domain_new) IsRCUDomain.
Proof.
  intros ?.
  iIntros (Φ) "_ HΦ".

  iApply wp_fupd.

  wp_apply (spec_rcu_base.rcu_domain_new_spec with "[//]") as (γb d) "[#BIRD BR]".
  iMod (ghost_map_alloc ∅) as (γdata) "[data _]".
  remember (encode (γb,γdata)) as γd eqn:Hγd.
  iMod (inv_alloc ((mgmtN N).@"simpl") _ (∃ Im Dm Rs, RCUInv γb γdata Im Dm Rs) with "[data BR]") as "#?".
  { iFrame. by rewrite !dom_empty_L. }

  iApply "HΦ". by iFrame (Hγd) "∗#".
Qed.

Lemma rcu_domain_register :
  rcu_domain_register' N IsRCUDomain Managed.
Proof.
  intros ????????.
  iIntros "#IRD (p↦ & †p & R)".
  iDestruct "IRD" as (γb γdata Hγd) "(BIRD & RI)".

  iInv "RI" as (???) ">(data & BRA & %Hdom)".

  iMod (spec_rcu_base.rcu_domain_register base (λ p lv i, i ↪[γdata]□ γ_p ∗ R p lv γ_p)%I
        (dom Dm)
        (λ i, ghost_map_auth γdata 1 (<[i := γ_p]> Dm) ∗ i ↪[γdata]□ γ_p)%I
      with "BIRD BRA p↦ †p [data $R]") as (i Hi) "(BRA & BM & [data #i↪□])"; [solve_ndisj..| |].
  { iIntros (i Hi).
    by iMod (ghost_map_insert_persist i γ_p with "data") as "[$ #$]"; [by apply not_elem_of_dom|].
  }

  iModIntro. iSplitL "BRA data".
  { iFrame. iPureIntro. rewrite !dom_insert_L. set_solver. }
  iModIntro. iFrame (Hγd) "∗#".
Qed.

Lemma guard_new_spec :
  guard_new_spec' N base.(guard_new) IsRCUDomain Guard.
Proof.
  intros ????.
  iIntros "#IRD" (Φ) "!> _ HΦ".
  iDestruct "IRD" as (γb γdata Hγd) "(BIRD & RI)".

  wp_apply (spec_rcu_base.guard_new_spec with "BIRD [//]") as (g) "BG"; [solve_ndisj|].

  iApply "HΦ". iFrame (Hγd) "∗".
Qed.

Lemma guard_activate_spec :
  guard_activate_spec' N base.(guard_activate) IsRCUDomain Guard.
Proof.
  intros ?????.
  iIntros "#IRD" (Φ) "!> G HΦ".
  iDestruct "IRD" as (γb γdata Hγd) "(BIRD & RI)".
  iDestruct "G" as (???) "BG". encode_agree Hγd.

  wp_apply (spec_rcu_base.guard_activate_spec with "BIRD BG") as (γg Syn) "BG"; [solve_ndisj|].

  iApply "HΦ". iFrame (Hγd) "∗". by iExists ∅.
Qed.

Lemma guard_managed_agree :
  guard_managed_agree' N Managed Guard NodeInfo.
Proof.
  intros ??????????.
  iIntros "#Info G M".
  iDestruct "Info" as (??? Hγd) "[#i↪□' BInfo]".
  iDestruct "G" as (??? Syn G Gb) "[BG #GInfo]".
  iDestruct "M" as (????) "[#i↪□ BM]". do 2 encode_agree Hγd.

  iDestruct (spec_rcu_base.guard_managed_agree with "BInfo BG BM") as %<-.
  by iDestruct (ghost_map_elem_agree with "i↪□ i↪□'") as %?.
Qed.

Lemma guard_protect :
  guard_protect' N IsRCUDomain Managed Guard NodeInfo.
Proof.
  intros ??????????.
  iIntros "#IRD M G".

  iDestruct "IRD" as (?? Hγd) "(BIRD & RI)".
  iDestruct "G" as (??? Syn G Gb) "[BG #GInfo]".
  iDestruct "M" as (????) "[#i↪□ BM]". do 2 encode_agree Hγd.

  iDestruct (spec_rcu_base.guard_managed_notin_syn with "BM BG") as %NotIn.
  iDestruct (spec_rcu_base.managed_get_node_info with "BM") as "#BInfo".
  iMod (spec_rcu_base.guard_protect_node_info with "BIRD BInfo BG") as "(BG & #BGInfo & %LookUp)"; [solve_ndisj|done|].

  iModIntro. iSplitL "BM".
  { iFrame (Hγd) "∗#". }

  iDestruct (big_sepM2_dom with "GInfo") as %Hdom.
  destruct (decide (is_Some (Gb !! p))) as [Hp|Hp%eq_None_not_Some]; last first.
  { assert (G !! p = None).
    { by rewrite -not_elem_of_dom Hdom not_elem_of_dom. }

    iSplit; iFrame (Hγd) "∗#".
    iExists (<[ p:= _ ]> G).

    rewrite (big_sepM2_insert _ _ _ p); [|done..].
    iFrame "#".
  }

  specialize (LookUp Hp) as HGbp.
  rewrite insert_id //.

  iDestruct (big_sepM2_lookup_r with "GInfo") as (? HGp) "#i↪□'"; [exact HGbp|].
  iDestruct (ghost_map_elem_agree with "i↪□ i↪□'") as %<-.

  iSplit; iFrame (Hγd) "∗#".
Qed.

Lemma guard_acc :
  guard_acc' N Guard NodeInfo.
Proof.
  intros ?????????.
  iIntros "#Info G".

  iDestruct "Info" as (??? Hγd) "[i↪□ BInfo]".
  iDestruct "G" as (??? Syn G Gb) "[BG #GInfo]".
  encode_agree Hγd.

  iMod (spec_rcu_base.guard_acc with "BInfo BG") as (lv) "(%Hlv & p↦ & [_ R] & BG & Close1)"; [solve_ndisj|].

  iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Close2".
  iExists lv. iFrame "∗%".

  iSplit.
  { iFrame "∗#". }

  iIntros (lv') "(%Hlv' & p↦ & R)".

  iMod "Close2".
  iMod ("Close1" with "[$p↦ R]"). { iFrame (Hlv') "∗#". }
  done.
Qed.

Lemma managed_acc :
  managed_acc' N Managed.
Proof.
  intros ???????.
  iDestruct 1 as (??? Hγd) "[#i↪ BM]".
  iMod (spec_rcu_base.managed_acc with "BM") as (lv) "(% & p↦ & [_ R] & BM & Close1)"; [solve_ndisj|].

  iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Close2".
  iExists lv. iFrame "∗%".

  iSplit.
  { iFrame "#". }

  iIntros (lv') "(%Hlv' & p↦ & R)".

  iMod "Close2".
  iMod ("Close1" with "[$p↦ R]"). { iFrame (Hlv') "∗#". }
  done.
Qed.

Lemma managed_exclusive :
  managed_exclusive' N Managed.
Proof.
  iDestruct 1 as (??? Hγd) "[#i↪ BM1]".
  iDestruct 1 as (??? ?) "[#i↪' BM2]".
  encode_agree Hγd.
  iApply (spec_rcu_base.managed_exclusive with "BM1 BM2").
Qed.

Lemma guard_deactivate_spec :
  guard_deactivate_spec' N base.(guard_deactivate) IsRCUDomain Guard.
Proof.
  intros ??????.
  iIntros "#IRD" (Φ) "!> G HΦ".

  iDestruct "IRD" as (γb γdata Hγd) "(BIRD & RI)".
  iDestruct "G" as (??????) "[BG #GInfo]". encode_agree Hγd.

  wp_apply (spec_rcu_base.guard_deactivate_spec with "BIRD BG") as "BG"; [solve_ndisj|].


  iApply "HΦ". iFrame (Hγd) "∗".
Qed.

Lemma guard_drop_spec :
  guard_drop_spec' N base.(guard_drop) IsRCUDomain Guard.
Proof.
  intros ??????.
  iIntros "#IRD" (Φ) "!> G HΦ".
  iDestruct "IRD" as (γb γdata Hγd) "(BIRD & RI)".
  iDestruct "G" as (???) "BG". encode_agree Hγd.

  destruct gs.
  - wp_apply (spec_rcu_base.guard_drop_inactive_spec with "BIRD BG"); [solve_ndisj|]. done.
  - iDestruct "BG" as (???) "[BG #GInfo]".
    wp_apply (spec_rcu_base.guard_drop_spec with "BIRD BG"); [solve_ndisj|]. done.
Qed.

Lemma rcu_domain_retire_spec :
  rcu_domain_retire_spec' N base.(rcu_domain_retire) IsRCUDomain Managed.
Proof.
  intros ????????.
  iIntros "#IRD" (Φ) "!> M HΦ".
  iDestruct "IRD" as (γb γdata Hγd) "(BIRD & RI)".
  iDestruct "M" as (????) "[#i↪ BM]". encode_agree Hγd.
  iApply (wp_step_fupd _ E E _ (_ -∗ _)%I with "[$HΦ]"); [done..|].

  awp_apply (spec_rcu_base.rcu_domain_retire_spec with "BIRD BM"); [solve_ndisj|].
  iInv "RI" as (???) ">(data & BRA & %Hdom)".
  iAaccIntro with "BRA".
  { iIntros. iFrame. done. }
  iIntros "BRA".

  iModIntro. iSplitL "BRA data".
  { iFrame. done. }
  iIntros "HΦ !>". iApply "HΦ". done.
Qed.

Lemma rcu_domain_do_reclamation_spec :
  rcu_domain_do_reclamation_spec' N base.(rcu_domain_do_reclamation) IsRCUDomain.
Proof.
  intros ????. iIntros "#IRD" (Φ) "!> _ HΦ".
  iDestruct "IRD" as (??) "(%Hγ & #BIRD & #RI)".
  wp_apply (spec_rcu_base.rcu_domain_do_reclamation_spec with "BIRD [//]"); [solve_ndisj|].
  iFrame "HΦ".
Qed.

End ebr.

#[export] Typeclasses Opaque IsRCUDomain Guard Managed NodeInfo.
