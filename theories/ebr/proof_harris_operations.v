From iris.algebra Require Import ofe.
From iris.base_logic.lib Require Import invariants ghost_var ghost_map.
From smr.program_logic Require Import atomic.
From smr.lang Require Import lang proofmode notation.
From smr Require Import sorted_list.
From iris.prelude Require Import options.

From smr Require Import helpers ebr.spec_rcu_traversal ebr.code_harris_operations ebr.spec_ordered_set.

Set Printing Projections.

Local Open Scope nat_scope.

Class hlG Σ := HLG {
  harris_list_absG :> ghost_varG Σ (list inf_Z);
  harris_list_ptrs_allG :> ghost_mapG Σ positive (inf_Z * blk);
  harris_list_ptrs_tagG :> ghost_mapG Σ positive (option (blk * positive) * bool);
}.

Definition hlΣ : gFunctors := #[ghost_varΣ (list inf_Z); ghost_mapΣ positive (inf_Z * blk); ghost_mapΣ positive (option (blk * positive) * bool)].

Global Instance subG_hlΣ {Σ} :
  subG hlΣ Σ → hlG Σ.
Proof. solve_inG. Qed.

Section harris_list.
Context `{!heapGS Σ, !hlG Σ}.
Notation iProp := (iProp Σ).
Notation type := (type Σ).
Context (listN rcuN : namespace) (DISJN : listN ## rcuN).

Variable (rcu : rcu_traversal_spec Σ rcuN).

Implicit Types
  (γp_a γp_t γl γr : gname)
  (i_p : positive)
  (p_all : gmap positive (inf_Z * blk))
  (p_tag : gmap positive ((option (blk * positive)) * bool))
  (L : list (inf_Z * bool * (blk * positive))).

Definition HList γl (L : list inf_Z) : iProp := ghost_var γl (1/2) L ∗ ⌜Sorted_inf_Z L⌝.

Global Instance HList_Timeless γl (L : list inf_Z) : Timeless (HList γl L).
Proof. apply _. Qed.

Lemma HList_sorted γl (L : list inf_Z) :
  HList γl L -∗ ⌜Sorted_inf_Z L⌝.
Proof. iDestruct 1 as "[_ $]". Qed.

Program Definition harris_type_pre γp_a γp_t γr (F : typeO Σ) : typeO Σ := {|
  ty_sz := nodeSize;
  ty_res (p : blk) lv i_p := ∃ (p_k : inf_Z) (p_on : option (blk * positive)) (p_t : Z),
          ⌜lv = [ #((blk_to_loc <$> (fst <$> p_on)) &ₜ p_t); #p_k]⌝ ∗
          i_p ↪[γp_a]□ (p_k,p) ∗
          rcu.(RCUPointsTo) γr p i_p next ((λ p, (p,F)) <$> p_on) ∗
          ( (* Not tagged *)
            ⌜p_t = 0⌝ ∗ i_p ↪[γp_t]{# 1/2} (p_on, false) ∨
            (* Tagged *)
            (* Note: spec is a bit weak. We know that p_on is Some. This may be useful in shortening certain parts of the proof. *)
            ⌜p_t = 1⌝ ∗ i_p ↪[γp_t]□ (p_on, true)
          );
|}%I.
Next Obligation. iIntros (???????). by iDestruct 1 as (??? ->) "_". Qed.

Global Instance harris_type_pre_contractive γp_a γp_t γr : TypeContractive (harris_type_pre γp_a γp_t γr).
Proof.
  intros n???. rewrite /harris_type_pre.
  constructor; simpl; [done|]. intros. rewrite dist_later_fin_iff.
  destruct n; [done|]. simpl in *.
  repeat apply bi.exist_ne => ?. repeat apply bi.sep_ne; try done.
  select (option _) ltac:(fun H => destruct H as [[??]|]); [simpl|done].
  by apply rcu.(RCUPointsTo_Some_Contractive).
Qed.

Definition harris_type γp_a γp_t γr : type := type_fixpoint (harris_type_pre γp_a γp_t γr).

Lemma harris_type_unfold γp_a γp_t γr :
  (harris_type γp_a γp_t γr) ≡ harris_type_pre γp_a γp_t γr (harris_type γp_a γp_t γr).
Proof. by rewrite /harris_type {1}(type_fixpoint_unfold (harris_type_pre γp_a γp_t γr)). Qed.

Lemma harris_node_destruct γp_a γp_t γr p lv i_p :
  ▷ ty_res (harris_type γp_a γp_t γr) p lv i_p -∗
  ▷ ∃ (p_k : inf_Z) (p_on : option (blk * positive)) (p_t : Z),
  ⌜lv = [ #((blk_to_loc <$> (fst <$> p_on)) &ₜ p_t); #p_k]⌝ ∗ i_p ↪[ γp_a ]□ (p_k, p) ∗
  rcu.(RCUPointsTo) γr p i_p next ((λ p, (p, harris_type γp_a γp_t γr)) <$> p_on) ∗
  (⌜p_t = 0⌝ ∗ i_p ↪[γp_t]{#1 / 2} (p_on, false) ∨ ⌜p_t = 1⌝ ∗ i_p ↪[γp_t]□ (p_on, true)).
Proof.
  iIntros "node !>". iEval (rewrite harris_type_unfold /=) in "node".
  iDestruct "node" as (? p_on p_t ->) "(#p↪□ & p.n↪rcu & p.n↪)".
  repeat iExists _. by iFrame "∗#%".
Qed.

(* TODO: ty_res should be first argument. *)
Lemma harris_node_destruct_agree γp_a γp_t γr p i_p (p_k : inf_Z) lv :
  ▷ i_p ↪[ γp_a ]□ (p_k, p) -∗
  ▷ ty_res (harris_type γp_a γp_t γr) p lv i_p -∗
  ▷ ∃ (p_on : option (blk * positive)) (p_t : Z),
  ⌜lv = [ #((blk_to_loc <$> (fst <$> p_on)) &ₜ p_t); #p_k]⌝ ∗
  rcu.(RCUPointsTo) γr p i_p next ((λ p, (p, harris_type γp_a γp_t γr)) <$> p_on) ∗
  (⌜p_t = 0⌝ ∗ i_p ↪[γp_t]{#1 / 2} (p_on, false) ∨ ⌜p_t = 1⌝ ∗ i_p ↪[γp_t]□ (p_on, true)).
Proof.
  iIntros "#p↪□ node".
  iDestruct (harris_node_destruct with "node") as (???) "(? & >p↪□' & ? & ?)". iNext.
  iDestruct (ghost_map_elem_agree with "p↪□ p↪□'") as %[= <-]; iClear "p↪□'".
  repeat iExists _. by iFrame "∗#%".
Qed.

Lemma harris_node_combine_on γp_a γp_t γr (p : blk) i_p (p_k : inf_Z) (p_on : option (blk * positive)) p_t :
  (blk_to_loc p) ↦∗ [ #((blk_to_loc <$> (fst <$> p_on)) &ₜ p_t); #p_k] -∗
  i_p ↪[ γp_a ]□ (p_k, p) -∗
  ▷ rcu.(RCUPointsTo) γr p i_p next ((λ p, (p, harris_type γp_a γp_t γr)) <$> p_on) -∗
  (⌜p_t = 0⌝ ∗ i_p ↪[γp_t]{#1 / 2} (p_on, false) ∨ ⌜p_t = 1⌝ ∗ i_p ↪[γp_t]□ (p_on, true)) -∗
  ∃ lv : list val, p ↦∗ lv ∗ ▷ (harris_type γp_a γp_t γr).(ty_res) p lv i_p.
Proof.
  iIntros "p↦ #p↪□ p.n↪rcu p.n↪". iExists _. iFrame "p↦".
  iNext. iEval (rewrite harris_type_unfold /=).
  iExists p_k,p_on,p_t. by iFrame "∗#%".
Qed.

Lemma harris_node_combine_some γp_a γp_t γr (p : blk) i_p (p_k : inf_Z) (p_n : blk) (i_p_n : positive) p_t :
  (blk_to_loc p) ↦∗ [ #((Some (blk_to_loc p_n)) &ₜ p_t); #p_k] -∗
  i_p ↪[ γp_a ]□ (p_k, p) -∗
  ▷ rcu.(RCUPointsTo) γr p i_p next (Some (p_n,i_p_n,harris_type γp_a γp_t γr)) -∗
  (⌜p_t = 0⌝ ∗ i_p ↪[γp_t]{#1 / 2} (Some (p_n,i_p_n), false) ∨ ⌜p_t = 1⌝ ∗ i_p ↪[γp_t]□ (Some (p_n,i_p_n), true)) -∗
  ∃ lv : list val, p ↦∗ lv ∗ ▷ (harris_type γp_a γp_t γr).(ty_res) p lv i_p.
Proof.
  iIntros "p↦ #p↪□ p.n↪rcu p.n↪". iExists _. iFrame "p↦".
  iNext. iEval (rewrite harris_type_unfold /=).
  iExists p_k,(Some (p_n,i_p_n)),p_t. by iFrame "∗#%".
Qed.

Definition AllPtrs p_all L γp_a γp_t : iProp :=
  [∗ map] i_p ↦ kp ∈ p_all, let '(k,p) := kp in
    ((∃ (i_p_n : positive) (p_n : blk) (p_n_k : inf_Z),
      i_p ↪[γp_t]□ (Some (p_n,i_p_n), true) ∗ i_p_n ↪[γp_a]□ (p_n_k, p_n))
      ∨ ⌜(k, false, (p,i_p)) ∈ L⌝).

Global Instance AllPtrs_timeless p_all L γp_a γp_t : Timeless (AllPtrs p_all L γp_a γp_t).
Proof. apply big_sepM_timeless. intros ?[??]. apply _. Qed.

Definition pp_to_mset (pn : option (blk * positive)) : gmultiset positive :=
  match pn with
  | Some (_,i_p) => {[+ i_p +]}
  | None => ∅
  end.

Definition ListNode (i : nat) (kbipp : inf_Z * bool * (blk * positive)) L γp_a γp_t γr : iProp :=
  ∃ (pn : option (blk * positive)) (pp : option (blk * positive)), let '(k,b,ipp) := kbipp in let '(p,i_p) := ipp in
  rcu.(Managed) γr p i_p (harris_type γp_a γp_t γr) (pp_to_mset pp) ∗
  i_p ↪[γp_a]□ (k,p) ∗
  (if (b : bool) then i_p ↪[γp_t]□ (pn, true) else i_p ↪[γp_t]{# 1/2} (pn, false)) ∗
  ⌜L.*2 !! (i + 1)%nat = pn ∧
  (* Info about prev ndoe *)
  match pp with
  | None => i = 0
  | Some (pp, i_pp) => i > 0 ∧ L.*2 !! (i - 1)%nat = Some (pp, i_pp)
  end⌝.

Definition Nodes L γp_a γp_t γr : iProp :=
  [∗ list] i ↦ kbp ∈ L, ListNode i kbp L γp_a γp_t γr .

Definition Nodes_rm_idx idx L γp_a  γp_t γr : iProp :=
  [∗ list] i ↦ kbp ∈ L,
    if decide (i = idx) then emp else ListNode i kbp L γp_a γp_t γr .

Definition Nodes_rm_idx_idx idx idx' L γp_a γp_t γr : iProp :=
  [∗ list] i ↦ kbγnn ∈ L,
  if decide (i = idx') then emp else (if decide (i = idx) then emp else ListNode i kbγnn L γp_a γp_t γr).

Global Instance case_next_node_persistent (b : bool) i_p (γp_t : gname) (pn : option (blk * positive)) : Persistent (if (b : bool) then i_p ↪[γp_t]□ (pn, true) else True)%I.
Proof. destruct b; apply _. Qed.

Definition HListInternalInv h γp_a γp_t γl i_h γr : iProp :=
  ∃ p_all p_tag L,
    ghost_var γl (1/2) (get_abs_state L) ∗
    ghost_map_auth γp_a 1 p_all ∗
    ghost_map_auth γp_t 1 p_tag ∗
    AllPtrs p_all L γp_a γp_t ∗
    Nodes L γp_a γp_t γr ∗
    ⌜Sorted_inf_Z (L.*1.*1) ∧
     L !! 0 = Some (-∞ᵢ, false, (h,i_h)) ∧
     (∃ i_tt, L !! (length L - 1) = Some (∞ᵢ, false, i_tt)) ∧
     dom p_all = dom p_tag⌝.

Definition IsHList (γp_a γp_t γl γr : gname) (l : loc) : iProp :=
  ∃ (d : loc) (h : blk) (i_h : positive),
    (l +ₗ domain) ↦□ #d ∗ (l +ₗ head) ↦□ #h ∗ i_h ↪[γp_a]□ (-∞ᵢ,h) ∗
    rcu.(IsRCUDomain) γr d ∗ inv listN (HListInternalInv h γp_a γp_t γl i_h γr).

Global Instance IsHList_Persistent γp_a γp_t γl γr l : Persistent (IsHList γp_a γp_t γl γr l).
Proof. apply _. Qed.

Lemma get_persistent_Nodes L idx k b i_p p γp_a γp_t γr :
  L !! idx = Some (k,b,(p,i_p)) →
  Nodes L γp_a γp_t γr -∗
  ∃ pn pp, i_p ↪[γp_a]□ (k,p) ∗ (if (b : bool) then i_p ↪[γp_t]□ (pn, true) else True) ∗
  ⌜L.*2 !! (idx + 1)%nat = pn ∧
  match pp with
  | None => idx = 0
  | Some (pp, i_pp) => idx > 0 ∧ L.*2 !! (idx - 1)%nat = Some (pp, i_pp)
  end⌝.
Proof.
  iIntros (Hidx) "Nodes". unfold Nodes,ListNode.
  rewrite big_sepL_delete; [|exact Hidx].
  iDestruct "Nodes" as "[p _]".
  iDestruct "p" as (pn pp) "(M & $ & p.n↦ & %)". iExists pn,pp.
  destruct b; iFrame "∗%".
Qed.

Lemma get_persistent_Nodes_rm_idx L idx k b i_p p γp_a γp_t γr idx' :
  L !! idx = Some (k,b,(p,i_p)) →
  idx ≠ idx' →
  Nodes_rm_idx idx' L γp_a γp_t  γr -∗
  ∃ pn pp, i_p ↪[γp_a]□ (k,p) ∗ (if (b : bool) then i_p ↪[γp_t]□ (pn, true) else True) ∗
  ⌜L.*2 !! (idx + 1)%nat = pn ∧
  match pp with
  | None => idx = 0
  | Some (pp, i_pp) => idx > 0 ∧ L.*2 !! (idx - 1)%nat = Some (pp, i_pp)
  end⌝.
Proof.
  iIntros (Hidx NE) "Nodes". unfold Nodes_rm_idx,ListNode.
  rewrite big_sepL_delete; [|exact Hidx].
  iDestruct "Nodes" as "[p _]". case_decide; [lia|].
  iDestruct "p" as (pn pp) "(M & $ & p.n↦ & %)". iExists pn,pp.
  destruct b; iFrame "∗%".
Qed.

Lemma Nodes_remove L idx k b i_p p γp_a γp_t γr :
  L !! idx = Some (k,b,(p,i_p)) →
  Nodes L γp_a γp_t γr -∗
  ∃ pn pp,
  (rcu.(Managed) γr p i_p (harris_type γp_a γp_t γr) (pp_to_mset pp) ∗
  i_p ↪[γp_a]□ (k,p) ∗
  (if (b : bool) then i_p ↪[γp_t]□ (pn, true) else i_p ↪[γp_t]{# 1/2} (pn, false))%I ∗
  ⌜L.*2 !! (idx + 1)%nat = pn ∧
  match pp with
  | None => idx = 0
  | Some (pp, i_pp) => idx > 0 ∧ L.*2 !! (idx - 1)%nat = Some (pp, i_pp)
  end⌝) ∗
  Nodes_rm_idx idx L γp_a γp_t γr.
Proof.
  iIntros (Hidx) "Nodes". unfold Nodes,ListNode.
  iEval (rewrite big_sepL_delete; [|exact Hidx]) in "Nodes".
  iDestruct "Nodes" as "[p Nodes]".
  iDestruct "p" as (pn pp) "(pM & #$ & p.n↦ & %)". iExists pn,pp.
  iFrame "∗#%".
Qed.

Lemma Nodes_combine L idx k b i_p p γp_a γp_t γr pn pp :
  L !! idx = Some (k,b,(p,i_p)) →
  L.*2 !! (idx + 1) = pn →
  match pp with
  | None => idx = 0
  | Some (pp, i_pp) => idx > 0 ∧ L.*2 !! (idx - 1)%nat = Some (pp, i_pp)
  end →
  Nodes_rm_idx idx L γp_a γp_t γr -∗
  rcu.(Managed) γr p i_p (harris_type γp_a γp_t γr) (pp_to_mset pp) -∗
  i_p ↪[γp_a]□ (k,p) -∗
  (if (b : bool) then i_p ↪[γp_t]□ (pn, true) else i_p ↪[γp_t]{# 1/2} (pn, false))%I -∗
  Nodes L γp_a γp_t γr.
Proof.
  iIntros (Hidx Hidx_next Hidx_prev) "Nodes M #i_p.k↪□ p.n↦". unfold Nodes,ListNode.
  iEval (rewrite big_sepL_delete; [|exact Hidx]). iFrame.
  iExists pn,pp. by iFrame "∗#%".
Qed.

Lemma Nodes_rm_idx_remove L idx k b i_p p γp_a γp_t γr idx' :
  L !! idx = Some (k,b,(p,i_p)) →
  idx' ≠ idx →
  Nodes_rm_idx idx' L γp_a γp_t γr -∗
  ∃ pn pp,
  (rcu.(Managed) γr p i_p (harris_type γp_a γp_t γr) (pp_to_mset pp) ∗
  i_p ↪[γp_a]□ (k,p) ∗
  (if (b : bool) then i_p ↪[γp_t]□ (pn, true) else i_p ↪[γp_t]{# 1/2} (pn, false))%I ∗
  ⌜L.*2 !! (idx + 1)%nat = pn ∧
  match pp with
  | None => idx = 0
  | Some (pp, i_pp) => idx > 0 ∧ L.*2 !! (idx - 1)%nat = Some (pp, i_pp)
  end⌝) ∗
  Nodes_rm_idx_idx idx' idx L γp_a γp_t γr.
Proof.
  iIntros (Hidx NE) "Nodes". unfold Nodes_rm_idx,ListNode.
  iEval (rewrite big_sepL_delete; [|exact Hidx]) in "Nodes".
  case_decide; [lia|].
  iDestruct "Nodes" as "[p Nodes]".
  iDestruct "p" as (pn pp) "(pM & #$ & p.n↦ & %)". iExists pn,pp.
  iFrame "∗#%".
Qed.

Lemma Nodes_rm_idx_combine L idx k b i_p p γp_a γp_t γr pn pp idx' :
  L !! idx = Some (k,b,(p,i_p)) →
  L.*2 !! (idx + 1) = pn →
  match pp with
  | None => idx = 0
  | Some (pp, i_pp) => idx > 0 ∧ L.*2 !! (idx - 1)%nat = Some (pp, i_pp)
  end →
  idx' ≠ idx →
  Nodes_rm_idx_idx idx' idx L γp_a γp_t γr -∗
  rcu.(Managed) γr p i_p (harris_type γp_a γp_t γr) (pp_to_mset pp) -∗
  i_p ↪[γp_a]□ (k,p) -∗
  (if (b : bool) then i_p ↪[γp_t]□ (pn, true) else i_p ↪[γp_t]{# 1/2} (pn, false))%I -∗
  Nodes_rm_idx idx' L γp_a γp_t γr.
Proof.
  iIntros (Hidx Hidx_next Hidx_prev NE) "Nodes M #i_p.k↪□ p.n↦". unfold Nodes_rm_idx,ListNode.
  iEval (rewrite big_sepL_delete; [|exact Hidx]).
  case_decide; [lia|]. iFrame.
  iExists pn,pp. by iFrame "∗#%".
Qed.

Lemma get_persistent_AllPtrs p_all L i_p p k γp_a γp_t :
  p_all !! i_p = Some (k,p) →
  AllPtrs p_all L γp_a γp_t -∗
  ((∃ (i_p_n : positive) (p_n : blk) (p_n_k : inf_Z),
      i_p ↪[γp_t]□ (Some (p_n,i_p_n), true) ∗ i_p_n ↪[γp_a]□ (p_n_k, p_n))
      ∨ ⌜(k, false, (p,i_p)) ∈ L⌝).
Proof.
  iIntros (Hp) "PTRS". unfold AllPtrs. rewrite big_sepM_delete; [|exact Hp]. simpl in *.
  iDestruct "PTRS" as "[$ _]".
Qed.

Definition harris_find_spec' (harris_find : val) : Prop :=
  ∀ (* Auxillary *) E (k : Z)
    (* harris inv *) (h : blk) γp_a γp_t γl i_h γr
    (* other locs *) l d g γg,
  ↑listN ∪ ↑rcuN ⊆ E →
  ⊢ rcu.(IsRCUDomain) γr d -∗
  rcu.(Guard) γr γg g -∗
  (l +ₗ head) ↦□ #h -∗
  i_h ↪[ γp_a ]□ (-∞ᵢ, h) -∗
  inv listN (HListInternalInv h γp_a γp_t γl i_h γr) -∗
  <<< ∀∀ (L : list inf_Z), HList γl L >>>
    harris_find #l #d #k @ E, (↑listN ∪ (↑ptrsN rcuN)), ↑mgmtN rcuN
  <<< ∃∃ (b : bool) (i_prev i_curr : positive) (idx : nat) (prev curr : blk) (prev_k curr_k : inf_Z),
      HList γl L ∗
      (* prev and curr are from the list. *)
      i_prev ↪[γp_a]□ (prev_k, prev) ∗ i_curr ↪[γp_a]□ (curr_k, curr) ∗
      ⌜L !! idx = Some prev_k ∧
      L !! (S idx) = Some curr_k ∧
      (* prev, c_prev_k and curr's key values are correct *)
      (prev_k < k)%inf_Z ∧ if b then curr_k = k else (k < curr_k)%inf_Z⌝,
      RET (#b, #prev, #curr),
        rcu.(Guard) γr γg g ∗
        rcu.(RCUNodeInfo) γr γg prev i_prev (harris_type γp_a γp_t γr) ∗
        rcu.(RCUNodeInfo) γr γg curr i_curr (harris_type γp_a γp_t γr)
      >>>.

Definition harris_find_au E γp_a γp_t γl γr (k : Z) g γg (Φ : val → iProp) : iProp :=
  AU  << ∃∃ (L : list inf_Z), HList γl L >> @ E ∖ (↑listN ∪ (↑ptrsN rcuN)), ↑mgmtN rcuN
      << ∀∀ (b : bool) (i_prev i_curr : positive) (idx : nat) (prev curr : blk) (prev_k curr_k : inf_Z),
          HList γl L ∗
          (* prev and curr are from the list. *)
          i_prev ↪[γp_a]□ (prev_k, prev) ∗ i_curr ↪[γp_a]□ (curr_k, curr) ∗
          ⌜L !! idx = Some prev_k ∧
          L !! (S idx) = Some curr_k ∧
          (* prev, c_prev_k and curr's key values are correct *)
          (prev_k < k)%inf_Z ∧ if b then curr_k = k else (k < curr_k)%inf_Z⌝,
          COMM ((rcu.(Guard) γr γg g ∗
                rcu.(RCUNodeInfo) γr γg prev i_prev (harris_type γp_a γp_t γr) ∗
                rcu.(RCUNodeInfo) γr γg curr i_curr (harris_type γp_a γp_t γr)) -∗
                Φ (#b, #prev, #curr)%V) >>.

Definition harris_helping_cas_spec' : Prop :=
  ∀ (committing : bool) Φ pr pr_v h γp_a γp_t γl i_h γr γg (d g : loc) (prev anchor curr : blk) p_k c_k i_p i_a i_c (k : Z) E,
  ↑listN ∪ ↑rcuN ⊆ E →
  (p_k < k)%inf_Z →
  {{{ inv listN (HListInternalInv h γp_a γp_t γl i_h γr) ∗
      rcu.(IsRCUDomain) γr d ∗
      rcu.(RCUNodeInfo) γr γg prev i_p (harris_type γp_a γp_t γr) ∗
      rcu.(RCUNodeInfo) γr γg anchor i_a (harris_type γp_a γp_t γr) ∗
      i_p ↪[ γp_a ]□ (p_k, prev) ∗
      i_c ↪[ γp_a ]□ (c_k, curr) ∗
      i_a ↪[ γp_t ]□ (Some (curr, i_c),true) ∗
      (if committing then proph pr pr_v ∗ harris_find_au E γp_a γp_t γl γr k g γg Φ else True) ∗
      rcu.(Guard) γr γg g ∗
      £ 1
  }}}
    CAS #(prev +ₗ 0%nat) #anchor #curr @ E
  {{{ (b : bool), RET #b;
      Guard rcu γr γg g ∗
      if (negb committing) then
        (if b then
          rcu.(Deleted) γr anchor i_a (harris_type γp_a γp_t γr)
        else
          True)
      else
        proph pr pr_v ∗
        (if b then
          rcu.(Deleted) γr anchor i_a (harris_type γp_a γp_t γr) ∗
          rcu.(RCUNodeInfo) γr γg curr i_c (harris_type γp_a γp_t γr) ∗
          (if decide (prophecy_to_bool pr_v ∨ (c_k < k)%inf_Z) then
            (* CAS success but curr is bad. *)
            harris_find_au E γp_a γp_t γl γr k g γg Φ
          else
            (* CAS success and commit. *)
            (* Impossible case, cause contradiction. *)
            (∃ (c_n : option (blk * positive)), i_c ↪[γp_t]□ (c_n,true)) ∨
            (Guard rcu γr γg g -∗ Φ (#(bool_decide (c_k = k)), #prev, #curr)%V))
        else
          harris_find_au E γp_a γp_t γl γr k g γg Φ)
  }}}.
End harris_list.

Record hfind_spec {Σ} `{!heapGS Σ, !hlG Σ} {listN rcuN : namespace}
    {DISJN : listN ## rcuN}
    {rcu : rcu_traversal_spec Σ rcuN}
  : Type := HarrisFindSpec {
  harris_find_spec_code :> harris_find_code;
  harris_find_spec : harris_find_spec' listN rcuN rcu harris_find_spec_code.(harris_find);
  harris_helping_cas_spec : harris_helping_cas_spec' listN rcuN rcu;
}.

Global Arguments hfind_spec : clear implicits.
Global Arguments hfind_spec _ {_ _} _ _ _ _ : assert.

Section proof.
Context `{!heapGS Σ, !hlG Σ}.
Context (listN rcuN : namespace) (DISJN : listN ## rcuN).
Variable (rcu : rcu_traversal_spec Σ rcuN) (harris_find : hfind_spec Σ listN rcuN DISJN rcu).
Notation iProp := (iProp Σ).
Notation IsHList := (IsHList listN rcuN rcu).
Notation harris_find_spec := (harris_find.(harris_find_spec)).
Notation harris_helping_cas_spec := (harris_find.(harris_helping_cas_spec)).
Notation harris_type := (harris_type rcuN rcu).

Lemma harris_new_spec γr d E :
  ↑listN ∪ ↑rcuN ⊆ E →
  {{{ rcu.(IsRCUDomain) γr d }}}
      harris_new #d @ E
  {{{ (l : loc) γp_a γp_t γl , RET #l; IsHList γp_a γp_t γl γr l ∗ HList γl [-∞ᵢ; ∞ᵢ] }}}.
Proof.
  iIntros (? Φ) "#IRD HΦ". wp_lam.
  wp_alloc pos as "pos↦" "†pos". wp_pures.
  wp_alloc neg as "neg↦" "†neg". wp_pures.
  do 2 (wp_apply (wp_store_offset with "neg↦") as "neg↦"; [by simplify_list_eq|]; wp_pures).
  do 2 (wp_apply (wp_store_offset with "pos↦") as "pos↦"; [by simplify_list_eq|]; wp_pures).
  wp_alloc l as "l↦" "†l". iClear "†l"; wp_pures.
  do 2 (wp_apply (wp_store_offset with "l↦") as "l↦"; [by simplify_list_eq|]; wp_pures). simpl in *.
  iMod (ghost_var_alloc [-∞ᵢ; ∞ᵢ]) as (γl) "[Labs Linv]".
  iMod (ghost_map_alloc (∅ : gmap positive (inf_Z * blk))) as (γp_a) "[●p_all _]".
  iMod (ghost_map_alloc (∅ : gmap positive (option (blk * positive) * bool))) as (γp_t) "[●p_tag _]".
  iApply "HΦ". iSplitR "Labs"; last first.
  { iFrame. iPureIntro. repeat constructor. }

  iMod (rcu.(rcu_domain_register) ∅ (harris_type γp_a γp_t γr)
        [None; None]
        (λ i_pos,
          ghost_map_auth γp_a 1 ({[ i_pos := (∞ᵢ,pos) ]}) ∗
          ghost_map_auth γp_t 1 ({[ i_pos := (None,false) ]}) ∗
          i_pos ↪[ γp_a ]□ (∞ᵢ,pos) ∗
          i_pos ↪[ γp_t ]{# 1/2 } (None, false))%I
        ∅
        with "IRD pos↦ †pos [] [●p_all ●p_tag]") as (i_pos) "(_ & posM & _ & ●p_all & ●p_tag & #pos↪□ & pos.n↪)";
        simpl; [solve_ndisj|solve_ndisj|solve_ndisj | rewrite harris_type_unfold //=; lia.. | done | |].
  { iIntros (i_pos _) "[pos.n↪rcu _]".
    iMod (ghost_map_insert_persist i_pos with "●p_all") as "[$ #pos↪□]"; [set_solver|].
    iMod (ghost_map_insert i_pos (None, false) with "●p_tag") as "[$ [pos.n↪ $]]"; [set_solver|].
    iModIntro. iFrame "#". iEval (rewrite harris_type_unfold /=).
    iExists _,None,_. simpl in *. iFrame "∗#%". iSplit; [done|]. iLeft. by iFrame.
  }
  iMod (rcu.(rcu_domain_register) {[ i_pos ]} (harris_type γp_a γp_t γr)
        [Some (pos, i_pos, harris_type γp_a γp_t γr, ∅); None]
        (λ i_neg,
          ghost_map_auth γp_a 1 {[ i_neg := (-∞ᵢ,neg) ; i_pos := (∞ᵢ, pos)]} ∗
          ghost_map_auth γp_t 1 {[ i_neg := (Some (pos,i_pos),false); i_pos := (None, false) ]} ∗
          i_neg ↪[ γp_a ]□ (-∞ᵢ,neg) ∗
          i_neg ↪[ γp_t ]{# 1/2 } (Some (pos,i_pos), false))%I
        ∅
        with "IRD neg↦ †neg [posM] [●p_all ●p_tag]") as (i_neg NE%not_elem_of_singleton) "(negM & posM & ●p_all & ●p_tag & #neg↪□ & neg.n↪)";
        simpl; [solve_ndisj|solve_ndisj|solve_ndisj | rewrite harris_type_unfold //=; lia.. | by iFrame | |].
  { iIntros (i_neg NotIn) "(neg.n↪rcu & _)".
    iMod (ghost_map_insert_persist i_neg with "●p_all") as "[$ #neg↪□]"; [rewrite -not_elem_of_dom; set_solver|].
    iMod (ghost_map_insert i_neg (Some (pos,i_pos), false) with "●p_tag") as "[$ [neg.n↪ $]]"; [rewrite -not_elem_of_dom; set_solver|].
    iModIntro. iFrame "#". iEval (rewrite harris_type_unfold /=).
    iExists _,(Some (_,_)),_. simpl in *. iFrame "∗#%". iSplit; [done|]. iLeft. by iFrame.
  }
  iDestruct "posM" as "[posM _]". rewrite (left_id ∅).

  iMod (array_persist with "l↦") as "l↦□".
  iEval (rewrite array_cons array_singleton) in "l↦□". iDestruct "l↦□" as "[l.h↦□ l.d↦□]".
  repeat iExists _. rewrite loc_add_0. iFrame "∗#%".

  iMod (inv_alloc listN _ (HListInternalInv _ _ _ _ _ _ _ _) with "[Linv ●p_all ●p_tag negM neg.n↪ posM pos.n↪]") as "$"; [|done].
  iNext. repeat iExists _.
  set (L := [(-∞ᵢ,false,(neg, i_neg));(∞ᵢ,false,(pos, i_pos))]).
  assert ([-∞ᵢ; ∞ᵢ] = get_abs_state L) as -> by done.
  iFrame "∗#". rewrite big_sepL_nil. iSplitR; [|iSplit].
  - rewrite /AllPtrs big_sepM_insert; [|by simplify_map_eq].
    rewrite big_sepM_singleton. iSplit; iRight; iPureIntro.
    all: apply elem_of_list_lookup.
    + by exists 0.
    + by exists 1.
  - iSplitL "neg.n↪ negM"; [|iSplit; [|done]].
    + iExists (Some (_,_)),None. iFrame. iPureIntro. by simplify_list_eq.
    + iExists None,(Some (_,_)). iFrame. iPureIntro. split_and!; [|lia|]; by simplify_list_eq.
  - iPureIntro. split_and!.
    + repeat constructor.
    + done.
    + by eexists.
    + set_solver.
Qed.

Lemma harris_lookup_spec E γp_a γp_t γl γr l g (k : Z) :
  ↑listN ∪ ↑rcuN ⊆ E →
  IsHList γp_a γp_t γl γr l -∗
  rcu.(Inactive) γr g -∗
  <<< ∀∀ L, HList γl L >>>
    (harris_lookup harris_find rcu) #l #g #k @ E,(↑listN ∪ (↑ptrsN rcuN)),↑mgmtN rcuN
  <<< ∃∃ b, HList γl L ∗ ⌜lookup_post L b k⌝, RET #b, rcu.(Inactive) γr g >>>.
Proof using All.
  intros ?.
  iIntros "IsHarris G" (Φ) "AU". iDestruct "IsHarris" as (d h i_h) "#(l.d↦□ & l.h↦□ & h↪□ & IRD & IsHarris)".
  wp_lam. wp_load. wp_pures.
  wp_apply (rcu.(guard_activate_spec) with "IRD G") as (γg) "G"; [solve_ndisj|]; wp_seq.
  awp_apply (harris_find_spec with "IRD G l.h↦□ h↪□ IsHarris"); [solve_ndisj|].
  iApply (aacc_aupd with "AU"); [solve_ndisj|].
  iIntros (L) "HList". iAaccIntro with "HList"; first eauto with iFrame.
  iIntros (b i_p i_c idx p c p_k c_k) "(HList & #p↪□ & #c↪□ & %Hp & %Hc & %Hp_k & %Hc_p_k) !>".
  iDestruct (HList_sorted with "HList") as %LSort.
  iRight. iExists b. iFrame. iSplit; [iPureIntro|]; last first.
  { iIntros "HΦ !> [G _]". wp_pures.
    wp_apply (rcu.(guard_deactivate_spec) with "IRD G") as "G"; [solve_ndisj|]; wp_pures.
    by iApply "HΦ".
  }
  apply (prove_lookup_post idx p_k c_k); done.
Qed.

Lemma harris_insert_spec E γp_a γp_t γl γr l g (k : Z) :
  ↑listN ∪ ↑rcuN ⊆ E →
  IsHList γp_a γp_t γl γr l -∗
  rcu.(Inactive) γr g -∗
  <<< ∀∀ L, HList γl L >>>
    (harris_insert harris_find rcu) #l #g #k @ E,(↑listN ∪ (↑ptrsN rcuN)),↑mgmtN rcuN
  <<< ∃∃ (b : bool) L', HList γl L' ∗
      ⌜if b then
        insert_succ_post L L' k
      else
        insert_fail_post L L' k⌝,
      RET #b,
      rcu.(Inactive) γr g
      >>>.
Proof.
  intros ?.
  iIntros "#IsHarris G" (Φ) "AU". iDestruct "IsHarris" as (d h i_h) "#(l.d↦□ & l.h↦□ & h↪□ & IRD & IsHarris)".
  wp_lam. wp_pures. wp_load. wp_pures.
  wp_apply (rcu.(guard_activate_spec) with "IRD G") as (γg) "G"; [solve_ndisj|]; wp_seq.
  wp_alloc n as "n↦" "†n". wp_pures.
  wp_apply (wp_store_offset with "n↦") as "n↦"; [by simplify_list_eq|]. wp_seq. simpl.
  wp_bind (harris_insert_loop _ _ _ _)%E.
  move: #0 => next.
  iLöb as "IH" forall (next).
  wp_lam. wp_pure credit: "Lc". wp_pures.
  awp_apply (harris_find_spec with "IRD G l.h↦□ h↪□ IsHarris"); [solve_ndisj|].
  iApply (aacc_aupd with "AU"); [solve_ndisj|]. iIntros (L) "HList".
  iAaccIntro with "HList"; first eauto with iFrame.
  iIntros ([] i_p i_c idx p c p_k c_k) "(HList & #p↪□ & #c↪□ & %Hp & %Hc & %Hp_k & %Hc_p_k) !>".
  { (* key found *)
    iRight. iExists false, L. iFrame. iSplit; [iPureIntro|]; last first.
    { iIntros "HΦ !> [G _]". wp_pures. wp_free; [done|]. wp_pures.
      wp_apply (rcu.(guard_deactivate_spec) with "IRD G") as "G"; [solve_ndisj|]. wp_pures.
      by iApply "HΦ".
    }
    by apply (prove_insert_fail_post (S idx) c_k).
  }
  (* key not found *)
  iLeft. iFrame. iIntros "AU !> (G & #pInfo & #cInfo)". wp_pures. clear dependent idx L.
  wp_apply (wp_store_offset with "n↦") as "n↦"; [by simplify_list_eq|]. wp_seq. simpl; clear next.
  wp_pures. wp_bind (CmpXchg _ _ _)%E.
  iInv "pInfo" as (lv) "(p↦ & node & G)".
  iDestruct (harris_node_destruct_agree with "p↪□ node") as (p_on p_t) "(>% & p.n↪rcu & >[[% p.n↪]|[% #p.n↪□]])"; subst lv p_t; last first.
  { (* prev tagged, fail CAS and retry *)
    wp_apply (wp_cmpxchg_fail_offset with "p↦") as "p↦"; [done..|destruct p_on; simpl; auto|].
    iModIntro. iDestruct (harris_node_combine_on with "p↦ p↪□ p.n↪rcu [$p.n↪□]") as "$"; [by iRight|].
    wp_pures. wp_apply ("IH" with "AU G †n n↦").
  }
  iInv "IsHarris" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
  iMod (lc_fupd_elim_later with "Lc Nodes") as "Nodes".
  iDestruct (ghost_map_lookup with "●p_all p↪□") as %Hptrs_p.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[p.n|%HLp]"; [exact Hptrs_p| |].
  { (* prev tagged, impossible *)
    iDestruct "p.n" as (γp_n p_n p_n_k) "[p.n↪□ p_n↪□]".
    iDestruct (ghost_map_elem_agree with "p.n↪□ p.n↪") as %[= ?].
  }
  (* prev not tagged, obtain next and check if it is still c. *)
  apply elem_of_list_lookup in HLp as [idx_p HLp].
  iDestruct (Nodes_remove with "Nodes") as (? p_p) "[(pM & _ & p.n↪' & %HLp_n & %HLp_p) Nodes]"; [exact HLp|]; simpl.
  iDestruct (ghost_map_elem_agree with "p.n↪ p.n↪'") as %[= <-].
  destruct (next_not_tail_is_Some idx_p L p_k false (p, i_p) p_on) as [[p_n i_p_n] [= ->]]; [naive_solver..|simpl in *].
  destruct (decide (p_n = c)) as [->|NE]; last first.
  { (* curr changed from c, CAS must fail *)
    wp_apply (wp_cmpxchg_fail_offset with "p↦") as "p↦"; [done|simpl;naive_solver..|].
    iDestruct (Nodes_combine with "Nodes pM [] [p.n↪']") as "Nodes"; [done..|].
    iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes".
    { repeat iExists _. by iFrame "∗#%". }
    iModIntro. iDestruct (harris_node_combine_some with "p↦ p↪□ p.n↪rcu [p.n↪]") as "$"; [iLeft; by iFrame|].
    wp_pures. wp_apply ("IH" with "AU G †n n↦").
  }
  (* curr is still c, CAS succeed *)
  iClear "IH". wp_apply (wp_cmpxchg_suc_offset with "p↦") as "p↦"; [simpl;auto..|]. simpl.

  (* prev is right before curr. *)
  apply list_lookup_fmap_Some in HLp_n as [[[p_n_k b] [??]] [HLc [= <- <-]]].
  iDestruct (Nodes_rm_idx_remove with "Nodes") as (c_n [[c_p i_c_p]|]) "[(cM & #c↪ & c.n↪ & %HLc_n & %HLc_p) Nodes]"; [exact HLc|lia| |lia].
  iDestruct (rcu.(guard_managed_agree) with "cInfo G cM") as %<-.
  iDestruct (ghost_map_elem_agree with "c↪□ c↪") as %[= <-].

  destruct HLc_p as [_ HLc_p].
  assert (c_p = p ∧ i_c_p = i_p) as [-> ->].
  { rewrite Nat.add_1_r Nat.sub_1_r /= in HLc_p. get_third HLp. naive_solver. }
  iClear "c↪". simpl in *.

  iMod (rcu.(rcu_points_to_unlink) with "IRD p.n↪rcu cM") as "[p.n↪rcu cM]"; [solve_ndisj|rewrite gmultiset_difference_diag].
  iMod (rcu.(rcu_domain_register) (dom p_all) (harris_type γp_a γp_t γr)
        [Some (c, i_c, harris_type γp_a γp_t γr, ∅); None]
        (λ i_n,
          ghost_map_auth γp_a 1 (<[i_n := (FinInt k,n)]> p_all) ∗
          ghost_map_auth γp_t 1 (<[i_n := (Some (c,i_c),false)]> p_tag) ∗
          i_n ↪[ γp_a ]□ (FinInt k,n) ∗
          i_n ↪[ γp_t ]{# 1/2 } (Some (c,i_c), false))%I
        ∅
        with "IRD n↦ †n [cM] [●p_all ●p_tag]") as (i_n NotIn%not_elem_of_dom) "(nM & cM & ●p_all & ●p_tag & #n↪□ & n.n↪)";
        simpl; [solve_ndisj|solve_ndisj|solve_ndisj | rewrite harris_type_unfold //=; lia.. | by iFrame | |].
  { iIntros (i_n NotIn) "[c.n↪rcu _]".
    iMod (ghost_map_insert_persist i_n with "●p_all") as "[$ #n↪□]"; [by rewrite -not_elem_of_dom|].
    iMod (ghost_map_insert i_n (Some (c,i_c), false) with "●p_tag") as "[$ [n.n↪ $]]"; [by rewrite -not_elem_of_dom -Hdom|].
    iModIntro. iFrame "#". iEval (rewrite harris_type_unfold /=).
    iExists _,(Some (_,_)),_. simpl in *. iFrame "∗#%". iSplit; [done|]. iLeft. by iFrame.
  }
  iDestruct "cM" as "[cM _]". rewrite (left_id ∅).
  iMod (rcu.(rcu_points_to_link) with "IRD p.n↪rcu nM") as "[p.n↪rcu nM]"; [solve_ndisj|rewrite (left_id ∅)].

  set (L' := insert_middle_nbl (S idx_p) k false (n,i_n) L) in *.
  iMod "AU" as (?) "[[Labs %HLabs] [_ Commit]]".
  iDestruct (ghost_var_agree with "Labs Linv") as %->.
  iMod (ghost_var_update_halves (get_abs_state L') with "Labs Linv") as "[Labs Linv]".
  assert (Sorted_inf_Z L'.*1.*1).
  { subst L'. rewrite insert_middle_nbl_insert_middle. apply insert_middle_inf_Z_sorted; [done| |].
    - intros z'. get_first HLp. rewrite take_last; [naive_solver|eauto].
    - intros z'. get_first HLc. rewrite lookup_drop Nat.add_0_r -Nat.add_1_r. naive_solver.
  }
  iMod ("Commit" $! true with "[$Labs]") as "HΦ".
  { iPureIntro. split.
    - by apply sorted_inf_Z_get_abs_state_sorted.
    - by apply (prove_insert_succ_post p_k c_k (p,i_p) (c,i_c) (n,i_n) idx_p b).
  }

  iCombine "p.n↪ p.n↪'" as "p.n↪".
  iMod (ghost_map_update (Some (n,i_n),false) with "●p_tag p.n↪") as "[●p_tag [p.n↪ p.n↪']]".
  iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes pM p.n↪ n.n↪ nM c.n↪ cM".
  { iNext. repeat iExists _. iFrame "Linv ●p_all ●p_tag #%".
    assert (idx_p + 1 < length L); [by apply lookup_lt_Some in HLc|].
    iSplitL "PTRS".
    - rewrite /AllPtrs big_sepM_insert; [|by simplify_map_eq].
      iSplitR "PTRS".
      + iRight. iPureIntro. rewrite elem_of_list_lookup.
        exists (S idx_p). subst L'. unfold insert_middle_nbl. simpl.
        rewrite lookup_app_r take_length_le; [|lia..].
        by rewrite Nat.sub_diag.
      + iApply (big_sepM_mono with "PTRS").
        iIntros (i_l' [k' l'] H_ptrs_l) "l'".
        iDestruct "l'" as "[$|%HLl']".
        iRight. iPureIntro.
        subst L'. unfold insert_middle_nbl.
        rewrite -(take_drop (S idx_p) L) in HLl'.
        apply elem_of_app. apply elem_of_app in HLl' as [HLl'|HLl'].
        * by left.
        * right. apply elem_of_app. by right.
    - iSplitL; last first.
      { iPureIntro. split_and!; [done|..].
        - subst L'. unfold insert_middle_nbl. rewrite lookup_app_l; [|rewrite take_length_le; lia].
          rewrite lookup_take; [done|lia].
        - destruct HLt as [t HLt]. exists t.
          subst L'. unfold insert_middle_nbl. rewrite !app_length drop_length take_length_le; [|lia].
          rewrite /= Nat.sub_0_r lookup_app_r take_length_le; [|lia..].
          rewrite lookup_cons_ne_0; [|lia]. rewrite lookup_drop -HLt. f_equal. lia.
        - rewrite dom_insert_L Hdom dom_insert_lookup_L; last first.
          { rewrite -elem_of_dom dom_insert_L -Hdom. apply elem_of_union_r,elem_of_dom. eauto. }
          by rewrite dom_insert_L.
      }
      simpl. unfold Nodes_rm_idx_idx.
      (* Split into respective parts. *)
      iEval (rewrite -{2}(take_drop_middle L idx_p (p_k, false, (p,i_p))); [|done]) in "Nodes".
      rewrite {1}(_ : take (S idx_p) L = take idx_p L ++ [(p_k, false, (p,i_p))]); [|by apply take_S_r].
      rewrite !big_sepL_app. simpl.
      iDestruct "Nodes" as "(NodesTake & _ & NodesDrop)".
      rewrite (drop_S _ ((c_k, b, (c, i_c)))); [|rewrite -HLc; f_equal; lia]. simpl in *.
      iDestruct "NodesDrop" as "[_ NodesDrop]".
      assert (idx_p <= length L) by lia.
      rewrite !Nat.add_0_r !take_length_le /=; [|lia|done].
      iSplitL "NodesTake p.n↪ pM"; [iSplitR "p.n↪ pM"|iSplitL "n.n↪ nM"; [|iSplitR "NodesDrop"]].
      + iApply (big_sepL_mono with "NodesTake"); iIntros (idx' [[z' b'] [l' i_l']] Hidx') "idx'".
        apply lookup_take_Some in Hidx' as [_ LE].
        repeat (case_decide; [lia|]).
        iDestruct "idx'" as (on op) "(l'M & $ & l'.n↦ & %HLl'_n & %HLl'_p)".
        iExists on,op. iFrame. iPureIntro.
        assert (idx' + 1 < length (take (S idx_p) L.*2)).
        { rewrite take_length_le; [lia|]. rewrite fmap_length. lia. }
        rewrite !fmap_app /= fmap_take !lookup_app_l; [|lia..].
        split.
        * rewrite -(take_drop (S idx_p) L) fmap_app lookup_app_l fmap_take in HLl'_n; done.
        * destruct op as [[op i_op]|]; simpl in *; [|done].
          destruct HLl'_p as [? HLl'_p]. split; [done|].
          rewrite -(take_drop (S idx_p) L) fmap_app lookup_app_l fmap_take in HLl'_p; [done|lia].
      + iSplit; [|done]. iExists (Some (n,i_n)),p_p. iFrame "∗#". iPureIntro. subst L'.
        rewrite !fmap_app lookup_app_r /= fmap_length take_length_le; [|lia..].
        rewrite Nat.add_1_r Nat.sub_diag. split; [done|].
        destruct p_p as [[p_p i_p_p]|]; simpl in *; [|done]. destruct HLp_p as [? HLp_p].
        split; [done|]. rewrite fmap_take lookup_app_l; last first.
        { rewrite take_length_le; [|rewrite fmap_length]; lia. }
        rewrite lookup_take; [done|lia].
      + iSplit; [|done]. iExists (Some (c,i_c)),(Some (p,i_p)). iFrame "∗#". iPureIntro. subst L'.
        rewrite !fmap_app lookup_app_r /= fmap_length take_length_le; try lia.
        rewrite /= lookup_cons_ne_0; [|lia]. get_third HLc. rewrite /= fmap_drop lookup_drop -HLc.
        split_and!; [f_equal;lia|lia|]. rewrite fmap_take lookup_app_l; last first.
        { rewrite take_length_le; [|rewrite fmap_length]; lia. }
        rewrite Nat.sub_0_r lookup_take; [|lia]. by get_third HLp.
      + iExists c_n,(Some (n,i_n)). iFrame "∗#". iPureIntro. subst L'.
        rewrite !fmap_app !(lookup_app_r (take (S idx_p) L).*2) /= !fmap_length !take_length_le; try lia.
        rewrite /= lookup_cons_ne_0; [|lia]. rewrite fmap_drop lookup_drop -HLc_n.
        split_and!; [f_equal;lia|lia|]. by rewrite Nat.add_1_r Nat.sub_0_r Nat.sub_diag.
      + iApply (big_sepL_mono with "NodesDrop"). iIntros (idx' [[z' b'] [l' i_l']] Hidx') "idx'".
        repeat (case_decide; [lia|]).
        iDestruct "idx'" as (on op) "(l'M & $ & l'.n↦ & %HLl'_n & %HLl'_p)".
        iExists on,op. iFrame. iPureIntro.
        rewrite !fmap_app !lookup_app_r /= fmap_length take_length_le /=; try lia.
        rewrite !fmap_drop !lookup_drop -HLl'_n. split; [f_equal; lia|].
        destruct op as [[op i_op]|]; [|lia]. destruct HLl'_p as [_ HLl'_p].
        split; [lia|]. rewrite -HLl'_p. f_equal. lia.
  }
  iModIntro. iDestruct (harris_node_combine_some with "p↦ p↪□ p.n↪rcu [p.n↪']") as "$"; [iLeft; by iFrame|].
  wp_pures.
  wp_apply (rcu.(guard_deactivate_spec) with "IRD G") as "G"; [solve_ndisj|]. wp_pures.
  by iApply "HΦ".
Qed.

Lemma harris_delete_spec E γp_a γp_t γl γr l g (k : Z) :
  ↑listN ∪ ↑rcuN ⊆ E →
  IsHList γp_a γp_t γl γr l -∗
  rcu.(Inactive) γr g -∗
  <<< ∀∀ L, HList γl L >>>
    (harris_delete harris_find rcu) #l #g #k @ E,(↑listN ∪ (↑ptrsN rcuN)),↑mgmtN rcuN
  <<< ∃∃ (b : bool) L', HList γl L' ∗
      ⌜if b then
        delete_succ_post L L' k
      else
        delete_fail_post L L' k⌝,
      RET #b,
      rcu.(Inactive) γr g
      >>>.
Proof.
  intros ?.
  iIntros "#IsHarris G" (Φ) "AU". iDestruct "IsHarris" as (d h i_h) "#(l.d↦□ & l.h↦□ & h↪□ & IRD & IsHarris)".
  wp_lam. wp_pures. wp_load. wp_pures.
  wp_apply (rcu.(guard_activate_spec) with "IRD G") as (γg) "G"; [solve_ndisj|]. wp_pures.
  iLöb as "IH".
  wp_lam. wp_pure credit: "Lc". wp_pures.
  awp_apply (harris_find_spec with "IRD G l.h↦□ h↪□ IsHarris"); [solve_ndisj|].
  iApply (aacc_aupd with "AU"); [solve_ndisj|]; iIntros (L) "HList".
  iAaccIntro with "HList"; first eauto with iFrame.
  iIntros ([] i_p i_c idx p c p_k c_k) "(HList & #p↪□ & #c↪□ & %Hp & %Hc & %Hp_k & %Hc_p_k) !>"; last first.
  { (* key not found *)
    iDestruct (HList_sorted with "HList") as %LSort.
    iRight. iExists false, L. iFrame. iSplit; [iPureIntro|]; last first.
    { iIntros "HΦ !> [G _]". wp_pures.
      wp_apply (rcu.(guard_deactivate_spec) with "IRD G") as "G"; [solve_ndisj|].
      wp_pures. by iApply "HΦ".
    }
    by apply (prove_delete_fail_post idx p_k c_k).
  }
  (* key found *)
  subst c_k. iLeft. iFrame. iIntros "AU !> (G & #pInfo & #cInfo)". wp_pures. clear dependent idx L.
  wp_bind (!_)%E.
  iInv "cInfo" as (lv) "(c↦ & node & G)".
  iDestruct (harris_node_destruct_agree with "c↪□ node") as (c_on c_t) "(>% & c.n↪rcu & >[[% c.n↪]|[% #c.n↪□]])"; subst lv c_t; last first.
  all: wp_apply (wp_load_offset with "c↦") as "c↦"; [done|].
  { (* tagged, retry delete *)
    iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu [$c.n↪□]") as "$"; [by iRight|].
    wp_pures. wp_apply ("IH" with "AU G").
  }
  iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu [c.n↪]") as "$"; [iLeft; by iFrame|].
  wp_pures.
  wp_bind (CmpXchg _ _ _)%E.
  iInv "cInfo" as (lv) "(c↦ & node & G)".
  iDestruct (harris_node_destruct_agree with "c↪□ node") as (c_on' c_t) "(>% & c.n↪rcu & >[[% c.n↪]|[% #c.n↪□]])"; subst lv c_t; last first.
  { (* tagged, CAS must fail *)
    wp_apply (wp_cmpxchg_fail_offset with "c↦") as "c↦"; [done..|simpl;auto|].
    iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu [$c.n↪□]") as "$"; [by iRight|].
    wp_pures. wp_apply ("IH" with "AU G").
  }
  (* Check if next changed. *)
  destruct (decide (fst <$> c_on = fst <$> c_on')) as [EQ|NE]; last first.
  { (* next changed, CAS must fail. *)
    wp_apply (wp_cmpxchg_fail_offset with "c↦") as "c↦"; [done|simpl;naive_solver..|].
    iModIntro. iDestruct (harris_node_combine_on with "c↦ c↪□ c.n↪rcu [c.n↪]") as "$"; [iLeft; by iFrame|].
    wp_pures. wp_apply ("IH" with "AU G").
  }
  (* next same, CAS succeed and commit. *)
  iInv "IsHarris" as (p_all p_tag L) "(>Linv & >●p_all & >●p_tag & >PTRS & Nodes & >(%HL & %HLh & %HLt & %Hdom))".
  iDestruct (ghost_map_lookup with "●p_all c↪□") as %Hptrs_c.
  iDestruct (get_persistent_AllPtrs with "PTRS") as "#[c.n|%HLc]"; [exact Hptrs_c| |].
  { (* curr tagged, impossible *)
    iDestruct "c.n" as (γ_c_n c_n c_n_k) "[c.n↪□ c_n↪□]".
    iDestruct (ghost_map_elem_agree with "c.n↪□ c.n↪") as %[= ?].
  }
  wp_apply (wp_cmpxchg_suc_offset with "c↦") as "c↦"; [done|rewrite EQ;auto|simpl;auto..|]. simpl in *.
  apply elem_of_list_lookup in HLc as [idx_c HLc].
  iDestruct (Nodes_remove with "Nodes") as (? c_p) "[(cM & _ & c.n↪' & %HLc_n & %HLc_p) Nodes]"; [exact HLc|]; simpl.
  iDestruct (ghost_map_elem_agree with "c.n↪ c.n↪'") as %[= <-].
  destruct (next_not_tail_is_Some idx_c L (FinInt k) false (c,i_c) c_on') as [[c_n i_c_n] [= ->]]; [naive_solver..|].
  destruct c_on as [[? ?]|]; [|inversion EQ]. injection EQ as [= ->]; simpl in *.
  iCombine "c.n↪ c.n↪'" as "c.n↪".
  iMod ((ghost_map_update (Some (c_n,i_c_n), true)) with "●p_tag c.n↪") as "[●p_tag c.n↪]".
  iMod (ghost_map_elem_persist with "c.n↪") as "#c.n↪□".
  set (L' := <[idx_c := (FinInt k, true, (c,i_c))]> L).
  iMod "AU" as (?) "[[Labs %HLabs] [_ Commit]]".
  iDestruct (ghost_var_agree with "Labs Linv") as %[= ->].
  iMod (ghost_var_update_halves (get_abs_state L') with "Labs Linv") as "[Labs Linv]".
  assert (Sorted_inf_Z L'.*1.*1).
  { rewrite !list_fmap_insert /= list_insert_id; [done|]. by get_first HLc. }
  assert (idx_c < length L) as idx_c_LT; [by apply lookup_lt_Some in HLc|].
  iMod ("Commit" $! true with "[$Labs]") as "HΦ".
  { iPureIntro. split.
    - by apply sorted_inf_Z_get_abs_state_sorted.
    - by apply (prove_delete_succ_post (c,i_c) idx_c L k).
  }
  apply list_lookup_fmap_Some in HLc_n as [[[c_n_k b] ?] [HLc_n [= <-]]].
  iDestruct (get_persistent_Nodes_rm_idx with "Nodes") as (??) "#(c_n↪ & _)"; [exact HLc_n|lia|].
  iModIntro. iSplitL "Linv ●p_all ●p_tag PTRS Nodes cM".
  { iNext. repeat iExists _. iFrame "Linv ●p_tag ∗#%".
    iSplitL "PTRS"; [|iSplit].
    - unfold AllPtrs. repeat (rewrite (big_sepM_delete _ p_all); [|exact Hptrs_c]).
      iDestruct "PTRS" as "[c PTRS]". iSplitL "c".
      + iDestruct "c" as "[#$|%HLc']". iLeft.
        repeat iExists _. iFrame "#".
      + iApply (big_sepM_mono with "PTRS"). iIntros (i_l' [z' l'] Hl') "l'".
        iDestruct "l'" as "[$|%HLl']".
        iRight. iPureIntro. subst L'. rewrite insert_take_drop; [|done].
        rewrite -(take_drop idx_c L) elem_of_app in HLl'.
        apply elem_of_app. destruct HLl' as [HLl'|HLl'].
        * by left.
        * right. apply elem_of_cons. right.
          rewrite (drop_S L (FinInt k, false, (c,i_c))) in HLl'; [|done].
          apply elem_of_cons in HLl' as [[= -> -> ->]|?]; [|done].
          by rewrite lookup_delete in Hl'.
    - unfold Nodes.
      rewrite (big_sepL_delete _ L' idx_c); last first.
      { subst L'. rewrite list_lookup_insert; done. }
      iSplitR "Nodes".
      { unfold ListNode. iExists (Some (c_n,i_c_n)),c_p. iFrame "∗#". iPureIntro.
        subst L'. rewrite list_fmap_insert /= list_lookup_insert_ne; [|lia].
        split.
        - get_third HLc_n. auto.
        - destruct c_p as [[??]|]; simpl in *; [|lia]. destruct HLc_p as [? HLc_p].
          split; [lia|]. rewrite list_lookup_insert_ne; [done|lia].
      }
      subst L'. rewrite {2}insert_take_drop; [|done].
      unfold Nodes_rm_idx.
      iEval (rewrite -{2}(take_drop_middle L idx_c (FinInt k,false,(c,i_c))); [|done]) in "Nodes".
      rewrite !big_sepL_app /=.
      iDestruct "Nodes" as "(NodesTake & _ & NodesDrop)".
      iSplitL "NodesTake"; [|iSplitR].
      + iApply (big_sepL_mono with "NodesTake").
        iIntros (i' [[z' b'] [γp' p']] Hi') "p'".
        apply lookup_take_Some in Hi' as [Hi' LT_i'].
        repeat case_decide; try lia.
        iDestruct "p'" as (on op) "(p'M & $ & p'.n↦ & %HLp'_n & %HLp'_p)".
        iExists on,op. iFrame. iPureIntro. rewrite list_fmap_insert /=.
        destruct (decide (idx_c = i' + 1)) as [->|NE].
        { get_third HLc. simplify_list_eq. split.
          - rewrite list_lookup_insert; [done|]. rewrite fmap_length. done.
          - destruct op as [[??]|]; simpl in *; [|done]. destruct HLp'_p as [? HLp'_p].
            split; [done|]. rewrite list_lookup_insert_ne; [done|lia].
        }
        split.
        * rewrite list_lookup_insert_ne; [done|lia].
        * destruct op as [[??]|]; simpl in *; [|done]. destruct HLp'_p as [? HLp'_p].
          split; [done|]. rewrite list_lookup_insert_ne; [done|lia].
      + rewrite take_length_le; last first.
        { apply lookup_lt_Some in HLc. lia. }
        case_decide; naive_solver.
      + iApply (big_sepL_mono with "NodesDrop").
        iIntros (i' [[z' b'] [γp' p']] Hi') "p'".
        rewrite take_length_le; [|lia]. case_decide; [lia|].
        iDestruct "p'" as (on op) "(p'M & $ & p'.n↦ & %HLp'_n & %HLp'_p)".
        iExists on,op. iFrame. iPureIntro.
        rewrite list_fmap_insert /= list_lookup_insert_ne; [|lia]. split; [done|].
        destruct op as [[??]|]; simpl in *; [|done]. destruct HLp'_p as [? HLp'_p].
        split; [done|].
        destruct (decide (i' = 0)) as [->|NE].
        { rewrite Nat.add_1_r Nat.sub_1_r /= list_lookup_insert; [|rewrite fmap_length; lia].
          get_third HLc. rewrite -HLp'_p -HLc. f_equal. lia.
        }
        rewrite list_lookup_insert_ne; [done|lia].
    - iPureIntro. subst L'. split_and!; [done|..].
      + rewrite list_lookup_insert_ne; [done|]. intros ->. naive_solver.
      + destruct HLt as [t HLt]. exists t. rewrite insert_length.
        rewrite list_lookup_insert_ne; [done|]. intros ->. naive_solver.
      + rewrite dom_insert_lookup_L; [done|].
        rewrite -elem_of_dom -Hdom elem_of_dom. eauto.
  }
  iModIntro. iDestruct (harris_node_combine_some with "c↦ c↪□ c.n↪rcu [$c.n↪□]") as "$"; [by iRight|].
  wp_pures.
  wp_apply (harris_helping_cas_spec false Φ 1%positive [] with "[$G $Lc]") as ([]) "(G & D)"; simpl in *; [done|exact Hp_k|iFrame "#"|..]; wp_pures.

  1: wp_apply (rcu.(rcu_domain_retire_spec) with "IRD D") as "_"; [solve_ndisj|by rewrite harris_type_unfold|].
  all: wp_pures; wp_apply (rcu.(guard_deactivate_spec) with "IRD G") as "G"; [solve_ndisj|]; wp_pures.
  all: by iApply "HΦ".
Qed.

(* Ordered set definition *)
Definition HSet (γs : gname) (abs_S : gset Z) : iProp :=
  ∃ (γp_a γp_t γl : gname) abs_L, ⌜γs = encode (γp_a, γp_t, γl)⌝ ∗
    ⌜abs_S = harris_list_into_set abs_L⌝ ∗ HList γl abs_L.

Global Instance HSet_timeless γs abs_S : Timeless (HSet γs abs_S).
Proof. apply _. Qed.

Definition IsHSet (γr : gname) (γs : gname) (l : loc) : iProp :=
  ∃ (γp_a γp_t γl : gname), ⌜γs = encode (γp_a, γp_t, γl)⌝ ∗
    IsHList γp_a γp_t γl γr l.

Global Instance IsHSet_persistent γr γs l : Persistent (IsHSet γr γs l).
Proof. apply _. Qed.

Lemma hset_new_spec :
  ordset_new_spec' listN rcuN harris_new rcu HSet IsHSet.
Proof.
  iIntros (γr d Φ) "!> #IRD HΦ".
  wp_apply (harris_new_spec with "IRD") as (l γp_a γp_t γl) "[#IsHarris Harris]"; [solve_ndisj|].

  remember (encode (γp_a, γp_t, γl)) as γs eqn:Hγs.
  iApply "HΦ".
  iSplit.
  all: repeat iExists _; iFrame (Hγs) "∗#"; done.
Qed.

Lemma hset_lookup_spec :
  ordset_lookup_spec' listN rcuN (harris_lookup harris_find rcu) rcu HSet IsHSet.
Proof.
  iIntros (?????) "#IsHarris G".
  iDestruct "IsHarris" as (??? Hγs) "#IsHarris".
  iIntros (Φ) "AU".

  awp_apply (harris_lookup_spec with "IsHarris G"); [naive_solver|].
  iApply (aacc_aupd with "AU"); [done|]. iIntros (abs_S) "Harris".
  iDestruct "Harris" as (????? Habs_S) "Harris". encode_agree Hγs.

  iAaccIntro with "Harris".
  { iIntros "Harris !>". iSplitL "Harris".
    { repeat iExists _. iFrame (Hγs) "∗%". }
    eauto with iFrame.
  }

  iIntros (b) "[Harris %Habs_L] !>".

  iRight. iExists b. iSplitL "Harris"; last first.
  { iIntros "$ !>". done. }
  iSplit.
  { repeat iExists _. iFrame (Hγs) "∗". done. }
  iPureIntro. subst abs_S.
  eapply lookup_list_post_to_set_post; done.
Qed.

Lemma hset_insert_spec :
  ordset_insert_spec' listN rcuN (harris_insert harris_find rcu) rcu HSet IsHSet.
Proof.
  iIntros (?????) "#IsHarris G".
  iDestruct "IsHarris" as (??? Hγs) "#IsHarris".
  iIntros (Φ) "AU".

  awp_apply (harris_insert_spec with "IsHarris G"); [solve_ndisj|].
  iApply (aacc_aupd with "AU"); [done|]. iIntros (abs_S) "Harris".
  iDestruct "Harris" as (????? Habs_S) "Harris". encode_agree Hγs.

  iAaccIntro with "Harris".
  { iIntros "Harris !>". iSplitL "Harris".
    { repeat iExists _. iFrame (Hγs) "∗%". }
    eauto with iFrame.
  }

  iIntros (b abs_L') "[Harris %Habs_L] !>".

  iRight. iExists b,_. iSplitL "Harris"; last first.
  { iIntros "$ !>". done. }
  iSplit.
  { repeat iExists _. iFrame (Hγs) "∗". done. }
  iPureIntro. subst abs_S.
  eapply insert_list_post_to_set_post. done.
Qed.

Lemma hset_delete_spec :
  ordset_delete_spec' listN rcuN (harris_delete harris_find rcu) rcu HSet IsHSet.
Proof.
  iIntros (?????) "#IsHarris G".
  iDestruct "IsHarris" as (??? Hγs) "#IsHarris".
  iIntros (Φ) "AU".

  awp_apply (harris_delete_spec with "IsHarris G"); [solve_ndisj|].
  iApply (aacc_aupd with "AU"); [done|]. iIntros (abs_S) "Harris".
  iDestruct "Harris" as (????? Habs_S) "Harris". encode_agree Hγs.
  iDestruct (HList_sorted with "Harris") as %HLSort.

  iAaccIntro with "Harris".
  { iIntros "Harris !>". iSplitL "Harris".
    { repeat iExists _. iFrame (Hγs) "∗%". }
    eauto with iFrame.
  }

  iIntros (b abs_L') "[Harris %Habs_L] !>".

  iRight. iExists b,_. iSplitL "Harris"; last first.
  { iIntros "$ !>". done. }
  iSplit.
  { repeat iExists _. iFrame (Hγs) "∗". done. }
  iPureIntro. subst abs_S.
  eapply delete_list_post_to_set_post; done.
Qed.

#[export] Typeclasses Opaque HSet IsHSet.

End proof.
