From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat ghost_map invariants mono_nat.
From iris.program_logic Require Export total_adequacy.
From smr.lang Require Export adequacy.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

Definition heap_total Σ `{!heapGpreS Σ} s e σ φ :
  (∀ `{!heapGS_gen HasNoLc Σ}, ⊢ inv_heap_inv -∗ WP e @ s; ⊤ [{ v, ⌜φ v⌝ }]) →
  sn erased_step ([e], σ).
Proof.
  intros Hwp; eapply (twp_total _ _); iIntros (?) "".

  iMod (ghost_map_alloc σ.(heap)) as (vγ) "[Hvγ ?]".
  iMod (own_alloc (● (to_inv_heap ∅))) as (iγ) "H●".
  { rewrite auth_auth_valid. exact: to_inv_heap_valid. }
  iMod (own_alloc (● (∅ : heap_freeableUR))) as (fγ) "Hfγ";
    first by apply auth_auth_valid.
  iMod (proph_map_init [] σ.(used_proph_id)) as (?) "Hp".
  iMod (mono_nat_own_alloc 0) as (nγ) "[Hsteps _]".
  set (Hheap := HeapGS _ _ _ vγ _ iγ _ fγ _ _ nγ _).
  iAssert (inv_heap_inv_P (gG:=Hheap)) with "[H●]" as "P".
  { iExists _. iFrame. done. }
  iMod (inv_alloc inv_heapN ⊤ inv_heap_inv_P with "P") as "Hi".
  iDestruct (Hwp Hheap with "Hi") as "Hwp".
  iModIntro.
  iExists (λ σ ns κs nt, (heap_ctx σ.(heap) ∗
                          proph_map_interp κs σ.(used_proph_id) ∗
                          mono_nat_auth_own nγ 1 ns))%I.
  iExists id, (λ _, True%I), _.
  iFrame. iExists ∅. by iFrame.
Qed.
