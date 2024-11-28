From stdpp Require Import namespaces.
From iris.bi Require Import telescopes.
From iris.bi.lib Require Export atomic.
From iris.proofmode Require Import proofmode classes environments.
From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Import invariants.
From iris.prelude Require Import options.

(* We need non-empty inner mask because SMR rules need their internal
invariant. (Similarly, iRC11 hardcodes inner mask to [↑histN].) To prove SMR
rules with tight masks (i.e. only SMR invariants), we need non-top "base" mask. *)
Definition atomic_wp `{!irisGS Λ Σ} {TA TB TP : tele}
  (e: expr Λ) (* expression *)
  (Eb E Ei : coPset) (* base mask, *implementation* mask, inner mask *)
  (α: TA → iProp Σ) (* atomic pre-condition *)
  (β: TA → TB → iProp Σ) (* atomic post-condition *)
  (POST: TA → TB → TP → option (iProp Σ))
  (f: TA → TB → TP → val Λ) (* Turn the return data into the return value *)
  : iProp Σ :=
    ∀ (Φ : val Λ → iProp Σ),
            (* The (outer) user mask is what is left after the implementation
            opened its things. *)
            atomic_update (Eb∖E) Ei α β (λ.. x y, ∀.. z, POST x y z -∗? Φ (f x y z)) -∗
            WP e @ Eb {{ Φ }}.

(* The way to read the [tele_app foo] here is that they convert the n-ary
function [foo] into a unary function taking a telescope as the argument. *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ Eb , E , Ei '<<{' ∃∃ y1 .. yn , β '|' z1 .. zn , 'RET' v ; POST '}>>'" :=
(* The way to read the [tele_app foo] here is that they convert the n-ary
function [foo] into a unary function taking a telescope as the argument. *)
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleS (λ z1, .. (TeleS (λ zn, TeleO)) .. ))
             e%E
             Eb E Ei
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn,
                                   tele_app $ λ z1, .. (λ zn, Some POST%I) ..
                                  ) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn,
                                   tele_app $ λ z1, .. (λ zn, v%V) ..
                                  ) ..
                        ) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, x1 binder, xn binder, y1 binder, yn binder, z1 binder, zn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  Eb , E , Ei  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' z1  ..  zn ,  RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* There are overall 16 of possible variants of this notation:
- with and without ∀∀ binders
- with and without ∃∃ binders
- with and without RET binders
- with and without POST

However we don't support the case where RET binders are present but anything
else is missing. Below we declare the 8 notations that involve no RET binders.
*)

(* No RET binders *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ Eb , E , Ei '<<{' ∃∃ y1 .. yn , β '|' 'RET' v ; POST '}>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             Eb E Ei
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app $ Some POST%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app $ v%V) ..
                        ) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  Eb , E , Ei  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No ∃∃ binders, no RET binders *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ Eb , E , Ei '<<{' β '|' 'RET' v ; POST '}>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             Eb E Ei
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ tele_app $ Some POST%I
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ tele_app $ v%V
                        ) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, x1 binder, xn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  Eb , E , Ei  '/' '<<{'  '[' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no RET binders *)
Notation "'<<{' α '}>>' e @ Eb , E , Ei '<<{' ∃∃ y1 .. yn , β '|' 'RET' v ; POST '}>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             Eb E Ei
             (tele_app $ α%I)
             (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app $ Some POST%I) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app $ v%V) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  Eb , E , Ei  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no ∃∃ binders, no RET binders *)
Notation "'<<{' α '}>>' e @ Eb , E , Ei '<<{' β '|' 'RET' v ; POST '}>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             Eb E Ei
             (tele_app $ α%I)
             (tele_app $ tele_app β%I)
             (tele_app $ tele_app $ tele_app $ Some POST%I)
             (tele_app $ tele_app $ tele_app $ v%V)
  )
  (at level 20, E, β, α, v, POST at level 200,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  Eb , E , Ei  '/' '<<{'  '[' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No RET binders, no POST *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ Eb , E , Ei '<<{' ∃∃ y1 .. yn , β '|' 'RET' v '}>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             Eb E Ei
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app None) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app v%V) ..
                        ) .. )
  )
  (at level 20, E, β, α, v at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  Eb , E , Ei  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(* No ∃∃ binders, no RET binders, no POST *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ Eb , E , Ei '<<{' β '|' 'RET' v '}>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             Eb E Ei
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
             (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app None) .. )
             (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app v%V) .. )
  )
  (at level 20, E, β, α, v at level 200, x1 binder, xn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  Eb , E , Ei  '/' '<<{'  '[' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no RET binders, no POST *)
Notation "'<<{' α '}>>' e @ Eb , E , Ei '<<{' ∃∃ y1 .. yn , β '|' 'RET' v '}>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             Eb E Ei
             (tele_app α%I)
             (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app None) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app v%V) .. )
  )
  (at level 20, E, β, α, v at level 200, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  Eb , E , Ei  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no ∃∃ binders, no RET binders, no POST *)
Notation "'<<{' α '}>>' e @ Eb , E , Ei '<<{' β '|' 'RET' v '}>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             Eb E Ei
             (tele_app α%I)
             (tele_app $ tele_app β%I)
             (tele_app $ tele_app $ tele_app None)
             (tele_app $ tele_app $ tele_app v%V)
  )
  (at level 20, E, β, α, v at level 200,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  Eb , E , Ei  '/' '<<{'  '[' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.


(** Theory *)
Section lemmas.
  Context `{!irisGS Λ Σ} {TA TB TP : tele}.
  Notation iProp := (iProp Σ).
  Implicit Types (α : TA → iProp) (β : TA → TB → iProp) (POST : TA → TB → TP → option iProp) (f : TA → TB → TP →  val Λ).

  (* Atomic triples imply sequential triples. *)
  Lemma atomic_wp_seq e Eb E Ei α β POST f :
    Ei ⊆ Eb ∖ E →
    atomic_wp e Eb E Ei α β POST f -∗
    ∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ WP e @ Eb {{ Φ }}.
  Proof.
    iIntros "% Hwp" (Φ x) "Hα HΦ".
    iApply (wp_frame_wand with "HΦ"). iApply "Hwp".
    iAuIntro. iAaccIntro with "Hα"; first by eauto. iIntros (y) "Hβ !>".
    (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
    rewrite ->!tele_app_bind. iIntros (z) "HPOST HΦ". iSpecialize ("HΦ" with "Hβ HPOST"). iApply "HΦ".
  Qed.

  (** This version matches the Texan triple, i.e., with a later in front of the
  [(∀.. y, β x y -∗ Φ (f x y))]. *)
  Lemma atomic_wp_seq_step e Eb E Ei α β POST f :
    Ei ⊆ Eb ∖ E →
    TCEq (to_val e) None →
    atomic_wp e Eb E Ei α β POST f -∗
    ∀ Φ, ∀.. x, α x -∗ ▷ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ WP e @ Eb {{ Φ }}.
  Proof.
    iIntros (??) "H"; iIntros (Φ x) "Hα HΦ".
    iApply (wp_step_fupd _ _ Eb _ (∀.. y : TB, _)
      with "[$HΦ //]"); first done.
    iApply (atomic_wp_seq with "H Hα"); [done..|].
    iIntros (y) "Hβ %z HPOST HΦ". iSpecialize ("HΦ" with "Hβ HPOST"). iApply "HΦ".
  Qed.

  (* Sequential triples with the inner mask for a physically atomic [e] are atomic. *)
  Lemma atomic_seq_wp_atomic e Eb E Ei α β POST f `{!Atomic WeaklyAtomic e} :
    Ei ⊆ Eb ∖ E →
    (∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ WP e @ Ei {{ Φ }}) -∗
    atomic_wp e Eb E Ei α β POST f.
  Proof.
    iIntros "% Hwp" (Φ) "AU". iMod "AU" as (x) "[Hα [_ Hclose]]".
    iApply wp_mask_mono; last iApply ("Hwp" with "Hα"); [solve_ndisj|]. iIntros (y) "Hβ %z HPOST".
    iMod ("Hclose" with "Hβ") as "HΦ".
    rewrite ->!tele_app_bind. by iApply "HΦ".
  Qed.

  (** Sequential triples with a persistent precondition and no initial quantifier
  are atomic. *)
  Lemma persistent_seq_wp_atomic e Eb E Ei (α : [tele] → iProp) (β : [tele] → TB → iProp)
        (POST : [tele] → TB → TP → option iProp) (f : [tele] → TB → TP → val Λ) {HP : Persistent (α [tele_arg])} :
    Ei ⊆ Eb ∖ E →
    (∀ Φ, α [tele_arg] -∗ (∀.. y, β [tele_arg] y -∗ ∀.. z, POST [tele_arg] y z -∗? Φ (f [tele_arg] y z)) -∗ WP e @ (Eb∖E) {{ Φ }}) -∗
    atomic_wp e Eb E Ei α β POST f.
  Proof.
    simpl in HP. iIntros "% Hwp" (Φ) "HΦ". iApply fupd_wp.
    iMod ("HΦ") as "[#Hα [Hclose _]]". iMod ("Hclose" with "Hα") as "HΦ".
    iApply wp_fupd. iApply wp_mask_mono; last iApply ("Hwp" with "Hα"); [solve_ndisj|]. iIntros "!>" (y) "Hβ %z HPOST".
    iMod ("HΦ") as "[_ [_ Hclose]]". iMod ("Hclose" with "Hβ") as "HΦ".
    (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
    rewrite ->!tele_app_bind. by iApply "HΦ".
  Qed.

  Lemma atomic_wp_mask_weaken e Eb E1 E2 Ei α β POST f :
    E1 ⊆ E2 → atomic_wp e Eb E1 Ei α β POST f -∗ atomic_wp e Eb E2 Ei α β POST f.
  Proof.
    iIntros (HE) "Hwp". iIntros (Φ) "AU". iApply "Hwp".
    iApply atomic_update_mask_weaken; last done. set_solver.
  Qed.

  (** We can open invariants around atomic triples.
      (Just for demonstration purposes; we always use [iInv] in proofs.) *)
  Lemma atomic_wp_inv e Eb E Ei α β POST f N I :
    ↑N ⊆ Eb →
    ↑N ⊆ E →
    Ei ⊆ Eb ∖ E →
    atomic_wp e Eb (E ∖ ↑N) Ei (λ.. x, ▷ I ∗ α x) (λ.. x y, ▷ I ∗ β x y) POST f -∗
    inv N I -∗ atomic_wp e Eb E Ei α β POST f.
  Proof.
    intros ???. iIntros "Hwp #Hinv" (Φ) "AU". iApply "Hwp". iAuIntro.
    iInv N as "HI". iApply (aacc_aupd with "AU"); first solve_ndisj.
    iIntros (x) "Hα". iAaccIntro with "[HI Hα]"; rewrite ->!tele_app_bind; first by iFrame.
    - (* abort *)
      iIntros "[HI $]". by eauto with iFrame.
    - (* commit *)
      iIntros (y). rewrite ->!tele_app_bind. iIntros "[HI Hβ]". iRight.
      iExists y. rewrite ->!tele_app_bind. by eauto with iFrame.
  Qed.

End lemmas.
