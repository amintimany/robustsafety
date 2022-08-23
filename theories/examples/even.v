From iris.program_logic Require Import lifting adequacy.
From RobustSafety Require Import lang rules logrel fundamental.
From iris.proofmode Require Import tactics.

(* The program 'prog' below corresponds to the following program:

let l = ref(0) in
let add2 () = FAA(l, 2); () in
let read () =
  let r = !l in
  assert (r `rem` 2 = 0); r
in
(add2, read)
*)
Definition even_reference : expr :=
  LetIn
    (Alloc (#n 0))
    (Pair
       (Lam (Seq (FAA (Var 1) (#n 2)) Unit))
       (Lam (LetIn
               (Load (Var 1))
               (Seq (Assert (BinOp Eq (BinOp Rem (Var 0) (#n 2)) (#n 0))) (Var 0))))).

(* is this a Coq bug!? why is modulo unfolded by simpl? *)
Opaque Nat.modulo.

Section even.
  Context `{heapIG Σ}.

  Definition add2_spec (add2 : val) : iProp Σ :=
    ∀ v, {{{ True }}} App (of_val add2) (of_val v) {{{ RET UnitV; True }}}.

  Definition read_spec (read : val) : iProp Σ :=
    ∀ v, {{{ True }}} App (of_val read) (of_val v) {{{ n, RET (#nv n); ⌜(2 | n)⌝ }}}.

  Lemma wp_even_reference :
    {{{ True }}}
      even_reference
    {{{ add2 read, RET (PairV add2 read);
        interp add2 ∗ interp read ∗ add2_spec add2 ∗ read_spec read }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply (wp_bind (fill [LetInCtx _])).
    iApply wp_alloc; first done.
    iNext.
    iIntros (l) "Hl /=".
    iMod (inv_alloc (nroot .@ "even") _ (∃ n, l ↦ (#nv n) ∧ ⌜(2 | n)⌝)%I with "[Hl]") as "#Hinv".
    { iNext; iExists _; iFrame. iPureIntro. apply Nat.divide_0_r. }
    iApply wp_pure_step_later; first done.
    iNext; iIntros "_".
    asimpl.
    iApply wp_value.
    iApply "HΦ".
    set (add2V := LamV (Seq (FAA (Loc l) (#n 2)) Unit)).
    set (readV := (LamV (LetIn (Load (Loc l))
          (Seq (Assert (BinOp Eq (BinOp Rem (ids 0) (#n 2)) (#n 0))) (ids 0))))).
    iAssert (add2_spec add2V ∗ read_spec readV)%I as "#[Has Hrs]".
    { iSplit.
      - iIntros (v Ψ) "!# _ HΨ /=".
        iApply wp_pure_step_later; first done.
        iNext; iIntros "_".
        simpl.
        iApply (wp_bind (fill [SeqCtx _])).
        iInv (nroot .@ "even") as (n) ">[Hl %]" "Hclose".
        iApply (wp_FAA with "Hl").
        iIntros "!> Hl".
        iMod ("Hclose" with "[Hl]") as "_".
        { iNext; iExists _; iFrame. iPureIntro.
          apply Nat.divide_add_r; first done. apply Nat.divide_refl. }
        simpl.
        iModIntro.
        iApply wp_pure_step_later; first done.
        iNext; iIntros "_".
        iApply wp_value.
        by iApply "HΨ".
      - iIntros (v Ψ) "!# _ HΨ /=".
        iApply wp_pure_step_later; first done.
        iNext; iIntros "_".
        asimpl.
        iApply (wp_bind (fill [LetInCtx _])).
        asimpl.
        iInv (nroot .@ "even") as (n) ">[Hl %]" "Hclose".
        iApply (wp_load with "Hl").
        iIntros "!> Hl".
        iMod ("Hclose" with "[Hl]") as "_".
        { iNext; iExists _; iFrame; done. }
        simpl.
        iModIntro.
        iApply wp_pure_step_later; first done.
        iNext; iIntros "_".
        asimpl.
        iApply (wp_bind (fill [SeqCtx _])).
        iApply (wp_bind (fill [AssertCtx])).
        iApply (wp_bind (fill [BinOpLCtx _ _])).
        iApply wp_pure_step_later; first done.
        iNext; iIntros "_".
        iApply wp_value; simpl.
        iApply wp_pure_step_later; first done.
        iNext; iIntros "_".
        simpl.
        rewrite bool_decide_eq_true_2; last by rewrite Nat.mod_divide.
        iApply wp_value; simpl.
        iApply wp_pure_step_later; first done.
        iNext; iIntros "_".
        iApply wp_value; simpl.
        iApply wp_pure_step_later; first done.
        iNext; iIntros "_".
        iApply wp_value.
        iApply "HΨ"; done. }
    repeat iSplit; [| |done|done].
    - rewrite interp_unfold /=.
      iIntros "!#" (v) "_".
      iApply wp_stuck_weaken.
      iApply ("Has" $! v with "[] []"); [done|rewrite interp_unfold //=].
    - rewrite interp_unfold /=.
      iIntros "!#" (v) "_".
      iApply wp_stuck_weaken.
      iApply ("Hrs" $! v with "[] []"); [done|].
      iNext; iIntros (? ?); rewrite interp_unfold //=.
  Qed.

  Definition even_linked_with_adversary (e : expr) : expr :=
    LetIn
      even_reference
      (LetIn (Fst (Var 0))
         (LetIn (Snd (Var 1))
            (Seq e (App (Var 0) Unit)))).

  Lemma even_linked_with_adversary_spec e :
    valid_adversary e →
    {{{ True }}} even_linked_with_adversary e ? {{{ n, RET (#nv n); ⌜(2 | n)⌝ }}}.
  Proof.
    iIntros (Hvad Φ) "_ HΦ".
    iApply (wp_bind (fill [LetInCtx _])).
    iApply wp_stuck_weaken.
    iApply wp_even_reference; first done.
    iNext.
    iIntros (add2 read) "(#Hai & #Hri & #Has & #Hrs) /=".
    iApply wp_pure_step_later; first done.
    iNext; iIntros "_". asimpl.
    iApply (wp_bind (fill [LetInCtx _])).
    iApply wp_pure_step_later; first done.
    iNext; iIntros "_".
    iApply wp_value.
    asimpl.
    iApply wp_pure_step_later; first done.
    iNext; iIntros "_".
    asimpl.
    iApply (wp_bind (fill [LetInCtx _])).
    iApply wp_pure_step_later; first done.
    iNext; iIntros "_".
    iApply wp_value.
    asimpl.
    iApply wp_pure_step_later; first done.
    iNext; iIntros "_".
    asimpl.
    iApply (wp_bind (fill [SeqCtx _])).
    iApply wp_wand.
    { iApply (fundamental _ Hvad $! [read; add2; PairV add2 read] with "[]").
      rewrite !interp_env_cons.
      repeat iSplit; [done|done|by rewrite {3}interp_unfold /=; eauto 10|by iApply interp_env_nil]. }
    iIntros (v) "Hv /=".
    iApply wp_pure_step_later; first done.
    iNext; iIntros "_".
    iApply wp_stuck_weaken.
    iApply ("Hrs" $! UnitV); done.
  Qed.

End even.

Theorem even_robust_safety :
  ∀ e,
    valid_adversary e →
    ∀ n κs v t2 σ2,
      language.nsteps n ([(even_linked_with_adversary e)], {|Heap := ∅; Failure := false|})
        κs (of_val v :: t2, σ2) →
      Failure σ2 = false ∧ ∃ n, v = #nv n.
Proof.
  intros e He n κs v t2 σ2.
  eapply (wp_strong_adequacy heapΣ _).
  iIntros (Hinv).
  iMod (gen_heap_init (∅ : gmap loc val)) as (?) "(Hh&_&_)".
  set (HeapIG heapΣ _ _).
  iAssert (WP even_linked_with_adversary e ? {{v, ∃ n, ⌜v = (#nv n)⌝}})%I as "Hwp".
  { iApply (even_linked_with_adversary_spec with "[] []"); [done|done|by eauto]. }
  iModIntro.
  iExists _, [_]%I, _, _; simpl.
  iSplitL; last iSplitL; [|iSplitL; last done; iExact "Hwp" |].
  { by simpl; iFrame. }
  iIntros (es' t2' Hv Hes' _) "[Hh %] Hposts _ /=".
  iMod (fupd_mask_weaken ∅ (P := True) with "[]") as "_"; first done.
  { iIntros "?"; iModIntro; done. }
  iModIntro.
  destruct es' as [|ev []]; [done| |done]; simpl.
  iDestruct "Hposts" as "[Hposts _]".
  pose proof (f_equal head Hv); simpl in *; simplify_eq.
  rewrite to_of_val /=.
  iDestruct "Hposts" as (?) "->".
  by eauto.
Qed.
