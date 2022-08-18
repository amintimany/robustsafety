From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris.base_logic Require Export invariants.
From iris.algebra Require Import auth frac agree gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export gen_heap.
From RobustSafety Require Export lang.
From iris.prelude Require Import options.

(** The CMRA for the heap of the implementation. This is linked to the
    physical heap. *)
Class heapIG Σ := HeapIG {
  heapI_invG : invGS Σ;
  heapI_gen_heapG :> gen_heapGS loc val Σ;
}.

Global Instance heapIG_irisG `{heapIG Σ} : irisGS LambdaRS_lang Σ := {
  iris_invGS := heapI_invG;
  num_laters_per_step _ := 0;
  state_interp σ  _ _ _ := (gen_heap_interp (Heap σ) ∗ ⌜Failure σ = false⌝)%I;
  fork_post _ := True%I;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

Notation "l ↦{ dq } v" := (mapsto (L:=loc) (V:=val) l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (mapsto (L:=loc) (V:=val) l DfracDiscarded v)
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (mapsto (L:=loc) (V:=val) l (DfracOwn q) v)
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (mapsto (L:=loc) (V:=val) l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Section lang_rules.
  Context `{heapIG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v w : val.

  Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : _ = of_val ?v |- _ =>
     is_var v; destruct v; first[discriminate H|injection H as H]
  | H : head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

  Local Hint Extern 0 (atomic _) => solve_atomic : core.
  Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.

  Local Hint Constructors head_step : core.
  Local Hint Resolve alloc_fresh : core.
  Local Hint Resolve to_of_val : core.

  (** Base axioms for core primitives of the language: Stateful reductions. *)
  Lemma wp_alloc E e v :
    IntoVal e v →
    {{{ True }}} Alloc e @ E {{{ l, RET (LocV l); l ↦ v }}}.
  Proof.
    iIntros (<- Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ????) "[Hh Hfl] !>"; iSplit; first by auto.
    iNext; iIntros (v2 σ2 efs Hstep) "_"; inv_head_step.
    iMod (@gen_heap_alloc with "Hh") as "(Hh & Hl & _)"; first done.
    iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_load E l dq v :
    {{{ ▷ l ↦{dq} v }}} Load (Loc l) @ E {{{ RET v; l ↦{dq} v }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ????) "[Hh Hfl] !>". iDestruct (@gen_heap_valid with "Hh Hl") as %?.
    iSplit; first by eauto.
    iNext; iIntros (v2 σ2 efs Hstep) "_"; inv_head_step.
    iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_store E l v' e v :
    IntoVal e v →
    {{{ ▷ l ↦ v' }}} Store (Loc l) e @ E
    {{{ RET UnitV; l ↦ v }}}.
  Proof.
    iIntros (<- Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ????) "[Hh Hfl] !>". iDestruct (@gen_heap_valid with "Hh Hl") as %?.
    iSplit; first by eauto. iNext; iIntros (v2 σ2 efs Hstep) "_"; inv_head_step.
    iMod (@gen_heap_update with "Hh Hl") as "[$ Hl]".
    iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_cas_fail E l dq v' e1 v1 e2 v2 :
    IntoVal e1 v1 → IntoVal e2 v2 → v' ≠ v1 →
    {{{ ▷ l ↦{dq} v' }}} CAS (Loc l) e1 e2 @ E
    {{{ RET (BoolV false); l ↦{dq} v' }}}.
  Proof.
    iIntros (<- <- ? Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ????) "[Hh Hfl] !>". iDestruct (@gen_heap_valid with "Hh Hl") as %?.
    iSplit; first by eauto.
    iNext; iIntros (v2' σ2 efs Hstep) "_"; inv_head_step.
    iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_cas_suc E l e1 v1 e2 v2 :
    IntoVal e1 v1 → IntoVal e2 v2 →
    {{{ ▷ l ↦ v1 }}} CAS (Loc l) e1 e2 @ E
    {{{ RET (BoolV true); l ↦ v2 }}}.
  Proof.
    iIntros (<- <- Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ????) "[Hh Hfl] !>". iDestruct (@gen_heap_valid with "Hh Hl") as %?.
    iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep) "_"; inv_head_step.
    iMod (@gen_heap_update with "Hh Hl") as "[$ Hl]".
    iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_FAA E l m e2 k :
    IntoVal e2 (#nv k) →
    {{{ ▷ l ↦ (#nv m) }}} FAA (Loc l) e2 @ E
    {{{ RET (#nv m); l ↦ #nv (m + k) }}}.
  Proof.
    iIntros (<- Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ????) "[Hh Hfl] !>". iDestruct (@gen_heap_valid with "Hh Hl") as %?.
    iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep) "_"; inv_head_step.
    iMod (@gen_heap_update with "Hh Hl") as "[$ Hl]".
    iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_fork E s e Φ :
    ▷ (|={E}=> Φ UnitV) ∗ ▷ WP e @ s; ⊤ {{ _, True }} ⊢ WP Fork e @ s; E {{ Φ }}.
  Proof.
    iIntros "[He HΦ]". iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1 ????) "Hσ !>"; iSplit; first by eauto.
    iNext; iIntros (v2 σ2 efs Hstep) "_"; inv_head_step. by iFrame.
  Qed.

  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
  Local Ltac solve_pure_exec :=
    unfold IntoVal in *;
    repeat match goal with H : AsVal _ |- _ => destruct H as [??] end; subst;
    intros ?; apply nsteps_once, pure_head_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].

  Global Instance pure_rec e1 e2 `{!AsVal e2} :
    PureExec True 1 (App (Rec e1) e2) e1.[(Rec e1), e2 /].
  Proof. solve_pure_exec. Qed.

  Global Instance pure_lam e1 e2 `{!AsVal e2} :
    PureExec True 1 (App (Lam e1) e2) e1.[e2 /].
  Proof. solve_pure_exec. Qed.

  Global Instance pure_LetIn e1 e2 `{!AsVal e1} :
    PureExec True 1 (LetIn e1 e2) e2.[e1 /].
  Proof. solve_pure_exec. Qed.

  Global Instance pure_seq e1 e2 `{!AsVal e1} :
    PureExec True 1 (Seq e1 e2) e2.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_fst e1 e2 `{!AsVal e1, !AsVal e2} :
    PureExec True 1 (Fst (Pair e1 e2)) e1.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_snd e1 e2 `{!AsVal e1, !AsVal e2} :
    PureExec True 1 (Snd (Pair e1 e2)) e2.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inl e0 e1 e2 `{!AsVal e0}:
    PureExec True 1 (Case (InjL e0) e1 e2) e1.[e0/].
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inr e0 e1 e2 `{!AsVal e0}:
    PureExec True 1 (Case (InjR e0) e1 e2) e2.[e0/].
  Proof. solve_pure_exec. Qed.

  Global Instance pure_if_true e1 e2 :
    PureExec True 1 (If (#♭ true) e1 e2) e1.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_if_false e1 e2 :
    PureExec True 1 (If (#♭ false) e1 e2) e2.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_nat_binop op a b :
    PureExec True 1 (BinOp op (#n a) (#n b)) (of_val (binop_eval op a b)).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_assert_true :
    PureExec True 1 (Assert (#♭ true)) Unit.
  Proof. solve_pure_exec. Qed.


  (* stuck rules *)

  Lemma var_stuck x Φ : ⊢ WP Var x ? {{v, Φ v}}.
  Proof.
    iApply wp_lift_pure_head_stuck; [done| |by split; [done|inversion 1]].
    intros K ?; destruct K as [|[]] using rev_ind; simpl; try rewrite fill_app; inversion 1; done.
  Qed.

  Lemma binop_stuck op v1 v2 Φ :
    non_nat_val v1 ∨ non_nat_val v2 →
    ⊢ WP BinOp op (of_val v1) (of_val v2) ? {{v, Φ v}}.
  Proof.
    intros Hnn.
    iApply wp_lift_pure_head_stuck; [done| |].
    - intros K e';
        destruct K as [|[] ? _] using rev_ind; simpl; try rewrite fill_app; try by inversion 1.
      + inversion 1 as [[Heqop Heq]]; simplify_eq.
        assert (is_Some (to_val e')) as [? ?]; last by intros?; simplify_eq.
        eapply fill_val with K; rewrite /= -Heq to_of_val; eauto.
      + inversion 1 as [[Heqop Heqv1 Heq]]; simplify_eq.
        assert (is_Some (to_val e')) as [? ?]; last by intros?; simplify_eq.
        eapply fill_val with K; rewrite /= -Heq to_of_val; eauto.
    - split; first done.
      inversion 1; simplify_eq; destruct v1; destruct v2;
        simplify_eq/=; destruct Hnn as [Hnn|Hnn]; inversion Hnn.
  Qed.

  Lemma fst_stuck v Φ : non_pair_val v → ⊢ WP Fst (of_val v) ? {{w, Φ w}}.
  Proof.
    intros Hnp.
    iApply wp_lift_pure_head_stuck; [done| |].
    - intros K e';
        destruct K as [|[] ? _] using rev_ind; simpl; try rewrite fill_app; try by inversion 1.
      inversion 1 as [[Heq]]; simplify_eq.
      assert (is_Some (to_val e')) as [? ?]; last by intros?; simplify_eq.
      eapply fill_val with K; rewrite /= -Heq to_of_val; eauto.
    - split; first done.
      inversion 1; simplify_eq; destruct v; simplify_eq/=; inversion Hnp.
  Qed.

  Lemma snd_stuck v Φ : non_pair_val v → ⊢ WP Snd (of_val v) ? {{w, Φ w}}.
  Proof.
    intros Hnp.
    iApply wp_lift_pure_head_stuck; [done| |].
    - intros K e';
        destruct K as [|[] ? _] using rev_ind; simpl; try rewrite fill_app; try by inversion 1.
      inversion 1 as [[Heq]]; simplify_eq.
      assert (is_Some (to_val e')) as [? ?]; last by intros?; simplify_eq.
      eapply fill_val with K; rewrite /= -Heq to_of_val; eauto.
    - split; first done.
      inversion 1; simplify_eq; destruct v; simplify_eq/=; inversion Hnp.
  Qed.

  Lemma case_stuck v e1 e2 Φ : non_sum_val v → ⊢ WP Case (of_val v) e1 e2 ? {{w, Φ w}}.
  Proof.
    intros Hns.
    iApply wp_lift_pure_head_stuck; [done| |].
    - intros K e';
        destruct K as [|[] ? _] using rev_ind; simpl; try rewrite fill_app; try by inversion 1.
      inversion 1 as [[Heq]]; simplify_eq.
      assert (is_Some (to_val e')) as [? ?]; last by intros?; simplify_eq.
      eapply fill_val with K; rewrite /= -Heq to_of_val; eauto.
    - split; first done.
      inversion 1; simplify_eq; destruct v; simplify_eq/=; inversion Hns.
  Qed.

  Lemma if_stuck v e1 e2 Φ : non_bool_val v → ⊢ WP If (of_val v) e1 e2 ? {{w, Φ w}}.
  Proof.
    intros Hnb.
    iApply wp_lift_pure_head_stuck; [done| |].
    - intros K e';
        destruct K as [|[] ? _] using rev_ind; simpl; try rewrite fill_app; try by inversion 1.
      inversion 1 as [[Heq]]; simplify_eq.
      assert (is_Some (to_val e')) as [? ?]; last by intros?; simplify_eq.
      eapply fill_val with K; rewrite /= -Heq to_of_val; eauto.
    - split; first done.
      inversion 1; simplify_eq; destruct v; simplify_eq/=; inversion Hnb.
  Qed.

  Lemma app_stuck v1 v2 Φ : non_fun_val v1 → ⊢ WP App (of_val v1) (of_val v2) ? {{w, Φ w}}.
  Proof.
    intros Hnf.
    iApply wp_lift_pure_head_stuck; [done| |].
    - intros K e';
        destruct K as [|[] ? _] using rev_ind; simpl; try rewrite fill_app; try by inversion 1.
      + inversion 1 as [[Heq]]; simplify_eq.
        assert (is_Some (to_val e')) as [? ?]; last by intros?; simplify_eq.
        eapply fill_val with K; rewrite /= -Heq to_of_val; eauto.
      + inversion 1 as [[z Heq]]; simplify_eq.
        assert (is_Some (to_val e')) as [? ?]; last by intros?; simplify_eq.
        eapply fill_val with K; rewrite /= -Heq to_of_val; eauto.
    - split; first done.
      inversion 1; simplify_eq; destruct v1; simplify_eq/=; inversion Hnf.
  Qed.

  Lemma load_stuck v Φ : non_loc_val v → ⊢ WP Load (of_val v) ? {{w, Φ w}}.
  Proof.
    intros Hnl.
    iApply wp_lift_pure_head_stuck; [done| |].
    - intros K e';
        destruct K as [|[] ? _] using rev_ind; simpl; try rewrite fill_app; try by inversion 1.
      inversion 1 as [[Heq]]; simplify_eq.
      assert (is_Some (to_val e')) as [? ?]; last by intros?; simplify_eq.
      eapply fill_val with K; rewrite /= -Heq to_of_val; eauto.
    - split; first done.
      inversion 1; simplify_eq; destruct v; simplify_eq/=; inversion Hnl.
  Qed.

  Lemma store_stuck v1 v2 Φ : non_loc_val v1 → ⊢ WP Store (of_val v1) (of_val v2) ? {{w, Φ w}}.
  Proof.
    intros Hnl.
    iApply wp_lift_pure_head_stuck; [done| |].
    - intros K e';
        destruct K as [|[] ? _] using rev_ind; simpl; try rewrite fill_app; try by inversion 1.
      + inversion 1 as [[Heq]]; simplify_eq.
        assert (is_Some (to_val e')) as [? ?]; last by intros?; simplify_eq.
        eapply fill_val with K; rewrite /= -Heq to_of_val; eauto.
      + inversion 1 as [[z Heq]]; simplify_eq.
        assert (is_Some (to_val e')) as [? ?]; last by intros?; simplify_eq.
        eapply fill_val with K; rewrite /= -Heq to_of_val; eauto.
    - split; first done.
      inversion 1; simplify_eq; destruct v1; simplify_eq/=; inversion Hnl.
  Qed.

  Lemma cas_stuck v1 v2 v3 Φ :
    non_loc_val v1 → ⊢ WP CAS (of_val v1) (of_val v2) (of_val v3) ? {{w, Φ w}}.
  Proof.
    intros Hnl.
    iApply wp_lift_pure_head_stuck; [done| |].
    - intros K e';
        destruct K as [|[] ? _] using rev_ind; simpl; try rewrite fill_app; try by inversion 1.
      + inversion 1 as [[Heq]]; simplify_eq.
        assert (is_Some (to_val e')) as [? ?]; last by intros?; simplify_eq.
        eapply fill_val with K; rewrite /= -Heq to_of_val; eauto.
      + inversion 1 as [[z Heq]]; simplify_eq.
        assert (is_Some (to_val e')) as [? ?]; last by intros?; simplify_eq.
        eapply fill_val with K; rewrite /= -Heq to_of_val; eauto.
      + inversion 1 as [[z1 z2 Heq]]; simplify_eq.
        assert (is_Some (to_val e')) as [? ?]; last by intros?; simplify_eq.
        eapply fill_val with K; rewrite /= -Heq to_of_val; eauto.
    - split; first done.
      inversion 1; simplify_eq; destruct v1; simplify_eq/=; inversion Hnl.
  Qed.

  Lemma faa_stuck_non_loc_or_non_nat v1 v2 Φ :
    non_loc_val v1 ∨ non_nat_val v2 → ⊢ WP FAA (of_val v1) (of_val v2) ? {{w, Φ w}}.
  Proof.
    intros Hnln.
    iApply wp_lift_pure_head_stuck; [done| |].
    - intros K e';
        destruct K as [|[] ? _] using rev_ind; simpl; try rewrite fill_app; try by inversion 1.
      + inversion 1 as [[Heq]]; simplify_eq.
        assert (is_Some (to_val e')) as [? ?]; last by intros?; simplify_eq.
        eapply fill_val with K; rewrite /= -Heq to_of_val; eauto.
      + inversion 1 as [[z Heq]]; simplify_eq.
        assert (is_Some (to_val e')) as [? ?]; last by intros?; simplify_eq.
        eapply fill_val with K; rewrite /= -Heq to_of_val; eauto.
    - split; first done.
      inversion 1; simplify_eq; destruct v1; destruct v2;
        simplify_eq/=; destruct Hnln as [Hnln|Hnln]; inversion Hnln;
        simplify_eq/=;
          repeat match goal with
            HX : context [to_val (of_val _)] |- _ => rewrite to_of_val /= in HX
          end; simplify_eq.
  Qed.

  Lemma faa_stuck_non_nat_loc E l n v Φ :
    non_nat_val v → l ↦ v ⊢ WP FAA (Loc l) (#n n) @ E ? {{w, Φ w}}.
  Proof.
    iIntros (Hnn) "Hl".
    iApply wp_lift_head_stuck; [done| |].
    - intros K e';
        destruct K as [|[] ? _] using rev_ind; simpl; try rewrite fill_app; try by inversion 1.
      + inversion 1 as [[Heq]]; simplify_eq.
        destruct K as [|[] ? _] using rev_ind; rewrite ?fill_app in Heq; simplify_eq/=; done.
      + inversion 1 as [[z Heq]]; simplify_eq.
        destruct K as [|[] ? _] using rev_ind; rewrite ?fill_app in Heq; simplify_eq/=; done.
    - iIntros (σ ns κs nt) "[Hh Hfl]".
      iMod ((fupd_mask_weaken ∅ (P := True)) with "[]") as "_";
        [set_solver|by iIntros "?"; iModIntro|].
      iModIntro.
      iDestruct (@gen_heap_valid with "Hh Hl") as %?.
      iPureIntro.
      split; first done.
      inversion 1; simplify_eq/=; inversion Hnn.
  Qed.

End lang_rules.
