From iris.base_logic Require Import invariants.
From iris.program_logic Require Import lifting ectx_lifting.
From iris.proofmode Require Import proofmode.
From RobustSafety Require Export logrel rules.
From iris.prelude Require Import options.

Section typed_interp.
  Context `{heapIG Σ}.
  Notation D := (persistent_predO val (iPropI Σ)).

  Lemma logrel_var x : ⊢ logrel (Var x).
  Proof.
    iIntros "!#" (vs) "Henv"; rewrite /interp_expr /=.
    destruct (vs !! x) eqn:Hvsx.
    - erewrite env_subst_lookup_some; last done.
      iApply wp_value.
      iApply interp_env_Some_l; done.
    - erewrite env_subst_lookup_none; last done.
      iApply var_stuck.
  Qed.

  Lemma logrel_unit : ⊢ logrel Unit.
  Proof. iIntros "!#" (vs) "Henv"; iApply wp_value; rewrite interp_unfold /=; done. Qed.

  Lemma logrel_nat n : ⊢ logrel (#n n).
  Proof. iIntros "!#" (vs) "Henv"; iApply wp_value; rewrite interp_unfold /=; done. Qed.

  Lemma logrel_bool b : ⊢ logrel (#♭ b).
  Proof. iIntros "!#" (vs) "Henv"; iApply wp_value; rewrite interp_unfold /=; done. Qed.

  Lemma interp_binop_eval op n1 n2 : ⊢ interp (binop_eval op n1 n2).
  Proof.
    rewrite interp_unfold; destruct op; simpl;
      try solve [done | by destruct Nat.eq_dec | by destruct Nat.lt_dec | by destruct Nat.le_dec].
  Qed.

  Lemma logrel_nat_binop op e1 e2 : logrel e1 -∗ logrel e2 -∗ logrel (BinOp op e1 e2).
  Proof.
    iIntros "#IH1 #IH2 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [BinOpLCtx _ _])).
    iApply wp_wand; first by iApply "IH1".
    iIntros (v1) "#Hv1 /=".
    iApply (wp_bind (fill [BinOpRCtx _ _])).
    iApply wp_wand; first by iApply "IH2".
    iIntros (v2) "#Hv2 /=".
    destruct (val_cases_nat v1) as [[? ->]|Hnn1].
    - destruct (val_cases_nat v2) as [[? ->]|Hnn2].
      + iApply wp_pure_step_later; first done.
        iNext; iIntros "_".
        iApply wp_value.
        iApply interp_binop_eval.
      + iApply binop_stuck; auto.
    - iApply binop_stuck; auto.
  Qed.

  Lemma logrel_pair e1 e2 : logrel e1 -∗ logrel e2 -∗ logrel (Pair e1 e2).
  Proof.
    iIntros "#IH1 #IH2 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [PairLCtx _])).
    iApply wp_wand; first by iApply "IH1".
    iIntros (v1) "#Hv1 /=".
    iApply (wp_bind (fill [PairRCtx _])).
    iApply wp_wand; first by iApply "IH2".
    iIntros (v2) "#Hv2 /=".
    iApply wp_value.
    rewrite {5}interp_unfold; simpl.
    eauto 6.
  Qed.

  Lemma logrel_fst e : logrel e -∗ logrel (Fst e).
  Proof.
    iIntros "#IH !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [FstCtx])).
    iApply wp_wand; first by iApply "IH".
    iIntros (v) "#Hv /=".
    destruct (val_cases_pair v) as [(? & ? & ->)|Hnp]; simpl.
    - rewrite {2}interp_unfold; simpl.
      iDestruct "Hv" as (? ?) "[>% [? ?]]"; simplify_eq.
      iApply wp_pure_step_later; first done.
      iNext; iIntros "_".
      by iApply wp_value.
    - iApply fst_stuck; done.
  Qed.

  Lemma logrel_snd e : logrel e -∗ logrel (Snd e).
  Proof.
    iIntros "#IH !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [SndCtx])).
    iApply wp_wand; first by iApply "IH".
    iIntros (v) "#Hv /=".
    destruct (val_cases_pair v) as [(? & ? & ->)|Hnp]; simpl.
    - rewrite {2}interp_unfold; simpl.
      iDestruct "Hv" as (? ?) "[>% [? ?]]"; simplify_eq.
      iApply wp_pure_step_later; first done.
      iNext; iIntros "_".
      by iApply wp_value.
    - iApply snd_stuck; done.
  Qed.

  Lemma logrel_injl e : logrel e -∗ logrel (InjL e).
  Proof.
    iIntros "#IH !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [InjLCtx])).
    iApply wp_wand; first by iApply "IH".
    iIntros (v) "#Hv /=".
    iApply wp_value.
    rewrite {3}interp_unfold; simpl.
    iLeft; eauto.
  Qed.

  Lemma logrel_injr e : logrel e -∗ logrel (InjR e).
  Proof.
    iIntros "#IH !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [InjRCtx])).
    iApply wp_wand; first by iApply "IH".
    iIntros (v) "#Hv /=".
    iApply wp_value.
    rewrite {3}interp_unfold; simpl.
    iRight; eauto.
  Qed.

  Lemma logrel_case e0 e1 e2 : logrel e0 -∗ logrel e1 -∗ logrel e2 -∗ logrel (Case e0 e1 e2).
  Proof.
    iIntros "#IH0 #IH1 #IH2 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [CaseCtx _ _])).
    iApply wp_wand; first by iApply "IH0".
    iIntros (v0) "#Hv0 /=".
    destruct (val_cases_sum v0) as [[[? ->]|[? ->]]|Hns].
    - rewrite {4}interp_unfold; simpl.
      iDestruct "Hv0" as "[Hv0|Hv0]"; iDestruct "Hv0" as (?) "[>% ?]"; [simplify_eq|done].
      iApply wp_pure_step_later; first done.
      iNext; iIntros "_".
      asimpl.
      iApply ("IH1" $! (_ :: _)); rewrite interp_env_cons; iFrame "#".
    - rewrite {4}interp_unfold; simpl.
      iDestruct "Hv0" as "[Hv0|Hv0]"; iDestruct "Hv0" as (?) "[>% ?]"; [done|simplify_eq].
      iApply wp_pure_step_later; first done.
      iNext; iIntros "_".
      asimpl.
      iApply ("IH2" $! (_ :: _)); rewrite interp_env_cons; iFrame "#".
    - iApply case_stuck; auto.
  Qed.

  Lemma logrel_if e0 e1 e2 : logrel e0 -∗ logrel e1 -∗ logrel e2 -∗ logrel (If e0 e1 e2).
  Proof.
    iIntros "#IH0 #IH1 #IH2 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [IfCtx _ _])).
    iApply wp_wand; first by iApply "IH0".
    iIntros (v0) "#Hv0 /=".
    destruct (val_cases_bool v0) as [[[] ->]|Hns].
    - iApply wp_pure_step_later; first done.
      iNext; iIntros "_".
      iApply "IH1"; done.
    - iApply wp_pure_step_later; first done.
      iNext; iIntros "_".
      iApply "IH2"; done.
    - iApply if_stuck; auto.
  Qed.

  Lemma logrel_rec e : logrel e -∗ logrel (Rec e).
  Proof.
    iIntros "#IH !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply wp_value.
    rewrite {2}interp_unfold; simpl.
    iModIntro.
    iLöb as "IHrec".
    iIntros (v) "#Hv".
    iApply wp_pure_step_later; first done.
    iNext; iIntros "_".
    asimpl.
    change (Rec _) with (of_val (RecV e.[upn 2 (env_subst vs)])) at 2.
    iApply ("IH" $! (_ :: _ :: vs)).
    rewrite ?interp_env_cons; iFrame "Hv Henv".
    rewrite {5}interp_unfold; simpl.
    iModIntro; done.
  Qed.

  Lemma logrel_lam e : logrel e -∗ logrel (Lam e).
  Proof.
    iIntros "#IH !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply wp_value.
    rewrite {2}interp_unfold; simpl.
    iModIntro.
    iIntros (v) "#Hv".
    iApply wp_pure_step_later; first done.
    iNext; iIntros "_".
    asimpl.
    iApply ("IH" $! (_ :: vs)).
    rewrite ?interp_env_cons; iFrame "#".
  Qed.

  Lemma logrel_letin e1 e2 : logrel e1 -∗ logrel e2 -∗ logrel (LetIn e1 e2).
  Proof.
    iIntros "#IH1 #IH2 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [LetInCtx _])).
    iApply wp_wand; first by iApply "IH1".
    iIntros (v) "#Hv /=".
    iApply wp_pure_step_later; first done.
    iNext; iIntros "_".
    asimpl.
    iApply ("IH2" $! (_ :: vs)).
    rewrite ?interp_env_cons; iFrame "#".
  Qed.

  Lemma logrel_seq e1 e2 : logrel e1 -∗ logrel e2 -∗ logrel (Seq e1 e2).
  Proof.
    iIntros "#IH1 #IH2 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [SeqCtx _])).
    iApply wp_wand; first by iApply "IH1".
    iIntros (v) "#Hv /=".
    iApply wp_pure_step_later; first done.
    iNext; iIntros "_".
    iApply "IH2"; done.
  Qed.

  Lemma logrel_app e1 e2 : logrel e1 -∗ logrel e2 -∗ logrel (App e1 e2).
  Proof.
    iIntros "#IH1 #IH2 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [AppLCtx _])).
    iApply wp_wand; first by iApply "IH1".
    iIntros (v1) "#Hv1 /=".
    iApply (wp_bind (fill [AppRCtx _])).
    iApply wp_wand; first by iApply "IH2".
    iIntros (v2) "#Hv2 /=".
    destruct (val_cases_fun v1) as [[[? ->]|[? ->]]|Hnf].
    - rewrite {3}interp_unfold; simpl.
      iApply "Hv1"; done.
    - rewrite {3}interp_unfold; simpl.
      iApply "Hv1"; done.
    - iApply app_stuck; done.
  Qed.

  Lemma logrel_fork e : logrel e -∗ logrel (Fork e).
  Proof.
    iIntros "#IH !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply wp_fork.
    iSplitR; iNext; first by rewrite {2}interp_unfold.
    iApply wp_wand_l. iSplitL; [|iApply "IH"; auto]; auto.
  Qed.

  Lemma logrel_alloc e : logrel e -∗ logrel (Alloc e).
  Proof.
    iIntros "#IH !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [AllocCtx])).
    iApply wp_wand; first by iApply "IH".
    iIntros (v) "#Hv /=".
    iApply wp_fupd.
    iApply wp_stuck_weaken.
    iApply wp_alloc; auto 1 using to_of_val.
    iNext; iIntros (l) "Hl".
    rewrite {3}interp_unfold /=.
    iMod (inv_alloc _ with "[Hl]") as "HN";
      [| iModIntro; iExists _; iSplit; trivial]; eauto.
  Qed.

  Lemma logrel_load e : logrel e -∗ logrel (Load e).
  Proof.
    iIntros "#IH !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [LoadCtx])).
    iApply wp_wand; first by iApply "IH".
    iIntros (v) "#Hv /=".
    destruct (val_cases_loc v) as [[? ->]|Hnf].
    - iApply wp_stuck_weaken.
      rewrite {2}interp_unfold /=.
      iDestruct "Hv" as (l) "[% #Hv]"; simplify_eq.
      iInv (logN .@ l) as (w) "[Hw1 #Hw2]" "Hclose".
      iApply (wp_load with "Hw1").
      iNext.
      iIntros "Hw1". iMod ("Hclose" with "[Hw1 Hw2]"); eauto.
    - iApply load_stuck; done.
  Qed.

  Lemma logrel_store e1 e2 : logrel e1 -∗ logrel e2 -∗ logrel (Store e1 e2).
  Proof.
    iIntros "#IH1 #IH2 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [StoreLCtx _])).
    iApply wp_wand; first by iApply "IH1".
    iIntros (v1) "#Hv1 /=".
    iApply (wp_bind (fill [StoreRCtx _])).
    iApply wp_wand; first by iApply "IH2".
    iIntros (v2) "#Hv2 /=".
    destruct (val_cases_loc v1) as [[? ->]|Hnf].
    - iApply wp_stuck_weaken.
      rewrite {3}interp_unfold /=.
      iDestruct "Hv1" as (l) "[% #Hv1]"; simplify_eq.
      iInv (logN .@ l) as (w) "[Hw1 #Hw2]" "Hclose".
      iApply (wp_store with "Hw1").
      iNext.
      iIntros "Hw1". iMod ("Hclose" with "[Hw1 Hw2]"); eauto.
      rewrite {6}interp_unfold /=; done.
    - iApply store_stuck; done.
  Qed.

  Lemma logrel_CAS e1 e2 e3 : logrel e1 -∗ logrel e2 -∗ logrel e3 -∗ logrel (CAS e1 e2 e3).
  Proof.
    iIntros "#IH1 #IH2 #IH3 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [CasLCtx _ _])).
    iApply wp_wand; first by iApply "IH1".
    iIntros (v1) "#Hv1 /=".
    iApply (wp_bind (fill [CasMCtx _ _])).
    iApply wp_wand; first by iApply "IH2".
    iIntros (v2) "#Hv2 /=".
    iApply (wp_bind (fill [CasRCtx _ _])).
    iApply wp_wand; first by iApply "IH3".
    iIntros (v3) "#Hv3 /=".
    destruct (val_cases_loc v1) as [[? ->]|Hnf].
    - iApply wp_stuck_weaken.
      rewrite {4}interp_unfold /=.
      iDestruct "Hv1" as (l) "[% #Hv1]"; simplify_eq.
      iInv (logN .@ l) as (w) "[Hw1 #Hw2]" "Hclose".
      destruct (decide (v2 = w)) as [|Hneq]; subst.
    + iApply (wp_cas_suc with "Hw1"); auto using to_of_val.
      iNext.
      iIntros "Hw1". iMod ("Hclose" with "[Hw1 Hw2]"); eauto.
      rewrite {8}interp_unfold /=; done.
    + iApply (wp_cas_fail with "Hw1"); auto using to_of_val.
      iNext.
      iIntros "Hw1". iMod ("Hclose" with "[Hw1 Hw2]"); eauto.
      rewrite {8}interp_unfold /=; done.
    - iApply cas_stuck; done.
  Qed.

  Lemma logrel_FAA e1 e2 : logrel e1 -∗ logrel e2 -∗ logrel (FAA e1 e2).
  Proof.
    iIntros "#IH1 #IH2 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [FAALCtx _])).
    iApply wp_wand; first by iApply "IH1".
    iIntros (v1) "#Hv1 /=".
    iApply (wp_bind (fill [FAARCtx _])).
    iApply wp_wand; first by iApply "IH2".
    iIntros (v2) "#Hv2 /=".
    destruct (val_cases_loc v1) as [[? ->]|Hnf];
      last by iApply faa_stuck_non_loc_or_non_nat; auto.
    destruct (val_cases_nat v2) as [[? ->]|Hnf];
      last by iApply faa_stuck_non_loc_or_non_nat; auto.
    rewrite {3}interp_unfold /=.
    iDestruct "Hv1" as (l) "[% #Hv1]"; simplify_eq.
    iInv (logN .@ l) as (w) "[>Hw1 #Hw2]" "Hclose".
    destruct (val_cases_nat w) as [[? ->]|Hnf].
    -iApply wp_stuck_weaken.
     iApply (wp_FAA with "Hw1"); auto using to_of_val.
     iNext.
     iIntros "Hw1".
     iMod ("Hclose" with "[Hw1]"); last by eauto.
     iNext; iExists _; iFrame.
     rewrite {6}interp_unfold /=; done.
    - iApply faa_stuck_non_nat_loc; done.
  Qed.

  (* an adversary proram is any program with no hard-coded locations or assert statements. *)
  Fixpoint valid_adversary (e : expr) : Prop :=
    match e with
    | Var _ => True
    | Rec e => valid_adversary e
    | App e1 e2 => valid_adversary e1 ∧ valid_adversary e2
    | Lam e => valid_adversary e
    | LetIn e1 e2 => valid_adversary e1 ∧ valid_adversary e2
    | Seq e1 e2 => valid_adversary e1 ∧ valid_adversary e2
    | Unit => True
    | Nat n => True
    | Bool b => True
    | BinOp op e1 e2 => valid_adversary e1 ∧ valid_adversary e2
    | If e0 e1 e2 =>
        valid_adversary e0 ∧ valid_adversary e1 ∧ valid_adversary e2
    | Pair e1 e2 => valid_adversary e1 ∧ valid_adversary e2
    | Fst e => valid_adversary e
    | Snd e => valid_adversary e
    | InjL e => valid_adversary e
    | InjR e => valid_adversary e
    | Case e0 e1 e2 =>
        valid_adversary e0 ∧ valid_adversary e1 ∧ valid_adversary e2
    | Fork e => valid_adversary e
    | Loc l => False
    | Alloc e => valid_adversary e
    | Load e => valid_adversary e
    | Store e1 e2 => valid_adversary e1 ∧ valid_adversary e2
    | CAS e0 e1 e2 =>
        valid_adversary e0 ∧ valid_adversary e1 ∧ valid_adversary e2
    | FAA e1 e2 => valid_adversary e1 ∧ valid_adversary e2
    | Assert e => False
    end.

  Theorem fundamental e : valid_adversary e → ⊢ logrel e.
  Proof.
    induction e; intros Hedv; simpl in *; intuition.
    - iApply logrel_var; done.
    - iApply logrel_rec; done.
    - iApply logrel_app; done.
    - iApply logrel_lam; done.
    - iApply logrel_letin; done.
    - iApply logrel_seq; done.
    - iApply logrel_unit; done.
    - iApply logrel_nat; done.
    - iApply logrel_bool; done.
    - iApply logrel_nat_binop; done.
    - iApply logrel_if; done.
    - iApply logrel_pair; done.
    - iApply logrel_fst; done.
    - iApply logrel_snd; done.
    - iApply logrel_injl; done.
    - iApply logrel_injr; done.
    - iApply logrel_case; done.
    - iApply logrel_fork; done.
    - iApply logrel_alloc; done.
    - iApply logrel_load; done.
    - iApply logrel_store; done.
    - iApply logrel_CAS; done.
    - iApply logrel_FAA; done.
  Qed.

End typed_interp.
