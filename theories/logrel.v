From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From RobustSafety Require Export persistent_pred.
From RobustSafety Require Export rules.
From iris.algebra Require Import list.
From iris.base_logic Require Import invariants.
From iris.prelude Require Import options.
Import uPred.

Definition logN : namespace := nroot .@ "logN".

(** interp : is a unary logical relation. *)
Section logrel.
  Context `{heapIG Σ}.
  Notation D := (persistent_predO val (iPropI Σ)).
  Implicit Types interp : D.

  Local Arguments ofe_car !_.

  Program Definition interp_prod : D -n> D :=
    λne interp, PersPred (λ w, ▷ ∃ w1 w2, ⌜w = PairV w1 w2⌝ ∧ interp w1 ∧ interp w2)%I.
  Solve Obligations with solve_proper.
  Instance interp_prod_contractive : Contractive interp_prod.
  Proof. solve_contractive. Qed.

  Program Definition interp_sum : D -n> D :=
    λne interp,
      PersPred (λ w, ▷ ((∃ w1, ⌜w = InjLV w1⌝ ∧ interp w1) ∨ (∃ w2, ⌜w = InjRV w2⌝ ∧ interp w2)))%I.
  Solve Obligations with solve_proper.
  Instance interp_sum_contractive : Contractive interp_sum.
  Proof. solve_contractive. Qed.

  Program Definition interp_arrow : D -n> D :=
    λne interp, PersPred (λ w, □ ∀ v, ▷ interp v → WP App (of_val w) (of_val v) ? {{ interp }})%I.
  Solve Obligations with solve_proper.
  Instance interp_arrow_contractive : Contractive interp_arrow.
  Proof.
    intros n interp interp' Hinterps w.
    rewrite /interp_arrow /=.
    f_equiv.
    f_equiv; intros v.
    f_equiv.
    - solve_contractive.
    - apply wp_contractive; first apply _.
      destruct n.
      { simpl in *. constructor. lia. }
      simpl. constructor. intros. by apply Hinterps.
  Qed.

  Program Definition interp_ref_inv (l : loc) : D -n> iPropO Σ :=
    λne interp, (∃ v, l ↦ v ∗ interp v)%I.
  Solve Obligations with solve_proper.

  Program Definition interp_ref : D -n> D :=
    λne interp, PersPred (λ w, ∃ l, ⌜w = LocV l⌝ ∧ inv (logN .@ l) (interp_ref_inv l interp))%I.
  Solve Obligations with solve_proper.
  Instance interp_ref_contractive : Contractive interp_ref.
  Proof. solve_contractive. Qed.

  Program Definition interp_of (w : val) : (D -n> D) :=
    λne interp, match w return D with
      | RecV _ | LamV _ => interp_arrow interp
      | UnitV => PersPred (λ _, True)
      | NatV _ => PersPred (λ _, True)
      | BoolV _ => PersPred (λ _, True)
      | PairV _ _ => interp_prod interp
      | InjLV _ | InjRV _ => interp_sum interp
      | LocV _ => interp_ref interp
      end%I.
  Next Obligation.
  Proof. intros []; solve_proper. Qed.

  Instance interp_of_contractive w : Contractive (interp_of w).
  Proof.
    destruct w; cbn -[interp_arrow interp_prod interp_sum interp_ref]; apply (_ : Contractive _).
  Qed.

  Program Definition interp_one : D -n> D :=
    λne interp, PersPred (λ w, interp_of w interp w).
  Next Obligation.
  Proof.
    intros ???? w; cbn -[interp_of]; f_equiv; by apply contractive_ne; first apply _.
  Qed.
  Instance interp_one_contractive : Contractive interp_one.
  Proof.
    intros n interp interp' Hinterps w; cbn -[interp_of]; f_equiv; apply (_ : Contractive _); done.
  Qed.

  Definition interp : D := fixpoint interp_one.

  Lemma interp_unfold : interp ≡ interp_one interp.
  Proof. rewrite /interp; apply fixpoint_unfold. Qed.

  Definition interp_env (vs : list val) : iProp Σ := [∗ list] v ∈ vs, interp v.

  Definition interp_expr (e : expr) : iProp Σ := WP e ? {{ interp }}%I.

  Global Instance interp_env_persistent vs : Persistent (interp_env vs) := _.

  Lemma interp_env_Some_l vs x v :
    vs !! x = Some v → interp_env vs ⊢ interp v.
  Proof.
    iIntros (?) "Henv".
    iApply (big_sepL_elem_of with "Henv").
    apply elem_of_list_lookup_2 with x; done.
  Qed.

  Lemma interp_env_nil : ⊢ interp_env [].
  Proof. done. Qed.
  Lemma interp_env_cons vs v :
    interp_env (v :: vs) ⊣⊢ interp v ∗ interp_env vs.
  Proof. done. Qed.

  (* The logical relation *)

  Definition logrel (e : expr) : iProp Σ := □ ∀ vs, interp_env vs -∗ interp_expr e.[env_subst vs].

End logrel.

Global Typeclasses Opaque interp_env.
