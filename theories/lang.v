From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.algebra Require Export ofe.
From stdpp Require Import gmap.
From Autosubst Require Export Autosubst.
From iris.prelude Require Import options.

Module LambdaRS.
  Definition loc := positive.

  Global Instance loc_dec_eq (l l' : loc) : Decision (l = l') := _.

  Inductive binop := Add | Sub | Mult | Eq | Le | Lt.

  Global Instance binop_dec_eq (op op' : binop) : Decision (op = op').
  Proof. solve_decision. Defined.

  Inductive expr :=
  | Var (x : var)
  | Rec (e : {bind 2 of expr})
  | App (e1 e2 : expr)
  | Lam (e : {bind expr})
  | LetIn (e1 : expr) (e2 : {bind expr})
  | Seq (e1 e2 : expr)
  (* Base Types *)
  | Unit
  | Nat (n : nat)
  | Bool (b : bool)
  | BinOp (op : binop) (e1 e2 : expr)
  (* If then else *)
  | If (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : {bind expr}) (e2 : {bind expr})
  (* Concurrency *)
  | Fork (e : expr)
  (* Reference Types *)
  | Loc (l : loc)
  | Alloc (e : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
  (* Compare and swap used for fine-grained concurrency *)
  | CAS (e0 : expr) (e1 : expr) (e2 : expr)
  (* Fetch and add for fine-grained concurrency *)
  | FAA (e1 : expr) (e2 : expr)
  (* Assersion *)
  | Assert (e : expr).
  Global Instance Ids_expr : Ids expr. derive. Defined.
  Global Instance Rename_expr : Rename expr. derive. Defined.
  Global Instance Subst_expr : Subst expr. derive. Defined.
  Global Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

  (* Notation for bool and nat *)
  Notation "#♭ b" := (Bool b) (at level 20).
  Notation "#n n" := (Nat n) (at level 20).

  Global Instance expr_dec_eq (e e' : expr) : Decision (e = e').
  Proof. solve_decision. Defined.

  Inductive val :=
  | RecV (e : {bind 1 of expr})
  | LamV (e : {bind expr})
  | UnitV
  | NatV (n : nat)
  | BoolV (b : bool)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
  | LocV (l : loc).

  (* Notation for bool and nat *)
  Notation "'#♭v' b" := (BoolV b) (at level 20).
  Notation "'#nv' n" := (NatV n) (at level 20).

  Definition binop_eval (op : binop) : nat → nat → val :=
    match op with
    | Add => λ a b, #nv(a + b)
    | Sub => λ a b, #nv(a - b)
    | Mult => λ a b, #nv(a * b)
    | Eq => λ a b, if (eq_nat_dec a b) then #♭v true else #♭v false
    | Le => λ a b, if (le_dec a b) then #♭v true else #♭v false
    | Lt => λ a b, if (lt_dec a b) then #♭v true else #♭v false
    end.

  Global Instance val_dec_eq (v v' : val) : Decision (v = v').
  Proof. solve_decision. Defined.

  Global Instance val_inh : Inhabited val := populate UnitV.

  Fixpoint of_val (v : val) : expr :=
    match v with
    | RecV e => Rec e
    | LamV e => Lam e
    | UnitV => Unit
    | NatV v => Nat v
    | BoolV v => Bool v
    | PairV v1 v2 => Pair (of_val v1) (of_val v2)
    | InjLV v => InjL (of_val v)
    | InjRV v => InjR (of_val v)
    | LocV l => Loc l
    end.

  Fixpoint to_val (e : expr) : option val :=
    match e with
    | Rec e => Some (RecV e)
    | Lam e => Some (LamV e)
    | Unit => Some UnitV
    | Nat n => Some (NatV n)
    | Bool b => Some (BoolV b)
    | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
    | InjL e => InjLV <$> to_val e
    | InjR e => InjRV <$> to_val e
    | Loc l => Some (LocV l)
    | _ => None
    end.

  (** Evaluation contexts *)
  Inductive ectx_item :=
  | AppLCtx (e2 : expr)
  | AppRCtx (v1 : val)
  | LetInCtx (e2 : expr)
  | SeqCtx (e2 : expr)
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | BinOpLCtx (op : binop) (e2 : expr)
  | BinOpRCtx (op : binop) (v1 : val)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : {bind expr}) (e2 : {bind expr})
  | IfCtx (e1 : {bind expr}) (e2 : {bind expr})
  | AllocCtx
  | LoadCtx
  | StoreLCtx (e2 : expr)
  | StoreRCtx (v1 : val)
  | CasLCtx (e1 : expr)  (e2 : expr)
  | CasMCtx (v0 : val) (e2 : expr)
  | CasRCtx (v0 : val) (v1 : val)
  | FAALCtx (e2 : expr)
  | FAARCtx (v1 : val)
  | AssertCtx.

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | AppLCtx e2 => App e e2
    | AppRCtx v1 => App (of_val v1) e
    | LetInCtx e2 => LetIn e e2
    | SeqCtx e2 => Seq e e2
    | PairLCtx e2 => Pair e e2
    | PairRCtx v1 => Pair (of_val v1) e
    | BinOpLCtx op e2 => BinOp op e e2
    | BinOpRCtx op v1 => BinOp op (of_val v1) e
    | FstCtx => Fst e
    | SndCtx => Snd e
    | InjLCtx => InjL e
    | InjRCtx => InjR e
    | CaseCtx e1 e2 => Case e e1 e2
    | IfCtx e1 e2 => If e e1 e2
    | AllocCtx => Alloc e
    | LoadCtx => Load e
    | StoreLCtx e2 => Store e e2
    | StoreRCtx v1 => Store (of_val v1) e
    | CasLCtx e1 e2 => CAS e e1 e2
    | CasMCtx v0 e2 => CAS (of_val v0) e e2
    | CasRCtx v0 v1 => CAS (of_val v0) (of_val v1) e
    | FAALCtx e2 => FAA e e2
    | FAARCtx v1 => FAA (of_val v1) e
    | AssertCtx => Assert e
    end.

  Record state : Type := {Heap : gmap loc val; Failure: bool}.

  Global Instance: Inhabited state := populate {|Heap := ∅; Failure := false|}.

  Definition update_heap (σ : state) (h : gmap loc val) : state :=
    {|Heap := h; Failure := Failure σ|}.
  Definition set_failure_bit (σ : state) : state := {|Heap := Heap σ; Failure := true|}.

  Inductive head_step : expr → state → list Empty_set → expr → state → list expr → Prop :=
  (* β *)
  | BetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      head_step (App (Rec e1) e2) σ [] e1.[(Rec e1), e2/] σ []
  (* Lam-β *)
  | LamBetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      head_step (App (Lam e1) e2) σ [] e1.[e2/] σ []
  (* LetIn-β *)
  | LetInBetaS e1 e2 v2 σ :
      to_val e1 = Some v2 →
      head_step (LetIn e1 e2) σ [] e2.[e1/] σ []
  (* Seq-β *)
  | SeqBetaS e1 e2 v2 σ :
      to_val e1 = Some v2 →
      head_step (Seq e1 e2) σ [] e2 σ []
  (* Products *)
  | FstS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      head_step (Fst (Pair e1 e2)) σ [] e1 σ []
  | SndS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      head_step (Snd (Pair e1 e2)) σ [] e2 σ []
  (* Sums *)
  | CaseLS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      head_step (Case (InjL e0) e1 e2) σ [] e1.[e0/] σ []
  | CaseRS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      head_step (Case (InjR e0) e1 e2) σ [] e2.[e0/] σ []
    (* nat bin op *)
  | BinOpS op a b σ :
      head_step (BinOp op (#n a) (#n b)) σ [] (of_val (binop_eval op a b)) σ []
  (* If then else *)
  | IfFalse e1 e2 σ :
      head_step (If (#♭ false) e1 e2) σ [] e2 σ []
  | IfTrue e1 e2 σ :
      head_step (If (#♭ true) e1 e2) σ [] e1 σ []
  (* Concurrency *)
  | ForkS e σ:
      head_step (Fork e) σ [] Unit σ [e]
  (* Reference Types *)
  | AllocS e v σ l :
     to_val e = Some v → Heap σ !! l = None →
     head_step (Alloc e) σ [] (Loc l) (update_heap σ (<[l:=v]>(Heap σ))) []
  | LoadS l v σ :
     Heap σ !! l = Some v →
     head_step (Load (Loc l)) σ [] (of_val v) σ []
  | StoreS l e v σ :
     to_val e = Some v → is_Some (Heap σ !! l) →
     head_step (Store (Loc l) e) σ [] Unit (update_heap σ (<[l:=v]>(Heap σ))) []
  (* Compare and swap *)
  | CasFailS l e1 v1 e2 v2 vl σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     Heap σ !! l = Some vl → vl ≠ v1 →
     head_step (CAS (Loc l) e1 e2) σ [] (#♭ false) σ []
  | CasSucS l e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     Heap σ !! l = Some v1 →
     head_step (CAS (Loc l) e1 e2) σ [] (#♭ true) (update_heap σ (<[l:=v2]>(Heap σ))) []
  | FAAS l m e2 k σ :
      to_val e2 = Some (NatV k) →
      Heap σ !! l = Some (NatV m) →
      head_step (FAA (Loc l) e2) σ [] (#n m) (update_heap σ (<[l:=NatV (m + k)]>(Heap σ))) []
  | AssertSucS e σ :
    to_val e = Some (#♭v true) →
    head_step (Assert e) σ [] Unit σ []
  | AssertFailc e σ :
    to_val e = Some (#♭v false) →
    head_step (Assert e) σ [] Unit (set_failure_bit σ) [].

  (** Basic properties about the language *)
  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. by induction v; simplify_option_eq. Qed.

  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof.
    revert v; induction e; intros; simplify_option_eq; auto with f_equal.
  Qed.

  Global Instance of_val_inj : Inj (=) (=) of_val.
  Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

  Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

  Lemma val_stuck e1 σ1 κs e2 σ2 ef :
    head_step e1 σ1 κs e2 σ2 ef → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma head_ctx_step_val Ki e σ1 κs e2 σ2 ef :
    head_step (fill_item Ki e) σ1 κs e2 σ2 ef → is_Some (to_val e).
  Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
    repeat match goal with
           | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
           end; auto.
  Qed.

  Lemma alloc_fresh e v σ :
    let l := fresh (dom (Heap σ)) in
    to_val e = Some v → head_step (Alloc e) σ [] (Loc l) (update_heap σ (<[l:=v]>(Heap σ))) [].
  Proof. by intros; apply AllocS, (not_elem_of_dom (D:=gset loc)), is_fresh. Qed.

  Lemma val_head_stuck e1 σ1 κs e2 σ2 efs : head_step e1 σ1 κs e2 σ2 efs → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
  Proof.
    split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
           fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
  Qed.

  Canonical Structure stateO := leibnizO state.
  Canonical Structure valO := leibnizO val.
  Canonical Structure exprO := leibnizO expr.
End LambdaRS.

Canonical Structure LambdaRS_ectxi_lang :=
  EctxiLanguage LambdaRS.lang_mixin.
Canonical Structure LambdaRS_ectx_lang :=
  EctxLanguageOfEctxi LambdaRS_ectxi_lang.
Canonical Structure LambdaRS_lang :=
  LanguageOfEctx LambdaRS_ectx_lang.

Export LambdaRS.

Global Hint Extern 20 (PureExec _ _ _) => progress simpl : typeclass_instances.

Global Hint Extern 5 (IntoVal _ _) =>
  eapply of_to_val; fast_done : typeclass_instances.
Global Hint Extern 10 (IntoVal _ _) =>
  rewrite /IntoVal; eapply of_to_val;
  rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Global Hint Extern 5 (AsVal _) =>
  eexists; eapply of_to_val; fast_done : typeclass_instances.
Global Hint Extern 10 (AsVal _) =>
  eexists; rewrite /IntoVal; eapply of_to_val;
  rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Definition is_atomic (e : expr) : Prop :=
  match e with
  | Alloc e => is_Some (to_val e)
  | Load e =>  is_Some (to_val e)
  | Store e1 e2 => is_Some (to_val e1) ∧ is_Some (to_val e2)
  | CAS e1 e2 e3 => is_Some (to_val e1) ∧ is_Some (to_val e2)
                   ∧ is_Some (to_val e3)
  | FAA e1 e2 => is_Some (to_val e1) ∧ is_Some (to_val e2)
  | _ => False
  end.
Local Hint Resolve language.val_irreducible : core.
Local Hint Resolve to_of_val : core.
Local Hint Unfold language.irreducible : core.
Global Instance is_atomic_correct s e : is_atomic e → Atomic s e.
Proof.
  intros Ha; apply strongly_atomic_atomic,  ectx_language_atomic.
  - destruct 1; simpl in *; try tauto; eauto.
  - intros K e' -> Hval%eq_None_not_Some.
    induction K as [|Ki K] using rev_ind; first done.
    simpl in Ha; rewrite fill_app in Ha; simpl in Ha.
    destruct Hval. apply (fill_val K e'); simpl in *.
    destruct Ki; naive_solver.
Qed.

Ltac solve_atomic :=
  apply is_atomic_correct; simpl; repeat split;
    rewrite ?to_of_val; eapply mk_is_Some; fast_done.

Global Hint Extern 0 (Atomic _ _) => solve_atomic : core.
Global Hint Extern 0 (Atomic _ _) => solve_atomic : typeclass_instances.

Fixpoint env_subst (vs : list val) : var → expr :=
  match vs with
  | [] => ids
  | v :: vs' => (of_val v) .: env_subst vs'
  end.

Lemma env_subst_lookup_some vs x v :
  vs !! x = Some v → env_subst vs x = of_val v.
Proof.
  revert vs; induction x as [|x IHx] => vs.
  - by destruct vs; inversion 1.
  - destruct vs as [|w vs]; first by inversion 1.
    rewrite -lookup_tail /=.
    apply IHx.
Qed.

Lemma env_subst_lookup_none vs x :
  vs !! x = None → env_subst vs x = Var (x - length vs).
Proof.
  revert vs; induction x as [|x IHx] => vs.
  - by destruct vs; inversion 1.
  - destruct vs as [|w vs]; first by inversion 1.
    rewrite -lookup_tail /=.
    apply IHx.
Qed.

Inductive non_nat_val : val → Prop :=
| NN_RecV e : non_nat_val (RecV e)
| NN_LamV e : non_nat_val (LamV e)
| NN_UnitV  : non_nat_val UnitV
| NN_BoolV b : non_nat_val (BoolV b)
| NN_PairV v1 v2 : non_nat_val (PairV v1 v2)
| NN_InjLV v : non_nat_val (InjLV v)
| NN_InjRV v : non_nat_val (InjRV v)
| NN_LocV l : non_nat_val (LocV l).

Lemma val_cases_nat v : (∃ n, v = #nv n) ∨ non_nat_val v.
Proof. destruct v; solve [right; constructor| eauto]. Qed.

Inductive non_bool_val : val → Prop :=
| NB_RecV e : non_bool_val (RecV e)
| NB_LamV e : non_bool_val (LamV e)
| NB_UnitV  : non_bool_val UnitV
| NB_NatV n : non_bool_val (NatV n)
| NB_PairV v1 v2 : non_bool_val (PairV v1 v2)
| NB_InjLV v : non_bool_val (InjLV v)
| NB_InjRV v : non_bool_val (InjRV v)
| NB_LocV l : non_bool_val (LocV l).

Lemma val_cases_bool v : (∃ b, v = #♭v b) ∨ non_bool_val v.
Proof. destruct v; solve [right; constructor| eauto]. Qed.

Inductive non_pair_val : val → Prop :=
| NP_RecV e : non_pair_val (RecV e)
| NP_LamV e : non_pair_val (LamV e)
| NP_UnitV  : non_pair_val UnitV
| NP_NatV n : non_pair_val (NatV n)
| NP_BoolV b : non_pair_val (BoolV b)
| NP_InjLV v : non_pair_val (InjLV v)
| NP_InjRV v : non_pair_val (InjRV v)
| NP_LocV l : non_pair_val (LocV l).

Lemma val_cases_pair v : (∃ v1 v2, v = PairV v1 v2) ∨ non_pair_val v.
Proof. destruct v; solve [right; constructor| eauto]. Qed.

Inductive non_sum_val : val → Prop :=
| NS_RecV e : non_sum_val (RecV e)
| NS_LamV e : non_sum_val (LamV e)
| NS_UnitV  : non_sum_val UnitV
| NS_NatV n : non_sum_val (NatV n)
| NS_BoolV b : non_sum_val (BoolV b)
| NS_PairV v1 v2 : non_sum_val (PairV v1 v2)
| NS_LocV l : non_sum_val (LocV l).

Lemma val_cases_sum v : ((∃ v', v = InjLV v') ∨ (∃ v', v = InjRV v')) ∨ non_sum_val v.
Proof. destruct v; solve [right; constructor| eauto]. Qed.

Inductive non_fun_val : val → Prop :=
| NF_UnitV  : non_fun_val UnitV
| NF_NatV n : non_fun_val (NatV n)
| NF_BoolV b : non_fun_val (BoolV b)
| NF_PairV v1 v2 : non_fun_val (PairV v1 v2)
| NF_InjLV v : non_fun_val (InjLV v)
| NF_InjRV v : non_fun_val (InjRV v)
| NF_LocV l : non_fun_val (LocV l).

Lemma val_cases_fun v : ((∃ e, v = RecV e) ∨ (∃ e, v = LamV e)) ∨ non_fun_val v.
Proof. destruct v; solve [right; constructor| eauto]. Qed.

Inductive non_loc_val : val → Prop :=
| NL_RecV e : non_loc_val (RecV e)
| NL_LamV e : non_loc_val (LamV e)
| NL_UnitV  : non_loc_val UnitV
| NL_NatV n : non_loc_val (NatV n)
| NL_BoolV b : non_loc_val (BoolV b)
| NL_PairV v1 v2 : non_loc_val (PairV v1 v2)
| NL_InjLV v : non_loc_val (InjLV v)
| NL_InjRV v : non_loc_val (InjRV v).

Lemma val_cases_loc v : (∃ l, v = LocV l) ∨ non_loc_val v.
Proof. destruct v; solve [right; constructor| eauto]. Qed.
