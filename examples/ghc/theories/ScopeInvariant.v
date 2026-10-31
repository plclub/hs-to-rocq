(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

From Coq Require Import ssreflect ssrbool.

Require Import Name.
Require Import Id.
Require Import Core.
Require Import CoreFVs.
Require Import CoreUtils.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Require Import Proofs.GHC.Base.

Require Import Proofs.Axioms.

Require Import Proofs.Base.
Require Import Proofs.GhcTactics.
Require Import Proofs.Forall.
Require Import Proofs.Unique.
Require Import Proofs.CoreFVs. 
Require Import Proofs.VarSet.
Require Import Proofs.VarSetStrong.
Require Import Proofs.VarEnv.
Require Import Proofs.CoreInduct.
Require Import Proofs.Var.
Require Import Proofs.VarSetFSet.

(* These extensional predicates are raw-true. No structural set operation
   receives an unrestricted Proper instance. *)
#[local] Instance Scope_Subset_Equal_m : Morphisms.Proper
  (Morphisms.respectful Equal (Morphisms.respectful Equal iff)) Subset.
Proof. intros s t E u v F; unfold Subset; setoid_rewrite E; setoid_rewrite F; reflexivity. Qed.

#[local] Instance Scope_elemVarSet_Equal_m x : Morphisms.Proper
  (Morphisms.respectful Equal Logic.eq) (elemVarSet x).
Proof. intros s t E. apply Bool.eq_true_iff_eq. exact (E x). Qed.

Local Lemma scope_disjoint_del_rev s xs t : WF s -> ValidVarSet s -> WF t ->
  disjointVarSet (delVarSetList s (rev xs)) t = disjointVarSet (delVarSetList s xs) t.
Proof.
  intros W V T. apply disjointVarSet_m; try solve [solve_varset_inv].
  - apply delVarSetList_rev; exact W.
  - reflexivity.
Qed.

Ltac scope_fresh_disjoint H :=
  lazymatch type of H with
  | disjointVarSet ?t ?u = true =>
    eapply (disjointVarSet_subVarSet_l _ t u);
      [solve_varset_inv | solve_varset_inv | solve_varset_inv | exact H |]
  end.

#[local] Hint Resolve exprFreeVars_WF exprFreeVars_valid
  exprsFreeVars_WF exprsFreeVars_valid : varset_inv.
#[local] Hint Resolve emptyVarSet_WF unitVarSet_WF mkVarSet_WF
  extendVarSet_WF extendVarSetList_WF delVarSet_WF delVarSetList_WF
  emptyVarSet_valid unitVarSet_valid mkVarSet_valid
  extendVarSet_valid extendVarSetList_valid delVarSet_valid delVarSetList_valid
  exprFreeVars_WF exprFreeVars_valid exprsFreeVars_WF exprsFreeVars_valid : core.

Import GHC.Base.Notations.

Set Bullet Behavior "Strict Subproofs".
Opaque GHC.Base.hs_string__.

Lemma contrapositive : forall (A B:Prop), (A -> B) -> (~ B) -> (~ A).
Proof.
  intros.
  intro h. apply H in h. apply H0. auto.
Qed.

Lemma and_iff_compat_both:
  forall A B C D : Prop,
    A <-> C -> B <-> D ->
    A /\ B <-> C /\ D.
Proof. intros. intuition. Qed.

Lemma Forall_iff:
  forall a P Q (xs : list a),
    Forall (fun x => P x <-> Q x) xs ->
    Forall P xs <-> Forall Q xs.
Proof. intros. rewrite -> !Forall_forall in *. firstorder. Qed.


(** * Core invariants related to variables and scope *)

(** ** The invariants *)

(* These are the original definitions of isGlobalScope and isLocalScope *)
Definition isGlobalScope : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Id _ _ _ _ GlobalId _ _ => true
    | _ => false
    end.

Definition isLocalScope : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Id _ _ _ _ (LocalId _) _ _ => true
    | _ => false
    end.

(**
First we define invariants for [Var] that are independent of scope, namely:
- It is a localVar iff the unique is local.
- The [Unique] cached in the [Var] is the same as the [Unique] of the name
  of the var.
- The var must be an identifier (i.e. a term variable)
- but not one that is a coercion variable.
*)
Definition GoodVar (v : Var) : Prop :=
  isLocalVar v = isLocalScope v /\ 
  varUnique v = nameUnique (varName v).

Definition GoodLocalVar (v : Var) : Prop :=
  GoodVar v /\ isLocalVar v = true.




(**

Next we define when a variable occurrence is ok in a given scope.
 * Global variables are always ok (not yet tracked).
 * Local variables are ok if they are in scope, and
   are almost the same as the binder; i.e., only the 
   [idInfo] may vary

*)

Definition WellScopedVar (v : Var) (in_scope : VarSet) : Prop :=
  if isLocalVar v then
   match lookupVarSet in_scope v with
    | None => False
    | Some v' => almostEqual v v' /\ GoodVar v
    end
  else GoodVar v (* we do not track global variables yet *).

(**

Finally, we lift this to whole expressions, keeping track of the variables
that are in [in_scope]. Remember that GHC allows shadowing!

*)

(* We don't care about ticks, and I'm not sure this case is correct *)

(* Definition WellScopedTickish (x : Tickish Var)(in_scope : VarSet) : Prop :=
  match x with
  | Breakpoint _ ids => Forall (fun e => WellScopedVar e in_scope) ids
  | _ => True
  end. *)


Fixpoint WellScoped (e : CoreExpr) (in_scope : VarSet) {struct e} : Prop :=
  match e with
  | Mk_Var v => WellScopedVar v in_scope
  | Lit l => True
  | App e1 e2 => WellScoped e1 in_scope /\  WellScoped e2 in_scope
  | Lam v e => GoodLocalVar v /\ WellScoped e (extendVarSet in_scope v)
  | Let bind body =>
      WellScopedBind bind in_scope /\
      WellScoped body (extendVarSetList in_scope (bindersOf bind))
  | Case scrut bndr ty alts  => 
    WellScoped scrut in_scope /\
    GoodLocalVar bndr /\
    Forall' (fun alt =>
      let '(Mk_Alt _ pats rhs) := alt in
      Forall GoodLocalVar pats /\
      let in_scope' := extendVarSetList in_scope (bndr :: pats) in
      WellScoped rhs in_scope') alts
  | Cast e _ =>   WellScoped e in_scope
(*  | Tick _ e =>   WellScoped e in_scope *) (* /\ WellScopedTickish t in_scope *) 
  | Mk_Type _  =>   True
  | Mk_Coercion _ => True 
  end
with WellScopedBind (bind : CoreBind) (in_scope : VarSet) : Prop :=
  match bind with
  | NonRec v rhs =>
    GoodLocalVar v /\
    WellScoped rhs in_scope
  | Rec pairs => 
    Forall (fun p => GoodLocalVar (fst p)) pairs /\
    NoDup (map varUnique (map fst pairs)) /\
    Forall' (fun p => WellScoped (snd p) (extendVarSetList in_scope (map fst pairs))) pairs
  end.

Definition WellScopedAlt bndr (alt : CoreAlt) in_scope  :=
    let '(Mk_Alt _ pats rhs) := alt in
    Forall GoodLocalVar pats /\
    let in_scope' := extendVarSetList in_scope (bndr :: pats) in
    WellScoped rhs in_scope'.

(**

A [CoreProgram] can be treated like one big recursive group, despite that it
is a sequence of [Rec] and [NonRec] bindings.

*)
Definition WellScopedProgram (pgm : CoreProgram) : Prop :=
   NoDup (map varUnique (bindersOfBinds pgm)) /\
   Forall' (fun p => WellScoped (snd p) (mkVarSet (bindersOfBinds pgm))) (flattenBinds pgm).



(** ** Lemmas *)


(** *** Lemmas about [GoodLocalVar] *)

Lemma GoodLocalVar_uniqAway:
  forall vss v, GoodLocalVar v -> GoodLocalVar (uniqAway vss v).
Proof.
  intros.
  unfold GoodLocalVar, GoodVar in *.
  destruct H. destruct H. (* destruct H2. *)
  rewrite isLocalVar_uniqAway.
  (* rewrite isLocalUnique_uniqAway. *)
  (* rewrite isId_uniqAway. *)
  (*  rewrite isCoVar_uniqAway. *)
  repeat split; auto.
  move: (idScope_uniqAway vss v) => h.   rewrite H. 
  unfold isLocalScope. destruct v. destruct uniqAway eqn:m. simpl in h. rewrite h. done.
  rewrite nameUnique_varName_uniqAway; auto.
Qed.

Lemma GoodLocalVar_asJoinId_mkSysLocal:
  forall s u w ty n,
  Unique.isLocalUnique u = true ->
  GoodLocalVar (Id.asJoinId (mkSysLocal s u w ty) n).
Proof.
  intros s u w ty n Hlocal.
  unfold GoodLocalVar, GoodVar.
  unfold Id.asJoinId, Core.setIdDetails.
  unfold mkSysLocal, Id.mkLocalId, Id.mkLocalIdWithInfo,
         Core.mkLocalVar, Core.mk_id.
  simpl.
  unfold isLocalVar, isGlobalId, Core.isGlobalId, Core.isLocalVar.
  unfold varUnique, Core.varUnique, Core.realUnique.
  unfold Name.mkSystemVarName, Name.mkSystemName, Name.mkSystemNameAt.
  simpl.
  unfold isLocalScope.
  rewrite Hlocal.
  repeat split; reflexivity.
Qed.


Lemma GoodLocalVar_almostEqual:
  forall v1 v2,
  GoodLocalVar v1 ->
  almostEqual v1 v2 ->
  GoodLocalVar v2.
Proof.
  intros.
  destruct H. 
  induction H0.
  * split; only 1: assumption.
    destruct ids; simpl in *; done.
(*   * split; only 1: split; assumption. *)
(*  * split; only 1: split; assumption.  *)
Qed.

Lemma GoodVar_almostEqual : 
  forall v1 v2, 
    GoodVar v1 -> almostEqual v1 v2 -> GoodVar v2.
Proof.
  move => v1 v2 h1 h2.
  destruct h2. 
  all: unfold GoodVar in *.
  simpl in *. auto.
Qed.
(*  elim => h1 h2. 
  move => h. inversion h. 
  all: unfold GoodVar.
  all: repeat split.
  all: rewrite <- H in *.
  all: simpl in *.
  all: try done.
Qed. *)


(** *** Structural lemmas *)

Lemma WellScopedVar_extendVarSet:
  forall v vs,
  WF vs ->
  GoodVar v ->
  WellScopedVar v (extendVarSet vs v).
Proof.
  intros.
  unfold WellScopedVar.
  rewrite -> lookupVarSet_extendVarSet_self by assumption.
  destruct_match.
  * split. apply almostEqual_refl. trivial.
  * trivial.
Qed.

Lemma WellScoped_varToCoreExpr:
  forall v isvs,
  WellScopedVar v isvs -> WellScoped (varToCoreExpr v) isvs.
Proof.
  intros.
  destruct v; simpl; trivial.
Qed. 


Lemma WellScoped_Lam:
  forall v e isvs,
  WellScoped (Lam v e) isvs <-> GoodLocalVar v /\ WellScoped e (extendVarSet isvs v).
Proof. intros. reflexivity. Qed.


Lemma WellScoped_mkLams:
  forall vs e isvs,
  WellScoped (mkLams vs e) isvs <-> Forall GoodLocalVar vs /\ WellScoped e (extendVarSetList isvs vs).
Proof.
  induction vs; intros.
  * intuition.
  * simpl.
    rewrite extendVarSetList_cons.
    rewrite Forall_cons_iff.
    rewrite and_assoc.
    rewrite <- (IHvs _ _).
    reflexivity.
Qed.

Lemma WellScoped_mkVarApps:
  forall e vs isvs,
  WellScoped e isvs -> 
  Forall (fun v => WellScopedVar v isvs) vs ->
  WellScoped (mkVarApps e vs) isvs.
Proof.
  intros.
  unfold mkVarApps.
  rewrite Foldable.hs_coq_foldl'_list.
  revert e H.
  induction H0; intros.
  * simpl. assumption.
  * simpl.
    apply IHForall; clear IHForall.
    constructor.
    -- assumption.
    -- apply WellScoped_varToCoreExpr; assumption.
Qed.

Lemma WellScoped_MkLetRec: forall pairs body isvs,
  WellScoped (mkLetRec pairs body) isvs <-> WellScoped (Let (Rec pairs) body) isvs .
Proof.
  intros.
  unfold mkLetRec.
  destruct pairs; try reflexivity.
  simpl.
  rewrite extendVarSetList_nil.
  split; intro; repeat split; try constructor; intuition.
Qed.

Lemma WellScoped_MkLet: forall bind body isvs,
  WellScoped (mkLet bind body) isvs <-> WellScoped (Let bind body) isvs .
Proof.
  intros.
  unfold mkLet.
  destruct bind; try reflexivity.
  destruct l; try reflexivity.
  simpl.
  rewrite extendVarSetList_nil.
  split; intro; repeat split; try constructor; intuition.
Qed.

(** *** Lemmas related to [StrongSubset] *)

Lemma WellScopedVar_StrongSubset : forall e vs1 vs2, 
    WellScopedVar e vs1 -> StrongSubset vs1 vs2 -> WellScopedVar e vs2.
Proof.
  intros v vs1 vs2 WS SS.
  unfold WellScopedVar, StrongSubset in *.
  destruct_match; only 2: trivial.
  specialize (SS v).
  destruct (lookupVarSet vs1 v); try contradiction.
  destruct (lookupVarSet vs2 v) eqn:LV2; try contradiction.
  intuition.
  eapply almostEqual_trans with (v2 := v0); auto.
Qed.


(* No such thing as WellScopedTickish anymore *)
(*
Lemma WellScopedTickish_StrongSubset : forall e vs1 vs2, 
    WellScopedTickish e vs1 -> StrongSubset vs1 vs2 -> WellScopedTickish e vs2.
Proof.
  move => e vs1 vs2 WS SS.
  unfold WellScopedTickish, StrongSubset in *.
  destruct_match; try done.
  eapply Forall_impl; eauto.
  move=> a h. eapply WellScopedVar_StrongSubset; eauto. simpl in h.
  auto.
Qed.
*)


(** *** Relation to [exprFreeVars] *)

Lemma WellScoped_subset:
  forall e vs,
    WellScoped e vs -> WF vs -> ValidVarSet vs ->
    subVarSet (exprFreeVars e) vs = true.
Proof.
  intro e.
  apply (core_induct e); intros.
  - unfold WellScoped, WellScopedVar in *.
    destruct (isLocalVar v) eqn:HisLocal.
    + destruct (lookupVarSet vs v) eqn:Hl; try contradiction.
      rewrite -> exprFreeVars_Var by assumption.
      rewrite -> subVarSet_unitVarSet by assumption.
      eapply lookupVarSet_elemVarSet; eassumption.
    + rewrite -> exprFreeVars_global_Var by assumption.
      apply subVarSet_emptyVarSet; assumption.
  - apply subVarSet_emptyVarSet; assumption.
  - simpl in H1.
    destruct H1 as [S1 S2].
    pose proof (H _ S1 H2 H3) as F1.
    pose proof (H0 _ S2 H2 H3) as F2.
    set_b_iff.
    rewrite exprFreeVars_App.
    fsetdec.
  - simpl in H0.
    destruct H0.
    specialize (H _ H3 (extendVarSet_WF _ _ H1) (extendVarSet_valid _ _ H1 H2)).
    set_b_iff. rewrite exprFreeVars_Lam.
    unfold Subset in H |- *.
    change (forall x, In x (remove v (exprFreeVars e0)) -> In x vs).
    intro x. rewrite -> remove_iff by solve_varset_inv.
    intro M. specialize (H x (proj1 M)).
    rewrite -> add_iff in H by solve_varset_inv. tauto.
  - destruct binds as [v rhs | pairs].
    + simpl in H1. decompose [and] H1; clear H1.
      match goal with S : WellScoped rhs vs |- _ => apply H in S; try solve [solve_varset_inv] end.
      match goal with S : WellScoped body _ |- _ => apply H0 in S; try solve [solve_varset_inv] end.
      rewrite -> extendVarSetList_cons, extendVarSetList_nil in *.
      set_b_iff. rewrite exprFreeVars_Let_NonRec. fsetdec.
      specialize (H5 a H1).
      rewrite -> add_iff in H5 by (exists x; exact H2). tauto.
    + simpl in H1. decompose [and] H1; clear H1.
      rewrite -> Forall'_Forall in *.
      match goal with S : WellScoped body _ |- _ => apply H0 in S; try solve [solve_varset_inv] end.
      clear H0.
      rewrite -> Core.bindersOf_Rec_cleanup in *.
      set_b_iff. rewrite exprFreeVars_Let_Rec.
      rewrite <- SubsetE by solve_varset_inv.
      apply subVarSet_delVarSetList_extendVarSetList_dual; try solve [solve_varset_inv].
      unfold is_true.
      rewrite -> subVarSet_unionVarSet, andb_true_iff by solve_varset_inv; split.
      * apply subVarSet_exprsFreeVars; try solve [solve_varset_inv].
        rewrite -> Forall_map, Forall_forall in *.
        intros [v rhs] HIn. simpl in *.
        apply (H _ _ HIn); try solve [solve_varset_inv].
        match goal with F : forall p, List.In p pairs -> WellScoped _ _ |- _ => exact (F _ HIn) end.
      * set_b_iff. assumption.
  - simpl in H1. decompose [and] H1; clear H1.
    rewrite -> Forall'_Forall in *.
    assert (WM : IntMapProofs.WF (VarSet_IntMap (mapUnionVarSet
      (fun '(Mk_Alt _ pats rhs) => delVarSetList (exprFreeVars rhs) (pats ++ [bndr])) alts))).
    { apply mapUnionVarSet_WF. intros [dc pats rhs] _. solve_varset_inv. }
    assert (VM : ValidVarSet (mapUnionVarSet
      (fun '(Mk_Alt _ pats rhs) => delVarSetList (exprFreeVars rhs) (pats ++ [bndr])) alts)).
    { apply mapUnionVarSet_valid; intros [dc pats rhs] _; solve_varset_inv. }
    set_b_iff. rewrite exprFreeVars_Case.
    rewrite <- SubsetE by (solve_varset_inv || (apply mapUnionVarSet_WF; intros [dc pats rhs] _; solve_varset_inv) || (apply mapUnionVarSet_valid; intros [dc pats rhs] _; solve_varset_inv)).
    unfold is_true.
    rewrite -> subVarSet_unionVarSet, andb_true_iff by (solve_varset_inv || (apply mapUnionVarSet_WF; intros [dc pats rhs] _; solve_varset_inv) || (apply mapUnionVarSet_valid; intros [dc pats rhs] _; solve_varset_inv)); split.
    * apply H; assumption.
    * apply subVarSet_mapUnionVarSet; try solve [solve_varset_inv];
        try solve [intros [dc pats rhs] _; solve_varset_inv].
      rewrite -> Forall_forall in *.
      intros [dc pats rhs] HIn.
      match goal with F : forall a, List.In a alts -> _ |- _ =>
        specialize (F _ HIn); destruct F
      end. simpl in *.
      rewrite -> delVarSetList_app, delVarSetList_single.
      set_b_iff.
      change (delVarSet (delVarSetList (exprFreeVars rhs) pats) bndr [<=] vs).
      rewrite <- delVarSetList_cons2 by solve_varset_inv.
      rewrite <- SubsetE by solve_varset_inv.
      apply subVarSet_delVarSetList_extendVarSetList_dual; try solve [solve_varset_inv].
      apply (H0 _ _ _ HIn); try solve [solve_varset_inv]; assumption.
  - specialize (H _ H0 H1 H2). set_b_iff. rewrite exprFreeVars_Cast. exact H.
(*  - rewrite exprFreeVars_Tick.
    simpl in H0.
    by apply H.

    rewrite exprFreeVars_Tick. 
    simpl in H0. move: H0 => [a b].
    destruct tickish; unfold tickishFreeVars in *; hs_simpl;
      try (apply H; assumption).
    simpl in b.
    rewrite -> subVarSet_unionVarSet, andb_true_iff; split.
    eauto.
    set_b_iff.
    move=> x InX.
    rewrite -> filter_iff in InX; try apply RespectsVar_isLocalVar.
    move: InX => [i0 i1].
    rewrite -> Forall_forall in b.
    rewrite -> extendVarSetList_iff in i0.
    destruct i0; try done.
    unfold In.
    move: (elem_exists_in _ _ H0) => [y [Iny eqy]].
    move: (b _ Iny) => WSy.
    unfold WellScopedVar in WSy.

    rewrite (RespectsVar_isLocalVar eqy) in i1.
    rewrite i1 in WSy.
    elim h: (lookupVarSet vs y) => [z|].
    erewrite (elemVarSet_eq _ eqy); eauto.
    eapply lookupVarSet_elemVarSet; eauto.
    rewrite h in WSy. done.
    *)
  - apply subVarSet_equal_empty; try solve [solve_varset_inv]. apply exprFreeVars_Type.
  - apply subVarSet_equal_empty; try solve [solve_varset_inv]. apply exprFreeVars_Coercion.
Qed.



(** *** Freshness *)

Lemma WellScopedVar_extendVarSetList_l:
  forall v vs1 vs2,
  WellScopedVar v vs1 ->
  elemVarSet v (mkVarSet vs2) = false ->
  WF vs1 ->
  WellScopedVar v (extendVarSetList vs1 vs2).
Proof.
  intros.
  unfold WellScopedVar in *.
  destruct_match; only 2: assumption.
  destruct_match; only 2: contradiction.
  rewrite -> lookupVarSet_extendVarSetList_l by (auto; rewrite H0; auto).
  rewrite Heq0.
  assumption.
Qed.

Lemma WellScopedVar_extendVarSetList_r:
  forall v vs1 vs2,
  Forall GoodVar vs2 ->
  List.In v vs2 ->
  NoDup (map varUnique vs2) ->
  WF vs1 ->
  WellScopedVar v (extendVarSetList vs1 vs2).
Proof.
  intros.
  unfold WellScopedVar in *.
  assert (Gv: GoodVar v). 
   { rewrite -> Forall_forall in *. auto. }
  destruct_match.
  rewrite -> lookupVarSet_extendVarSetList_self_in by assumption.
  intuition.
  assumption.
Qed.


Lemma WellScopedVar_extendVarSetList_fresh_under v vs vs1 vs2 :
  disjointVarSet (delVarSetList (exprFreeVars (Mk_Var v)) (rev vs2))
                 (mkVarSet vs1) = true ->
  WF vs ->
  WellScopedVar v (extendVarSetList (extendVarSetList vs vs1) vs2) <->
  WellScopedVar v (extendVarSetList vs vs2).
Proof.
    intros H W.
    unfold WellScopedVar.
    destruct_match; only 2: reflexivity.
    enough (lookupVarSet (extendVarSetList (extendVarSetList vs vs1) vs2) v = 
            lookupVarSet (extendVarSetList vs vs2) v) as Htmp
      by (rewrite Htmp; reflexivity).
    rewrite -> exprFreeVars_Var in H by assumption.
    rewrite -> scope_disjoint_del_rev in H by solve_varset_inv.
    clear -H W.
    (* duplication with isJoinPointsValid_fresh_updJPSs_aux here *)
    induction vs2 using rev_ind.
    + rewrite !extendVarSetList_nil.
      rewrite delVarSetList_nil in H.
      revert vs W; induction vs1; intros.
      - rewrite extendVarSetList_nil.
        reflexivity.
      - rewrite extendVarSetList_cons.
        rewrite -> fold_is_true in H.
        rewrite -> disjointVarSet_mkVarSet_cons in H by solve_varset_inv.
        destruct H.
        rewrite -> IHvs1 by (assumption || solve_varset_inv).
        apply lookupVarSet_extendVarSet_neq; [exact W|].
        rewrite <- elemVarSet_unitVarSet_is_eq. intro.
        contradict H. rewrite H1=>//.
    + rewrite -> delVarSetList_app, delVarSetList_cons, delVarSetList_nil in H.
      rewrite -> !extendVarSetList_append, !extendVarSetList_cons, !extendVarSetList_nil.
      destruct (x GHC.Base.== v) eqn:?.
      -- rewrite -> !lookupVarSet_extendVarSet_eq by (assumption || solve_varset_inv).
         reflexivity.
      -- rewrite <- not_true_iff_false in Heqb.
         rewrite -> !lookupVarSet_extendVarSet_neq by (assumption || solve_varset_inv).
         apply IHvs2.
         rewrite -> fold_is_true in *.
         rewrite -> disjointVarSet_mkVarSet in * by solve_varset_inv.
         eapply Forall_impl; only 2: eapply H. intros v2 ?.
         cbv beta in H0.
         rewrite -> delVarSet_elemVarSet_false in H0; try solve [solve_varset_inv]; only 1: assumption.
         clear -Heqb.
         apply elemVarSet_delVarSetList_false_l; try solve [solve_varset_inv].
         rewrite elemVarSet_unitVarSet_is_eq.
         apply negbTE, notE => //. 
Qed.


(* There are a number of variants of the freshness lemmas.
   The simplest one that implies all others is this, so lets
   only do one induction:
*)



Lemma WellScoped_extendVarSetList_fresh_under:
  forall vs1 vs2 e vs,
  disjointVarSet (delVarSetList (exprFreeVars e) vs2) (mkVarSet vs1)  = true ->
  WF vs ->
  WellScoped e (extendVarSetList (extendVarSetList vs vs1) vs2) <->
  WellScoped e (extendVarSetList vs vs2).
Proof.
 (* This proof is similar to isJoinPointsValid_fresh_updJPSs_aux
    In particular, proving the assumtion [disjointVarSet ..] for all the inductive
    cases is identical (although here we have more inductive cases than there.
    Once could common it up with a deidcated induction rule. Or live with the duplication.
  *)
  intros vs1 vs2 e vs H W.
  rewrite <- scope_disjoint_del_rev in H by solve_varset_inv.
  revert vs2 vs H W.
  apply (core_induct e); intros.
  * simpl.
    eapply WellScopedVar_extendVarSetList_fresh_under; eauto.
  * reflexivity.
  * simpl.
    apply and_iff_compat_both.
    - apply H; try assumption.
      scope_fresh_disjoint H1.
      apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
      set_b_iff. rewrite exprFreeVars_App.
      set_b_iff; fsetdec.
    - apply H0; try assumption.
      scope_fresh_disjoint H1.
      apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
      set_b_iff. rewrite exprFreeVars_App.
      set_b_iff; fsetdec.
  * simpl.
    apply and_iff_compat_both; try reflexivity.
    rewrite <- !extendVarSetList_singleton.
    rewrite <- !extendVarSetList_append with (vs1 := vs2).
    apply H; try assumption.
    rewrite rev_app_distr.
    simpl.
    rewrite delVarSetList_cons.
    set_b_iff.
    assert (E : delVarSetList (exprFreeVars (Lam v e0)) (rev vs2) [=]
      delVarSetList (delVarSet (exprFreeVars e0) v) (rev vs2)).
    { apply delVarSetList_m; try solve [solve_varset_inv].
      - apply exprFreeVars_Lam.
      - clear -vs2. induction (rev vs2) as [|x xs IH].
        + exact (SetoidList.eqlistA_nil _).
        + apply SetoidList.eqlistA_cons; [apply Eq_refl|exact IH]. }
    intros x M. apply H0. exact (proj2 (E x) M).
  * simpl.
    apply and_iff_compat_both.
    - destruct binds as [v rhs | pairs].
      + simpl.
        apply and_iff_compat_both; only 1: reflexivity.
        apply H; try assumption.
        scope_fresh_disjoint H1.
        apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
        set_b_iff. rewrite exprFreeVars_Let_NonRec.
        set_b_iff; fsetdec.
      + simpl.
        repeat apply and_iff_compat_both; try reflexivity.
        rewrite !Forall'_Forall.
        apply Forall_iff.
        rewrite Forall_forall.
        intros [v rhs] HIn.
        rewrite <- !extendVarSetList_append with (vs1 := vs2).
        apply (H _ _ HIn); try assumption.
        scope_fresh_disjoint H1.
        rewrite rev_app_distr; simpl.
        rewrite delVarSetList_app.
        apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
        set_b_iff. rewrite exprFreeVars_Let_Rec.
        pose proof (subVarSet_exprFreeVars_exprsFreeVars _ _ _ HIn).
        rewrite -> delVarSetList_rev by solve_varset_inv.
        rewrite <- SubsetE by solve_varset_inv.
        apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
        set_b_iff; fsetdec.
    - rewrite <- !extendVarSetList_append with (vs1 := vs2).
      apply H0; try assumption.
      scope_fresh_disjoint H1.
      rewrite -> rev_app_distr, delVarSetList_app.
      apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
      destruct binds as [v rhs | pairs].
      -- set_b_iff. rewrite exprFreeVars_Let_NonRec.
         simpl.
         rewrite -> delVarSetList_cons, delVarSetList_nil.
         set_b_iff; fsetdec.
      -- set_b_iff. rewrite exprFreeVars_Let_Rec.
         simpl. rewrite Core.bindersOf_Rec_cleanup.
         rewrite -> delVarSetList_rev by solve_varset_inv.
         rewrite <- SubsetE by solve_varset_inv.
         apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
         set_b_iff; fsetdec.

  * simpl.
    repeat apply and_iff_compat_both; try reflexivity.
    - apply H; try assumption.
      scope_fresh_disjoint H1.
      apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
      set_b_iff. rewrite exprFreeVars_Case.
      set_b_iff; fsetdec.
      apply union_2; [solve_varset_inv| |exact H2].
      apply mapUnionVarSet_WF; intros [dc pats rhs] _; solve_varset_inv.
    - rewrite !Forall'_Forall.
      apply Forall_iff.
      rewrite Forall_forall.
      intros [dc pats rhs] HIn; simpl.
      repeat apply and_iff_compat_both; try reflexivity.
      rewrite <- !extendVarSetList_append with (vs1 := vs2).
      apply (H0 _ _ _ HIn); try assumption.
      scope_fresh_disjoint H1.
      rewrite rev_app_distr; simpl.
      rewrite -> !delVarSetList_app, delVarSetList_cons, delVarSetList_nil.
      apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
      set_b_iff. rewrite exprFreeVars_Case.
      unfold is_true.
      match goal with HIn : List.In _ ?xs |- context [mapUnionVarSet ?f ?xs] =>
        let Wf := fresh "Wf" in let Vf := fresh "Vf" in
        assert (Wf : forall y, List.In y xs -> WF (f y)) by (intros [dc' pats' rhs'] _; solve_varset_inv);
        assert (Vf : forall y, List.In y xs -> ValidVarSet (f y)) by (intros [dc' pats' rhs'] _; solve_varset_inv);
        let H := fresh "HM" in pose proof (@mapUnionVarSet_In_subVarSet _ _ xs f Wf HIn) as H;
        let WM := fresh in pose proof (mapUnionVarSet_WF f xs Wf) as WM;
        let VM := fresh in pose proof (mapUnionVarSet_valid f xs Wf Vf) as VM;
        simpl in H end.
      assert (E : delVarSet (delVarSetList (exprFreeVars rhs) (rev pats)) bndr [=]
        delVarSetList (exprFreeVars rhs) (pats ++ [bndr])).
      { transitivity (delVarSet (delVarSetList (exprFreeVars rhs) pats) bndr).
        - apply delVarSet_m; try solve [solve_varset_inv].
          + apply delVarSetList_rev; solve_varset_inv.
          + apply Eq_refl.
        - rewrite -> delVarSetList_app, delVarSetList_single. reflexivity. }
      match goal with |- Subset _ ?s =>
        change (delVarSet (delVarSetList (exprFreeVars rhs) (rev pats)) bndr [<=] s)
      end.
      rewrite E. set_b_iff.
      intros x M. apply union_3; try solve [solve_varset_inv].
      match goal with HM : Subset _ _ |- _ => apply HM; exact M end.
  * apply H; try assumption.
    scope_fresh_disjoint H0.
    apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
    set_b_iff. rewrite exprFreeVars_Cast.
    set_b_iff; fsetdec.
(*  * simpl.
    apply H.
    eapply disjointVarSet_subVarSet_l; only 1: apply H0.
    apply subVarSet_delVarSetList_both.
    rewrite exprFreeVars_Tick.
    set_b_iff; fsetdec.
    (*
    simpl.
    eapply and_iff_compat_both.
    ++ apply H.
       eapply disjointVarSet_subVarSet_l; only 1: apply H0.
       apply subVarSet_delVarSetList_both.
       rewrite exprFreeVars_Tick.
       set_b_iff; fsetdec. 
    ++ destruct tickish; try done.
       simpl. 
       rewrite -> exprFreeVars_Tick in H0.
       apply Forall_iff.
       rewrite Forall_forall.
       move=> x In.
       eapply WellScopedVar_extendVarSetList_fresh_under.
       unfold tickishFreeVars in H0.
       eapply disjointVarSet_subVarSet_l.
       eapply H0.
       eapply subVarSet_delVarSetList_both.
       elim LV: (isLocalVar x).
       -- rewrite (exprFreeVars_Var x LV).
          rewrite subVarSet_unitVarSet.
          hs_simpl. apply /orP. right.
          rewrite elemVarSet_filterVarSet => //.
          apply /andP. split. auto.
          hs_simpl.
          apply list_in_elem.
          auto.
       -- rewrite (exprFreeVars_global_Var x LV).
          apply subVarSet_emptyVarSet.
    *) *)
  * reflexivity.
  * reflexivity. 
Qed.

Lemma WellScoped_extendVarSetList_fresh:
  forall vs e vs1,
  disjointVarSet (exprFreeVars e) (mkVarSet vs) = true ->
  WF vs1 ->
  WellScoped e (extendVarSetList vs1 vs) <->
  WellScoped e vs1.
Proof.
  intros vs e vs1 H W.
  assert (D : disjointVarSet (delVarSetList (exprFreeVars e) []) (mkVarSet vs) = true).
  { rewrite delVarSetList_nil. exact H. }
  pose proof (WellScoped_extendVarSetList_fresh_under vs [] e vs1 D W) as K.
  rewrite !extendVarSetList_nil in K. exact K.
Qed.

Lemma WellScoped_extendVarSet_fresh:
  forall v e vs,
  elemVarSet v (exprFreeVars e) = false ->
  WF vs ->
  WellScoped e (extendVarSet vs v) <-> WellScoped e vs.
Proof.
  intros v e vs H W.
  assert (D : disjointVarSet (exprFreeVars e) (mkVarSet [v]) = true).
  { rewrite -> fold_is_true.
    rewrite -> disjointVarSet_mkVarSet_cons, disjointVarSet_mkVarSet_nil by solve_varset_inv.
    split; [exact H|reflexivity]. }
  pose proof (WellScoped_extendVarSetList_fresh [v] e vs D W) as K.
  rewrite -> extendVarSetList_cons, extendVarSetList_nil in K. exact K.
Qed.

Lemma WellScoped_extendVarSetList_fresh_between:
  forall (vs1 vs2 vs3 : list Var) (e : CoreExpr) (vs : VarSet),
  disjointVarSet (delVarSetList (exprFreeVars e) vs3) (mkVarSet vs2) = true ->
  WF vs ->
  WellScoped e (extendVarSetList vs ((vs1 ++ vs2) ++ vs3)) <->
  WellScoped e (extendVarSetList vs (vs1 ++ vs3)).
Proof.
  intros.
  rewrite <- app_assoc.
  rewrite !extendVarSetList_append.
  apply WellScoped_extendVarSetList_fresh_under; [assumption|solve_varset_inv].
Qed.

(** *** The invariants respect [StrongSubset] *)


Instance Respects_StrongSubset_WellScopedVar v : Respects_StrongSubset (WellScopedVar v).
Proof.
  intros vs1 vs2 W1 W2 H H0.
  unfold WellScopedVar in *.
  destruct_match; only 2: assumption.
  destruct_match; only 2: contradiction.
  specialize (H v).
  rewrite Heq0 in H.
  destruct_match; only 2: contradiction.
  intuition.
  eapply almostEqual_trans; eassumption.
Qed.

(*
Instance Respects_StrongSubset_WellScopedTickish v : Respects_StrongSubset (WellScopedTickish v).
Proof.
  intros ????.
  unfold WellScopedTickish in *.
  destruct v; try done.
  rewrite -> Forall_forall in *.
  move=> x In.
  move: (H0 x In) => h.
  eapply Respects_StrongSubset_WellScopedVar; eauto.
Qed.
*)

Instance Respects_StrongSubset_WellScoped e : Respects_StrongSubset (WellScoped e).
Proof.
  apply (core_induct e); intros; simpl.
  * apply Respects_StrongSubset_WellScopedVar.
  * apply Respects_StrongSubset_const.
  * apply Respects_StrongSubset_and; assumption.
  * apply Respects_StrongSubset_and; try apply Respects_StrongSubset_const.
    apply Respects_StrongSubset_extendVarSet.
    assumption.
  * apply Respects_StrongSubset_and.
    - destruct_match.
      + apply Respects_StrongSubset_and; try apply Respects_StrongSubset_const.
        assumption.
      + simpl.
        repeat apply Respects_StrongSubset_and; try apply Respects_StrongSubset_const.
        setoid_rewrite Forall'_Forall.
        apply Respects_StrongSubset_forall.
        rewrite Forall_forall.
        intros [v rhs] HIn.
        specialize (H _ _ HIn).
        apply Respects_StrongSubset_extendVarSetList.
        apply H.
    - apply Respects_StrongSubset_extendVarSetList.
      apply H0.
   * repeat apply Respects_StrongSubset_and; try apply Respects_StrongSubset_const.
     - apply H.
     - setoid_rewrite Forall'_Forall.
       apply Respects_StrongSubset_forall.
       rewrite Forall_forall.
       intros [dc pats rhs] HIn.
       repeat apply Respects_StrongSubset_and; try apply Respects_StrongSubset_const.
       specialize (H0 _ _ _ HIn).
       apply Respects_StrongSubset_extendVarSetList.
       apply H0.
   * apply H.
(*   * apply H.
     (*
     unfold Respects_StrongSubset
     move=> vs1 vs2 SS.
     move=> [WSE WST].
     split.
     eauto.
     eapply Respects_StrongSubset_WellScopedTickish; eauto.
     *) *)
   * apply Respects_StrongSubset_const.
   * apply Respects_StrongSubset_const. 
Qed.

Lemma WellScoped_StrongSubset : forall e vs1 vs2,
    WellScoped e vs1 -> StrongSubset vs1 vs2 ->
    WF vs1 -> WF vs2 -> WellScoped e vs2.
Proof.
  intros e vs1 vs2 S H W1 W2.
  exact (Respects_StrongSubset_WellScoped e vs1 vs2 W1 W2 H S).
Qed.



(* This seems straitforward to prove given our current
   theories of exprFreeVars. 
   However, a stronger result is possible: that the free vars  
   are a *strong subset* of the in_scope set.
*)
Lemma WellScoped_exprFreeVars :
  forall e vs, WellScoped e vs -> WF vs -> ValidVarSet vs ->
  exprFreeVars e [<=] vs.
Proof.
  intros e vs S W V.
  apply (proj1 (SubsetE _ _ (exprFreeVars_WF e) W)).
  apply WellScoped_subset; assumption.
Qed.

Print Assumptions WellScoped_subset.
Print Assumptions WellScoped_extendVarSetList_fresh_between.
Print Assumptions WellScoped_StrongSubset.
