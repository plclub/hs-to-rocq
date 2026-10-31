(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.



Require Import CoreFVs.
Require Import Id.
Require Import Exitify.
Require Import Core.
Require Import Proofs.CoreInduct.
Require Import Proofs.FV.

Require Import Proofs.Data.Foldable.
Require Import Proofs.Data.Tuple.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Proofs.Axioms.
Require Import Proofs.GhcTactics.
Require Import Proofs.Base.
Require Import Proofs.CoreInduct.
Require Import Proofs.Core.
Require Import Proofs.GHC.List.
Require Import Proofs.Util.

Require Import Proofs.Var.
Require Import Proofs.VarSet.
Import VarSetFSet.
Import VarSetDecide.
Import VarSetFacts.
Import VarSetProperties.
Import VarSetFSet.Notin.

Require Import Proofs.GHC.Base.
Require GHC.Base.
Import GHC.Base.ManualNotations.

(*
Require Import Proofs.ScopeInvariant.
*)

Set Bullet Behavior "Strict Subproofs".

Require GHC.Core.TyCo.FVs.
Require NestedRecursionHelpers.

(* tyCoFVsOfType and tyCoFVsOfCo are axiomatized in the lib.
   Since types/coercions are fully axiomatized (AxiomatizedTypes.v) and
   type substitution is identity (substTyUnchecked_id), type/coercion
   free variables are effectively empty — there are no capturable variables. *)

Axiom tyCoFVsOfType_is_emptyFV : forall ty,
  GHC.Core.TyCo.FVs.tyCoFVsOfType ty = FV.emptyFV.
Axiom tyCoFVsOfCo_is_emptyFV : forall co,
  GHC.Core.TyCo.FVs.tyCoFVsOfCo co = FV.emptyFV.

(* These independently axiomatized DSet variants are membership-empty only.
   Neither contract asserts structural WF or validity. *)
Axiom tyCoVarsOfTypeDSet_empty : forall ty,
  GHC.Core.TyCo.FVs.tyCoVarsOfTypeDSet ty [=] emptyVarSet.
Axiom tyCoVarsOfCoDSet_empty : forall co,
  GHC.Core.TyCo.FVs.tyCoVarsOfCoDSet co [=] emptyVarSet.

Lemma tyCoFVsOfType_WF : forall ty, WF_fv (GHC.Core.TyCo.FVs.tyCoFVsOfType ty).
Proof. intros. rewrite tyCoFVsOfType_is_emptyFV. apply empty_FV_WF. Qed.

Lemma tyCoFVsOfCo_WF : forall co, WF_fv (GHC.Core.TyCo.FVs.tyCoFVsOfCo co).
Proof. intros. rewrite tyCoFVsOfCo_is_emptyFV. apply empty_FV_WF. Qed.

(* Derived: no local vars (follows from emptyFV) *)
Lemma fvVarSet_emptyFV : FV.fvVarSet FV.emptyFV = emptyVarSet.
Proof. reflexivity. Qed.

Lemma tyCoFVsOfType_not_local : forall ty,
  filterVarSet isLocalVar (FV.fvVarSet (GHC.Core.TyCo.FVs.tyCoFVsOfType ty)) [=] emptyVarSet.
Proof.
  intros. rewrite tyCoFVsOfType_is_emptyFV. rewrite fvVarSet_emptyFV.
  rewrite filterVarSet_emptyVarSet. reflexivity.
Qed.

Lemma tyCoFVsOfCo_not_local : forall co,
  filterVarSet isLocalVar (FV.fvVarSet (GHC.Core.TyCo.FVs.tyCoFVsOfCo co)) [=] emptyVarSet.
Proof.
  intros. rewrite tyCoFVsOfCo_is_emptyFV. rewrite fvVarSet_emptyFV.
  rewrite filterVarSet_emptyVarSet. reflexivity.
Qed.

Lemma varTypeTyCoFVs_emptyFV : forall v, varTypeTyCoFVs v = FV.emptyFV.
Proof.
  intros v. unfold varTypeTyCoFVs.
  rewrite tyCoFVsOfType_is_emptyFV.
  destruct (Core.varMultMaybe v).
  - rewrite tyCoFVsOfType_is_emptyFV. reflexivity.
  - reflexivity.
Qed.

Lemma varTypeTyCoFVs_WF : forall v, WF_fv (varTypeTyCoFVs v).
Proof. intros. rewrite varTypeTyCoFVs_emptyFV. apply empty_FV_WF. Qed.

#[export] Hint Resolve tyCoFVsOfType_WF : core.
#[export] Hint Resolve tyCoFVsOfCo_WF : core.
#[export] Hint Resolve varTypeTyCoFVs_WF : core.

Lemma unzip_fst {A B} l : forall (l0 : list A) (l1 : list B), List.unzip l = (l0, l1) -> List.map fst l = l0.
Proof. 
  induction l. 
  - simpl. move=> l0 l1 h. inversion h. auto.
  - move=> l0 l1. destruct a; simpl. 
    destruct (List.unzip l) eqn:LL.
    move=> h. inversion h. subst.
    f_equal. eapply IHl. eauto.
Qed.




(** ** [FV] *)

Lemma emptyVarSet_bndrRuleAndUnfoldingFVs bndr :
  Denotes emptyVarSet (bndrRuleAndUnfoldingFVs bndr).
Proof.
  destruct bndr; unfold bndrRuleAndUnfoldingFVs; simpl.
  eapply emptyVarSet_emptyFV.
(*  unfold idRuleFVs, idUnfoldingFVs, stableUnfoldingFVs. simpl.
  rewrite union_empty_l.
  eapply emptyVarSet_emptyFV. *)
Qed.

Lemma addBndr_fv fv bndr vs :
  Denotes vs fv ->
  Denotes (delVarSet vs bndr) (addBndr bndr fv).
Proof.
  move=> h.
  unfold addBndr.
  rewrite varTypeTyCoFVs_emptyFV.
  rewrite union_empty_l.
  eapply delVarSet_delFV.
  eauto.
Qed.

Lemma addBndr_WF : forall fv bndr,
    WF_fv fv ->
    WF_fv (addBndr bndr fv).
Proof.
  move=> fv bndr H.
  unfold addBndr.
  apply union_FV_WF.
  - apply varTypeTyCoFVs_WF.
  - apply del_FV_WF. exact H.
Qed.


Lemma addBndrs_fv fv bndrs vs :
  Denotes vs fv -> 
  Denotes (delVarSetList vs bndrs) (addBndrs bndrs fv).
Proof.
  intro D. pose proof (Denotes_WF D) as W.
  pose proof (Denotes_valid D) as V.
  induction bndrs as [|b bs IH].
  - rewrite -> delVarSetList_nil. exact D.
  - unfold addBndrs in *. rewrite -> !hs_coq_foldr_list in *. simpl.
    apply Denotes_Equal with (vs1 := delVarSet (delVarSetList vs bs) b).
    + solve_varset_inv.
    + solve_varset_inv.
    + symmetry. apply delVarSetList_cons2. exact W.
    + apply addBndr_fv. exact IH.
Qed.

Lemma addBndrs_WF : forall fv bndrs,
    WF_fv fv ->
    WF_fv (addBndrs bndrs fv).
Proof.
  induction bndrs; unfold addBndrs;
    rewrite hs_coq_foldr_list; auto.
  intros. simpl. apply addBndr_WF. auto.
Qed.

Lemma bndrRuleAndUnfoldingFVs_WF bndr : WF_fv (bndrRuleAndUnfoldingFVs bndr).
Proof.
  destruct bndr; unfold bndrRuleAndUnfoldingFVs; simpl.
  eapply empty_FV_WF.
(*   unfold idRuleFVs, idUnfoldingFVs, stableUnfoldingFVs. simpl.
  eapply union_FV_WF; eapply empty_FV_WF. *)
Qed.


Lemma expr_fvs_WF : forall e,
    WF_fv (expr_fvs e).
Proof.
  intro e.
  apply (core_induct e); intros.
  - simpl. auto.
  - simpl. auto.
  - simpl. apply union_FV_WF; auto.
  - simpl. apply addBndr_WF; auto.
  - destruct binds.
    + simpl. apply union_FV_WF.
      * apply union_FV_WF; auto. apply bndrRuleAndUnfoldingFVs_WF.
      * apply addBndr_WF; auto.
    + simpl. apply addBndrs_WF.
      apply union_FV_WF; auto.
      apply unions_FV_WF. intros fv Hin.
      rewrite in_map_iff in Hin. destruct Hin as [[v rhs] [Heq Hin]].
      subst. apply union_FV_WF.
      * eapply H. eauto.
      * apply bndrRuleAndUnfoldingFVs_WF.
  - simpl. apply union_FV_WF.
    + apply union_FV_WF; auto.
    + apply addBndr_WF. apply unions_FV_WF.
      intros fv Hin. rewrite in_map_iff in Hin.
      destruct Hin as [a [Heq Hin]]. destruct a as [dc pats rhs].
      subst. apply addBndrs_WF. eauto.
  - simpl. apply union_FV_WF; auto.
  - simpl. auto.
  - simpl. auto.
Qed.

(* These are invariants of the actual accumulator result, not a transfer
   along membership equality (which would be unsound for raw IntMaps). *)
Lemma exprFreeVars_WF e : IntMapProofs.WF (VarSet_IntMap (exprFreeVars e)).
Proof.
  unfold exprFreeVars, exprFVs, Base.op_z2218U__.
  apply fvVarSet_WF. apply filter_FV_WF.
  - apply RespectsVar_isLocalVar.
  - apply expr_fvs_WF.
Qed.

Lemma exprFreeVars_valid e : ValidVarSet (exprFreeVars e).
Proof.
  unfold exprFreeVars, exprFVs, Base.op_z2218U__.
  apply fvVarSet_valid. apply filter_FV_WF.
  - apply RespectsVar_isLocalVar.
  - apply expr_fvs_WF.
Qed.

Lemma exprFVs_WF e : WF_fv (exprFVs e).
Proof. apply filter_FV_WF; [apply RespectsVar_isLocalVar|apply expr_fvs_WF]. Qed.
Lemma exprsFVs_WF es : WF_fv (exprsFVs es).
Proof. apply map_union_FV_WF; intros; apply exprFVs_WF. Qed.
Lemma exprsFreeVars_WF es : IntMapProofs.WF (VarSet_IntMap (exprsFreeVars es)).
Proof. apply fvVarSet_WF, exprsFVs_WF. Qed.
Lemma exprsFreeVars_valid es : ValidVarSet (exprsFreeVars es).
Proof. apply fvVarSet_valid, exprsFVs_WF. Qed.
#[export] Hint Resolve exprFreeVars_WF exprFreeVars_valid exprsFreeVars_WF exprsFreeVars_valid : varset_inv.

Lemma filterFV_unionFV f x y : FV.filterFV f (FV.unionFV x y) =
  FV.unionFV (FV.filterFV f x) (FV.filterFV f y).
Proof. reflexivity. Qed.
Lemma filterFV_delFV f x v : FV.filterFV f (FV.delFV v x) = FV.delFV v (FV.filterFV f x).
Proof. reflexivity. Qed.
Lemma filterFV_mapUnionFV A f (g : A -> FV.FV) xs :
  FV.filterFV f (FV.mapUnionFV g xs) = FV.mapUnionFV (fun x => FV.filterFV f (g x)) xs.
Proof.
  apply functional_extensionality; intro p.
  apply functional_extensionality; intro s.
  apply functional_extensionality; intro a.
  revert a; induction xs as [|x xs IH]; intro acc; simpl; auto.
  change (FV.filterFV f (FV.mapUnionFV g xs) p s (FV.filterFV f (g x) p s acc) =
    FV.mapUnionFV (fun x => FV.filterFV f (g x)) xs p s (FV.filterFV f (g x) p s acc)).
  apply IH.
Qed.
Lemma bndrRuleAndUnfoldingFVs_empty b : bndrRuleAndUnfoldingFVs b = FV.emptyFV.
Proof. destruct b; reflexivity. Qed.
Lemma addBndr_empty b fv : addBndr b fv = FV.delFV b fv.
Proof. unfold addBndr; rewrite varTypeTyCoFVs_emptyFV; reflexivity. Qed.

Lemma filterFV_addBndrs f bs fv : FV.filterFV f (addBndrs bs fv) = addBndrs bs (FV.filterFV f fv).
Proof.
  induction bs as [|b bs IH]; unfold addBndrs in *; rewrite -> !hs_coq_foldr_list in *; simpl.
  - reflexivity.
  - rewrite -> !addBndr_empty, filterFV_delFV, IH. reflexivity.
Qed.

Lemma fvVarSet_filterFV_addBndrs f bs fv : RespectsVar f -> WF_fv fv ->
  FV.fvVarSet (FV.filterFV f (addBndrs bs fv)) [=]
  delVarSetList (FV.fvVarSet (FV.filterFV f fv)) bs.
Proof.
  intros R H. rewrite -> filterFV_addBndrs.
  apply DenotesfvVarSet, addBndrs_fv, fvVarSet_Denotes, filter_FV_WF; assumption.
Qed.

(** Unfolding tactics *)

Ltac unfold_FV :=
  repeat unfold Base.op_z2218U__, FV.filterFV, FV.fvVarSet,
       FV.unitFV, FV.fvVarAcc.


Definition disjoint E F := inter E F [=] empty.

(** ** [exprFreeVars] *)

(* Nice rewrite rules for [exprFreeVars] *)

Lemma exprFreeVars_Var: forall v, 
    isLocalVar v = true -> 
    exprFreeVars (Mk_Var v) = unitVarSet v.
Proof.
  intros v NG.
  unfold exprFreeVars, exprFVs, expr_fvs.
  unfold_FV. unfold elemVarSet; simpl.
  set_b_iff. rewrite NG.
  simpl. unfold singleton, unitVarSet, UniqSet.unitUniqSet.
  repeat (f_equal; try apply proof_irrelevance).
Qed.

Lemma exprFreeVars_global_Var: forall v, 
    isLocalVar v = false -> 
    exprFreeVars (Mk_Var v) = emptyVarSet.
Proof.
intros v NG.
unfold exprFreeVars, exprFVs, expr_fvs.
unfold_FV.
set_b_iff.
rewrite NG.
auto.
Qed.

Lemma exprFreeVars_Lit : forall i, 
    exprFreeVars (Lit i) = emptyVarSet.
Proof.
  intro. reflexivity.
Qed.

#[export] Hint Rewrite exprFreeVars_Lit : hs_simpl.

Lemma exprFreeVars_App:
  forall e1 e2,
  exprFreeVars (App e1 e2) [=] unionVarSet (exprFreeVars e1) (exprFreeVars e2).
Proof.
  intros e1 e2. change
    (FV.fvVarSet (FV.unionFV (exprFVs e1) (exprFVs e2)) [=]
      unionVarSet (FV.fvVarSet (exprFVs e1)) (FV.fvVarSet (exprFVs e2))).
  apply fvVarSet_unionFV; apply exprFVs_WF.
Qed.

#[export] Hint Rewrite exprFreeVars_App : hs_simpl.


Lemma exprFreeVars_mkLams_rev:
  forall vs e, exprFreeVars (mkLams (rev vs) e) [=] delVarSetList (exprFreeVars e) vs.
Proof.
  intros vs e.
  assert (E : forall bs, expr_fvs (mkLams bs e) = addBndrs bs (expr_fvs e)).
  { intro bs; induction bs as [|b bs IH]; unfold mkLams, addBndrs in *;
      rewrite -> !hs_coq_foldr_list in *; simpl; [reflexivity|].
    rewrite -> IH. reflexivity. }
  transitivity (delVarSetList (exprFreeVars e) (rev vs)).
  - unfold exprFreeVars, exprFVs, Base.op_z2218U__. rewrite -> E.
    apply fvVarSet_filterFV_addBndrs; [apply RespectsVar_isLocalVar|apply expr_fvs_WF].
  - apply delVarSetList_rev, exprFreeVars_WF.
Qed.

Lemma exprFreeVars_mkLams:
  forall vs e, exprFreeVars (mkLams vs e) [=] delVarSetList (exprFreeVars e) (rev vs).
Proof.
  intros vs e. replace vs with (rev (rev vs)) at 1.
  - apply exprFreeVars_mkLams_rev.
  - apply rev_involutive.
Qed.



Lemma exprFreeVars_Lam:	
  forall v e, exprFreeVars (Lam v e) [=] delVarSet (exprFreeVars e) v.
Proof.
  intros v e.
  replace (Lam v e) with (mkLams (rev [v]) e).
  - rewrite <- delVarSetList_single. apply exprFreeVars_mkLams_rev.
  - simpl. unfold mkLams. rewrite hs_coq_foldr_list. reflexivity.
Qed.

#[export] Hint Rewrite exprFreeVars_Lam : hs_simpl.

Lemma exprFreeVars_Let_NonRec:
  forall v rhs body,
  exprFreeVars (Let (NonRec v rhs) body) [=]
    unionVarSet (exprFreeVars rhs) (delVarSet (exprFreeVars body) v).
Proof.
  intros v rhs body. unfold exprFreeVars, exprFVs, Base.op_z2218U__.
  change (expr_fvs (Let (NonRec v rhs) body)) with
    (FV.unionFV (FV.unionFV (expr_fvs rhs) (bndrRuleAndUnfoldingFVs v))
      (addBndr v (expr_fvs body))).
  rewrite -> bndrRuleAndUnfoldingFVs_empty, union_empty_r, addBndr_empty,
    filterFV_unionFV, filterFV_delFV.
  apply DenotesfvVarSet, unionVarSet_unionFV_forward.
  - apply fvVarSet_Denotes, filter_FV_WF; [apply RespectsVar_isLocalVar|apply expr_fvs_WF].
  - apply delVarSet_delFV, fvVarSet_Denotes, filter_FV_WF;
      [apply RespectsVar_isLocalVar|apply expr_fvs_WF].
Qed.

Lemma Denotes_fvVarSet e: Denotes (FV.fvVarSet (expr_fvs e)) (expr_fvs e).
Proof. 
  apply fvVarSet_Denotes, expr_fvs_WF.
Qed.


Lemma exprFreeVars_Let_Rec:
  forall pairs body,
  exprFreeVars (Let (Rec pairs) body) [=]
    delVarSetList 
       (unionVarSet (exprsFreeVars (map snd pairs))
                    (exprFreeVars body))
          (map fst pairs).
Proof.
  intros pairs body.
  assert (E : exprFVs (Let (Rec pairs) body) =
    addBndrs (map fst pairs) (FV.unionFV (exprsFVs (map snd pairs)) (exprFVs body))).
  { unfold exprFVs, Base.op_z2218U__.
    change (FV.filterFV isLocalVar (addBndrs (map fst pairs)
      (FV.unionFV (FV.unionsFV (map (fun '(b,r) => FV.unionFV (expr_fvs r)
        (bndrRuleAndUnfoldingFVs b)) pairs)) (expr_fvs body))) =
      addBndrs (map fst pairs) (FV.unionFV (exprsFVs (map snd pairs))
        (FV.filterFV isLocalVar (expr_fvs body)))).
    rewrite -> filterFV_addBndrs, filterFV_unionFV. f_equal. f_equal.
    unfold FV.unionsFV, exprsFVs.
    rewrite -> filterFV_mapUnionFV, !mapUnionFV_map. f_equal.
    apply functional_extensionality; intros [b r].
    rewrite -> bndrRuleAndUnfoldingFVs_empty, union_empty_r. reflexivity. }
  unfold exprFreeVars, Base.op_z2218U__ at 1. rewrite -> E.
  apply DenotesfvVarSet, addBndrs_fv, unionVarSet_unionFV_forward.
  - apply fvVarSet_Denotes, exprsFVs_WF.
  - apply fvVarSet_Denotes, exprFVs_WF.
Qed.

Lemma exprFreeVars_Case:
  forall scrut bndr ty alts,
  exprFreeVars (Case scrut bndr ty alts) [=]
    unionVarSet (exprFreeVars scrut) (mapUnionVarSet (fun '(Mk_Alt dc pats rhs) => delVarSetList (exprFreeVars rhs) (pats ++ [bndr])) alts).
Proof.
  intros scrut bndr ty alts.
  assert (E : exprFVs (Case scrut bndr ty alts) =
    FV.unionFV (exprFVs scrut)
      (FV.mapUnionFV (fun '(Mk_Alt dc pats rhs) =>
        FV.delFV bndr (addBndrs pats (exprFVs rhs))) alts)).
  { unfold exprFVs, Base.op_z2218U__.
    change (FV.filterFV isLocalVar
      (FV.unionFV (FV.unionFV (expr_fvs scrut) (GHC.Core.TyCo.FVs.tyCoFVsOfType ty))
        (addBndr bndr (FV.unionsFV (map (fun '(Mk_Alt _ bs rhs) =>
          addBndrs bs (expr_fvs rhs)) alts)))) =
      FV.unionFV (FV.filterFV isLocalVar (expr_fvs scrut))
        (FV.mapUnionFV (fun '(Mk_Alt dc pats rhs) => FV.delFV bndr
          (addBndrs pats (FV.filterFV isLocalVar (expr_fvs rhs)))) alts)).
    rewrite -> tyCoFVsOfType_is_emptyFV, union_empty_r, addBndr_empty,
      filterFV_unionFV, filterFV_delFV.
    f_equal. unfold FV.unionsFV.
    rewrite -> filterFV_mapUnionFV, mapUnionFV_map, delFV_mapUnionFV.
    f_equal. apply functional_extensionality; intros [dc pats rhs].
    cbn [Base.id]. rewrite -> filterFV_addBndrs. reflexivity. }
  unfold exprFreeVars, Base.op_z2218U__ at 1. rewrite -> E.
  apply DenotesfvVarSet, unionVarSet_unionFV_forward.
  - apply fvVarSet_Denotes, exprFVs_WF.
  - apply mapUnionVarSet_mapUnionFV.
    clear E. induction alts as [|[dc pats rhs] alts IH]; simpl.
    + constructor.
    + constructor; [|exact IH].
      rewrite -> delVarSetList_app, delVarSetList_single.
      apply delVarSet_delFV, addBndrs_fv, fvVarSet_Denotes, exprFVs_WF.
Qed.


Lemma exprFreeVars_Cast:
  forall e co,
  exprFreeVars (Cast e co) [=] exprFreeVars e.
Proof.
  intros e co.
  unfold exprFreeVars, exprFVs, Base.op_z2218U__.
  change (expr_fvs (Cast e co)) with (FV.unionFV (expr_fvs e) (GHC.Core.TyCo.FVs.tyCoFVsOfCo co)).
  rewrite tyCoFVsOfCo_is_emptyFV.
  rewrite union_empty_r.
  reflexivity.
Qed.

(*

Definition tickishFreeVars := 
fun arg_0__ : Tickish Var => match arg_0__ with
                          | Breakpoint _ ids => mkVarSet ids
                          | _ => emptyVarSet
                          end.
*)

Lemma mkVarSet_mapUnionFV vs : 
  Denotes (mkVarSet vs) (FV.mapUnionFV FV.unitFV vs). 
Proof.
  induction vs as [|x xs IH]; [apply emptyVarSet_emptyFV|].
  rewrite -> mapUnionFV_cons.
  apply Denotes_Equal with (vs1 := unionVarSet (unitVarSet x) (mkVarSet xs)).
  - apply mkVarSet_WF.
  - apply mkVarSet_valid.
  - rewrite -> !mkVarSet_extendVarSetList.
    change (unionVarSet (unitVarSet x) (extendVarSetList emptyVarSet xs) [=]
      extendVarSetList (extendVarSet emptyVarSet x) xs).
    rewrite -> extendVarSetList_extendVarSet_iff by solve_varset_inv.
    apply unionSingle_l. solve_varset_inv.
  - apply unionVarSet_unionFV; [apply unitVarSet_unitFV|exact IH].
Qed.

(*
Lemma Denotes_tickish co : 
  Denotes (tickishFreeVars co) (tickish_fvs co).
Proof.
  elim C: co; simpl.
  all: try (apply emptyVarSet_emptyFV).
  unfold FV.mkFVs.
  apply mkVarSet_mapUnionFV.
Qed.
*)

(*
Lemma exprFreeVars_Tick:
  forall e t,
  exprFreeVars (Tick t e) [=] (unionVarSet (exprFreeVars e) (filterVarSet isLocalVar (tickishFreeVars t))).
Proof. 
  move=> e co.
  unfold exprFreeVars, exprFVs, Base.op_z2218U__.  
  unfold expr_fvs. fold expr_fvs.
  move: (expr_fvs_WF e) => [vs D].
  move: (filterVarSet_filterFV isLocalVar _ _ RespectsVar_isLocalVar D) => D1.
  move: (DenotesfvVarSet _ _ D1) => D2.
  rewrite D2.

  move: (unionVarSet_unionFV _ _ _ _ D (Denotes_tickish co)) => D3.
  move: (filterVarSet_filterFV isLocalVar _ _ RespectsVar_isLocalVar D3) => D4.
  move: (DenotesfvVarSet _ _ D4) => D5.
  rewrite D5.
  rewrite <- unionVarSet_filterVarSet; try done.
Qed.
*)

(*
Lemma exprFreeVars_Tick:
  forall e t,
  exprFreeVars (Tick t e) [=] exprFreeVars e.
Proof. done. Qed.
*)

Lemma exprFreeVars_Type:
  forall t,
  exprFreeVars (Mk_Type t) [=] emptyVarSet.
Proof.
  intros t.
  unfold exprFreeVars, exprFVs, Base.op_z2218U__.
  change (expr_fvs (Mk_Type t)) with (GHC.Core.TyCo.FVs.tyCoFVsOfType t).
  rewrite tyCoFVsOfType_is_emptyFV. reflexivity.
Qed.

Lemma exprFreeVars_Coercion:
  forall co,
  exprFreeVars (Mk_Coercion co) [=] emptyVarSet.
Proof.
  intros co.
  unfold exprFreeVars, exprFVs, Base.op_z2218U__.
  change (expr_fvs (Mk_Coercion co)) with (GHC.Core.TyCo.FVs.tyCoFVsOfCo co).
  rewrite tyCoFVsOfCo_is_emptyFV. reflexivity.
Qed.


(* ---------------------------------------------------------- *)

Lemma exprsFreeVars_nil : exprsFreeVars [] = emptyVarSet. 
Proof.
  unfold exprsFreeVars.
  unfold Base.op_z2218U__.
  unfold exprsFVs.
  unfold FV.mapUnionFV.
  unfold FV.fvVarSet.
  unfold Base.op_z2218U__ .
  unfold FV.fvVarAcc.
  simpl.
  reflexivity.
Qed.
#[export] Hint Rewrite exprsFreeVars_nil : hs_simpl.


Lemma exprsFreeVars_cons x xs : exprsFreeVars (x :: xs) [=] 
             unionVarSet (exprsFreeVars xs) (exprFreeVars x).
Proof.
  change (FV.fvVarSet (FV.unionFV (exprsFVs xs) (exprFVs x)) [=]
    unionVarSet (FV.fvVarSet (exprsFVs xs)) (FV.fvVarSet (exprFVs x))).
  apply fvVarSet_unionFV; [apply exprsFVs_WF|apply exprFVs_WF].
Qed.
#[export] Hint Rewrite exprsFreeVars_cons : hs_simpl.


Lemma subVarSet_exprFreeVars_exprsFreeVars:
  forall v rhs (pairs : list (CoreBndr * CoreExpr)) ,
  List.In (v, rhs) pairs ->
  subVarSet (exprFreeVars rhs) (exprsFreeVars (map snd pairs)) = true.
Proof.
  intros v rhs pairs H.
  apply (proj2 (subVarSet_spec _ _ (exprFreeVars_WF rhs)
    (exprsFreeVars_WF (map snd pairs)))).
  intros x M. revert H. induction pairs as [|[b r] ps IH]; intro H; [contradiction|].
  change (elemVarSet x (exprsFreeVars (r :: map snd ps)) = true).
  rewrite -> (equal_members _ _ (exprsFreeVars_cons r (map snd ps)) x),
    elemVarSet_union by solve_varset_inv.
  apply Bool.orb_true_iff. destruct H as [E|H].
  - inversion E; subst. right; exact M.
  - left. apply IH; exact H.
Qed.

Lemma subVarSet_exprsFreeVars:
  forall (es : list CoreExpr) vs,
  WF vs ->
  Forall (fun e => subVarSet (exprFreeVars e) vs = true) es ->
  subVarSet (exprsFreeVars es) vs = true.
Proof.
  intros es vs W H.
  apply (proj2 (subVarSet_spec _ _ (exprsFreeVars_WF es) W)).
  induction H as [|e es E F IH]; intros x M.
  - rewrite -> exprsFreeVars_nil in M. discriminate M.
  - rewrite -> (equal_members _ _ (exprsFreeVars_cons e es) x),
      elemVarSet_union in M by solve_varset_inv.
    apply Bool.orb_true_iff in M. destruct M as [M|M].
    + apply IH; exact M.
    + exact (proj1 (subVarSet_spec _ _ (exprFreeVars_WF e) W) E x M).
Qed.

Lemma elemVarSet_exprFreeVars_Var_false: forall v' v,
    varUnique v' <> varUnique v ->
    elemVarSet v' (exprFreeVars (Mk_Var v)) = false.
Proof.
  intros v' v Hneq.
  destruct (isLocalVar v) eqn:Hloc.
  - rewrite exprFreeVars_Var; [|auto].
    rewrite elemVarSet_unitVarSet_is_eq.
    remember (GHC.Base.op_zeze__ v' v) as b eqn:Hb.
    destruct b; [|reflexivity].
    exfalso. apply Hneq. apply varUnique_iff.
    unfold is_true. symmetry. exact Hb.
  - rewrite exprFreeVars_global_Var; [|auto].
    apply elemVarSet_emptyVarSet.
Qed.

(** Working with [exprFreeVars] *)

 
(** Working with [freeVars] *)

Ltac DVarToVar := 
    replace unionDVarSet with unionVarSet; auto;
    replace emptyDVarSet with emptyVarSet; auto;
    replace delDVarSet with delVarSet; auto;
    replace FV.fvDVarSet with FV.fvVarSet; auto;
    replace unionDVarSets with unionVarSets; auto.

Lemma no_TyCoVars bndr: (dVarTypeTyCoVars bndr) [=] emptyVarSet.
Proof.
  unfold dVarTypeTyCoVars, FV.fvDVarSet.
  rewrite varTypeTyCoFVs_emptyFV.
  reflexivity.
Qed.

Lemma no_RuleAndUnfoldingFVs l0 : 
  (FV.fvVarSet (FV.mapUnionFV bndrRuleAndUnfoldingFVs l0)) [=] emptyVarSet.
Proof.
  assert (E : FV.mapUnionFV bndrRuleAndUnfoldingFVs l0 = FV.emptyFV).
  { induction l0 as [|b bs IH]; [reflexivity|].
    rewrite -> mapUnionFV_cons, bndrRuleAndUnfoldingFVs_empty, union_empty_r. exact IH. }
  rewrite -> E. reflexivity.
Qed.

(* Helper tactic: reduce freeVarsOf (freeVars ...) without over-unfolding.
   simpl aggressively unfolds unionDVarSet/unionFVs merging VarSet internals;
   instead we use cbn with delta exclusions to keep DVarSet operations opaque. *)
Local Ltac reduce_freeVars :=
  unfold freeVarsOf; simpl fst;
  cbn -[dVarTypeTyCoVars GHC.Core.TyCo.FVs.tyCoVarsOfTypeDSet
         GHC.Core.TyCo.FVs.tyCoVarsOfCoDSet
         unionFVs unionDVarSet aFreeVar emptyDVarSet
         delBinderFV delBindersFV bndrRuleAndUnfoldingVarsDSet
         unionFVss freeVarsBind].

(* Annotation sets use the independently axiomatized DSet functions. Their
   membership-only empty contracts are not representation invariants. This
   optional annotation theorem therefore exposes the additional model evidence;
   exprFreeVars and the de-annotation roundtrip do not depend on it. *)
Section AnnotationSets.
Variables
  (typeDSet_WF : forall ty, WF (GHC.Core.TyCo.FVs.tyCoVarsOfTypeDSet ty))
  (coDSet_WF : forall co, WF (GHC.Core.TyCo.FVs.tyCoVarsOfCoDSet co)).

Lemma delBinderFV_WF b s : WF s -> WF (delBinderFV b s).
Proof.
  intro W. unfold delBinderFV, unionFVs, dVarTypeTyCoVars.
  rewrite -> varTypeTyCoFVs_emptyFV. change (WF (unionVarSet (delVarSet s b) emptyVarSet)).
  solve_varset_inv.
Qed.
Lemma delBindersFV_WF bs s : WF s -> WF (delBindersFV bs s).
Proof.
  intro W. unfold delBindersFV. rewrite -> hs_coq_foldr_list.
  induction bs as [|b bs IH]; simpl; [exact W|apply delBinderFV_WF; exact IH].
Qed.
#[local] Hint Resolve typeDSet_WF coDSet_WF delBinderFV_WF delBindersFV_WF : varset_inv.

Lemma dVarTypeTyCoVars_WF b : WF (dVarTypeTyCoVars b).
Proof. unfold dVarTypeTyCoVars; rewrite -> varTypeTyCoFVs_emptyFV. apply emptyVarSet_WF. Qed.
Lemma bndrRuleAndUnfoldingVarsDSet_WF b : WF (bndrRuleAndUnfoldingVarsDSet b).
Proof. unfold bndrRuleAndUnfoldingVarsDSet; rewrite -> bndrRuleAndUnfoldingFVs_empty. apply emptyVarSet_WF. Qed.
Lemma unionFVs_WF s t : WF s -> WF t -> WF (unionFVs s t).
Proof. apply unionVarSet_WF. Qed.
Lemma unionFVss_WF ss : (forall s, List.In s ss -> WF s) -> WF (unionFVss ss).
Proof. apply unionVarSets_WF. Qed.
#[local] Hint Resolve dVarTypeTyCoVars_WF bndrRuleAndUnfoldingVarsDSet_WF unionFVs_WF unionFVss_WF : varset_inv.

Lemma freeVarsOf_freeVars_WF e : WF (freeVarsOf (freeVars e)).
Proof.
  apply (core_induct e); intros.
  - destruct (isLocalVar v) eqn:E; unfold freeVars, freeVarsOf; rewrite -> E.
    + change (WF (unionFVs (unionFVs (aFreeVar v) (dVarTypeTyCoVars v))
        (GHC.Core.TyCo.FVs.tyCoVarsOfTypeDSet (Core.varMult v)))).
      apply unionFVs_WF; [apply unionFVs_WF|apply typeDSet_WF].
      * apply unitVarSet_WF.
      * apply dVarTypeTyCoVars_WF.
    + apply emptyVarSet_WF.
  - apply emptyVarSet_WF.
  - change (WF (unionFVs (freeVarsOf (freeVars e1)) (freeVarsOf (freeVars e2)))). solve_varset_inv.
  - unfold freeVars; fold freeVars. destruct (freeVars e0) as [s ann] eqn:E.
    change (WF (unionFVs (GHC.Core.TyCo.FVs.tyCoVarsOfTypeDSet (Id.idType v))
      (delBinderFV v s))).
    apply unionFVs_WF; [apply typeDSet_WF|apply delBinderFV_WF; exact H].
  - destruct binds as [b rhs|ps].
    + change (WF (unionFVs (unionFVs (freeVarsOf (freeVars rhs))
        (delBinderFV b (freeVarsOf (freeVars body)))) (bndrRuleAndUnfoldingVarsDSet b))).
      apply unionFVs_WF; [apply unionFVs_WF|apply bndrRuleAndUnfoldingVarsDSet_WF].
      * exact H.
      * apply delBinderFV_WF. exact H0.
    + unfold freeVars; fold freeVars.
      destruct (List.unzip ps) as [bs rs].
      change (WF (delBindersFV bs (unionFVs
          (Foldable.foldr (fun x s => unionFVs (freeVarsOf x) s) (freeVarsOf (freeVars body))
            (Base.map (fun p => freeVars (snd p)) ps))
          (FV.fvDVarSet (FV.mapUnionFV bndrRuleAndUnfoldingFVs bs))))).
      apply delBindersFV_WF, unionFVs_WF.
      * rewrite -> hs_coq_foldr_list.
        induction ps as [|[b rhs] ps IH]; simpl; [exact H0|].
        apply unionFVs_WF.
        -- apply H with b. left; reflexivity.
        -- apply IH. intros b' rhs' I. apply H with b'. right; exact I.
      * unfold FV.fvDVarSet. apply fvVarSet_WF, map_union_FV_WF.
        intros; apply bndrRuleAndUnfoldingFVs_WF.
  - unfold freeVars; fold freeVars.
    rewrite -> NestedRecursionHelpers.map_unzip.
    destruct (List.unzip _) as [ss alts'] eqn:Z.
    change (WF (unionFVs (unionFVs (delBinderFV bndr (unionFVss ss))
      (freeVarsOf (freeVars scrut))) (GHC.Core.TyCo.FVs.tyCoVarsOfTypeDSet ty))).
    apply unionFVs_WF; [apply unionFVs_WF; [apply delBinderFV_WF|exact H]|apply typeDSet_WF].
    apply unionFVss_WF. rewrite <- (unzip_fst _ _ _ Z), List.map_map.
    intros s I. apply in_map_iff in I. destruct I as [[dc pats rhs] [E I]]; simpl in E; subst s.
    apply delBindersFV_WF. eapply H0; exact I.
  - change (WF (unionFVs (freeVarsOf (freeVars e0)) (GHC.Core.TyCo.FVs.tyCoVarsOfCoDSet co))). solve_varset_inv.
  - apply typeDSet_WF.
  - apply coDSet_WF.
Qed.
#[local] Hint Resolve freeVarsOf_freeVars_WF : varset_inv.

Local Ltac annotation_sets :=
  unfold Equal in *; let a := fresh "q" in intro a;
  repeat match goal with
  | H : forall v, _ <-> _ |- _ => specialize (H a)
  end;
  set_b_iff; set_iff; tauto.

Lemma fold_freeVars_equal (ps : list (CoreBndr * CoreExpr)) s t :
  WF s -> WF t -> s [=] t ->
  (forall b rhs, List.In (b,rhs) ps -> freeVarsOf (freeVars rhs) [=] exprFreeVars rhs) ->
  let r := Foldable.foldr (fun ann acc => unionFVs (freeVarsOf ann) acc) s
    (map (fun p => freeVars (snd p)) ps) in
  WF r /\ r [=] unionVarSet (exprsFreeVars (map snd ps)) t.
Proof.
  intros W V E H. rewrite -> hs_coq_foldr_list.
  revert H. induction ps as [|[b rhs] ps IH]; intro H.
  - split; [exact W|]. change (s [=] unionVarSet emptyVarSet t). annotation_sets.
  - destruct (IH (fun b rhs I => H b rhs (or_intror I))) as [X Y].
    cbn [map snd fold_right] in X,Y |- *.
    pose proof (freeVarsOf_freeVars_WF rhs) as Z.
    split; [apply unionFVs_WF; assumption|].
    pose proof (H b rhs (or_introl Logic.eq_refl)) as F.
    pose proof (exprsFreeVars_cons rhs (map snd ps)) as L.
    unfold unionFVs. annotation_sets.
Qed.

Lemma delVarSetList_equal s t bs : WF s -> WF t -> s [=] t ->
  delVarSetList s bs [=] delVarSetList t bs.
Proof.
  intros W V E q. rewrite -> !delVarSetList_iff by assumption.
  rewrite -> E. reflexivity.
Qed.

Lemma delBindersFV_equal bs s : WF s -> delBindersFV bs s [=] delVarSetList s bs.
Proof.
  intro W. unfold delBindersFV. rewrite -> hs_coq_foldr_list.
  induction bs as [|b bs IH].
  - rewrite -> delVarSetList_nil. reflexivity.
  - cbn [fold_right]. transitivity (delVarSet (delVarSetList s bs) b).
    + pose proof (delBindersFV_WF bs s W) as V.
      pose proof (dVarTypeTyCoVars_WF b) as Y.
      pose proof (no_TyCoVars b) as T.
      unfold delBinderFV, unionFVs. DVarToVar. annotation_sets.
    + symmetry; apply delVarSetList_cons2; exact W.
Qed.

Lemma fold_union_members ss s q :
  (forall t, List.In t ss -> WF t) -> WF s ->
  (In q (fold_right unionVarSet s ss) <->
    In q s \/ exists t, List.In t ss /\ In q t).
Proof.
  intros W V. revert W. induction ss as [|t ts IH]; intro W.
  - simpl. split; [auto|intros [H|[u [I M]]]; [exact H|contradiction]].
  - assert (Wt : WF t) by (apply W; left; reflexivity).
    assert (Wts : WF (fold_right unionVarSet s ts)) by
      (apply fold_unionVarSet_WF; [intros u I; apply W; right; exact I|exact V]).
    cbn [fold_right]. rewrite -> unionVarSet_union, union_iff by assumption.
    rewrite -> IH by (intros u I; apply W; right; exact I).
    clear W IH V. simpl List.In. firstorder subst; auto.
Qed.

Lemma unionFVss_map_members A (f : A -> VarSet) xs q :
  (forall x, List.In x xs -> WF (f x)) ->
  (In q (unionFVss (map f xs)) <-> exists x, List.In x xs /\ In q (f x)).
Proof.
  intro W. destruct xs as [|x xs].
  - change (In q empty <-> exists x, List.In x [] /\ In q (f x)).
    rewrite -> empty_iff. firstorder.
  - change (In q (fold_right unionVarSet (f x) (map f xs)) <->
      exists y, List.In y (x :: xs) /\ In q (f y)).
    rewrite -> fold_union_members.
    + clear W. setoid_rewrite in_map_iff.
      simpl List.In. firstorder subst; auto.
    + intros s I. apply in_map_iff in I. destruct I as [y [E I]]; subst s.
      apply W; right; exact I.
    + apply W; left; reflexivity.
Qed.

Lemma mapUnionVarSet_members A (f : A -> VarSet) xs q :
  (forall x, List.In x xs -> WF (f x)) ->
  (In q (mapUnionVarSet f xs) <-> exists x, List.In x xs /\ In q (f x)).
Proof.
  intro W. revert W; induction xs as [|x xs IH]; intro W.
  - change (In q empty <-> exists x, List.In x [] /\ In q (f x)).
    rewrite -> empty_iff. firstorder.
  - change (In q (unionVarSet (f x) (mapUnionVarSet f xs)) <->
      exists y, List.In y (x :: xs) /\ In q (f y)).
    rewrite -> unionVarSet_union, union_iff.
    + rewrite -> IH by (intros y I; apply W; right; exact I).
      clear W IH. simpl List.In. firstorder subst; auto.
    + apply W; left; reflexivity.
    + apply mapUnionVarSet_WF; intros y I; apply W; right; exact I.
Qed.

Lemma unionFVss_map_del_equal A (f g : A -> VarSet) xs b :
  (forall x, List.In x xs -> WF (f x)) ->
  (forall x, List.In x xs -> WF (g x)) ->
  (forall x, List.In x xs -> delVarSet (f x) b [=] g x) ->
  delBinderFV b (unionFVss (map f xs)) [=] mapUnionVarSet g xs.
Proof.
  intros W V E q.
  assert (S : WF (unionFVss (map f xs))).
  { apply unionFVss_WF. intros s I. apply in_map_iff in I.
    destruct I as [x [H I]]; subst s; apply W; exact I. }
  unfold delBinderFV, unionFVs. DVarToVar.
  rewrite -> unionVarSet_union, union_iff by
    (solve [apply delVarSet_WF; exact S | apply dVarTypeTyCoVars_WF]).
  rewrite -> delVarSet_remove, remove_iff by exact S.
  rewrite -> unionFVss_map_members by exact W.
  rewrite -> (no_TyCoVars b q), emptyVarSet_empty, empty_iff.
  rewrite -> mapUnionVarSet_members by exact V.
  split.
  - intros [[ [x [I M]] N]|F]; [|contradiction].
    exists x; split; [exact I|]. apply (proj1 (E x I q)).
    rewrite -> delVarSet_remove, remove_iff by (apply W; exact I). auto.
  - intros [x [I M]]. apply (proj2 (E x I q)) in M.
    rewrite -> delVarSet_remove, remove_iff in M by (apply W; exact I).
    destruct M as [M N]. left; split; [exists x; auto|exact N].
Qed.

Lemma freeVarsOf_freeVars_revised:
  forall e,
  (freeVarsOf (freeVars e)) [=] exprFreeVars e.
Proof.
  intro e; apply (core_induct e).
  - (* Var *)
    intros x.
    destruct (isLocalVar x) eqn:IS.
    + rewrite exprFreeVars_Var; [|auto].
       reduce_freeVars. rewrite IS. cbv beta iota.
       unfold unionFVs, aFreeVar. DVarToVar.
       pose proof (no_TyCoVars x) as T.
       pose proof (tyCoVarsOfTypeDSet_empty (varMult x)) as U.
       pose proof (dVarTypeTyCoVars_WF x) as W.
       pose proof (typeDSet_WF (varMult x)) as V.
       annotation_sets.
    + rewrite exprFreeVars_global_Var; [|auto].
      reduce_freeVars. rewrite IS. cbv beta iota. reflexivity.
  - (* Lit *)
    intros l. rewrite exprFreeVars_Lit. reflexivity.
  - (* App *)
     intros e1 e2 h1 h2. rewrite exprFreeVars_App.
     change (unionFVs (freeVarsOf (freeVars e1)) (freeVarsOf (freeVars e2)) [=]
       unionVarSet (exprFreeVars e1) (exprFreeVars e2)).
     unfold unionFVs. DVarToVar.
     pose proof (freeVarsOf_freeVars_WF e1) as W1.
     pose proof (freeVarsOf_freeVars_WF e2) as W2. annotation_sets.
  - (* Lam *)
     intros v e0 H.
     rewrite exprFreeVars_Lam.
     pose proof (freeVarsOf_freeVars_WF e0) as W.
     unfold freeVars; fold freeVars.
     destruct (freeVars e0). unfold freeVarsOf.
     unfold unionFVs, delBinderFV. DVarToVar.
     pose proof (no_TyCoVars v) as T.
     pose proof (tyCoVarsOfTypeDSet_empty (Id.idType v)) as U.
     pose proof (dVarTypeTyCoVars_WF v) as V.
     pose proof (typeDSet_WF (Id.idType v)) as Y.
     annotation_sets.
  - (* Let *)
    intros binds body H H0.
    destruct binds.
     + (* NonRec *)
       rewrite exprFreeVars_Let_NonRec.
       change (unionFVs (unionFVs (freeVarsOf (freeVars e0))
         (delBinderFV c (freeVarsOf (freeVars body)))) (bndrRuleAndUnfoldingVarsDSet c) [=]
         unionVarSet (exprFreeVars e0) (delVarSet (exprFreeVars body) c)).
       unfold delBinderFV, unionFVs, bndrRuleAndUnfoldingVarsDSet.
       rewrite -> bndrRuleAndUnfoldingFVs_empty. DVarToVar.
       rewrite -> fvVarSet_emptyFV.
       pose proof (no_TyCoVars c) as T.
       pose proof (dVarTypeTyCoVars_WF c) as V.
       pose proof (freeVarsOf_freeVars_WF e0) as W1.
       pose proof (freeVarsOf_freeVars_WF body) as W2. annotation_sets.
     + (* Rec *)
       rewrite exprFreeVars_Let_Rec.
       destruct (fold_freeVars_equal l (freeVarsOf (freeVars body)) (exprFreeVars body)
         (freeVarsOf_freeVars_WF body) (exprFreeVars_WF body) H0 H) as [X Y].
       unfold freeVars; fold freeVars.
       destruct (List.unzip l) as [bs rs] eqn:Z.
       change (delBindersFV bs (unionFVs
         (Foldable.foldr (fun ann acc => unionFVs (freeVarsOf ann) acc)
           (freeVarsOf (freeVars body)) (map (fun p => freeVars (snd p)) l))
         (FV.fvDVarSet (FV.mapUnionFV bndrRuleAndUnfoldingFVs bs))) [=]
         delVarSetList (unionVarSet (exprsFreeVars (map snd l)) (exprFreeVars body)) (map fst l)).
       rewrite -> (unzip_fst _ _ _ Z).
       assert (R : WF (FV.fvVarSet (FV.mapUnionFV bndrRuleAndUnfoldingFVs bs))).
       { apply fvVarSet_WF, map_union_FV_WF; intros; apply bndrRuleAndUnfoldingFVs_WF. }
       transitivity (delVarSetList (unionFVs
         (Foldable.foldr (fun ann acc => unionFVs (freeVarsOf ann) acc)
           (freeVarsOf (freeVars body)) (map (fun p => freeVars (snd p)) l))
         (FV.fvDVarSet (FV.mapUnionFV bndrRuleAndUnfoldingFVs bs))) bs).
       * apply delBindersFV_equal, unionFVs_WF; assumption.
       * apply delVarSetList_equal.
         -- apply unionFVs_WF; assumption.
         -- apply unionVarSet_WF; [apply exprsFreeVars_WF|apply exprFreeVars_WF].
         -- pose proof (no_RuleAndUnfoldingFVs bs) as T.
            unfold unionFVs. DVarToVar. annotation_sets.
  - (* Case *)
    intros scrut bndr ty alts H H0.
    rewrite exprFreeVars_Case.
    unfold freeVars; fold freeVars.
    rewrite NestedRecursionHelpers.map_unzip.
     destruct List.unzip as [alt_fvs_s alts2] eqn:Z.
     assert (L : alt_fvs_s = map (fun '(Mk_Alt _ pats rhs) =>
       delBindersFV pats (freeVarsOf (freeVars rhs))) alts).
     { rewrite <- (unzip_fst _ _ _ Z), List.map_map.
       apply map_ext; intros [dc pats rhs]; reflexivity. }
     assert (Q : delBinderFV bndr (unionFVss alt_fvs_s) [=]
       mapUnionVarSet (fun '(Mk_Alt _ pats rhs) =>
         delVarSetList (exprFreeVars rhs) (pats ++ [bndr])) alts).
     { rewrite -> L. apply unionFVss_map_del_equal.
       - intros [dc pats rhs] I. apply delBindersFV_WF, freeVarsOf_freeVars_WF.
       - intros [dc pats rhs] I. apply delVarSetList_WF, exprFreeVars_WF.
       - intros [dc pats rhs] I. rewrite -> delVarSetList_app, delVarSetList_single.
         apply delVarSet_m.
         + apply delBindersFV_WF, freeVarsOf_freeVars_WF.
         + apply delVarSetList_WF, exprFreeVars_WF.
         + transitivity (delVarSetList (freeVarsOf (freeVars rhs)) pats).
           * apply delBindersFV_equal, freeVarsOf_freeVars_WF.
           * apply delVarSetList_equal; [apply freeVarsOf_freeVars_WF|apply exprFreeVars_WF|].
             eapply H0; exact I.
         + apply E.eq_refl. }
     assert (WAlt : WF (delBinderFV bndr (unionFVss alt_fvs_s))).
     { apply delBinderFV_WF, unionFVss_WF. rewrite -> L.
       intros s I. apply in_map_iff in I. destruct I as [[dc pats rhs] [F I]]; subst s.
       apply delBindersFV_WF, freeVarsOf_freeVars_WF. }
     assert (VAlt : WF (mapUnionVarSet (fun '(Mk_Alt _ pats rhs) =>
       delVarSetList (exprFreeVars rhs) (pats ++ [bndr])) alts)).
     { apply mapUnionVarSet_WF. intros [dc pats rhs] I.
       apply delVarSetList_WF, exprFreeVars_WF. }
     change (unionFVs (unionFVs (delBinderFV bndr (unionFVss alt_fvs_s))
       (freeVarsOf (freeVars scrut))) (GHC.Core.TyCo.FVs.tyCoVarsOfTypeDSet ty) [=]
       unionVarSet (exprFreeVars scrut) (mapUnionVarSet (fun '(Mk_Alt _ pats rhs) =>
         delVarSetList (exprFreeVars rhs) (pats ++ [bndr])) alts)).
     pose proof (tyCoVarsOfTypeDSet_empty ty) as T.
     pose proof (typeDSet_WF ty) as V.
     pose proof (freeVarsOf_freeVars_WF scrut) as W.
     unfold unionFVs. DVarToVar. clear H0 Z L. annotation_sets.

  - (* Cast *)
     intros e0 co H. rewrite exprFreeVars_Cast.
     change (unionFVs (freeVarsOf (freeVars e0)) (GHC.Core.TyCo.FVs.tyCoVarsOfCoDSet co) [=]
       exprFreeVars e0).
     pose proof (tyCoVarsOfCoDSet_empty co) as T.
     pose proof (coDSet_WF co) as V.
     pose proof (freeVarsOf_freeVars_WF e0) as W.
     unfold unionFVs. DVarToVar. annotation_sets.
  - (* Type *)
    intros t. rewrite exprFreeVars_Type.
    unfold freeVars, freeVarsOf. simpl.
    rewrite tyCoVarsOfTypeDSet_empty. reflexivity.
  - (* Coercion *)
    intros co. rewrite exprFreeVars_Coercion.
    unfold freeVars, freeVarsOf. simpl.
    rewrite tyCoVarsOfCoDSet_empty. reflexivity.
Qed.

End AnnotationSets.

(* Helper for the Rec case of deAnnotate_freeVars *)
Lemma rec_roundtrip :
  forall (l : list (CoreBndr * CoreExpr)),
    (forall v rhs, List.In (v, rhs) l -> deAnnotate (freeVars rhs) = rhs) ->
    forall l0 l1,
      List.unzip l = (l0, l1) ->
      Coq.Lists.List.flat_map
        (fun '(pair v rhs) => cons (pair v (deAnnotate rhs)) nil)
        (List.zip l0 (GHC.Base.map (fun x : CoreBndr * CoreExpr => freeVars x.2) l)) = l.
Proof.
  induction l as [|[v0 rhs0] l' IHl']; simpl; intros.
  - inversion H0. reflexivity.
  - destruct (List.unzip l') as [ls rs] eqn:Hl'.
    injection H0 as Hl0eq Hl1eq. subst l0 l1. simpl.
    assert (Hrhs: deAnnotate (freeVars rhs0) = rhs0).
    { eapply H. left; reflexivity. }
    rewrite Hrhs.
    assert (Htail: flat_map (fun '(v, rhs) => [(v, deAnnotate rhs)])
                            (List.zip ls (GHC.Base.map (fun x : CoreBndr * CoreExpr => freeVars x.2) l')) = l').
    { specialize (IHl' (fun v rhs Hin => H v rhs (or_intror Hin)) ls rs Logic.eq_refl).
      exact IHl'. }
    rewrite Htail. reflexivity.
Qed.

(* Helper for the Case case of deAnnotate_freeVars *)
Lemma case_alts_roundtrip' :
  forall (alts : list (Alt CoreBndr)),
    (forall dc pats rhs, List.In (Mk_Alt dc pats rhs) alts -> deAnnotate (freeVars rhs) = rhs) ->
    GHC.Base.map deAnnAlt
      (snd (NestedRecursionHelpers.mapAndUnzipFix
        (fun '(Mk_Alt con args rhs) =>
           let rhs2 := freeVars rhs in
           (delBindersFV args (freeVarsOf rhs2), Mk_AnnAlt con args rhs2)) alts)) = alts.
Proof.
  induction alts as [|[con pats rhs] alts' IHalts']; simpl; intros.
  - reflexivity.
  - destruct (NestedRecursionHelpers.mapAndUnzipFix
                (fun '(Mk_Alt con0 args rhs0) =>
                   let rhs2 := freeVars rhs0 in
                   (delBindersFV args (freeVarsOf rhs2), Mk_AnnAlt con0 args rhs2))
                alts') as [ls2 as2] eqn:Hmu'.
    simpl.
    assert (Hrhs : deAnnotate (freeVars rhs) = rhs).
    { eapply H. left. reflexivity. }
    unfold deAnnAlt. unfold deAnnotate in Hrhs |- *.
    destruct (freeVars rhs) as [fa aa]. simpl. simpl in Hrhs.
    rewrite Hrhs. f_equal.
    apply IHalts'. intros. eapply H. right. eassumption.
Qed.

Lemma deAnnotate_freeVars:
  forall e, deAnnotate (freeVars e) = e.
Proof.
  intro e; apply (core_induct e);
    intros; simpl; try reflexivity;
      try solve [destruct (freeVars e0) eqn:Hfv; simpl in H; rewrite H; reflexivity].
  - (* Var *) destruct (isLocalVar v); reflexivity.
  - (* App *) symmetry. f_equal.
    + destruct (freeVars e1) eqn:fv. rewrite <- H; reflexivity.
    + destruct (freeVars e2) eqn:fv. rewrite <- H0; reflexivity.
  - (* Lam *) destruct (freeVars e0) eqn:Hfv.
    unfold deAnnotate in H. simpl; rewrite H; reflexivity.
  - (* Let *) destruct binds; simpl.
    + (* NonRec *)
      destruct (freeVars body) eqn:Hfv. rewrite <- H0.
      destruct (freeVars e0) eqn:Hfv'. rewrite <- H. reflexivity.
    + (* Rec *)
      destruct (List.unzip l) eqn:Hl.
      simpl.
      f_equal.
      * f_equal. exact (rec_roundtrip l H l0 l1 Hl).
      * exact H0.
  - (* Case *)
    destruct NestedRecursionHelpers.mapAndUnzipFix eqn:Hmu. simpl.
    destruct (freeVars scrut) eqn:Hfv. simpl in H. rewrite H.
    f_equal.
    (* Goal: GHC.Base.map deAnnAlt l0 = alts *)
    assert (l0 = snd (NestedRecursionHelpers.mapAndUnzipFix
        (fun '(Mk_Alt con args rhs) =>
           let rhs2 := freeVars rhs in
           (delBindersFV args (freeVarsOf rhs2), Mk_AnnAlt con args rhs2)) alts)) as Hl0.
    { rewrite Hmu. reflexivity. }
    rewrite Hl0.
    apply case_alts_roundtrip'. exact H0.
Qed.

Lemma deAnnotate'_snd_freeVars:
  forall e, deAnnotate' (snd (freeVars e)) = e.
Proof.
  intros. symmetry. rewrite <- deAnnotate_freeVars at 1.
  destruct (freeVars e); reflexivity.
Qed.


Lemma collectNAnnBndrs_freeVars_mkLams:
  forall vs rhs,
  collectNAnnBndrs (length vs) (freeVars (mkLams vs rhs)) = (vs, freeVars rhs).
Proof.
  intros vs rhs.
  name_collect collect.
  assert (forall vs1 vs0 n, 
             n = length vs1 ->
             collect n vs0 (freeVars (mkLams vs1 rhs)) = (List.app (List.reverse vs0)  vs1, freeVars rhs)).
  { induction vs1; intros.
    + simpl in *.  subst. 
      unfold mkLams.
      unfold_Foldable.
      simpl. 
      rewrite List.app_nil_r.
      auto.
    + simpl in *. 
      destruct n; inversion H.
      pose (IH := IHvs1 (cons a vs0) n H1). clearbody IH. clear IHvs1.
      unfold mkLams in IH.
      unfold Foldable.foldr in IH.
      unfold Foldable.Foldable__list in IH.
      unfold Foldable.foldr__ in IH.
      simpl. 
      remember (freeVars (Foldable.Foldable__list_foldr Lam rhs vs1)) as fv.
      destruct fv.
      rewrite <-  H1.
      rewrite reverse_append in IH.
      auto.
  }       
  pose (K := H vs nil (length vs) Logic.eq_refl).
  simpl in K.
  auto.
Qed.
