From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat.
Set Bullet Behavior "Strict Subproofs".

Require Import Coq.Lists.List.

Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import Data.Foldable.
Require Import Data.Traversable.

Require Import Proofs.GHC.Base.
Require Import Proofs.Data.Foldable.
Require Import Proofs.Data.Traversable.

Require Import BasicTypes.
Require Import Id.
Require Import Core.
Require Import CoreUtils.
Require Import CoreSubst.

Require Import Proofs.Core.
Require Import Proofs.CoreInduct.
Require Import Proofs.CoreSubst.
Require Import Proofs.ScopeInvariant.
Require Import Proofs.Forall.
Require Import Proofs.OrdList.
Require Import Proofs.Var.
Require Import Proofs.VarSet.
Require Import Proofs.VarSetStrong.
Require Import Proofs.VarEnv.

Require Import CSE.
Require Import TrieMap.
Require Import Proofs.TrieMap.

Opaque GHC.Base.hs_string__.

(** * Evaluating CSE *)
(* We really ought to be able to automate these things *)

Lemma cseExpr_App env f a :
  cseExpr env (App f a) = App (cseExpr env f) (tryForCSE env a).
Proof. reflexivity. Qed.
#[export] Hint Rewrite cseExpr_App : hs_simpl.

Lemma cseExpr_Let env bind e :
  cseExpr env (Let bind e) = let: (env', bind') := cseBind NotTopLevel env bind
                             in Let bind' (cseExpr env' e).
Proof. reflexivity. Qed.
#[export] Hint Rewrite cseExpr_Let : hs_simpl.

(* The RHS and body environments are distinct in the five-argument cse_bind. *)
Lemma cseBind_NonRec toplevel env b e :
  cseBind toplevel env (NonRec b e) =
    let: (env1, b1)       := addBinder env b in
    let: (env2, (b2, e2)) := cse_bind toplevel env env1 (b,e) b1 in
    (env2, NonRec b2 e2).
Proof. reflexivity. Qed.
#[export] Hint Rewrite cseBind_NonRec : hs_simpl.

(** * Stripping ticks *)

Lemma stripTicksE_id {b} p (e : Expr b) :
  stripTicksE p e = e.
Proof.
  apply (core_induct' e); intros; try reflexivity.
  - (* App *) change (App (stripTicksE p e1) (stripTicksE p e2) = App e1 e2).
    rewrite H H0. reflexivity.
  - (* Lam *) change (Lam v (stripTicksE p e0) = Lam v e0).
    rewrite H. reflexivity.
  - (* Let *)
    destruct binds as [v0 rhs0 | pairs].
    + change (Let (NonRec v0 (stripTicksE p rhs0)) (stripTicksE p body) = Let (NonRec v0 rhs0) body).
      rewrite H H0. reflexivity.
    + change (Let (Rec (GHC.Base.map (fun '(pair b0 e0) => pair b0 (stripTicksE p e0)) pairs)) (stripTicksE p body) = Let (Rec pairs) body).
      rewrite H0. f_equal. f_equal.
      transitivity (GHC.Base.map id pairs).
      { rewrite hs_coq_map.
        apply Coq.Lists.List.map_ext_in.
        intros [v0 rhs0] HIn. simpl. f_equal.
        apply (H v0 rhs0 HIn). }
      { apply map_id. }
  - (* Case *)
    change (Case (stripTicksE p scrut) bndr ty
                 (GHC.Base.map (fun '(Mk_Alt c bs e0) => Mk_Alt c bs (stripTicksE p e0)) alts) =
            Case scrut bndr ty alts).
    rewrite H. f_equal.
    transitivity (GHC.Base.map id alts).
    { rewrite hs_coq_map.
      apply Coq.Lists.List.map_ext_in.
      intros [dc pats rhs0] HIn. simpl. f_equal.
      apply (H0 dc pats rhs0 HIn). }
    { apply map_id. }
  - (* Cast *) change (Cast (stripTicksE p e0) co = Cast e0 co).
    rewrite H. reflexivity.
Qed.

#[export] Hint Rewrite @stripTicksE_id : hs_simpl.
#[export] Hint Rewrite (@stripTicksE_id CoreBndr) : hs_simpl.

(* Helper: extract the internal OrdList-valued traversal from stripTicksT
   so we can prove it always returns nilOL (since Expr has no Tick constructor). *)
Section StripTicksT_go.
  Variable b : Type.

  Fixpoint stripTicksT_go (e : Expr b) : OrdList.OrdList GHC.Types.Tickish.CoreTickish :=
    match e with
    | App e1 e2 => OrdList.appOL (stripTicksT_go e1) (stripTicksT_go e2)
    | Lam _ e0 => stripTicksT_go e0
    | Let bd e0 => OrdList.appOL (stripTicksT_go_bs bd) (stripTicksT_go e0)
    | Case e0 _ _ alts =>
        OrdList.appOL (stripTicksT_go e0)
              (OrdList.concatOL (GHC.Base.map (fun '(Mk_Alt _ _ rhs) => stripTicksT_go rhs) alts))
    | Cast e0 _ => stripTicksT_go e0
    | _ => OrdList.nilOL
    end
  with stripTicksT_go_bs (bd : Bind b) : OrdList.OrdList GHC.Types.Tickish.CoreTickish :=
    match bd with
    | NonRec _ e0 => stripTicksT_go e0
    | Rec pairs => OrdList.concatOL (GHC.Base.map (fun '(pair _ rhs) => stripTicksT_go rhs) pairs)
    end.

  Lemma stripTicksT_go_nilOL : forall e, stripTicksT_go e = OrdList.nilOL.
  Proof.
    fix IH 1.
    destruct e; cbn [stripTicksT_go stripTicksT_go_bs]; try reflexivity.
    - (* App *) rewrite !IH. reflexivity.
    - (* Lam *) apply IH.
    - (* Let *) rewrite IH. rewrite appOL_nilOL_right.
      destruct b0 as [v rhs | pairs]; cbn [stripTicksT_go_bs].
      + apply IH.
      + induction pairs as [|[v0 rhs0] rest IHrest].
        * reflexivity.
        * cbn [GHC.Base.map]. rewrite hs_coq_map.
          simpl. rewrite IH. simpl. rewrite <- hs_coq_map. exact IHrest.
    - (* Case *) rewrite IH. simpl.
      induction l as [|[dc pats rhs0] rest IHrest].
      + reflexivity.
      + cbn [GHC.Base.map]. rewrite hs_coq_map.
        simpl. rewrite IH. simpl. rewrite <- hs_coq_map. exact IHrest.
    - (* Cast *) apply IH.
  Qed.

End StripTicksT_go.

Lemma stripTicksT_nil {b} p (e : Expr b) :
  stripTicksT p e = nil.
Proof.
  (* stripTicksT p e unfolds to OrdList.fromOL (stripTicksT_go b e) *)
  change (OrdList.fromOL (stripTicksT_go b e) = nil).
  rewrite stripTicksT_go_nilOL.
  reflexivity.
Qed.

#[export] Hint Rewrite @stripTicksT_nil : hs_simpl.
#[export] Hint Rewrite (@stripTicksT_nil CoreBndr) : hs_simpl.

(** * Well-scopedness for CSE *)

(* vars = set of variables in scope AFTER `cs_subst` is applied *)
Record WellScopedCSEnv (env : CSEnv) (vars : VarSet) : Prop :=
 IsWellScopedCSEnv
   { ws_subst   : WellScoped_Subst (cs_subst env) vars
   ; ws_map     : const True (cs_map env)
   ; ws_rec_map : const True (cs_rec_map env) }.

Lemma tryForCSE_simpl env expr :
  tryForCSE env expr = match lookupCSEnv env (cseExpr env expr) with
                       | Some e => e
                       | None   => cseExpr env expr
                       end.
Proof.
  unfold tryForCSE, try_for_cse.
  destruct (lookupCSEnv env (cseExpr env expr)); reflexivity.
Qed.

(* Inherited well-scopedness admission, outside the control-flow equations. *)
Definition WS_cseExpr vars env e :
  WellScopedCSEnv env             vars ->
  WellScoped      e               vars ->
  WellScoped      (cseExpr env e) (getSubstInScopeVars (cs_subst env)).
Proof. Admitted.
