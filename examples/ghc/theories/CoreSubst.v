(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".


From Coq Require Import ssreflect ssrbool.


Require Import GHC.Base.
Import GHC.Base.Notations.
Import GHC.Base.ManualNotations.

Require Import Core.
Require Import GHC.Core.TyCo.Subst.
Require Import CoreSubst.  (* imported after GHC.Core.TyCo.Subst to shadow substCo/substTyUnchecked *)
Require Import Coq.Lists.List.

Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.
Require Import Proofs.Data.Foldable.
Require Import Proofs.Data.Traversable. 

Require Import Proofs.Axioms.
Require Import Proofs.GhcTactics.
Require Import Proofs.CoreInduct.
Require Import Proofs.Core.
Require Import Proofs.VarSet.
Require Import Proofs.VarSetFSet.
Require Import Proofs.VarSetInvariant.
Require Import Proofs.VarSetStrong.
Require Import Proofs.VarEnv.
Require Import Proofs.Var.
Require Import Proofs.ScopeInvariant.
Require Import Proofs.Forall.
Require Import Lia.



(* Make sure that we don't try to reduce any strings to normal form. *)
Opaque Base.hs_string__.
Opaque HsToRocq.Err.default.

Open Scope nat_scope.
Set Bullet Behavior "Strict Subproofs".

#[local] Hint Resolve emptyVarSet_WF unitVarSet_WF mkVarSet_WF
  extendVarSet_WF extendVarSetList_WF delVarSet_WF delVarSetList_WF
  filterVarSet_WF emptyVarSet_valid unitVarSet_valid mkVarSet_valid
  extendVarSet_valid extendVarSetList_valid delVarSet_valid delVarSetList_valid
  filterVarSet_valid minusDom_WF minusDom_valid
  emptyVarEnv_WF extendVarEnv_WF delVarEnv_WF : core.
#[local] Hint Resolve minusDom_WF minusDom_valid : varset_inv.
(* Use only preservation facts here. Including core would re-enter the
   certificate Hint Extern rules when a raw input has no certificate. *)
Ltac subst_varset_certificate := solve [
  unfold VarSetFSet.WF, minusDom in *;
  eauto 8 with nocore varset_inv].
#[local] Hint Extern 2 (WF _) => subst_varset_certificate : core.
#[local] Hint Extern 2 (ValidVarSet _) => subst_varset_certificate : core.

(* ---------------------------- *)

(* General purpose lemmas. *)


Lemma map_snd_zip' :
  forall {a}{b}{c} (f:b -> c) (xs : list a) ys ,
    length xs = length ys ->
    (map (fun ps => f (snd ps)) (List.zip xs ys)) =
    (map f ys).
Proof.
  move=> a b c f xs ys Hle.
  rewrite <- (map_map (snd (A:=a)) f).
  rewrite -> map_snd_zip; auto.
Qed.

Lemma map_Tuple_snd_zip : forall {A B} (l1 : list A) (l2 : list B),
  length l1 = length l2 ->
  map Data.Tuple.snd (List.zip l1 l2) = l2.
Proof.
  induction l1; intros; destruct l2; simpl in *; try discriminate; auto.
  f_equal. apply IHl1. auto.
Qed.

Lemma map_Tuple_fst_zip : forall {A B} (l1 : list A) (l2 : list B),
  length l1 = length l2 ->
  map Data.Tuple.fst (List.zip l1 l2) = l1.
Proof.
  induction l1; intros; destruct l2; simpl in *; try discriminate; auto.
  f_equal. apply IHl1. auto.
Qed.

(* ---------------------------------------------------------------- *)

(* No shadowing either *)

Fixpoint UniqScoped (e : CoreExpr) (in_scope : VarSet) {struct e} : Prop :=
  match e with
  | Mk_Var v => WellScopedVar v in_scope
  | Lit l => True
  | App e1 e2 => UniqScoped e1 in_scope /\  UniqScoped e2 in_scope
  | Lam v e => GoodLocalVar v /\ UniqScoped e (extendVarSet in_scope v)
                             /\ elemVarSet v in_scope = false 
  | Let bind body =>
      UniqScopedBind bind in_scope /\
      UniqScoped body (extendVarSetList in_scope (bindersOf bind))
  | Case scrut bndr ty alts  => 
    UniqScoped scrut in_scope /\
    GoodLocalVar bndr /\
    Forall' (fun alt =>
      let '(Mk_Alt _ pats rhs) := alt in
      Forall GoodLocalVar pats /\
      let in_scope' := extendVarSetList in_scope (bndr :: pats) in
      UniqScoped rhs in_scope') alts
  | Cast e _ =>   UniqScoped e in_scope
(*  | Tick _ e =>   UniqScoped e in_scope *) (* /\ UniqScopedTickish t in_scope *) 
  | Mk_Type _  =>   True
  | Mk_Coercion _ => True 
  end
with UniqScopedBind (bind : CoreBind) (in_scope : VarSet) : Prop :=
  match bind with
  | NonRec v rhs =>
    GoodLocalVar v /\
    UniqScoped rhs in_scope
  | Rec pairs => 
    Forall (fun p => GoodLocalVar (fst p)) pairs /\
    NoDup (map varUnique (map fst pairs)) /\
    Forall' (fun p => UniqScoped (snd p) (extendVarSetList in_scope (map fst pairs))) pairs
  end.

   
(* ---------------------------------------------------------------- *)

(** ** [substExpr] simplification lemmas and tactics *)

(* GHC 9.10: subst_expr renamed to substExpr, substBind now axiomatized.
   These simplification lemmas are axiomatized since the underlying
   functions are axioms. *)

Lemma substExpr_App : forall subst e1 e2,
    substExpr subst (App e1 e2) =
    App (substExpr subst e1) (substExpr subst e2).
Proof. reflexivity. Qed.

(*
Lemma substExpr_Tick : forall subst tic e,
        substExpr subst (Tick tic e) =
        CoreUtils.mkTick (substTickish subst tic) (substExpr subst e).
*)

Lemma substExpr_Lam : forall subst bndr body,
        substExpr subst (Lam bndr body) =
        let (subst', bndr') := substBndr subst bndr in
        Lam bndr' (substExpr subst' body).
Proof. intros. unfold substExpr, substExpr_. destruct (substBndr subst bndr). reflexivity. Qed.

Lemma substExpr_LetNonRec : forall subst c e0 body,
  substExpr subst (Let (NonRec c e0) body) =
    let (subst', bndr') := substBndr subst c in
    Let (NonRec bndr' (substExpr subst e0)) (substExpr subst' body).
Proof. intros. unfold substExpr, substExpr_, substBind_. destruct (substBndr subst c). reflexivity. Qed.

Lemma substExpr_Let : forall subst bind body,
  substExpr subst (Let bind body) =
   let '(subst', bind') := substBind subst bind in Let bind' (substExpr subst' body).
Proof.
  intros. unfold substExpr, substBind.
  destruct bind as [v0 e0 | pairs0]; simpl.
  - destruct (substBndr subst v0). reflexivity.
  - destruct (substRecBndrs subst _). reflexivity.
Qed.

Lemma substBind_NonRec : forall subst c e0,
    substBind subst (NonRec c e0) =
    let '(subst', bndr') := substBndr subst c in
    (subst', NonRec bndr' (substExpr subst e0)).
Proof. intros. unfold substBind, substBind_, substExpr. destruct (substBndr subst c). reflexivity. Qed.

Lemma substBind_Rec : forall subst pairs,
    substBind subst (Rec pairs) =
    let bndrs := GHC.Base.map Data.Tuple.fst pairs in
    let '(subst'0, bndrs') := substRecBndrs subst bndrs in
    (subst'0 , Rec (GHC.List.zip bndrs' ((fix go_rhss ps := match ps with
       | nil => nil | cons (pair _ rhs) rest => cons (substExpr subst'0 rhs) (go_rhss rest) end) pairs))).
Proof.
  intros. unfold substBind, substBind_, substExpr.
  destruct (substRecBndrs subst _). reflexivity.
Qed.


Definition substAlt subst (alt: Alt CoreBndr) :=
  let '(Mk_Alt con bndrs rhs) := alt in
  let '(subst', bndrs') := substBndrs subst bndrs in
  Mk_Alt con bndrs' (substExpr subst' rhs).

Lemma substExpr_Case : forall s e b u l,
    substExpr s (Case e b u l) =
    let '(subst', bndr') := substBndr s b in
    Case (substExpr s e) bndr' (substTyUnchecked s u)
         ((fix go_alts as' := match as' with
            | nil => nil
            | cons (Mk_Alt con bndrs rhs) rest =>
                let '(subst'', bndrs') := substBndrs subst' bndrs in
                cons (Mk_Alt con bndrs' (substExpr subst'' rhs)) (go_alts rest)
            end) l).
Proof.
  intros. unfold substExpr, substExpr_.
  destruct (substBndr s b). reflexivity.
Qed.

Lemma go_alts_eq_map_substAlt : forall subst' l,
    (fix go_alts as' := match as' with
        | nil => nil
        | cons (Mk_Alt con bndrs rhs) rest =>
            let '(subst'', bndrs') := substBndrs subst' bndrs in
            cons (Mk_Alt con bndrs' (substExpr subst'' rhs)) (go_alts rest)
        end) l = map (substAlt subst') l.
Proof.
  intros subst' l. induction l as [|a rest IH].
  - reflexivity.
  - simpl. destruct a as [con bndrs rhs].
    unfold substAlt at 1.
    destruct (substBndrs subst' bndrs) as [subst'' bndrs'].
    f_equal. exact IH.
Qed.

Lemma go_rhss_eq_map : forall (subst' : Subst) (pairs : list (Var * CoreExpr)),
    (fix go_rhss ps := match ps with
      | nil => nil
      | cons (pair _ rhs) rest => cons (substExpr subst' rhs) (go_rhss rest)
      end) pairs = map (substExpr subst') (map Data.Tuple.snd pairs).
Proof.
  intros. induction pairs as [|[v rhs] rest IH].
  - reflexivity.
  - simpl. f_equal. exact IH.
Qed.

Lemma go_rhss_eq_map_substExpr : forall (s : Subst) (ps : list (Var * CoreExpr)),
    (fix go_rhss (l : list (Var * CoreExpr)) : list CoreExpr :=
      match l with
      | nil => nil
      | (_, rhs) :: rest => substExpr s rhs :: go_rhss rest
      end) ps = map (substExpr s) (map Data.Tuple.snd ps).
Proof.
  intros s ps. induction ps as [|[v rhs] rest IHps]; simpl.
  - reflexivity.
  - f_equal. exact IHps.
Qed.

Lemma substBind_Rec' : forall (subst : Subst) (pairs : list (Var * CoreExpr)),
    substBind subst (Rec pairs) =
    let bndrs := GHC.Base.map Data.Tuple.fst pairs in
    let '(subst', bndrs') := substRecBndrs subst bndrs in
    (subst', Rec (GHC.List.zip bndrs' (map (substExpr subst') (map Data.Tuple.snd pairs)))).
Proof.
  intros.
  transitivity
    (let bndrs := GHC.Base.map Data.Tuple.fst pairs in
     let '(subst', bndrs') := substRecBndrs subst bndrs in
     (subst', Rec (GHC.List.zip bndrs' ((fix go_rhss ps := match ps with
        | nil => nil | cons (pair _ rhs) rest => cons (substExpr subst' rhs) (go_rhss rest) end) pairs)))).
  { apply substBind_Rec. }
  cbv zeta.
  destruct (substRecBndrs subst (GHC.Base.map Data.Tuple.fst pairs)) as [subst' bndrs'].
  f_equal. f_equal. f_equal. apply go_rhss_eq_map.
Qed.

Lemma substExpr_Case' : forall s e b u l,
    substExpr s (Case e b u l) =
    let '(subst', bndr') := substBndr s b in
    Case (substExpr s e) bndr' (substTyUnchecked s u) (map (substAlt subst') l).
Proof.
  intros. rewrite substExpr_Case. destruct (substBndr s b).
  f_equal. apply go_alts_eq_map_substAlt.
Qed.

Lemma substExpr_Cast : forall subst e co,
   substExpr subst (Cast e co) =
   Cast (substExpr subst e) (substCo subst co).
Proof. reflexivity. Qed.


#[export] Hint Rewrite substExpr_App substExpr_Case' substExpr_Cast
     substBind_NonRec substBind_Rec substExpr_Let substExpr_Lam
     (* substExpr_Tick *) : hs_simpl.


(* ---------------------------------------------------------------- *)


(** ** [WellScoped_Subst] Substitution invariant *)

(* GHC 9.10: Subst has structural axioms — use projections instead of pattern match *)
Definition getSubstInScopeVars (s : Subst) : VarSet :=
  getInScopeVars (substInScope s).




(* From the GHC implementation comments:

   When calling (subst subst tm) it should be the case that
   the in_scope_set in the substitution describes the scope after 
   the substituition has been applied.

  That means that it should be a superset of both:

  (SIa) The free vars of the range of the substitution
  (SIb) The free vars of ty minus the domain of the substitution

  ----

  We enforce this in WellScoped_Subst by requiring

    - the current scope minus the domain is a strongSubset of in_scope_set
    - the range of the subst_env is wellscoped according to the in_scope_set

  We *should* also enforce that 

    - the domain of the substitution only contains good local *identifiers*
      (i.e. not global ids, type vars or coercion vars.) 

  However, we cannot access the domain of VarEnvs directly. So we can not 
  capture this invariant here. Instead, we should only lookup localIds in this 
  subst_env.

*)


(* The certificates concern the internal maps, not the WellScoped predicate.
   Lookup-based scope equivalence alone does not certify a raw IntMap. *)
Definition WellScoped_Subst (s : Subst) (vs : VarSet) : Prop :=
  minusDom vs (substIdEnv s) {<=} getInScopeVars (substInScope s)
  /\
  (forall var,
    match lookupVarEnv (substIdEnv s) var with
    | Some expr => WellScoped expr (getInScopeVars (substInScope s))
    | None => True
    end) /\
  WF vs /\ ValidVarSet vs /\
  WF (getInScopeVars (substInScope s)) /\
  ValidVarSet (getInScopeVars (substInScope s)) /\
  IntMapProofs.WF (VarEnv_IntMap (substIdEnv s)).

Lemma WellScoped_Subst_input_WF s vs : WellScoped_Subst s vs -> WF vs.
Proof. unfold WellScoped_Subst. tauto. Qed.
Lemma WellScoped_Subst_input_valid s vs : WellScoped_Subst s vs -> ValidVarSet vs.
Proof. unfold WellScoped_Subst. tauto. Qed.
Lemma WellScoped_Subst_scope_WF s vs : WellScoped_Subst s vs ->
  WF (getInScopeVars (substInScope s)).
Proof. unfold WellScoped_Subst. tauto. Qed.
Lemma WellScoped_Subst_scope_valid s vs : WellScoped_Subst s vs ->
  ValidVarSet (getInScopeVars (substInScope s)).
Proof. unfold WellScoped_Subst. tauto. Qed.
Lemma WellScoped_Subst_env_WF s vs : WellScoped_Subst s vs ->
  IntMapProofs.WF (VarEnv_IntMap (substIdEnv s)).
Proof. unfold WellScoped_Subst. tauto. Qed.

#[local] Hint Resolve WellScoped_Subst_input_WF WellScoped_Subst_input_valid
  WellScoped_Subst_scope_WF WellScoped_Subst_scope_valid
  WellScoped_Subst_env_WF : core.

Ltac subst_certificate :=
  match goal with
  | |- WF _ => idtac
  | |- ValidVarSet _ => idtac
  | |- IntMapProofs.WF _ => idtac
  end;
  repeat rewrite ?substInScope_Mk_Subst ?substIdEnv_Mk_Subst
    ?getInScopeVars_extendInScopeSet ?getInScopeVars_extendInScopeSetList;
  eauto.

Ltac destruct_WellScoped_Subst :=
    match goal with
      | [H0 : WellScoped_Subst ?s ?vs |- _ ] =>
         unfold WellScoped_Subst in H0;
         destruct H0 as [? [? [Wvs [Vvs [Wis [Vis Wenv]]]]]]
  end.


(* Not actually used in this file. *)
Lemma WellScoped_Subst_StrongSubset : forall vs1 s vs2,
  WF vs2 -> ValidVarSet vs2 ->
  vs2 {<=} vs1 ->
  WellScoped_Subst s vs1 ->
  WellScoped_Subst s vs2.
Proof.
  move=> vs1 s vs2 W2 V2 h1 h2.
  destruct_WellScoped_Subst.
  repeat split; auto.
  eapply (@StrongSubset_trans (minusDom vs2 (substIdEnv s))); eauto.
  eapply StrongSubset_minusDom; eauto.
Qed.


(* ---------------------------------------- *)


Definition Disjoint {a}`{Eq_ a} (l1 l2 : list a) :=
  Forall (fun x => ~ (List.In x l2)) l1. 

Lemma Forall_app : forall {A} {p} {l1 l2 : list A}, 
      Forall p l1 -> Forall p l2 -> Forall p (l1 ++ l2).
Proof.
  intros.
  induction l1; simpl; auto.
  inversion H. subst.  eapply Forall_cons; eauto.
Qed.

#[export] Hint Constructors NoDup : core.

Lemma NoDup_app_1 : forall (a : Type)`{Eq_ a} (l1 l2 : list a), 
    NoDup l1 ->
    NoDup l2 ->
    Disjoint l1 l2 ->
    NoDup (l1 ++ l2).
Proof.
  move=> a EQ l1. 
  elim: l1.
  move=> l2 Nl1 N2 D; simpl; auto.
  move=> x xs IH l2 Nl1 N2 D; simpl.
  inversion Nl1. 
  inversion D.
  subst.
  econstructor.
  - intro h.
    apply in_app_or in h.
    destruct h; eauto. 
  - eapply IH; eauto.
Qed. 




Lemma NoDup_app : forall (l1 l2 : list Var), 
    NoDup (map varUnique l1) ->
    NoDup (map varUnique l2) ->
    Disjoint (map varUnique l1) (map varUnique l2) ->
    NoDup (map varUnique l1 ++ map varUnique l2).
Proof.
  intros l1 l2.
  eapply NoDup_app_1 with (l1 := map varUnique l1)
                          (l2 := map varUnique l2).
Qed. 

(* ---------------------------------------- *)


(* Actually from Coq.Program.Tactics. *)
Ltac destruct_one_pair :=
 match goal with
   | [H : (_ /\ _) |- _] => destruct H
   | [H : prod _ _ |- _] => destruct H
 end.

(* Variants for CoreSubst. *)
Ltac destruct_one_id var2 :=
  match goal with [ H : exists var2:Id, _ |- _ ] =>
    destruct H as [var2 ?]; 
    repeat destruct_one_pair 
  end.
Ltac destruct_one_expr val1 :=
  match goal with 
    [ H : exists v : CoreExpr, _ |- _ ] =>
    destruct H as [val1 ?];
    repeat destruct_one_pair 
  end.



(* This property describes the invariants we need about the freshened
   binder list and new VarEnv after a use of substIdBndrs.
  
  - [e2] is a subst env extended from [e1], where the binders in [vars]
    have been freshened to [vars']. 

*)


Definition VarEnvExtends
           (e1  : VarEnv CoreExpr) (vars  : list Var)
           (e2  : VarEnv CoreExpr) (vars' : list Var) : Prop :=
  forall var, 
    match lookupVarEnv e2 var with
    | Some val2 => 
      (* If a variable is in the dom of the new substitution, then 
         either, it is a renaming of a binding variable... *)
      (exists var2, val2 = Mk_Var var2 
                /\ List.In var2 vars'
                /\ Foldable.elem var vars = true) \/

     (* or it was also in the old substitution, with 
         the same definition ... *)
      (exists val1, lookupVarEnv e1 var = Some val1 /\
               val1 = val2 )

    | None =>
      (* If a variable is NOT in the dom of the new substitution, then 
         either .... *) 
      match lookupVarEnv e1 var with 

      | None  =>  True 
        (* ... it wasn't in the dom of the old substitution
           (and isn't a binder) 
        not (List.In var vars) /\ not (List.In var vars') *)

      | Some val1 => 

        (* .. or it was in the old substitution, 
           but it is a "sufficiently fresh" binder that 
           we dropped. *)
          
          (Foldable.elem var vars && Foldable.elem var vars') = true

      end
    end.

Lemma VarEnvExtends_trans : forall beg mid end_env vars1 vars2 vars1' vars2', 
  Disjoint (map varUnique vars1') (map varUnique vars2') -> 
  VarEnvExtends beg vars1 mid vars1' ->
  VarEnvExtends mid vars2 end_env vars2' ->
  VarEnvExtends beg (vars1 ++ vars2) end_env (vars1' ++ vars2').
Proof.
  intros.
  unfold VarEnvExtends in *. 
  intros var. specialize_all var.
  destruct (lookupVarEnv end_env var) eqn:LU2;
    destruct (lookupVarEnv mid var) eqn:LU0; 
    destruct (lookupVarEnv beg var) eqn:LU4; auto.
  all: repeat try match goal with 
                    [H : (?A \/ ?B) |- _] => destruct H end.
  all: repeat destruct_one_pair.
  all: try destruct_one_id var2.
  all: try destruct_one_id var3.
  all: try destruct_one_expr val1.
  all: try destruct_one_expr val2.
  all: try inversion H0.
  all: try inversion H1.
  all: subst.
  all: try solve [left; eexists;
    repeat split; auto;
      try (apply in_or_app; tauto);
        rewrite -> Foldable_elem_app;
        rewrite -> orb_true_iff; tauto].
  - right; eexists; repeat split; eauto.
  - left.  eexists. repeat split.
    apply in_or_app. tauto.
    rewrite -> H5.
    rewrite -> Foldable_elem_app.
    rewrite -> orb_true_iff.
    tauto.
  - rewrite H6. hs_simpl. rewrite H3 /=.
    move/andP in H6. tauto.
  - rewrite H1. hs_simpl.
    move: H1 => /andP [-> ->].
    tauto.
  - rewrite H3. hs_simpl.
    move: H3 => /andP [-> ->].
    tauto.
Qed.


(* This property describes the invariants we need about the freshened
   binder list and new subst after a use of substIdBndrs.
  
  - [s2] is a subst extended from [s1], where the binders in [vars]
    have been freshened to [vars']

*)


(* Concrete definition using Subst structural axioms *)
Definition SubstExtends (s1 : Subst) (vars : list Var)
                        (s2 : Subst) (vars' : list Var) : Prop :=
  length vars = length vars' /\
  NoDup (map varUnique vars') /\
  Forall GoodLocalVar vars' /\
  (* The new variables are fresh for the original substitution. *)
  freshList vars' (getInScopeVars (substInScope s1)) /\
  (* For the in_scope_set: new = old + vars' *)
  (getInScopeVars (substInScope s2)) {=}
    (extendVarSetList (getInScopeVars (substInScope s1)) vars') /\
  (* ... and we can subtract out the old binders. *)
  (minusDom (extendVarSetList (getInScopeVars (substInScope s1)) vars)
            (substIdEnv s2) {<=}
   getInScopeVars (substInScope s2)) /\
  (* Anything in the new substitution is either a renamed variable from
     the old substitution or was already in the old substitution *)
  VarEnvExtends (substIdEnv s1) vars (substIdEnv s2) vars' /\
  (* Preserve structural certificates explicitly: strong equivalence only
     compares lookups, so cannot supply these certificates by itself. *)
  WF (getInScopeVars (substInScope s1)) /\
  ValidVarSet (getInScopeVars (substInScope s1)) /\
  IntMapProofs.WF (VarEnv_IntMap (substIdEnv s1)) /\
  WF (getInScopeVars (substInScope s2)) /\
  ValidVarSet (getInScopeVars (substInScope s2)) /\
  IntMapProofs.WF (VarEnv_IntMap (substIdEnv s2)).


Ltac destruct_SubstExtends :=
  repeat
    match goal with
    | [ H : SubstExtends ?s1 ?vs ?s2 ?vs1 |- _ ] =>
      unfold SubstExtends in H; unfold StrongEquivalence in *;
      repeat (destruct_one_pair)
    end.


(* Prove goals about lookupVarSet, given StrongSubset assumptions *)
Ltac lookup_StrongSubset :=
    match goal with 
      [ h1 : (extendVarSetList ?i3 ?vars1) {<=} ?i,
        h2 : forall v:Var, is_true (Foldable.elem v ?vars1) -> lookupVarSet ?i3 v = None,
        m  : lookupVarSet ?i ?v  = ?r |- 
             lookupVarSet ?i3 ?v = ?r ] =>
      let k := fresh in
      assert (k : StrongSubset i3 i); 
        [ eapply StrongSubset_trans with (vs2 := (extendVarSetList i3 vars1)); 
          eauto;
          eapply StrongSubset_extendVarSetList_fresh; eauto |
          unfold StrongSubset in k;
          specialize (k v);
          rewrite -> m in k;
          destruct (lookupVarSet i3 v) eqn:LY;
          [contradiction| auto]]
    end.


Lemma SubstExtends_refl : forall s,
    WF (getInScopeVars (substInScope s)) ->
    ValidVarSet (getInScopeVars (substInScope s)) ->
    IntMapProofs.WF (VarEnv_IntMap (substIdEnv s)) ->
    SubstExtends s nil s nil.
Proof.
  intros.
  unfold SubstExtends.
  repeat split; simpl; try rewrite extendVarSetList_nil; auto.
  apply freshList_nil.
  eapply StrongSubset_refl.
  eapply StrongSubset_refl.
  eapply StrongSubset_minusDom_left; eauto.
  unfold VarEnvExtends. intros var.
  destruct (lookupVarEnv (substIdEnv s) var) eqn:LU; try tauto.
  right. eexists.
  repeat split; eauto.
Qed.

    
Lemma SubstExtends_trans : forall s2 s1 s3 vars1 vars2 vars1' vars2',
    Disjoint (map varUnique vars1') (map varUnique vars2') ->
    SubstExtends s1 vars1 s2 vars1' -> SubstExtends s2 vars2 s3 vars2'->
    SubstExtends s1 (vars1 ++ vars2) s3 (vars1' ++ vars2').
Proof.
  intros s2 s1 s3 vars1 vars2 vars1' vars2' Hdisj HSE1 HSE2.
  unfold SubstExtends in HSE1, HSE2.
  destruct HSE1 as [LEN1 [ND1 [GLV1 [FR1 [SE1 [MD1 [VE1 [Wi1 [Vi1 [We1 [Wi2 [Vi2 We2]]]]]]]]]]]].
  destruct HSE2 as [LEN2 [ND2 [GLV2 [FR2 [SE2 [MD2 [VE2 [Wi2' [Vi2' [We2' [Wi3 [Vi3 We3]]]]]]]]]]]].
  unfold StrongEquivalence in SE1, SE2.
  destruct SE1 as [SE1a SE1b]. destruct SE2 as [SE2a SE2b].

  assert (k : VarEnvExtends (substIdEnv s1) (vars1 ++ vars2) (substIdEnv s3) (vars1' ++ vars2')).
  eapply VarEnvExtends_trans; eauto.

  unfold SubstExtends.
  repeat split; auto.
  - rewrite -> app_length. rewrite -> app_length. auto.
  - rewrite -> map_app.
    apply NoDup_app; auto.
  - eauto using Forall_app.
  - rewrite -> freshList_app.
    split; auto.
    unfold freshList in *.
    intros v IN.
    pose (m := FR2 _ IN); clearbody m.
    lookup_StrongSubset.
  - rewrite -> extendVarSetList_append.
    eapply StrongSubset_trans; [exact SE2a|].
    eapply StrongSubset_extendVarSetList.
    + exact Wi2.
    + apply extendVarSetList_WF. exact Wi1.
    + exact SE1a.
  - rewrite -> extendVarSetList_append.
    eapply StrongSubset_trans with
        (vs2 := extendVarSetList (getInScopeVars (substInScope s2)) vars2'); [|exact SE2b].
    eapply StrongSubset_extendVarSetList.
    + apply extendVarSetList_WF. exact Wi1.
    + exact Wi2.
    + exact SE1b.
  - (* This is the hard case: minusDom StrongSubset *)
    intros var.
    unfold StrongSubset, Subset, In, elt in *.
    unfold VarEnvExtends in *.
    specialize_all var.

    case ELEM: (lookupVarEnv (substIdEnv s3) var) => [a|].
    rewrite lookup_minusDom_inDom; auto.
    rewrite lookupVarEnv_elemVarEnv_true; eauto.
    rewrite -> lookupVarSet_minusDom_1 by auto.
    rewrite -> lookupVarSet_minusDom_1 in MD2 by auto.

    rewrite -> ELEM in VE2.
    rewrite -> ELEM in k.

    (* Is var in the mid_env? *)
    case ELEM2: (lookupVarEnv (substIdEnv s2) var) => [cc|].
    + rewrite ELEM2 in VE2.
      move: VE2 => /andP [Helem1 Helem2].
      hs_simpl.
      move: (@lookupVarSet_extendVarSetList_self_exists_LastIn vars2 var (extendVarSetList (getInScopeVars (substInScope s1)) vars1) ltac:(auto) Helem1) => [v' [-> q r]].
      move: (@lookupVarSet_extendVarSetList_self_exists_LastIn vars2 var (getInScopeVars (substInScope s2)) ltac:(auto) Helem1) => [v'2 [p2 q2 r2]].
      rewrite p2 in MD2.
      case LF: (lookupVarSet (getInScopeVars (substInScope s3)) var) => [a0|] ;
      rewrite LF // in MD2.
      apply almostEqual_trans with (v2 := v'2); eauto.
      eapply LastIn_inj in r; eauto. subst.
      apply almostEqual_refl.
      eapply Eq_trans; first rewrite Eq_sym; eassumption.
    + clear VE2.
      rewrite -> lookupVarSet_minusDom_1 in MD1 by auto.
      rewrite ELEM2 in VE1.
      destruct (Foldable.elem var vars2) eqn:InV2; hs_simpl.
      ++ move:(@lookupVarSet_extendVarSetList_self_exists_LastIn vars2 var
                 (extendVarSetList (getInScopeVars (substInScope s1)) vars1) ltac:(auto) InV2) => [v1 [-> q1 r1]].
         move:(@lookupVarSet_extendVarSetList_self_exists_LastIn vars2 var
                 (getInScopeVars (substInScope s2)) ltac:(auto) InV2) => [v2 [p2 q2 r2]].
         rewrite p2 in MD2.
         destruct (lookupVarSet (getInScopeVars (substInScope s3)) var) eqn:InF; try done.
         eapply LastIn_inj in r2; try eapply r1.
         subst. auto.
         eapply Eq_trans; first rewrite Eq_sym; eassumption.
      ++ have InV2': ~~ Foldable.elem var vars2 by rewrite InV2.
         rewrite -> lookupVarSet_extendVarSetList_false by auto.
         rewrite -> lookupVarSet_extendVarSetList_false in MD2 by auto.
         destruct (Foldable.elem var vars1) eqn:InV1; hs_simpl.
         ** move:(@lookupVarSet_extendVarSetList_self_exists_LastIn vars1 var
                    (getInScopeVars (substInScope s1)) ltac:(auto) InV1) => [v1 [p1 q1 r1]].
            rewrite p1.
            rewrite p1 in MD1.
            case InM1: (lookupVarSet (getInScopeVars (substInScope s2)) var) => [b|];
                                                                         rewrite InM1 in MD1; try done.
            rewrite InM1 in MD2.
            case InF1: (lookupVarSet (getInScopeVars (substInScope s3)) var) => [cc0|];
                                                                         rewrite InF1 in MD2; try done.
            eapply almostEqual_trans; eauto.
         ** have InV1': ~~ Foldable.elem var vars1 by rewrite InV1.
            rewrite -> lookupVarSet_extendVarSetList_false by auto.
            rewrite -> lookupVarSet_extendVarSetList_false in MD1 by auto.
            case InI1: (lookupVarSet (getInScopeVars (substInScope s1)) var) => [a0|] //.
            rewrite InI1 in MD1.
            case InM1: (lookupVarSet (getInScopeVars (substInScope s2)) var) => [b|] //;
                                                                            rewrite InM1 // in MD1.
            rewrite InM1 in MD2.
            case InF1: (lookupVarSet (getInScopeVars (substInScope s3)) var) => [cc0|] //;
                                                                             rewrite InF1 // in MD2.
            eapply almostEqual_trans; eauto.
Qed.

Lemma Subset_VarEnvExtends : forall old_env vars new_env vars' vs1 vs2,
    WF vs1 -> ValidVarSet vs1 -> WF vs2 -> ValidVarSet vs2 ->
    IntMapProofs.WF (VarEnv_IntMap old_env) ->
    IntMapProofs.WF (VarEnv_IntMap new_env) ->
    VarEnvExtends old_env vars new_env vars' ->
    minusDom vs1 old_env {<=} vs2 ->
    minusDom (extendVarSetList vs1 vars) new_env
     {<=} minusDom (extendVarSetList vs2 vars) new_env.
Proof.
  intros old_env vars new_env vars' vs1 vs2 W1 V1 W2 V2 We1 We2 H H0.
  unfold VarEnvExtends in *.
  unfold StrongSubset in *. 
  intros var. specialize_all var.
  destruct (lookupVarEnv new_env var) eqn:LU.
  - rewrite -> lookup_minusDom_inDom; auto.
    rewrite -> lookupVarEnv_elemVarEnv_true by auto.
    eauto.
  - rewrite -> lookupVarSet_minusDom_1; auto.
    rewrite -> lookupVarSet_minusDom_1; auto.
    destruct (lookupVarEnv old_env var) eqn:LU2.
    -- rewrite -> andb_true_iff in *.
       move: H => [h0 h1]. 
       move: (@extendVarSetList_same var vars vs1 vs2 ltac:(auto) ltac:(auto) h0) => e.
       rewrite e.
       elim h2: (lookupVarSet (extendVarSetList vs2 vars) var) => [a|] //.
       apply almostEqual_refl.
    -- rewrite -> lookupVarSet_minusDom_1 in *; auto.
       destruct (Foldable.elem var vars) eqn:ELEM.
       move: (@extendVarSetList_same var vars vs1 vs2 ltac:(auto) ltac:(auto) ELEM) => e.
       rewrite e.
       elim h2: (lookupVarSet (extendVarSetList vs2 vars) var) => [a|] //.
       apply almostEqual_refl.
       rewrite -> lookupVarSet_extendVarSetList_false; auto.
       rewrite -> lookupVarSet_extendVarSetList_false; auto.
       rewrite ELEM //.
       rewrite ELEM //.
Qed.



(* To be usable with the induction hypothesis inside a renamed scope, 
   we need to know that the new substitution is well-scoped with respect 
   to the *old* list of binders. *)

Lemma SubstExtends_WellScoped_Subst : forall s1 s2 vs vars vars',
    Forall GoodLocalVar vars ->
    SubstExtends s1 vars s2 vars' ->
    WellScoped_Subst s1 vs ->
    WellScoped_Subst s2 (extendVarSetList vs vars).
Proof.
  intros.
  rewrite -> Forall_forall in H.
  destruct_WellScoped_Subst.
  unfold SubstExtends in H0.
  destruct H0 as [LEN [ND [GLV [FR [SE [MD [VE [Wi1 [Vi1 [We1 [Wi2 [Vi2 We2]]]]]]]]]]]].
  unfold WellScoped_Subst.
  repeat split; auto.
  + eapply StrongSubset_trans with
        (vs2 := minusDom (extendVarSetList (getInScopeVars (substInScope s1)) vars) (substIdEnv s2)).
    eapply Subset_VarEnvExtends; eauto.
    auto.
  + unfold StrongEquivalence in SE. destruct SE as [SEa SEb].
    unfold VarEnvExtends in *.
    intros var. specialize (VE var).
    destruct (lookupVarEnv (substIdEnv s2) var) eqn:LU; auto.
    destruct VE.
    ++ destruct H0 as [var2 [Heq [HIn Helem]]].
       subst.
       eapply WellScoped_StrongSubset with
       (vs1 := extendVarSetList (getInScopeVars (substInScope s1)) vars'); auto.
       unfold WellScoped.
       unfold WellScopedVar.
       replace (isLocalVar var2) with true; swap 1 2. {
        symmetry.
        rewrite -> Forall_forall in GLV.
        specialize (GLV _ HIn).
        unfold GoodLocalVar in GLV. intuition.
       }
       rewrite -> lookupVarSet_extendVarSetList_self_in; auto.
       split.
       eapply almostEqual_refl; auto.
       rewrite -> Forall_forall in GLV.
       specialize (GLV _ HIn).
       unfold GoodLocalVar in GLV.
       apply GLV.
    ++ destruct H0 as [val1 [Hlook Heq]].
       specialize (H2 var). rewrite -> Hlook in H2. subst.
       eapply WellScoped_StrongSubset with
       (vs1 := extendVarSetList (getInScopeVars (substInScope s1)) vars'); auto.
       eapply WellScoped_StrongSubset; eauto.
       eapply StrongSubset_extendVarSetList_fresh; try solve [subst_certificate].
       auto.
Qed.


(* GHC 9.10: Subst axiomatized *)
Lemma WellScoped_substBody : forall vs vars vars' body s1 s2,
   forall (IH : forall subst,
      WellScoped_Subst subst (extendVarSetList vs vars) ->
      WellScoped (substExpr subst body) (getSubstInScopeVars subst)),
   Forall GoodLocalVar vars ->
   SubstExtends s1 vars s2 vars' ->
   WellScoped_Subst s1 vs ->
   WellScoped (substExpr s2 body)
              (extendVarSetList (getSubstInScopeVars s1) vars').
Proof.
  intros.
  assert (HSE : SubstExtends s1 vars s2 vars') by auto.
  unfold SubstExtends in HSE.
  destruct HSE as [LEN [ND [GLV [FR [SE [MD [VE [Wi1 [Vi1 [We1 [Wi2 [Vi2 We2]]]]]]]]]]]].
  eapply WellScoped_StrongSubset; try solve [subst_certificate].
  eapply IH.
  eapply SubstExtends_WellScoped_Subst; eauto.
  unfold getSubstInScopeVars.
  unfold StrongEquivalence in SE. destruct SE; auto.
Qed.

(*
Lemma GoodLocalVar_setIdType : forall x t, GoodLocalVar x -> GoodLocalVar (Id.setIdType x t).
Proof.
  intros. move: H => [[h0 [h2 [h3 h4]]] h1].  destruct x; simpl in *; econstructor; try done. 
Qed.

Lemma Eq_setIdType : forall x t, 
    x GHC.Base.== Id.setIdType x t.
Proof.
  intros x t. destruct x; simpl; unfold_zeze; simpl; 
  rewrite (N.eqb_refl realUnique); auto.
Qed. *)

Lemma WellScoped_Subst_substIdBndr : forall s1 s2 subst subst' bndr' v vs,
  forall (SB : substIdBndr s1 s2 subst v = (subst', bndr')),
  GoodLocalVar v ->
  WellScoped_Subst subst vs ->
  SubstExtends subst (cons v nil) subst' (cons bndr' nil) /\
  WellScoped_Subst subst' (extendVarSet vs v).
Proof.
  intros s1 s2 subst subst' bndr' v vs SB GLVv WSS.
  unfold substIdBndr in SB.
  unfold substIdInfo in SB. simpl Id.maybeModifyIdInfo in SB.
  set (in_scope := substInScope subst) in *.
  set (env := substIdEnv subst) in *.
  inversion SB; subst; clear SB.
  unfold WellScoped_Subst in WSS.
  change (substIdEnv subst) with env in WSS.
  change (substInScope subst) with in_scope in WSS.
  destruct WSS as [SS [LVi [Wvs [Vvs [Wis [Vis Wenv]]]]]].
  (* Case analysis on whether we freshen the binder v. *)
  destruct (uniqAway in_scope v == v) eqn:NC.
  + (* Binder [v] is already fresh enough. *)
    apply uniqAway_eq_same in NC.
    unfold WellScoped_Subst, SubstExtends.
    change (substIdEnv subst) with env.
    change (substInScope subst) with in_scope.
    repeat split.
    all: try rewrite -getInScopeVars_extendInScopeSetList
                      extendInScopeSetList_cons
                      extendInScopeSetList_nil.
    all: try rewrite /getSubstInScopeVars.
    all: try rewrite substInScope_Mk_Subst.
    all: try solve [subst_certificate].
    -- econstructor.
       inversion 1.
       econstructor.
    -- econstructor; eauto.
       rewrite NC. auto.
    --
       rewrite /freshList => v1.
       hs_simpl.
       move => InV.
       rewrite NC in InV.
       rewrite (@lookupVarSet_eq v1 v (getInScopeVars in_scope) InV) -NC.
       apply uniqAway_lookupVarSet_fresh.
    -- rewrite NC. apply StrongSubset_refl.
    -- rewrite NC. apply StrongSubset_refl.
    -- rewrite substIdEnv_Mk_Subst.
       rewrite getInScopeVars_extendInScopeSet.
       eapply StrongSubset_trans.
       eapply minusDom_extend; try solve [subst_certificate].
       rewrite getInScopeVars_extendInScopeSet NC.
       eapply StrongSubset_extend; try solve [subst_certificate].
       eapply StrongSubset_minusDom_left; auto.
    -- rewrite substIdEnv_Mk_Subst.
       rewrite /VarEnvExtends => var.
       pose proof (LVi var) as LVivar.
       destruct (v == var) eqn:EQv.
       ++ (* The arbitrary var is the same as the binder
             which was sufficiently fresh. *)
         move: (uniqAway_lookupVarSet_fresh v in_scope) => k0.
         rewrite -> lookupVarEnv_delVarEnv_eq by auto.
         destruct (lookupVarEnv env var) eqn:INSUBST; [|auto].
         rewrite NC !elem_cons !elem_nil !orb_false_r.
         rewrite andb_diag Eq_sym EQv //.
       ++ unfold Id in *.
          rewrite lookupVarEnv_delVarEnv_neq; try solve [subst_certificate]; last by rewrite EQv.
          destruct (lookupVarEnv env var) eqn:LU.
          ** right. exists c. auto.
          ** auto.
    -- rewrite substIdEnv_Mk_Subst.
       rewrite -> getInScopeVars_extendInScopeSet.
       eapply StrongSubset_trans with (vs2 := extendVarSet (minusDom vs env) v).
       eapply minusDom_extend; try solve [subst_certificate].
       rewrite -> NC.
       eapply StrongSubset_extend; try solve [subst_certificate].
       auto.
    -- rewrite substIdEnv_Mk_Subst.
       intro var.
       destruct (v == var) eqn:Evvar.
       rewrite -> lookupVarEnv_delVarEnv_eq; auto.
       rewrite -> lookupVarEnv_delVarEnv_neq; try solve [subst_certificate].
       specialize (LVi var).
       destruct (lookupVarEnv env var); auto.
       rewrite -> getInScopeVars_extendInScopeSet.
       eapply WellScoped_StrongSubset; eauto.
       eapply StrongSubset_extend_fresh; try solve [subst_certificate].
       rewrite <- NC.
       eapply uniqAway_lookupVarSet_fresh.
       unfold CoreBndr in *. intro h. rewrite h in Evvar. discriminate.

  + (* Binder needs to be freshened. *)
    unfold WellScoped_Subst.
    unfold SubstExtends.
    change (substIdEnv subst) with env.
    change (substInScope subst) with in_scope.
    repeat split.
    all: try rewrite /getSubstInScopeVars.
    all: try rewrite substInScope_Mk_Subst.
    all: try solve [subst_certificate].
    -- simpl. eauto.
    -- rewrite Forall.Forall_cons_iff.
       split.
       eapply GoodLocalVar_uniqAway; auto.
       eauto.
    -- unfold freshList.
       intros v0 InV.
       rewrite -> elem_cons, orE in InV.
       destruct InV as [InV1 | InV2].
       erewrite -> lookupVarSet_eq; eauto.
       apply uniqAway_lookupVarSet_fresh.
       rewrite -> elem_nil in InV2.
       discriminate.
    -- rewrite <- getInScopeVars_extendInScopeSetList.
       rewrite -> extendInScopeSetList_cons.
       rewrite -> extendInScopeSetList_nil.
       eapply StrongSubset_refl.
    -- rewrite <- getInScopeVars_extendInScopeSetList.
       rewrite -> extendInScopeSetList_cons.
       rewrite -> extendInScopeSetList_nil.
       eapply StrongSubset_refl.
    -- (* We have freshened binder v. *)
       rewrite substIdEnv_Mk_Subst.
       rewrite <- getInScopeVars_extendInScopeSetList.
       rewrite -> extendInScopeSetList_cons.
       rewrite -> extendInScopeSetList_nil.
       rewrite -> getInScopeVars_extendInScopeSet.
       rewrite -> getInScopeVars_extendInScopeSet.
       pose (k0 := uniqAway_lookupVarSet_fresh v in_scope).
       clearbody k0.
       set (v' := uniqAway in_scope v) in *.

       eapply StrongSubset_trans.
       eapply StrongSubset_minusDom_extend_extend; auto.
       eapply StrongSubset_trans.
       eapply StrongSubset_minusDom_left; auto.
       eapply StrongSubset_extendVarSet_fresh; try solve [subst_certificate].
       auto.
    -- rewrite substIdEnv_Mk_Subst.
       unfold VarEnvExtends.
       intro var. specialize_all var.
       destruct (v == var) eqn:EQ.
       ++ rewrite -> lookupVarEnv_extendVarEnv_eq; auto.
       left. exists (uniqAway in_scope v).
       repeat split. econstructor; eauto.
       rewrite -> elem_cons.
       rewrite -> Base.Eq_sym.
       rewrite -> orb_true_iff.
       left. auto.
       ++ rewrite -> lookupVarEnv_extendVarEnv_neq; try solve [subst_certificate].
          destruct (lookupVarEnv env var) eqn:LU.
          ** right. exists c. auto.
          ** auto.
          ** unfold Id in *. intro h. rewrite -> h in EQ. auto.
    -- rewrite substIdEnv_Mk_Subst.
       eapply StrongSubset_trans; eauto.
       eapply StrongSubset_minusDom_extend_extend; auto.
       eapply StrongSubset_trans; eauto.
       rewrite -> getInScopeVars_extendInScopeSet.
       eapply StrongSubset_extendVarSet_fresh; try solve [subst_certificate].
       eapply uniqAway_lookupVarSet_fresh.
    -- rewrite substIdEnv_Mk_Subst.
       intros var.
       destruct (v == var) eqn:Eq_vvar.
       - rewrite -> lookupVarEnv_extendVarEnv_eq; auto.
         unfold WellScoped, WellScopedVar.
         destruct_match.
         rewrite -> getInScopeVars_extendInScopeSet.
         rewrite -> lookupVarSet_extendVarSet_self by auto.
         split.
         eapply almostEqual_refl.
         eapply GoodLocalVar_uniqAway in GLVv.
         unfold GoodLocalVar in GLVv.
         eapply GLVv.
         eapply GoodLocalVar_uniqAway in GLVv.
         unfold GoodLocalVar in GLVv.
         eapply GLVv.
       - rewrite -> lookupVarEnv_extendVarEnv_neq; auto.
         specialize (LVi var).
         destruct lookupVarEnv eqn:LU.
         rewrite -> getInScopeVars_extendInScopeSet.
         eapply WellScoped_StrongSubset; eauto.
         eapply StrongSubset_extendVarSet_fresh; try solve [subst_certificate].
         eapply uniqAway_lookupVarSet_fresh.
         auto.
         unfold Id in *.
         intro h. rewrite -> h in Eq_vvar. discriminate.
Qed.

Lemma WellScoped_Subst_substBndr : forall subst subst' bndr' v vs,
  forall (SB : substBndr subst v = (subst', bndr')),
  GoodLocalVar v ->
  WellScoped_Subst subst vs ->
  SubstExtends subst (cons v nil) subst' (cons bndr' nil) /\
  WellScoped_Subst subst' (extendVarSet vs v).
Proof.
  intros. unfold substBndr in SB.
  eapply WellScoped_Subst_substIdBndr; eauto.
Qed.

Lemma WellScoped_substBndr : forall subst subst' bndr' body v vs,
  forall (IH : forall subst',
      WellScoped_Subst subst' (extendVarSet vs v) ->
      WellScoped (substExpr subst' body)
                 (getSubstInScopeVars subst')),
  forall (SB : substBndr subst v = (subst', bndr')),
  GoodLocalVar v ->
  WellScoped_Subst subst vs ->
  WellScoped (substExpr subst' body)
             (extendVarSet (getSubstInScopeVars subst) bndr').
Proof.
  intros subst subst' bndr' body v vs IH SB GLV WSS.
  destruct (WellScoped_Subst_substBndr _ _ _ _ _ SB GLV WSS) as [HSE HWS].
  unfold SubstExtends in HSE.
  destruct HSE as [LEN [ND [GLV' [FR [SE [MD [VE [Wi1 [Vi1 [We1 [Wi2 [Vi2 We2]]]]]]]]]]]].
  eapply WellScoped_StrongSubset; try solve [subst_certificate].
  eapply IH. eauto.
  unfold getSubstInScopeVars.
  unfold StrongEquivalence in SE. destruct SE as [SE1 SE2].
  eapply StrongSubset_trans.
  2: { exact SE1. }
  simpl.
  eapply StrongSubset_refl.
Qed.


Ltac lift_let_in_eq H :=
   match goal with 
      | [ SB : (let '(x,y) := ?sb in ?e1) = ?e2 |- _ ] => 
         destruct sb as [ x y ] eqn:H
      | [ SB : ?e2 = (let '(x,y) := ?sb in ?e1) |- _ ] => 
         destruct sb as [ x y ] eqn:H
    end.


Lemma GoodLocalVar_substIdBndr : forall s1 s2 bndr bndr' subst subst',
  GoodLocalVar bndr ->
  substIdBndr s1 s2 subst bndr = (subst', bndr') ->
  GoodLocalVar bndr'.
Proof.
  intros s1 s2 bndr bndr' subst subst' GLV SB.
  unfold substIdBndr in SB.
  (* substIdInfo always returns None; maybeModifyIdInfo None x = x *)
  unfold substIdInfo in SB. simpl Id.maybeModifyIdInfo in SB.
  inversion SB; clear SB; subst.
  eapply GoodLocalVar_uniqAway; assumption.
Qed.

Lemma GoodLocalVar_substBndr : forall bndr bndr' subst subst',
  GoodLocalVar bndr ->
  substBndr subst bndr = (subst', bndr') ->
  GoodLocalVar bndr'.
Proof.
  intros. unfold substBndr in H0.
  eapply GoodLocalVar_substIdBndr; eauto.
Qed.

Lemma SubstExtends_step : forall a s' y bndrs subst subst' ys,
  SubstExtends subst (a :: nil) s' (y :: nil) ->
  SubstExtends s' bndrs subst' ys ->
  SubstExtends subst ((a :: nil) ++ bndrs) subst' (y :: ys).
Proof.
  intros a s' y bndrs subst subst' ys SE1 SE2.
  replace (y :: ys) with (cons y nil ++ ys); try reflexivity.
  eapply SubstExtends_trans with (s2 := s'); [|exact SE1|exact SE2].
  destruct SE1 as [LEN [ND [GLV [FR [[SEa SEb] [MD [VE
    [Wi1 [Vi1 [We1 [Wi2 [Vi2 We2]]]]]]]]]]]].
  destruct SE2 as [LEN' [ND' [GLV' [FR' REST]]]].
  unfold Disjoint. simpl. constructor; [|constructor].
  intro IN. rewrite -> In_varUnique_elem in IN.
  specialize (FR' y IN). specialize (SEb y).
  rewrite -> extendVarSetList_cons, extendVarSetList_nil in SEb.
  rewrite -> lookupVarSet_extendVarSet_self in SEb by exact Wi1.
  rewrite FR' in SEb. exact SEb.
Qed.



Lemma SubstExtends_mapAccumL_substBndr :
  forall (bndrs : list Var) (subst subst' : Subst) (bndrs' : list Var) (vs : VarSet)
    (SB: Traversable.mapAccumL substBndr subst bndrs = (subst', bndrs')),
    Forall GoodLocalVar bndrs ->
    WellScoped_Subst subst vs ->
    SubstExtends subst bndrs subst' bndrs' /\
    WellScoped_Subst subst' (extendVarSetList vs bndrs).
Proof.
  induction bndrs; intros.
  + rewrite -> mapAccumL_nil in SB.
    inversion SB; subst; clear SB.
    split. eapply SubstExtends_refl; eauto.
    rewrite -> extendVarSetList_nil. auto.
  + rewrite -> mapAccumL_cons in SB.
    lift_let_in_eq Hsb1.
    lift_let_in_eq Hsb2.
    inversion SB. subst; clear SB.
    inversion H.
    destruct (WellScoped_Subst_substBndr _ _ y _ _  Hsb1 ltac:(auto) H0) as [h0 h1].
    destruct (IHbndrs s' subst' ys _ Hsb2 ltac:(auto) h1) as [h2 h3].

    replace (a :: bndrs) with (cons a nil ++ bndrs); try reflexivity.
    subst. 
    split.
    ++ eapply SubstExtends_step; eauto.
    ++ simpl. rewrite -> extendVarSetList_cons.
       auto.
Qed.


Lemma SubstExtends_substBndrs : forall bndrs subst subst' bndrs' vs,
  forall (SB : substBndrs subst bndrs = (subst', bndrs')),
    Forall GoodLocalVar bndrs ->
    WellScoped_Subst subst vs ->
    SubstExtends subst bndrs subst' bndrs' /\
    WellScoped_Subst subst' (extendVarSetList vs bndrs).
Proof.
  intros. unfold substBndrs in SB.
  eapply SubstExtends_mapAccumL_substBndr; eauto.
Qed.

Lemma SubstExtends_substRecBndrs : forall bndrs subst subst' bndrs' vs,
  forall (SB : substRecBndrs subst bndrs = (subst', bndrs')),
  Forall GoodLocalVar bndrs ->
  WellScoped_Subst subst vs ->
  SubstExtends subst bndrs subst' bndrs'  /\
  WellScoped_Subst subst' (extendVarSetList vs bndrs).
Proof.
  unfold substRecBndrs.
  intros.
  destruct ( Traversable.mapAccumL
           (substIdBndr (Datatypes.id &"rec-bndr") (Err.error Panic.someSDoc)) subst
           bndrs) eqn:EQ.
  inversion SB; subst; clear SB.
  revert bndrs subst subst' bndrs' vs EQ H H0.
  induction bndrs; intros.
  + rewrite -> mapAccumL_nil in EQ.
    inversion EQ; subst.
    split. eapply SubstExtends_refl; eauto.
    rewrite -> extendVarSetList_nil. auto.
  + rewrite -> mapAccumL_cons in EQ.
    lift_let_in_eq Hsb1.
    lift_let_in_eq Hsb2.
    inversion EQ; subst; clear EQ.
    rewrite -> Forall.Forall_cons_iff in H.
    destruct H.
    eapply WellScoped_Subst_substIdBndr in Hsb1; eauto.
    destruct Hsb1 as [? ?].

    destruct (IHbndrs s' subst' _ (extendVarSet vs a) Hsb2) as [h2 h3]; auto.
    replace (a :: bndrs) with (cons a nil ++ bndrs); try reflexivity.
    split.
    ++ eapply SubstExtends_step; eauto.
    ++ simpl. rewrite -> extendVarSetList_cons.
       auto.
Qed.
  
Lemma lookupIdSubst_ok v subst vs :
  WellScoped_Subst subst      vs ->
  WellScoped       (Mk_Var v) vs ->
  WellScoped (lookupIdSubst subst v) (getSubstInScopeVars subst).
Proof.
  rewrite /lookupIdSubst /getSubstInScopeVars => WSsubst WSvar.
  destruct WSsubst as [ss [vv [Wvs [Vvs [Wis [Vis Wenv]]]]]]. specialize (vv v).
  unfold WellScoped,WellScopedVar in WSvar.
  destruct (isLocalId v) eqn:HLocal.
  -- (* isLocalId v = true *)
    cbn beta iota delta [negb].
    destruct (lookupVarEnv (substIdEnv subst) v) eqn:HLookup.
      + tauto.
      + unfold StrongSubset in ss.
        specialize (ss v).
        rewrite -> lookupVarSet_minusDom_1 in ss by auto.
        apply isLocalVar_isLocalId in HLocal.
        rewrite HLocal in WSvar.
        destruct (lookupVarSet vs v) as [vvs|] eqn:LVS; try contradiction.
        destruct (substInScope subst) as [in_scope_vs] eqn:Hsubst_is.
        simpl lookupInScope. simpl getInScopeVars.
        simpl getInScopeVars in ss.
        destruct (lookupVarSet in_scope_vs v) as [vis|] eqn:LI; try contradiction.
        move: WSvar => [v2_eq h].
        assert (ae_v_vis : almostEqual v vis) by (eapply almostEqual_trans; eauto).
        assert (HWS: WellScopedVar vis in_scope_vs).
        { unfold WellScopedVar.
          destruct (isLocalVar vis) eqn:Lv2.
          - erewrite lookupVarSet_eq.
            2: { move: Vis => VV.
                 unfold ValidVarSet in VV. rewrite -> Base.Eq_sym. eapply VV. exact LI. }
            rewrite LI. split.
            + apply almostEqual_refl.
            + eapply GoodVar_almostEqual; eauto.
          - exact (GoodVar_almostEqual v vis h ae_v_vis).
        }
        exact HWS.
 -- (* isLocalId v = false - Impossible case *)
    cbn beta iota delta [negb].
    unfold WellScopedVar.
    destruct (isLocalVar v) eqn:h.
    + (* isLocalVar v = true, but isLocalId v = false *)
      destruct (lookupVarSet vs v) eqn:h0; try contradiction.
      unfold GoodVar in WSvar.
      destruct WSvar as [ ? h1 ].
      destruct v; simpl in *; try done.
      unfold isLocalVar, isGlobalId in h. unfold isLocalId in HLocal.
      rewrite HLocal in h. done.
    + (* isLocalVar v = false *)
      unfold WellScoped, WellScopedVar. rewrite h. exact WSvar.
Qed.


 
Lemma substExpr_ok : forall e vs subst,
    WellScoped_Subst subst vs ->
    WellScoped e vs ->
    WellScoped (substExpr subst e)
               (getSubstInScopeVars subst).
Proof.
  intros e.
  apply (core_induct e).

  - (* Var case *)
    intros v vs subst WSS WSvar.
    change (substExpr subst (Mk_Var v)) with (lookupIdSubst subst v).
    eapply lookupIdSubst_ok; eassumption.

  - (* Lit case *)
    intros. unfold substExpr, substExpr_.
    unfold WellScoped in *; auto.

  - (* App case *)
    intros e1 e2 IH1 IH2 vs subst WSS WSapp.
    rewrite substExpr_App.
    unfold WellScoped in *; fold WellScoped in *.
    destruct WSapp as [WS1 WS2].
    split; eauto.

  - (* Lam case *)
    intros v body IH vs subst WSS WSlam.
    rewrite substExpr_Lam.
    destruct (substBndr subst v) as [subst' bndr'] eqn:SB.
    unfold WellScoped in *; fold WellScoped in *.
    destruct WSlam as [GLV WSbody].
    split.
    + eapply GoodLocalVar_substBndr; eauto.
    + eapply WellScoped_substBndr; eauto.

  - (* Let case *)
    destruct binds.
    + (* NonRec *)
      intros body He0 Hbody vs subst WSS WSlet.
      rewrite substExpr_LetNonRec.
      destruct (substBndr subst c) as [subst' bndr'] eqn:SB.

      unfold WellScoped in *. fold WellScoped in *.
      destruct WSlet as [[GLV WSe] WSb].

      split; only 1: split; eauto.
      ++ eapply GoodLocalVar_substBndr; eauto.
      ++ unfold bindersOf in *.
         hs_simpl.
         hs_simpl in WSb.
         eapply WellScoped_substBndr; eauto.

    + (* Rec *)
      intros body IHrhs IHbody vs subst WSvs WSe.
      rewrite substExpr_Let.
      rewrite substBind_Rec'.
      cbv zeta.
      destruct WSe as [[GLV [ND FF]] WSB].

      unfold bindersOf in WSB.
      rewrite -> bindersOf_Rec_cleanup in WSB.

      destruct (List.unzip l) as [vars rhss] eqn:UZ.

      assert (EQL : length vars = length rhss).
      { eapply unzip_equal_length; eauto. }
      apply unzip_zip in UZ.
      subst l.

      rewrite -> map_fst_zip in *; auto.
      rewrite -> map_snd_zip in *; auto.

      assert (NDV: NoDup vars). eapply NoDup_map_inv; eauto.

      (* Save GLV as Forall GoodLocalVar vars before destructive rewrites *)
      assert (GLVV : Forall GoodLocalVar vars).
      { rewrite <- Forall.Forall_map with (f := fst) in GLV.
        rewrite -> map_fst_zip in GLV; auto. }

      destruct (substRecBndrs subst vars) as [subst' bndrs'] eqn:SRB.
      eapply SubstExtends_substRecBndrs in SRB; eauto.
      destruct_one_pair.
      rewrite -> Forall.Forall'_Forall in FF.
      rewrite -> Forall_forall in FF.
      unfold WellScoped in *. fold WellScoped in *.

      set (rhss' := map (substExpr subst') rhss).
      assert (LRR : length bndrs' = length rhss').
      { unfold rhss'. rewrite -> map_length. destruct_SubstExtends.
        unfold CoreBndr, CoreExpr, Id in *. rewrite <- H. auto. }
      assert (LBR : length bndrs' = length rhss).
      { unfold rhss' in LRR. rewrite -> map_length in LRR. auto. }

      repeat split.
      ++ (* Forall GoodLocalVar (fst) on zipped pairs *)
         destruct_SubstExtends.
         rewrite <- Forall.Forall_map with (f := fst).
         rewrite -> map_fst_zip; auto.
      ++ (* NoDup varUnique *)
         destruct_SubstExtends.
         rewrite -> map_fst_zip; auto.
      ++ (* Forall' WellScoped *)
         rewrite -> Forall.Forall'_Forall.
         rewrite -> Forall_forall.
         intros x Hx.
         destruct x as [bndr' rhs'].
         simpl.
         rewrite -> map_fst_zip; auto.
         destruct (In_zip_snd rhss Hx) as [rhs InR]; auto.
         destruct (In_zip_fst vars InR) as [bndr InB].
         { unfold rhss'. rewrite -> map_length. auto. }
         apply In_zip_swap in InB.
         specialize (IHrhs bndr rhs InB).
         assert (rhs' = substExpr subst' rhs).
         { unfold rhss' in InR. apply In_zip_map in InR. auto. }
         specialize (FF (bndr, rhs) InB).
         subst rhs'.
         eapply WellScoped_substBody with (vars := vars).
         ** intros subst0 WS0. eapply IHrhs; eauto.
         ** exact GLVV.
         ** eauto.
         ** auto.
      ++ (* WellScoped body *)
         unfold bindersOf.
         rewrite -> bindersOf_Rec_cleanup.
         rewrite -> map_fst_zip; auto.
         eapply WellScoped_substBody with (vars := vars).
         ** intros subst0 WS0. eapply IHbody; eauto.
         ** exact GLVV.
         ** eauto.
         ** auto.

  - (* Case *)
    intros scrut bndr ty alts IHscrut IHalts vs subst WSS WScase.
    rewrite substExpr_Case'.
    destruct (substBndr subst bndr) as [subst' bndr'] eqn:SB.
    unfold WellScoped in *. fold WellScoped in *.
    destruct WScase as [WSscrut [GLV WSalts]].
    rewrite -> Forall.Forall'_Forall in *.
    rewrite -> Forall_forall in *.
    split; [|split].
    + eauto.
    + eapply GoodLocalVar_substBndr; eauto.
    + intros alt IA.
      unfold substAlt in IA.
      rewrite -> in_map_iff in IA.
      destruct IA as [[dc pats rhs] [IAA IN]].
      destruct (substBndrs subst' pats) as [subst'' bndr''] eqn:SB2.
      destruct alt as [dc0 bdnr''0 ss0]. inversion IAA. subst. clear IAA.
      pose (wf := WSalts _ IN). clearbody wf. simpl in wf.
      simpl.
      destruct_one_pair.

      destruct (WellScoped_Subst_substBndr _ _ _ _ vs SB) as [h0 h1]; auto.

      destruct (SubstExtends_substBndrs _ _ _ _ (extendVarSet vs bndr)
                                        SB2) as [h2 h3]; auto.
      split.
      { destruct_SubstExtends. auto. }

      eapply WellScoped_StrongSubset.
      eapply IHalts. eapply IN.
      eauto.
      rewrite -> extendVarSetList_cons in *.
      auto.
      destruct_SubstExtends.
      eapply StrongSubset_trans; eauto.
      rewrite -> extendVarSetList_cons in *.
      rewrite -> extendVarSetList_nil in *.
      eapply StrongSubset_extendVarSetList.
      eauto.
      all: unfold getSubstInScopeVars in *; eauto.
      apply extendVarSetList_WF.
      exact (WellScoped_Subst_scope_WF _ _ WSS).

  - (* Cast case *)
    intros e0 co IH vs subst WSS WScast.
    rewrite substExpr_Cast.
    unfold WellScoped in *; fold WellScoped in *.
    eauto.

  - (* Type case *)
    intros ty vs subst WSS WSty.
    unfold substExpr, substExpr_.
    unfold WellScoped in *; auto.

  - (* Coercion case *)
    intros co vs subst WSS WSco.
    unfold substExpr, substExpr_.
    unfold WellScoped in *; auto.
Qed.

Lemma WellScoped_substExpr : forall e vs subst,
    WellScoped_Subst subst vs ->
    WellScoped e vs ->
    WellScoped (substExpr subst e)
               (getSubstInScopeVars subst).
Proof. intros. eapply substExpr_ok; eauto. Qed.


Print Assumptions WellScoped_substExpr.
Print Assumptions lookupIdSubst_ok.
