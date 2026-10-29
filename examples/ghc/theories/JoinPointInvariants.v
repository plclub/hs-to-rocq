Require Import Id.
Require Import Core.
Require Import BasicTypes.
Import GHC.Base.Notations.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.BinNat.
Require Import Psatz.

Import ListNotations.

Require Import Proofs.Forall.
Require Import Proofs.Core.
Require Import Proofs.CoreInduct.
Require Import Proofs.Var.
Require Import Proofs.VarSet.
Require Import Proofs.VarSetStrong.
Require Import Proofs.GhcTactics.
Require Import Proofs.VarSetFSet.

(* Membership and subset are extensional even on raw sets. Structural
   operations below use explicit preservation evidence, not Proper instances. *)
Local Lemma disjoint_del_rev s xs t : WF s -> Axioms.ValidVarSet s -> WF t ->
  disjointVarSet (delVarSetList s (rev xs)) t = disjointVarSet (delVarSetList s xs) t.
Proof.
  intros W V T. apply disjointVarSet_m; try solve [solve_varset_inv].
  - apply delVarSetList_rev; exact W.
  - reflexivity.
Qed.

#[local] Instance Subset_Equal_m : Morphisms.Proper
  (Morphisms.respectful Equal (Morphisms.respectful Equal iff)) Subset.
Proof. intros s t E u v F; unfold Subset; setoid_rewrite E; setoid_rewrite F; reflexivity. Qed.

#[local] Instance elemVarSet_Equal_m x : Morphisms.Proper
  (Morphisms.respectful Equal Logic.eq) (elemVarSet x).
Proof. intros s t E. apply Bool.eq_true_iff_eq. exact (E x). Qed.

Ltac fresh_disjoint H :=
  lazymatch type of H with
  | disjointVarSet ?t ?u = true =>
    eapply (disjointVarSet_subVarSet_l _ t u);
      [solve_varset_inv | solve_varset_inv | solve_varset_inv |
       solve_varset_inv | solve_varset_inv | exact H |]
  end.

#[local] Hint Resolve emptyVarSet_WF unitVarSet_WF mkVarSet_WF
  extendVarSet_WF extendVarSetList_WF delVarSet_WF delVarSetList_WF
  emptyVarSet_valid unitVarSet_valid mkVarSet_valid
  extendVarSet_valid extendVarSetList_valid delVarSet_valid delVarSetList_valid : core.

Set Bullet Behavior "Strict Subproofs".

Open Scope nat_scope.

Notation "a =? b" := (Nat.eqb a b).
Notation "a <=? b" := (Nat.leb a b).
Notation "a <? b" := (Nat.ltb a b).

(** * Join point invariants *)

(**
The following is taken from the GHC source code:

Note [Invariants on join points]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Join points must follow these invariants:

  1. All occurrences must be tail calls. Each of these tail calls must pass the
     same number of arguments, counting both types and values; we call this the
     "join arity" (to distinguish from regular arity, which only counts values).

  2. For join arity n, the right-hand side must begin with at least n lambdas.
     No ticks, no casts, just lambdas!  C.f. CoreUtils.joinRhsArity.

  2a. Moreover, this same constraint applies to any unfolding of the binder.
     Reason: if we want to push a continuation into the RHS we must push it
     into the unfolding as well.

  3. If the binding is recursive, then all other bindings in the recursive group
     must also be join points.

  4. The binding's type must not be polymorphic in its return type (as defined
     in Note [The polymorphism rule of join points]).
*)

(** 

We can check 1, 2, 3.

We will be able to check 2a when we translate more of IdInfo.

We will be able to check 4 when we translate types.

Additionally, we found these invariant:

 * The join arity must be non-negative.
 * A lambda-, case- or pattern-bound variable is not a join point
*)

(** ** [updJPS] and [updJPSs] *)

(**
As we go under a binder [x], we either have to add it to the set of valid
join points, or remove it from there, depending on whether [x] is a join point:
*)

Definition updJPS jps v :=
   if isJoinId v
   then extendVarSet jps v
   else delVarSet    jps v.

(**
We also have to do this for lists:
*)

Definition updJPSs jps vs :=
  fold_left updJPS vs jps.

Lemma updJPS_WF jps v : WF jps ->
  IntMapProofs.WF (Axioms.VarSet_IntMap (updJPS jps v)).
Proof. unfold updJPS; destruct (isJoinId v); intros; solve_varset_inv. Qed.

Lemma updJPS_valid jps v : WF jps -> Axioms.ValidVarSet jps ->
  Axioms.ValidVarSet (updJPS jps v).
Proof. unfold updJPS; destruct (isJoinId v); intros; solve_varset_inv. Qed.

Lemma updJPSs_WF jps vs : WF jps ->
  IntMapProofs.WF (Axioms.VarSet_IntMap (updJPSs jps vs)).
Proof.
  revert jps; induction vs; intros jps W; simpl; [exact W|].
  apply IHvs. apply updJPS_WF. exact W.
Qed.

Lemma updJPSs_valid jps vs : WF jps -> Axioms.ValidVarSet jps ->
  Axioms.ValidVarSet (updJPSs jps vs).
Proof.
  revert jps; induction vs; intros jps W V; simpl; [exact V|].
  apply IHvs; [apply updJPS_WF|apply updJPS_valid]; assumption.
Qed.

#[local] Hint Resolve updJPS_WF updJPS_valid updJPSs_WF updJPSs_valid : varset_inv.
#[local] Hint Resolve updJPS_WF updJPS_valid updJPSs_WF updJPSs_valid : core.

(**
These two functions behave very similar to [extendVarSet] and [delVarset], and we
have a number of simiar lemmas:
**)

Lemma updJPSs_nil:
  forall jps, updJPSs jps [] = jps.
Proof. intros. reflexivity. Qed.

Lemma updJPSs_cons:
  forall jps v vs, updJPSs jps (v :: vs) = updJPSs (updJPS jps v) vs.
Proof. intros. reflexivity. Qed.

Lemma updJPSs_singleton:
  forall jps v, updJPSs jps [v] = updJPS jps v.
Proof. intros. reflexivity. Qed.


Lemma updJPSs_append:
  forall jps vs1 vs2, updJPSs jps (vs1 ++ vs2) = updJPSs (updJPSs jps vs1) vs2.
Proof. intros. apply fold_left_app. Qed.

Lemma updJPS_not_joinId:
  forall jps v,
  isJoinId v = false ->
  updJPS jps v = delVarSet jps v.
Proof. intros. unfold updJPS. rewrite H. reflexivity. Qed.

Lemma updJPS_joinId:
  forall jps v,
  isJoinId v = true ->
  updJPS jps v = extendVarSet jps v.
Proof. intros. unfold updJPS. rewrite H. reflexivity. Qed.

Lemma updJPSs_not_joinId:
  forall jps vs,
  forallb (fun v => negb (isJoinId v)) vs = true ->
  updJPSs jps vs = delVarSetList jps vs.
Proof. 
  intros. induction vs using rev_ind.
  * rewrite delVarSetList_nil. reflexivity.
  * rewrite updJPSs_append, updJPSs_cons, updJPSs_nil.
    rewrite delVarSetList_app, delVarSetList_cons, delVarSetList_nil.
    rewrite forallb_app in H. simpl in H. rewrite andb_true_r, andb_true_iff, negb_true_iff in H. 
    rewrite IHvs by intuition.
    rewrite updJPS_not_joinId by intuition.
    reflexivity.
Qed.

Lemma updJPSs_joinId:
  forall jps vs,
  forallb isJoinId vs = true ->
  updJPSs jps vs = extendVarSetList jps vs.
Proof. 
  intros. induction vs using rev_ind.
  * rewrite extendVarSetList_nil. reflexivity.
  * rewrite updJPSs_append, updJPSs_cons, updJPSs_nil.
    rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil.
    rewrite forallb_app in H. simpl in H. rewrite andb_true_r, andb_true_iff in H. 
    rewrite IHvs by intuition.
    rewrite updJPS_joinId by intuition.
    reflexivity.
Qed.

Lemma elemVarSet_updJPS_l:
  forall v jps v',
  WF jps ->
  (v' GHC.Base.== v) = false ->
  elemVarSet v (updJPS jps v') = elemVarSet v jps.
Proof.
  intros.
  unfold updJPS.
  destruct_match.
   + rewrite elemVarSet_extendVarSet by assumption.
     rewrite H0.
    reflexivity.
   + rewrite elemVarSet_delVarSet by assumption.
     rewrite H0.
    reflexivity.
Qed.

Lemma elemVarSet_updJPS_cong:
  forall v jps1 jps2 v',
  WF jps1 -> WF jps2 ->
  ((v' GHC.Base.== v) = false -> elemVarSet v jps1 = elemVarSet v jps2) ->
  elemVarSet v (updJPS jps1 v') = elemVarSet v (updJPS jps2 v').
Proof.
  intros.
  unfold updJPS.
  destruct_match.
   + rewrite !elemVarSet_extendVarSet by assumption.
    destruct (v' GHC.Base.== v); intuition.
   + rewrite !elemVarSet_delVarSet by assumption.
    destruct (v' GHC.Base.== v); intuition.
Qed.


Lemma elemVarSet_updJPSs_l:
  forall v jps vs,
  WF jps ->
  elemVarSet v jps  = true  ->
  elemVarSet v (mkVarSet vs) = false ->
  elemVarSet v (updJPSs jps vs) = true .
Proof.
   intros v jps vs W M N.
   revert jps W M N. induction vs; intros.
   * apply M.
   * simpl.
     rewrite elemVarSet_mkVarSet_cons in N.
     destruct N as [Ne N].
     apply IHvs.
     + apply updJPS_WF; assumption.
     + rewrite elemVarSet_updJPS_l by assumption. assumption.
     + assumption.
Qed.

Lemma subVarSet_updJPS_extendVarSet:
  forall jps isvs v,
  WF jps -> WF isvs -> Axioms.ValidVarSet jps ->
  subVarSet jps isvs = true ->
  subVarSet (updJPS jps v) (extendVarSet isvs v) = true.
Proof.
   intros jps isvs v Wj Wi Vj S.
   unfold updJPS.
   destruct_match.
   * apply subVarSet_extendVarSet_both; assumption.
   * eapply subVarSet_trans with (t := jps).
     all: try solve [solve_varset_inv].
     + apply subVarSet_delVarSet; assumption.
     + apply subVarSet_extendVarSet; assumption.
Qed.

Lemma subVarSet_updJPSs_extendVarSetList:
  forall jps isvs vs,
  WF jps -> WF isvs -> Axioms.ValidVarSet jps ->
  subVarSet jps isvs = true ->
  subVarSet (updJPSs jps vs) (extendVarSetList isvs vs) = true.
Proof.
   intros jps isvs vs Wj Wi Vj S.
   revert jps isvs Wj Wi Vj S. induction vs; intros.
   * rewrite updJPSs_nil, extendVarSetList_nil.
     assumption.
   * rewrite updJPSs_cons, extendVarSetList_cons.
     apply IHvs; try solve [solve_varset_inv].
     apply subVarSet_updJPS_extendVarSet; assumption.
Qed.

(** ** The definition of the invariants *)

(**
In this module, we define the invariant as a boolean predicate, using [Fixpoint].

Ideally, we would define these funtions

 * [isJoinPointsValid] for expressions (with an accumulator to count the number
   of arguments this expression is applied to).
 * [isJoinRHS] for the right-hand sides of join points (to strip off the correct
   number of [Lam] constructors)
 * [isJoinPointsValidPair] for when a pair (binder + definition) is valid, which
   builds on the two aboe.

Unfortunately, requirements from Coq’s termination checker make things a bit
more complicated…

We first define [isJoinPointsValidPair_aux], which is [isJoinPointsValidPair]
abstracted over the other two.
*)

Definition isJoinPointsValidPair_aux
  isJoinPointsValid isJoinRHS_aux
  (v : CoreBndr) (rhs : CoreExpr) (jps : VarSet) : bool :=
    match isJoinId_maybe v with
    | None => isJoinPointsValid rhs 0 emptyVarSet  (* Non-tail-call position *)
    | Some a => 
      if (a =? 0) (* Uh, all for the termination checker *)
      then isJoinPointsValid rhs 0 jps            (* tail-call position *)
      else isJoinRHS_aux a rhs jps                (* tail-call position *)
    end.

(** See below for why we have the [a=0] case here. *)


(** Now the other two functions: *)

Fixpoint isJoinPointsValid (e : CoreExpr) (n : nat) (jps : VarSet) {struct e} : bool :=
  match e with
  | Mk_Var v => match isJoinId_maybe v with
    | None => true
    | Some a => isLocalVar v && (a <=? n) && elemVarSet v jps
    end
  | Lit l => true
  | App e1 e2 =>
    isJoinPointsValid e1 (n+1) jps &&   (* Tail-call-position *)
    isJoinPointsValid e2 0 emptyVarSet    (* Non-tail-call position *)
  | Lam v e =>
    negb (isJoinId v) &&
    isJoinPointsValid e 0 emptyVarSet     (* Non-tail-call position *)
  | Let (NonRec v rhs) body => 
      isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS_aux v rhs jps &&
      let jps' := updJPS jps v in
      isJoinPointsValid body 0 jps'
  | Let (Rec pairs) body => 
      negb (List.null pairs) &&  (* Not join-point-specific, could be its own invariant *)
      (forallb (fun p => negb (isJoinId (fst p))) pairs ||
       forallb (fun p =>       isJoinId (fst p))  pairs) &&
      let jps' := updJPSs jps (map fst pairs) in
      forallb (fun '(v,e) => isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS_aux v e jps') pairs &&
      isJoinPointsValid body 0 jps'
  | Case scrut bndr ty alts  => 
    negb (isJoinId bndr) &&
    isJoinPointsValid scrut 0 emptyVarSet &&  (* Non-tail-call position *)
    let jps' := delVarSet jps bndr in
    forallb (fun '(Mk_Alt dc pats rhs) =>
      let jps'' := delVarSetList jps' pats  in
      forallb (fun v => negb (isJoinId v)) pats &&
      isJoinPointsValid rhs 0 jps'') alts  (* Tail-call position *)
  | Cast e _ =>    isJoinPointsValid e 0 jps
(*  | Tick _ e =>    isJoinPointsValid e 0 jps *)
  | Mk_Type _  =>   true
  | Mk_Coercion _ => true 
  end
with isJoinRHS_aux (a : JoinArity) (rhs : CoreExpr) (jps : VarSet) {struct rhs} : bool :=
  if a <? 1 then false else
  match rhs with
    | Lam v e => negb (isJoinId v) &&
                 if a =? 1
                 then isJoinPointsValid e 0 (delVarSet jps v) (* tail-call position *)
                 else isJoinRHS_aux (a-1) e (delVarSet jps v)
    | _ => false
    end.

(**
The definition of [isJoinRHS_aux] is not what we want: Ideally, in the [Some] case in
[isJoinPointsValidPair_aux] we’d simply call [isJoinRHS], and if the join arity is actually
[0], then [isJoinRHS] callse [isJoinPointsValid] directly. But then the argument would not
decrease going from [isJoinRHS] to [isJoinPointsValid], and the termination checker would
not be happy. So we have to write [isJoinRHS_aux] in a way that it *always* destructs its
argument.
*)

(**
Convenience definitions, including the [isJoinRHS] we would have liked to write.
*)


Definition isJoinRHS rhs a jps :=
      if (a =? 0)
      then isJoinPointsValid rhs 0 jps
      else isJoinRHS_aux a rhs jps.


Definition isjoinPointsAlt : CoreAlt -> VarSet -> bool :=
  fun '(Mk_Alt dc pats rhs) jps =>
      let jps'' := delVarSetList jps pats  in
      forallb (fun v => negb (isJoinId v)) pats &&
      isJoinPointsValid rhs 0 jps''.

Definition isJoinPointsValidPair := isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS_aux.

(**
Conjuction of [isJoinId] and [isJoinPointsValidPair]
*)

Definition isValidJoinPointsPair
  (v : CoreBndr) (rhs : CoreExpr) (jps : VarSet) : bool :=
    match isJoinId_maybe v with
    | None => false (* NB *)
    | Some a => isJoinRHS rhs a jps
    end.



(** Join-point validity of whole programs *)

Definition isJoinPointsValidProgram (pgm : CoreProgram)  :=
  Forall (fun '(v,e) =>
    isJoinId v = false /\
    isJoinPointsValid e 0 emptyVarSet = true) (flattenBinds pgm).

(** ** Lemmas *)

Lemma isJoinPointsValidPair_isJoinPoints_isJoinRHS:
  forall v rhs jps a,
  isJoinPointsValidPair v rhs jps = true ->
  isJoinId_maybe v = Some a ->
  isJoinRHS rhs a jps = true.
Proof.
  intros.
  unfold isJoinPointsValidPair,isJoinPointsValidPair_aux in H.
  rewrite H0 in H.
  apply H.
Qed.

Lemma isJoinPointsValidPair_isJoinRHS:
  forall v rhs jps a,
  isJoinId_maybe v = Some a ->
  isJoinPointsValidPair v rhs jps = true <->
  isJoinRHS rhs a jps = true.
Proof.
  intros.
  unfold isJoinPointsValidPair,isJoinPointsValidPair_aux.
  rewrite H.
  unfold isJoinRHS.
  reflexivity.
Qed.

Lemma isJoinPointsValidPair_isJoinPointsValid:
  forall v rhs jps,
  isJoinId_maybe v = None ->
  isJoinPointsValidPair v rhs jps = true <->
  isJoinPointsValid rhs 0 emptyVarSet = true.
Proof.
  intros.
  unfold isJoinPointsValidPair,isJoinPointsValidPair_aux.
  rewrite H.
  unfold isJoinRHS.
  reflexivity.
Qed.



Lemma isValidJoinPointsPair_isJoinPointsValidPair:
  forall v rhs jps,
  isValidJoinPointsPair v rhs jps = true -> isJoinPointsValidPair v rhs jps = true.
Proof.
  intros.
  unfold isValidJoinPointsPair, isJoinPointsValidPair, isJoinPointsValidPair_aux in *.
  destruct_match.
  * assumption.
  * congruence.
Qed.

Lemma isValidJoinPointsPair_isJoinId:
  forall v rhs jps,
  isValidJoinPointsPair v rhs jps = true -> isJoinId v = true.
Proof.
  intros.
  unfold isValidJoinPointsPair in *.
  rewrite isJoinId_eq.
  destruct_match; congruence.
Qed.


Lemma Forall_isValidJoinPointsPair_forallb_isJoinId_isJoinPointsValidPair:
  forall pairs jps,
  Forall (fun p => isValidJoinPointsPair (fst p) (snd p) jps = true) pairs <->
  forallb (fun p : Var * Expr CoreBndr => isJoinId (fst p)) pairs = true /\
  forallb (fun '(v, e) => isJoinPointsValidPair v e jps) pairs = true.
Proof.
  intros.
  rewrite Forall_forall, !forallb_forall.
  split; intro; only 1: split.
  * intros [v e] HIn.
    specialize (H _ HIn).
    simpl in *.
    eapply isValidJoinPointsPair_isJoinId; eassumption.
  * intros [v e] HIn.
    specialize (H _ HIn).
    simpl in *.
    eapply isValidJoinPointsPair_isJoinPointsValidPair; eassumption.
  * intros [v e] HIn.
    destruct H.
    specialize (H _ HIn).
    specialize (H0 _ HIn).
    simpl in *.
    unfold isValidJoinPointsPair in *.
    rewrite isJoinId_eq in H.
    destruct_match; auto.
    eapply isJoinPointsValidPair_isJoinPoints_isJoinRHS; eassumption.
Qed.

Lemma isJoinRHS_mkLams:
  forall vs e jps,
  Forall (fun v => isJoinId v = false) vs ->
  isJoinPointsValid e 0 (delVarSetList jps vs) = true <->
  isJoinRHS (mkLams vs e) (length vs) jps = true.
Proof.
  intros. revert jps H.
  induction vs; intros jps Hdisjoint.
  * rewrite delVarSetList_nil.
    reflexivity.
  * simpl.
    replace (mkLams _ _) with (Lam a (mkLams vs e)) by reflexivity.
    rewrite delVarSetList_cons.
    unfold isJoinRHS.
    destruct_match.
    + apply PeanoNat.Nat.eqb_eq in Heq. congruence.
    + clear Heq.
      inversion_clear Hdisjoint.
      rewrite IHvs by assumption.
      simpl.
      rewrite PeanoNat.Nat.sub_0_r.
      unfold isJoinRHS.
      rewrite H.
      reflexivity.
Qed.

Lemma isJoinRHS_mkLams2:
  forall vs e jps,
  isJoinRHS (mkLams vs e) (length vs) jps = true ->
  Forall (fun v => isJoinId v = false) vs /\ isJoinPointsValid e 0 (updJPSs jps vs) = true.
Proof.
  intros. revert jps H.
  induction vs; intros jps H.
  * rewrite updJPSs_nil.
    intuition.
  * simpl.
    replace (mkLams _ _) with (Lam a (mkLams vs e)) in H by reflexivity.
    unfold isJoinRHS in H.
    destruct_match.
    + apply PeanoNat.Nat.eqb_eq in Heq. simpl in Heq. congruence.
    + clear Heq.
      simpl in H.
      rewrite PeanoNat.Nat.sub_0_r in H.
      rewrite andb_true_iff, negb_true_iff in H.
      destruct H as [Hnot_isJoin H].
      change (isJoinRHS (mkLams vs e) (length vs) (delVarSet jps a) = true) in H.
      specialize (IHvs _ H).
      unfold updJPS. rewrite Hnot_isJoin.
      intuition.
Qed.

Lemma isJoinRHS_mkLams3:
  forall e ja jps,
  isJoinRHS e ja jps = true ->
  exists body vs,
  e = mkLams vs body /\ ja = length vs.
Proof.
  intros. revert e jps H. induction ja; intros.
  * exists e. exists nil.
    repeat apply conj.
    + reflexivity.
    + reflexivity.
  * unfold isJoinRHS in H.
    destruct (PeanoNat.Nat.eqb_spec (S ja) 0); only 1: (exfalso; lia). clear n.
    destruct e; simpl in H; try congruence.
    simpl_bool.
    destruct H as [HnotJoinId H].
    rewrite negb_true_iff in HnotJoinId.
    rewrite PeanoNat.Nat.sub_0_r in H.
    change (isJoinRHS e ja (delVarSet jps c) = true) in H.
    specialize (IHja _ _ H).
    destruct IHja as [body [vs [Heq1 Heq2]]].
    subst.
    exists body. exists (c :: vs).
    repeat apply conj.
    + reflexivity.
    + reflexivity.
Qed.

Lemma isJoinPointsValid_mkVarApps:
  forall e n vs jps,
  Forall (fun v => isJoinId v = false) vs ->
  isJoinPointsValid e (n + length vs) jps = true ->
  isJoinPointsValid (mkVarApps e vs) n jps = true.
Proof.
  intros ???? Hnot_iJI HiJPV.
  unfold mkVarApps.
  rewrite Foldable.foldl'_is_foldl.
  rewrite Foldable.hs_coq_foldl_list.
  revert e HiJPV.
  induction Hnot_iJI; intros.
  * simpl.
    simpl in HiJPV. rewrite PeanoNat.Nat.add_0_r in HiJPV.
    assumption.
  * simpl.
    apply IHHnot_iJI; clear IHHnot_iJI.
    simpl.
    rewrite andb_true_iff. split.
    - simpl in HiJPV.
      replace (_ + _ + _) with (n + S (length l)) by lia. 
      assumption.
    - unfold varToCoreExpr. simpl.
      rewrite isJoinId_eq in H.
      destruct (isJoinId_maybe x); try reflexivity.
      discriminate.
Qed.

Lemma isJoinPointsValid_MkLetRec: forall pairs body jps,
  isJoinPointsValid (mkLetRec pairs body) 0 jps = true <->
  ( (forallb (fun p => negb (isJoinId (fst p))) pairs ||
     forallb (fun p =>       isJoinId (fst p))  pairs) &&
     let jps' := updJPSs jps (map fst pairs) in
     forallb (fun '(v,e) => isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS_aux v e jps') pairs &&
     isJoinPointsValid body 0 jps'
  ) = true.
Proof.
  intros.
  unfold mkLetRec.
  destruct pairs; try reflexivity.
Qed.

Lemma isJoinPointsValid_MkLet_Rec: forall pairs body jps,
  isJoinPointsValid (mkLet (Rec pairs) body) 0 jps = true <->
  ( (forallb (fun p => negb (isJoinId (fst p))) pairs ||
     forallb (fun p =>       isJoinId (fst p))  pairs) &&
     let jps' := updJPSs jps (map fst pairs) in
     forallb (fun '(v,e) => isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS_aux v e jps') pairs &&
     isJoinPointsValid body 0 jps'
  ) = true.
Proof.
  intros.
  destruct pairs; try reflexivity.
Qed.


(**
There may be more arguments passed to the expression.
*)

Lemma isJoinPointsValid_more_args:
  forall e n n' jps,
  n <= n' ->
  isJoinPointsValid e n jps = true ->
  isJoinPointsValid e n' jps = true.
Proof.
  intros.
  revert n n' jps H H0. apply (core_induct e);
    intros; simpl in *;
    try assumption.
  * (* Var *)
    destruct_match; only 2: reflexivity.
    destruct (PeanoNat.Nat.leb_spec j n), (PeanoNat.Nat.leb_spec j n').
    - assumption.
    - exfalso. lia.
    - exfalso. simpl_bool. destruct H0. congruence.
    - assumption.
  * (* App *)
    simpl_bool. destruct H2. split.
    - refine (H _ _ _ _ H2). lia.
    - assumption.
Qed.

(** ** Lemmas about freshness *)

Lemma forallb_conq:
  forall a (P1 P2 : a -> bool) xs,
  Forall (fun x => P1 x = P2 x) xs ->
  forallb P1 xs = forallb P2 xs.
Proof.
  intros.
  induction H.
  * reflexivity.
  * simpl. f_equal; assumption.
Qed.

Require Import CoreFVs.
Require Import Proofs.CoreFVs.
Require Import Proofs.VarSetFSet.

(* There is some worrying duplication/similarity with
[WellScoped_extendVarSetList_fresh_between] *)
Lemma isJoinPointsValid_fresh_updJPSs_aux:
  forall (vs2 vs3 : list Var) (e : CoreExpr) (jps : VarSet),
  disjointVarSet (delVarSetList (exprFreeVars e) vs3) (mkVarSet vs2) = true ->
  WF jps ->
  (forall n,
  isJoinPointsValid e n (updJPSs jps (vs2 ++ vs3)) =
  isJoinPointsValid e n (updJPSs jps vs3)
  )
  /\
  (forall v, isJoinRHS_aux v e (updJPSs jps (vs2 ++ vs3)) =
  isJoinRHS_aux v e (updJPSs jps vs3)).
Proof.
  intros vs2 vs3 e jps H W.
  rewrite <- disjoint_del_rev in H by solve_varset_inv.
  revert vs3 jps H W.
  apply (core_induct e); intros;
    (split; intro; simpl; [| try solve[ destruct_match; reflexivity]] ).
  - simpl.
    destruct_match; only 2: reflexivity.
    destruct (isLocalVar v) eqn:?; only 2: reflexivity.
    f_equal.
    rewrite updJPSs_append.
    rewrite exprFreeVars_Var in H by assumption.
    rewrite disjoint_del_rev in H by solve_varset_inv.
    clear -H W.
    induction vs3 using rev_ind.
    + rewrite !updJPSs_nil.
      rewrite delVarSetList_nil in H.
      revert jps W; induction vs2; intros.
       * rewrite updJPSs_nil.
         reflexivity.
       * rewrite updJPSs_cons.
         rewrite fold_is_true in H.
          rewrite disjointVarSet_mkVarSet_cons in H by solve_varset_inv.
         destruct H.
          rewrite IHvs2 by (assumption || solve_varset_inv).
          apply elemVarSet_updJPS_l; [exact W|].
         rewrite <- elemVarSet_unitVarSet_is_eq. apply H.
    + rewrite delVarSetList_app, delVarSetList_cons, delVarSetList_nil in H.
      rewrite !updJPSs_append, !updJPSs_cons, !updJPSs_nil.
      apply elemVarSet_updJPS_cong.
      * repeat apply updJPSs_WF. exact W.
      * apply updJPSs_WF. exact W.
      * intros Hne. apply IHvs3.
      rewrite fold_is_true in *.
      rewrite disjointVarSet_mkVarSet in * by solve_varset_inv.
      eapply Forall_impl; only 2: eapply H. intros v2 ?.
      cbv beta in H0.
      rewrite delVarSet_elemVarSet_false in H0; try solve [solve_varset_inv]; only 1: assumption.
      clear -Hne.
      apply elemVarSet_delVarSetList_false_l; try solve [solve_varset_inv].
      rewrite elemVarSet_unitVarSet_is_eq. apply Hne.
  - reflexivity.
  - f_equal.
    apply H; try assumption.
    fresh_disjoint H1.
    apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
    set_b_iff. rewrite exprFreeVars_App.
    set_b_iff; fsetdec.
  - reflexivity.
  - destruct_match; only 1: reflexivity.
    destruct (isJoinId v) eqn:?; only 1: reflexivity.
    simpl.
    rewrite <- !updJPS_not_joinId by assumption.
    rewrite <- !updJPSs_singleton.
    rewrite <- !updJPSs_append.
    rewrite <- app_assoc.
    destruct_match.
    + apply H; try assumption.
      fresh_disjoint H0.
      rewrite rev_app_distr. simpl.
      rewrite delVarSetList_cons.
      apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
      set_b_iff. rewrite exprFreeVars_Lam.
      set_b_iff; fsetdec.
    + apply H; try assumption.
      fresh_disjoint H0.
      rewrite rev_app_distr. simpl.
      rewrite delVarSetList_cons.
      apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
      set_b_iff. rewrite exprFreeVars_Lam.
      set_b_iff; fsetdec.
  - destruct binds as [v rhs | pairs].
    + f_equal.
      ** unfold isJoinPointsValidPair_aux.
         destruct_match; only 2: reflexivity.
         destruct_match.
         -- apply H; try assumption.
            fresh_disjoint H1.
            apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
            set_b_iff. rewrite exprFreeVars_Let_NonRec.
            set_b_iff; fsetdec.
         -- apply H; try assumption.
            fresh_disjoint H1.
            apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
            set_b_iff. rewrite exprFreeVars_Let_NonRec.
            set_b_iff; fsetdec.
      ** rewrite <- !updJPSs_singleton.
         rewrite <- !updJPSs_append.
         rewrite <- app_assoc.
         apply H0; try assumption.
         fresh_disjoint H1.
         rewrite rev_app_distr; simpl.
         rewrite delVarSetList_cons.
         apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
         set_b_iff. rewrite exprFreeVars_Let_NonRec.
         set_b_iff; fsetdec.
    + simpl.
      rewrite <- !updJPSs_append.
      rewrite <- app_assoc.
      f_equal. f_equal.
      ** apply forallb_conq.
         rewrite Forall_forall.
         intros [v rhs0] HIn.
         specialize (H _ _ HIn).
         unfold isJoinPointsValidPair_aux.
         destruct_match; only 2: reflexivity.
         destruct_match.
         -- apply H; try assumption.
            fresh_disjoint H1.
            rewrite rev_app_distr; simpl.
            rewrite delVarSetList_app.
            apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
            set_b_iff. rewrite exprFreeVars_Let_Rec.
            pose proof (subVarSet_exprFreeVars_exprsFreeVars _ _ _ HIn).
            rewrite delVarSetList_rev by solve_varset_inv.
            rewrite <- SubsetE by solve_varset_inv.
            apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
            set_b_iff; fsetdec.
         -- apply H; try assumption.
            fresh_disjoint H1.
            rewrite rev_app_distr; simpl.
            rewrite delVarSetList_app.
            apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
            set_b_iff. rewrite exprFreeVars_Let_Rec.
            rewrite delVarSetList_rev by solve_varset_inv.
            pose proof (subVarSet_exprFreeVars_exprsFreeVars _ _ _ HIn).
            rewrite <- SubsetE by solve_varset_inv.
            apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
            set_b_iff; fsetdec.
      ** apply H0; try assumption.
         fresh_disjoint H1.
         rewrite rev_app_distr; simpl.
         rewrite delVarSetList_app.
         apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
         set_b_iff. rewrite exprFreeVars_Let_Rec.
         rewrite delVarSetList_rev by solve_varset_inv.
         rewrite <- SubsetE by solve_varset_inv.
         apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
         set_b_iff; fsetdec.
  - destruct (isJoinId bndr) eqn:?; only 1: reflexivity; simpl.
    f_equal.
    apply forallb_conq.
    rewrite Forall_forall.
    intros [dc pats rhs] HIn.
    destruct (forallb (fun v : Var => negb (isJoinId v)) pats) eqn:?; only 2: reflexivity; simpl.
    rewrite <- !updJPSs_not_joinId by assumption.
    rewrite <- !updJPS_not_joinId by assumption.
    rewrite <- !updJPSs_cons.
    rewrite <- !updJPSs_append.
    rewrite <- app_assoc.
    specialize (H0 _ _ _ HIn).
    apply H0; try assumption.
    fresh_disjoint H1.
    rewrite rev_app_distr; simpl.
    rewrite !delVarSetList_app, delVarSetList_cons, delVarSetList_nil.
    apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
    set_b_iff. rewrite exprFreeVars_Case.
    rewrite fold_is_true in *.
    match goal with HIn : List.In _ ?xs |- context [mapUnionVarSet ?f ?xs] =>
      let Wf := fresh "Wf" in let Vf := fresh "Vf" in
      assert (Wf : forall y, List.In y xs -> WF (f y)) by (intros [dc' pats' rhs'] _; solve_varset_inv);
      assert (Vf : forall y, List.In y xs -> Axioms.ValidVarSet (f y)) by (intros [dc' pats' rhs'] _; solve_varset_inv);
      let H := fresh in pose proof (@mapUnionVarSet_In_subVarSet _ _ xs f Wf Vf HIn) as H;
      let WM := fresh in pose proof (mapUnionVarSet_WF f xs Wf) as WM;
      let VM := fresh in pose proof (mapUnionVarSet_valid f xs Wf Vf) as VM;
      simpl in H end.
    assert (E : delVarSet (delVarSetList (exprFreeVars rhs) (rev pats)) bndr [=]
      delVarSetList (exprFreeVars rhs) (pats ++ [bndr])).
    { transitivity (delVarSet (delVarSetList (exprFreeVars rhs) pats) bndr).
      - apply delVarSet_m; try solve [solve_varset_inv].
        + apply delVarSetList_rev; solve_varset_inv.
        + apply Proofs.GHC.Base.Eq_refl.
      - rewrite delVarSetList_app, delVarSetList_single. reflexivity. }
    match goal with |- Subset _ ?s =>
      change (delVarSet (delVarSetList (exprFreeVars rhs) (rev pats)) bndr [<=] s)
    end.
    rewrite E.
    set_b_iff.
    intros x M. apply union_3; try solve [solve_varset_inv].
    match goal with HM : Subset _ _ |- _ => apply HM; exact M end.
  - apply H; try assumption.
    fresh_disjoint H0.
    apply subVarSet_delVarSetList_both; try solve [solve_varset_inv].
    set_b_iff. rewrite exprFreeVars_Cast.
    set_b_iff; fsetdec.
  - reflexivity.
  - reflexivity.
Qed.

Lemma isJoinPointsValid_fresh_updJPSs:
  forall (vs2 vs3 : list Var) n (e : CoreExpr) (jps : VarSet),
  disjointVarSet (delVarSetList (exprFreeVars e) vs3) (mkVarSet vs2) = true ->
  WF jps ->
  isJoinPointsValid e n (updJPSs jps (vs2 ++ vs3)) =
  isJoinPointsValid e n (updJPSs jps vs3).
Proof.
  intros.
  apply isJoinPointsValid_fresh_updJPSs_aux; assumption.
Qed.


Lemma isJoinPointsValid_fresh_between:
  forall (vs1 vs2 vs3 : list Var) (e : CoreExpr) (jps : VarSet),
  disjointVarSet (delVarSetList (exprFreeVars e) vs3) (mkVarSet vs2) = true ->
  WF jps ->
  isJoinPointsValid e 0 (updJPSs jps ((vs1 ++ vs2) ++ vs3)) =
  isJoinPointsValid e 0 (updJPSs jps (vs1 ++ vs3)).
Proof.
  intros.
  rewrite <- app_assoc.
  rewrite !updJPSs_append with (vs1 := vs1).
  apply isJoinPointsValid_fresh_updJPSs; [assumption|].
  apply updJPSs_WF. assumption.
Qed.

(** ** Lemmas about [StrongSubset] *)

Lemma StrongSubset_updJPS:
  forall (v : Var) (vs1 vs2 : VarSet),
  WF vs1 -> WF vs2 ->
  StrongSubset vs1 vs2 ->
  StrongSubset (updJPS vs1 v) (updJPS vs2 v).
Proof.
  intros.
  unfold updJPS.
  destruct_match.
   * apply StrongSubset_extend; assumption.
   * apply StrongSubset_delVarSet; assumption.
Qed.


Lemma StrongSubset_updJPSs:
  forall (vs3 : list Var) (vs1 vs2 : VarSet),
  WF vs1 -> WF vs2 ->
  StrongSubset vs1 vs2 ->
  StrongSubset (updJPSs vs1 vs3) (updJPSs vs2 vs3).
Proof.
  induction vs3; intros.
  * assumption.
  * simpl.
     apply IHvs3; try solve [apply updJPS_WF; assumption].
     apply StrongSubset_updJPS; assumption.
Qed.

Lemma StrongSubset_updJPS_fresh :
  forall vs v,
  WF vs ->
  elemVarSet v vs = false ->
  StrongSubset vs (updJPS vs v).
Proof.
   intros vs v W N.
   unfold updJPS. destruct_match.
   * apply StrongSubset_extend_fresh; auto.
     apply lookupVarSet_None_elemVarSet; assumption.
   * apply StrongSubset_delete_fresh; auto.
     apply lookupVarSet_None_elemVarSet; assumption.
Qed.

Lemma lookupVarSet_updJPS_neq:
  forall (v1 v2 : Var) (vs : VarSet),
  WF vs ->
  v1 GHC.Base.== v2 = false ->
  lookupVarSet (updJPS vs v1) v2 = lookupVarSet vs v2.
Proof.
   intros v1 v2 vs W N.
   unfold updJPS.
   destruct_match.
   * apply lookupVarSet_extendVarSet_neq; [exact W|rewrite N; congruence].
   * apply lookupVarSet_delVarSet_neq; [exact W|rewrite N; congruence].
Qed.

Lemma StrongSubset_updJPSs_fresh :
  forall vs vs2,
  WF vs -> Axioms.ValidVarSet vs ->
  disjointVarSet vs (mkVarSet vs2) = true ->
  StrongSubset vs (updJPSs vs vs2).
Proof.
   intros vs vs2 W V H.
  (* A naive induction using [StrongSubset_updJPS_fresh] does not go through
     because we do not know that the [vs2] are disjoint.
  *)
  intro v.
  destruct_match; only 2: apply I.
  assert (lookupVarSet (updJPSs vs vs2) v = Some v0).
  { induction vs2 using rev_ind; intros.
    * apply Heq.
    * rewrite fold_is_true in *.
      rewrite disjointVarSet_mkVarSet_append, disjointVarSet_mkVarSet_cons in H by solve_varset_inv.
      destruct H. destruct H0.
      rewrite updJPSs_append, updJPSs_cons, updJPSs_nil.
      assert (x GHC.Base.== v = false).
      { rewrite <- lookupVarSet_None_elemVarSet in H0 by assumption.
        apply not_true_is_false. intro.
        erewrite lookupVarSet_eq  in H0 by eassumption.
        congruence.
      }
      rewrite lookupVarSet_updJPS_neq by (assumption || (apply updJPSs_WF; exact W)).
      apply IHvs2.
      assumption.
  }
  rewrite H0. apply almostEqual_refl.
Qed.


(** ** Lemmas about [Respects_StrongSubset] *)

Lemma Respects_StrongSubset_updJPS:
  forall v P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (updJPS vs v)).
Proof.
  intros.
  unfold updJPS.
  destruct_match; [apply Respects_StrongSubset_extendVarSet | apply Respects_StrongSubset_delVarSet ]; assumption.
Qed.

Lemma Respects_StrongSubset_updJPSs:
  forall vs2 P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (updJPSs vs vs2)).
Proof.
  intros.
  induction vs2.
  * apply H.
  * simpl.
    apply Respects_StrongSubset_updJPS with (P := fun vs => P (updJPSs vs vs2)).
    apply IHvs2.
Qed.

Lemma Respects_StrongSubset_isJoinPointsValid_aux:
  forall e,
  (forall n,
  Respects_StrongSubset (fun jps => isJoinPointsValid e n jps = true)
  )
  /\
  (forall v,
  Respects_StrongSubset (fun jps => isJoinRHS_aux v e jps = true)).
Proof.
  intros.
  apply (core_induct e); intros;
    (split; intro; simpl; [| try solve[ destruct_match; apply Respects_StrongSubset_const]]).
  * destruct_match; only 2: apply Respects_StrongSubset_const.
    apply Respects_StrongSubset_andb; only 1: apply Respects_StrongSubset_const.
    apply Respects_StrongSubset_elemVarSet.
  * apply Respects_StrongSubset_const.
  * apply Respects_StrongSubset_andb; only 2: apply Respects_StrongSubset_const.
    apply H.
  * apply Respects_StrongSubset_const.
  * destruct_match; try apply Respects_StrongSubset_const.
    apply Respects_StrongSubset_andb; try apply Respects_StrongSubset_const.
    destruct_match.
    - apply Respects_StrongSubset_delVarSet with (P := fun jps => isJoinPointsValid e0 0 jps = true).
      apply H.
    - apply Respects_StrongSubset_delVarSet with (P := fun jps => isJoinRHS_aux (v0 - 1) e0 jps = true).
      apply H.
  * destruct binds as [v rhs | pairs].
    - apply Respects_StrongSubset_andb.
      + unfold isJoinPointsValidPair_aux.
        destruct_match; only 2: apply Respects_StrongSubset_const.
        destruct_match; apply H.
      + apply Respects_StrongSubset_updJPS with (P := fun jps => isJoinPointsValid body 0 jps = true).
        apply H0.
    - repeat apply Respects_StrongSubset_andb; try apply Respects_StrongSubset_const.
      + apply Respects_StrongSubset_forallb.
        rewrite Forall_forall.
        intros [v rhs] HIn.
        specialize (H _ _ HIn).
        apply Respects_StrongSubset_updJPSs with
          (P := fun jps => isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS_aux v rhs jps = true).
        unfold isJoinPointsValidPair_aux.
        destruct_match; only 2: apply Respects_StrongSubset_const.
        destruct_match; apply H.
      + apply Respects_StrongSubset_updJPSs with
          (P := fun jps => isJoinPointsValid body 0 jps = true).
        apply H0.
   * repeat apply Respects_StrongSubset_andb; try apply Respects_StrongSubset_const.
     apply Respects_StrongSubset_forallb.
     rewrite Forall_forall.
     intros [dc pats rhs] HIn.
     specialize (H0 _ _ _ HIn).
     repeat apply Respects_StrongSubset_andb; try apply Respects_StrongSubset_const.
     apply Respects_StrongSubset_delVarSet with
          (P := fun jps => isJoinPointsValid rhs 0 (delVarSetList jps pats) = true).
     apply Respects_StrongSubset_delVarSetList with
          (P := fun jps => isJoinPointsValid rhs 0 jps = true).
     apply H0.
   * apply H.
(*   * apply H. *)
   * apply Respects_StrongSubset_const.
   * apply Respects_StrongSubset_const. 
Qed.

Instance Respects_StrongSubset_isJoinPointsValid e n :
  Respects_StrongSubset (fun jps => isJoinPointsValid e n jps = true).
Proof. apply Respects_StrongSubset_isJoinPointsValid_aux. Qed.

Instance Respects_StrongSubset_isValidJoinPointsPair x e :
  Respects_StrongSubset (fun jps => isValidJoinPointsPair x e jps = true).
Proof.
  unfold isValidJoinPointsPair.
  destruct_match; try apply Respects_StrongSubset_const.
  unfold isJoinRHS.
  destruct_match; try apply Respects_StrongSubset_const;
  apply Respects_StrongSubset_isJoinPointsValid_aux.
Qed.

Print Assumptions updJPSs_WF.
Print Assumptions updJPSs_valid.
Print Assumptions isJoinPointsValid_fresh_between.
Print Assumptions Respects_StrongSubset_isJoinPointsValid.
