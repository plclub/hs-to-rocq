(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".


From Coq Require Import ssreflect ssrbool.

Require Import Coq.Lists.List.

Require Import GHC.Base.
Require Import Proofs.Data.Foldable.

Require Import Id.
Require Import Core.

Require Import Proofs.Axioms.
Require Import Proofs.ContainerProofs.

Require Import Proofs.Core.
Require Import Proofs.Var.
Require Import Proofs.Unique.
Require Import Proofs.VarSetFSet.

Require Import Proofs.GHC.Base.

Set Bullet Behavior "Strict Subproofs".

Definition VarEnv_IntMap {a} (env : VarEnv a) : Data.IntMap.Internal.IntMap a :=
  match env with UniqFM.UFM m => m end.

Lemma emptyVarEnv_WF a : IntMapProofs.WF (VarEnv_IntMap (@emptyVarEnv a)).
Proof. apply IntMapProofs.empty_WF. Qed.

Lemma extendVarEnv_WF a (env : VarEnv a) v x :
  IntMapProofs.WF (VarEnv_IntMap env) ->
  IntMapProofs.WF (VarEnv_IntMap (extendVarEnv env v x)).
Proof. destruct env; apply IntMapProofs.insert_WF. Qed.

Lemma delVarEnv_WF a (env : VarEnv a) v :
  IntMapProofs.WF (VarEnv_IntMap env) ->
  IntMapProofs.WF (VarEnv_IntMap (delVarEnv env v)).
Proof. destruct env; apply IntMapProofs.delete_WF. Qed.

#[local] Hint Resolve emptyVarEnv_WF extendVarEnv_WF delVarEnv_WF : core.
#[local] Hint Resolve emptyVarSet_WF unitVarSet_WF mkVarSet_WF
  extendVarSet_WF extendVarSetList_WF delVarSet_WF delVarSetList_WF
  filterVarSet_WF emptyVarSet_valid unitVarSet_valid mkVarSet_valid
  extendVarSet_valid extendVarSetList_valid delVarSet_valid delVarSetList_valid
  filterVarSet_valid : core.


(** ** [VarEnv] axiomatization *)

(* Eventually replace these with container axioms. *)

Lemma lookupVarEnv_elemVarEnv_true :
  forall A v (vs : VarEnv A),
   IntMapProofs.WF (VarEnv_IntMap vs) ->
   elemVarEnv v vs = true <-> (exists a, lookupVarEnv vs v = Some a).
Proof.
  move=> A v vs.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM.
  intro W. rewrite <- (@member_lookup _ _ i W). done.
Qed.

Lemma lookupVarEnv_elemVarEnv_false :
  forall A v (vs : VarEnv A),
   IntMapProofs.WF (VarEnv_IntMap vs) ->
   elemVarEnv v vs = false <-> (lookupVarEnv vs v = None).
Proof.
  move=> A v vs.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM.
  intro W. rewrite (@non_member_lookup _ _ i W).
  done.
Qed.

Lemma lookupVarEnv_eq :
  forall A v1 v2 (vs : VarEnv A),
    (v1 == v2) = true ->
    lookupVarEnv vs v1 = lookupVarEnv vs v2.
Proof.
  move=> A v1 v2 vs.
  elim: vs => [i].
  unfold lookupVarEnv.
  unfold UniqFM.lookupUFM.
  move=> h.
  apply eq_unique in h.
  rewrite h.
  reflexivity.
Qed.

Lemma elemVarEnv_eq :
  forall A v1 v2 (vs : VarEnv A),
    (v1 == v2) = true ->
    elemVarEnv v1 vs = elemVarEnv v2 vs.
Proof.
  move=> A v1 v2 vs.
  elim: vs => [i].
  unfold elemVarEnv.
  unfold UniqFM.elemUFM.
  move=> h.
  apply eq_unique in h.
  rewrite h.
  reflexivity.
Qed.


Lemma lookupVarEnv_extendVarEnv_eq :
  forall A v1 v2 (vs : VarEnv A) val, 
    v1 == v2 = true ->
    lookupVarEnv (extendVarEnv vs v1 val) v2 = Some val.
Proof.
  move=> A v1 v2 vs val.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv, extendVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM, UniqFM.addToUFM.
  move=> h.
  erewrite lookup_eq.
  erewrite lookup_insert ; eauto.
  apply eq_unique in h.
  rewrite h.
  reflexivity.
Qed.



Lemma lookupVarEnv_extendVarEnv_neq :
  forall A v1 v2 (vs : VarEnv A) val, 
    IntMapProofs.WF (VarEnv_IntMap vs) ->
    v1 == v2 <> true ->
    lookupVarEnv (extendVarEnv vs v1 val) v2 = lookupVarEnv vs v2.
Proof.
  move=> A v1 v2 vs val.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv, extendVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM, UniqFM.addToUFM.
  move=> h.
  intro NE. rewrite (@lookup_insert_neq _ _ _ _ i h) //.
   move => nh.
  rewrite <- eq_unique in nh.
  rewrite Eq_sym in nh.
  exact (NE nh).
Qed.

Lemma elemVarEnv_extendVarEnv_eq :
  forall A v1 v2 (vs : VarEnv A) val, 
    IntMapProofs.WF (VarEnv_IntMap vs) ->
    v1 == v2 = true ->
    elemVarEnv v2 (extendVarEnv vs v1 val) = true.
Proof.
  move=> A v1 v2 vs val.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv, extendVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM, UniqFM.addToUFM.
  move=> h.
  intro E. rewrite (@member_insert _ _ _ _ i h).
  apply /orP.
  left.
  change (is_true (v1 == v2)) in E.
  rewrite -> eq_unique in E.
  rewrite E.
  reflexivity.
Qed.

Lemma elemVarEnv_extendVarEnv_neq :
  forall A v1 v2 (vs : VarEnv A) val,
    IntMapProofs.WF (VarEnv_IntMap vs) ->
    v1 == v2 <> true ->
    elemVarEnv v2 (extendVarEnv vs v1 val) = elemVarEnv v2 vs.
Proof.
  move=> A v1 v2 vs val.
  elim: vs => [i].
  unfold elemVarEnv, extendVarEnv.
  unfold UniqFM.elemUFM, UniqFM.addToUFM.
  move=> h.
  intro NE. rewrite (@member_insert _ _ _ _ i h).
  have HEQ: (Unique.getWordKey (Unique.getUnique v2) ==
             Unique.getWordKey (Unique.getUnique v1)) = false.
  { apply /Eq_eq. move => h0. apply NE. apply eq_unique. auto. }
  rewrite HEQ. simpl. reflexivity.
Qed.  



Lemma elemVarEnv_delVarEnv_eq :
  forall A v1 v2 (vs : VarEnv A), 
    IntMapProofs.WF (VarEnv_IntMap vs) ->
    v1 == v2 = true ->
    elemVarEnv v2 (delVarEnv vs v1) = false.
Proof.
  move=> A v1 v2 vs.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv, extendVarEnv, delVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM, UniqFM.addToUFM, UniqFM.delFromUFM.
  move => W h.
  change (is_true (v1 == v2)) in h.
  rewrite -> eq_unique in h.
  rewrite h.
  rewrite (@non_member_lookup _ _
    (Data.IntMap.Internal.delete (Unique.getWordKey (Unique.getUnique v2)) i)
    (IntMapProofs.delete_WF (Unique.getWordKey (Unique.getUnique v2)) i
      W)).
  apply delete_eq. exact W.
Qed.


Lemma elemVarEnv_delVarEnv_neq :
  forall A v1 v2 (env: VarEnv A), IntMapProofs.WF (VarEnv_IntMap env) -> (v1 == v2) = false ->
               elemVarEnv v2 (delVarEnv env v1) = elemVarEnv v2 env.
Proof.
  move=> A v1 v2 vs.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv, extendVarEnv, delVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM, UniqFM.addToUFM, UniqFM.delFromUFM.
  move => h.
  intro E. rename h into W. rename E into h.
  set k1 := (Unique.getWordKey (Unique.getUnique v1)).
  set k2 := (Unique.getWordKey (Unique.getUnique v2)).
  assert (k1 <> k2).
   { move => h1. subst k1. subst k2.
     rewrite <- eq_unique in h1.
     rewrite h1 in h.
     done. }
   apply member_delete_neq.
   all: auto.
Qed.

Lemma lookupVarEnv_delVarEnv_eq :
  forall A v1 v2 (vs : VarEnv A), 
    IntMapProofs.WF (VarEnv_IntMap vs) ->
    v1 == v2 = true ->
    lookupVarEnv (delVarEnv vs v1) v2 = None.
Proof. 
  move=> A v1 v2 vs.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv, extendVarEnv, delVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM, UniqFM.addToUFM, UniqFM.delFromUFM.
  move => h.
  intro E. rename h into W. rename E into h.
  change (is_true (v1 == v2)) in h.
  erewrite eq_unique in h.
  rewrite h.
  apply delete_eq. exact W.
Qed.

Lemma lookupVarEnv_delVarEnv_neq :
  forall A v1 v2 (vs : VarEnv A), 
    IntMapProofs.WF (VarEnv_IntMap vs) ->
    v1 == v2 <> true ->
    lookupVarEnv (delVarEnv vs v1) v2 = lookupVarEnv vs v2.
Proof.
  move=> A v1 v2 vs.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv, extendVarEnv, delVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM, UniqFM.addToUFM, UniqFM.delFromUFM.
  move => h.
  intro NE. apply delete_neq.
  exact h.
  move => h0.
  erewrite <- eq_unique in h0.
  rewrite Eq_sym in h0.
  rewrite h0 in NE.
  done.
Qed.

(** [minusDom] **)

Require Import Proofs.VarSet.
Require Import Proofs.VarSetStrong.

Lemma elemVarSet_uniqAway:
  forall v iss vs,
  WF vs -> WF (getInScopeVars iss) ->
  subVarSet vs (getInScopeVars iss) = true ->
  elemVarSet (uniqAway iss v) vs = false.
Proof.
  intros v iss vs W X H.
  eapply subVarSet_elemVarSet_false; [exact W|exact X|exact H|].
  apply (proj1 (lookupVarSet_None_elemVarSet _ _ X)).
  apply uniqAway_lookupVarSet_fresh.
Qed.

(* To be able to specify the property of a wellformed substitution, 
   we need to define the operation of taking a variable set and 
   removing all of the vars that are part of the domain of the 
   substitution. *)


Definition minusDom {a} (vs : VarSet) (e : VarEnv a) : VarSet :=
  filterVarSet (fun v => negb (elemVarEnv v e)) vs.

Lemma minusDom_WF a vs (e : VarEnv a) : WF vs -> WF (minusDom vs e).
Proof. apply filterVarSet_WF. Qed.

Lemma minusDom_valid a vs (e : VarEnv a) :
  WF vs -> ValidVarSet vs -> ValidVarSet (minusDom vs e).
Proof. apply filterVarSet_valid. Qed.

#[local] Hint Resolve minusDom_WF minusDom_valid : core.


Ltac specialize_all var := 
  repeat 
    match goal with 
    | [ H : forall var:Var, _ |- _ ] => specialize (H var)
    end.

(* After a case split on whether a var is present in a minusDom'ed env, 
   rewrite a use of minusDom appropriately. *)
Ltac rewrite_minusDom_true := 
  match goal with 
  | [ H : elemVarEnv ?var ?init_env = true |- 
      context [ lookupVarSet 
                  (minusDom ?s ?init_env) ?var ] ] =>  
    unfold minusDom;
    repeat rewrite -> lookupVarSet_filterVarSet_false with 
        (f := (fun v0 : Var => negb (elemVarEnv v0 init_env ))); try rewrite H; auto 
  | [ H : elemVarEnv ?var ?init_env = true, 
          H2: context [ lookupVarSet 
                          (minusDom ?s ?init_env) ?var ] |- _ ] =>  
    unfold minusDom in H2;
    rewrite -> lookupVarSet_filterVarSet_false with
        (f := (fun v0 : Var => negb (elemVarEnv v0 init_env ))) in H2; 
    try rewrite H; auto 
                                                                    
  end.

Ltac rewrite_minusDom_false := 
  match goal with 
  | [ H : elemVarEnv ?var ?init_env  = false |- 
      context [ lookupVarSet 
                  (minusDom ?s ?init_env) ?var ] ] =>  
    unfold minusDom;
    repeat rewrite -> lookupVarSet_filterVarSet_true
    with (f := (fun v0 : Var => negb (elemVarEnv v0 init_env ))); 
    try rewrite H; auto 
  | [ H : elemVarEnv ?var ?init_env = false, 
          H2: context [ lookupVarSet 
                          (minusDom ?s ?init_env) ?var ] |- _ ] =>  
    unfold minusDom in H2;
    rewrite -> lookupVarSet_filterVarSet_true with 
        (f := (fun v0 : Var => negb (elemVarEnv v0 init_env ))) in H2 ; 
    try rewrite H; auto  
  end.

Lemma RespectsVar_negbElemVarEnv A (e :VarEnv A) : 
  RespectsVar (fun v0 : Var => ~~ elemVarEnv v0 e).
Proof. 
  move=> x1 x2 Eq.
  f_equal.
  erewrite elemVarEnv_eq; try done.
Qed.
#[export] Hint Resolve RespectsVar_negbElemVarEnv : core.

Lemma lookup_minusDom a vs (env : VarEnv a) v :
  WF vs -> ValidVarSet vs ->
  lookupVarSet (minusDom vs env) v =
    if elemVarEnv v env then None else lookupVarSet vs v.
Proof.
  intros W V. unfold minusDom.
  destruct (elemVarEnv v env) eqn:E.
  - apply lookupVarSet_filterVarSet_false; auto. rewrite E. reflexivity.
  - apply lookupVarSet_filterVarSet_true; auto. rewrite E. reflexivity.
Qed.

Lemma StrongSubset_minusDom {a} : forall vs1 vs2 (e: VarEnv a), 
    WF vs1 -> WF vs2 -> ValidVarSet vs1 -> ValidVarSet vs2 ->
    vs1 {<=} vs2 ->
    minusDom vs1 e {<=} minusDom vs2 e.
Proof.
  intros vs1 vs2 e W1 W2 V1 V2 H.
  intro var.
  rewrite -> (lookup_minusDom _ _ _ _ W1 V1), (lookup_minusDom _ _ _ _ W2 V2).
  destruct (elemVarEnv var e); [exact I|apply H].
Qed.


Lemma lookupVarSet_minusDom_1 :
  forall a (env : VarEnv a) vs v,
    IntMapProofs.WF (VarEnv_IntMap env) -> WF vs -> ValidVarSet vs ->
    lookupVarEnv env v = None -> 
    lookupVarSet (minusDom vs env) v = lookupVarSet vs v.
Proof.
  intros a env vs v We W V H.
  rewrite <- lookupVarEnv_elemVarEnv_false in H; [|exact We].
  rewrite -> (lookup_minusDom _ _ _ _ W V), H. reflexivity.
Qed.



Lemma lookup_minusDom_inDom : forall a vs (env:VarEnv a) v',
    WF vs -> ValidVarSet vs ->
    elemVarEnv v' env = true ->
    lookupVarSet (minusDom vs env) v' = None.
Proof.
  intros a vs env v W V H.
  rewrite -> (lookup_minusDom _ _ _ _ W V), H. reflexivity.
Qed. 


Lemma minusDom_extend : 
  forall a vs (env : VarEnv a) v,
    WF vs -> ValidVarSet vs -> IntMapProofs.WF (VarEnv_IntMap env) ->
    minusDom (extendVarSet vs v) (delVarEnv env v) {<=} 
    extendVarSet (minusDom vs env) v.
Proof.
  intros a vs env v W V We.
  intro var.
  rewrite lookup_minusDom; try solve [solve_varset_inv]; auto.
  destruct (elemVarEnv var (delVarEnv env v)) eqn:IN; [exact I|].
  destruct (v == var) eqn:EQ.
  - repeat rewrite lookupVarSet_extendVarSet_eq; auto using almostEqual_refl.
  - repeat rewrite lookupVarSet_extendVarSet_neq; auto; try (rewrite EQ; discriminate).
    rewrite lookup_minusDom; auto.
    rewrite elemVarEnv_delVarEnv_neq in IN; auto.
    rewrite IN. destruct (lookupVarSet vs var); auto using almostEqual_refl.
Qed.


Lemma lookup_minusDom_extend : forall a vs (env:VarEnv a) v v' e,
    WF vs -> ValidVarSet vs -> IntMapProofs.WF (VarEnv_IntMap env) ->
    v ==  v' <> true ->
    lookupVarSet (minusDom (extendVarSet vs v) (extendVarEnv env v e)) v' =
    lookupVarSet (minusDom vs env) v'.
Proof.
  intros a vs env v v' e W V We H.
  repeat rewrite lookup_minusDom; try solve [solve_varset_inv]; auto.
  rewrite elemVarEnv_extendVarEnv_neq; auto.
  rewrite lookupVarSet_extendVarSet_neq; auto.
Qed.

Lemma StrongSubset_minusDom_left {a} : forall vs (e: VarEnv a), 
    WF vs -> ValidVarSet vs ->
    minusDom vs e {<=} vs.
Proof.
  intros vs e W V var.
  rewrite (lookup_minusDom _ _ _ _ W V).
  destruct (elemVarEnv var e); [exact I|].
  destruct (lookupVarSet vs var); auto using almostEqual_refl.
Qed.


Lemma StrongSubset_minusDom_extend_extend : forall vs v e (env: IdEnv CoreExpr),
           WF vs -> ValidVarSet vs -> IntMapProofs.WF (VarEnv_IntMap env) ->
           minusDom (extendVarSet vs v) (extendVarEnv env v e) {<=} minusDom vs env.
Proof.
  intros vs v e env W V We.
  intro var.
  destruct (v == var) eqn:EQ.
   - rewrite lookup_minusDom; try solve [solve_varset_inv]; auto.
    rewrite elemVarEnv_extendVarEnv_eq; auto.
  - rewrite lookup_minusDom_extend; auto; try (rewrite EQ; discriminate).
    destruct (lookupVarSet (minusDom vs env) var); auto using almostEqual_refl.
Qed.


(** ** [InScopeSet] *)

Lemma getInScopeVars_extendInScopeSet:
  forall iss v,
  getInScopeVars (extendInScopeSet iss v) = extendVarSet (getInScopeVars iss) v.
Proof.
  intros.
  unfold getInScopeVars.
  unfold extendInScopeSet.
  destruct iss.
  reflexivity.
Qed.

Lemma getInScopeVars_extendInScopeSetList:
  forall iss vs,
  getInScopeVars (extendInScopeSetList iss vs) = extendVarSetList (getInScopeVars iss) vs.
Proof.
  intros.
  rewrite -> extendVarSetList_foldl'.
  unfold getInScopeVars.
  unfold extendInScopeSetList.
  destruct iss.
  unfold_Foldable_foldl'.
  unfold_Foldable_foldl.
  f_equal.
Qed.


Lemma extendInScopeSetList_cons : forall v vs in_scope_set,
           (extendInScopeSetList in_scope_set (v :: vs) =
            (extendInScopeSetList (extendInScopeSet in_scope_set v) vs)).
Proof.
  unfold extendInScopeSetList.
  destruct in_scope_set.
  unfold_Foldable_foldl.
  simpl.
  f_equal.
Qed.

Lemma extendInScopeSetList_nil : forall in_scope_set,
           extendInScopeSetList in_scope_set nil = in_scope_set.
Proof.
  unfold extendInScopeSetList.
  destruct in_scope_set.
  unfold_Foldable_foldl.
  simpl.
  f_equal.
Qed.

(* These contracts consume explicit structural/key-validity evidence. *)
Print Assumptions lookupVarEnv_elemVarEnv_true.
Print Assumptions lookupVarEnv_extendVarEnv_neq.
Print Assumptions elemVarEnv_delVarEnv_eq.
Print Assumptions minusDom_extend.
Print Assumptions StrongSubset_minusDom_extend_extend.
