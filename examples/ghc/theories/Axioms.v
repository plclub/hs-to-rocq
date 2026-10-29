(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

(* This file gathers and explains axioms about the GHC development. *)

From Coq Require Import ssreflect ssrbool.



Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Classes.Morphisms. 

Require Import GHC.Base.

Require Import Outputable.
Require Import PrelNames.
Require Import Id.
Require Import Core.
Require Import Unique.
Require Import CoreFVs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


(**

** Local uniques

The Uniques in GHC are partitioned in classes, e.g. local variables have a different
class than external names, which are different from data constructors and so on.

The class is encoded in the upper 8 bits of the Unique. Our representation does not have 
upper bits... and we hope we can make do with less details. For our proofs, it would suffice
to axiomatize what we need:

 * A predicate that distinguishes the uniques used for (module)-local variables, [isLocalUnique]
 * An axiom stating that [uniqAway] always generates local uniques (see below).
 * An axiom stating that some uniques are local: in particular, initExitJoinUnique.

But in order to prove our invariants for concrete Core terms as dumped from GHC, we
need the [isLocalUnique] function to compute. So hence it is a definition.

*)


(*

From Unique.hs:

Allocation of unique supply characters:
        v,t,u : for renumbering value-, type- and usage- vars.
        B:   builtin
        C-E: pseudo uniques     (used in native-code generator)
        X:   uniques derived by deriveUnique
        _:   unifiable tyvars   (above)
        0-9: prelude things below
             (no numbers left any more..)
        ::   (prelude) parallel array data constructors

        other a-z: lower case chars for unique supplies.  Used so far:

        d       desugarer
        f       AbsC flattener
        g       SimplStg
        k       constraint tuple tycons
        m       constraint tuple datacons
        n       Native codegen
        r       Hsc name cache
        s       simplifier
        z       anonymous sums
*)

(*
Open Scope N_scope.
Definition isLocalUnique  (u : Unique.Unique) : bool :=
  (u == mkPreludeMiscIdUnique  0) (* The wild card key is local *)
  || let '(c,i) := unpkUnique u in
     negb (List.elem c &"B0123456789:kmnrz").
*)

(* GHC 9.10: initExitJoinUnique moved to GHC.Builtin.Uniques (not translated) *)
(* Axiom isLocalUnique_initExitJoinUnique:
  Unique.isLocalUnique Unique.initExitJoinUnique = true. *)



(** ** [uniqAway] axiomatization *)


(* If uniqAway returns a variable with the same unique, 
   it returns the same variable. *)      
Axiom uniqAway_eq_same : forall v in_scope_set,
    (uniqAway in_scope_set v == v) ->
    (uniqAway in_scope_set v = v).

(* The variable returned by uniqAway is fresh. *)
Axiom uniqAway_lookupVarSet_fresh : forall v in_scope_set,
    lookupVarSet (getInScopeVars in_scope_set) (uniqAway in_scope_set v) = None.

(* Unique away preserves the classification of Vars. *)   
Axiom idScope_uniqAway: forall iss v, idScope v = idScope (uniqAway iss v).
Axiom id_details_uniqAway: forall iss v, id_details v = id_details (uniqAway iss v).

(* Variables have a unique cached inside.  This unique *should* be 
   the same as the unique stored in the name of the variable. *)
Axiom nameUnique_varName_uniqAway:
  forall vss v,
  Name.nameUnique (varName v) = varUnique v ->
  Name.nameUnique (varName (uniqAway vss v)) = varUnique (uniqAway vss v).
Axiom isLocalId_uniqAway:
  forall iss v,
  isLocalId (uniqAway iss v) = isLocalId v.




(* GHC 9.10: Id.idJoinPointHood is now defined in the Id midamble.
   This follows from id_details_uniqAway. *)
Lemma idJoinPointHood_uniqAway:
  forall s v,
  Id.idJoinPointHood (uniqAway s v) = Id.idJoinPointHood v.
Proof.
  intros s v.
  unfold Id.idJoinPointHood, Core.isId, Core.idDetails.
  destruct v as [n u t m sc d i].
  destruct (uniqAway s (Mk_Id n u t m sc d i)) as [n' u' t' m' sc' d' i'] eqn:E.
  simpl.
  move: (id_details_uniqAway s (Mk_Id n u t m sc d i)) => H.
  simpl in H. rewrite E in H. simpl in H. rewrite H.
  reflexivity.
Qed.

Lemma isLocalUnique_uniqAway:
  forall iss v,
    Unique.isLocalUnique (varUnique v) -> 
    Unique.isLocalUnique (varUnique (uniqAway iss v)).
Proof.
  move=>iss v h.
  move: (isLocalId_uniqAway iss v) => h0.
  unfold isLocalId in h0.
  rewrite h0.
  auto.
Qed.



(* Because we removed constructors from the Var type, these 
   three are provable directly. However, in the full system, we would 
   have to know more about uniqAway to know that they are true. *)
Lemma isLocalVar_uniqAway:
  forall iss v,
  isLocalVar (uniqAway iss v) = isLocalVar v.
Proof.
  move=> iss v.
  move: (isLocalId_uniqAway iss v) => h.
  destruct v. 
  unfold isLocalId in *. unfold isLocalVar in *.
  unfold isGlobalId. 
  destruct uniqAway.
(*  destruct idScope0, idScope; done. *)
  rewrite h. auto.
Qed.

Lemma isId_uniqAway:
  forall iss v,
    isId (uniqAway iss v) = isId v.
Proof.
  intros iss v. unfold isId. destruct uniqAway. destruct v. 
  done.
Qed.

Lemma isCoVar_uniqAway:
  forall iss v,
    isCoVar (uniqAway iss v) = isCoVar v.
Proof.
  unfold isCoVar. destruct v, uniqAway. done.
Qed.

  
(**** *)

(* GHC 9.10: Id.idJoinPointHood is now defined in the Id midamble.
   These follow from the concrete definitions. *)
Lemma idJoinPointHood_setIdOccInfo:
  forall v occ_info,
  Id.idJoinPointHood (setIdOccInfo v occ_info) = Id.idJoinPointHood v.
Proof.
  intros v occ_info.
  unfold Id.idJoinPointHood, setIdOccInfo, Id.modifyIdInfo, Id.setIdInfo,
         Id.lazySetIdInfo, Core.lazySetIdInfo.
  destruct v as [n u t m s d i]. simpl. reflexivity.
Qed.

Lemma idJoinPointHood_asJoinId:
  forall v a,
  isLocalId v = true ->
  Id.idJoinPointHood (Id.asJoinId v a) = Outputable.JoinPoint a.
Proof.
  intros v a Hlocal.
  unfold Id.idJoinPointHood, Id.asJoinId, Core.setIdDetails.
  destruct v as [n u t m s d i]. simpl. reflexivity.
Qed.  


  
(** ** Valid VarSets *)

(* This property is an invariant of the VarSet/UniqFM type. We may want to either 
   axiomatize it or add it to a sigma type in one of the definitions. *)

Definition ValidVarSet (vs : VarSet) : Prop :=
  forall v1 v2, lookupVarSet vs v1 = Some v2 -> (v1 == v2).

Axiom ValidVarSet_Axiom : forall vs, ValidVarSet vs.


(** ** Strong Valid VarSets *)

(* StrongValidVarSet says that every entry (k, v) in a VarSet's underlying
   IntMap has key_of(v) = k. This is key-surjectivity: it ensures that every
   key in the IntMap comes from the Unique of the stored Var. This is needed
   for proofs that go from "no Var is a member" to "the map is empty", or
   from "all Vars pass a predicate" to "all stored values pass". *)

Definition StrongValidVarSet (vs : VarSet) : Prop :=
  match vs with
  | UniqSet.Mk_UniqSet (UniqFM.UFM m) =>
    forall k v, Data.IntMap.Internal.lookup k m = Some v ->
      Unique.getWordKey (Unique.getUnique v) = k
  end.

(* The stronger invariant is derived from ValidVarSet: every raw key can
   be queried with a Var carrying that unique. Reuse the stored Var's other
   fields so that this argument needs no additional inhabitance assumptions. *)
Lemma ValidVarSet_StrongValidVarSet :
  forall vs, ValidVarSet vs -> StrongValidVarSet vs.
Proof.
  intros [[m]] Hvalid k [n [u] t mult sc d i] Hlookup.
  pose proof (Hvalid (Mk_Id n (Unique.MkUnique k) t mult sc d i)
                    (Mk_Id n (Unique.MkUnique u) t mult sc d i)
                    Hlookup) as Heq.
  change (BinNat.N.eqb k u = true) in Heq.
  change (u = k).
  symmetry. apply BinNat.N.eqb_eq. exact Heq.
Qed.

Lemma StrongValidVarSet_Axiom : forall vs, StrongValidVarSet vs.
Proof.
  intros vs. apply ValidVarSet_StrongValidVarSet.
  apply ValidVarSet_Axiom.
Qed.


(** ** Extensional equality for VarSets *)

(* Two VarSets with the same membership (elemVarSet) have equal underlying
   IntMaps (via _==_). This combines three facts about VarSets:
   1. StrongValidVarSet: every key comes from a Var's unique
   2. WF PATRICIA tries: same key domain → same tree structure
   3. Values at same key are ==-equal (same unique)
   Proving this formally requires ~150 lines of Desc_unique-style reasoning
   from IntMapProofs. We axiomatize it as a sound property of VarSets. *)
(* Formulated with destructured VarSet to avoid match in conclusion *)
Definition VarSet_IntMap (vs : VarSet) :=
  match vs with UniqSet.Mk_UniqSet (UniqFM.UFM m) => m end.

Axiom VarSet_extensional_equal : forall vs1 vs2 : VarSet,
  (forall v, elemVarSet v vs1 = elemVarSet v vs2) ->
  GHC.Base.op_zeze__ (VarSet_IntMap vs1) (VarSet_IntMap vs2) = true.


(********************************* *)


