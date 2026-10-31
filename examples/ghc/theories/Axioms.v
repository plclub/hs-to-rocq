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
Require GHC.Builtin.Uniques.
Require Import CoreFVs.
Require Proofs.ContainerProofs.

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

(* The baseline locality assumption, at its GHC 9.10 module path.
   initExitJoinUnique is concrete; isLocalUnique remains abstract. *)
Axiom isLocalUnique_initExitJoinUnique:
  Unique.isLocalUnique GHC.Builtin.Uniques.initExitJoinUnique = true.



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

(* This property must be established for each raw VarSet. A value can be
   stored at an unrelated key through the exposed UniqFM constructors. *)

Definition ValidVarSet (vs : VarSet) : Prop :=
  forall v1 v2, lookupVarSet vs v1 = Some v2 -> (v1 == v2).

(** ** Strong Valid VarSets *)

(* StrongValidVarSet says that the stored variable's unique agrees with its
   lookup key in the underlying IntMap. This agreement is needed
   for relating queries to stored payloads, for example when going from
   "all Vars pass a predicate" to "all stored values pass". It is equivalent
   to ValidVarSet, independently of the IntMap's structural well-formedness. *)

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

(** ** Extensional equality for VarSets *)

(* Well-formed, key-valid VarSets with equal membership have boolean-equal
   underlying IntMaps. The explicit premises supply three required facts:
   1. StrongValidVarSet: every key comes from a Var's unique
   2. WF PATRICIA tries: same key domain → same tree structure
   3. Values at same key are ==-equal (same unique)
   The proof maps stored values to keys before applying semantic uniqueness. *)
(* Formulated with destructured VarSet to avoid match in conclusion *)
Definition VarSet_IntMap (vs : VarSet) :=
  match vs with UniqSet.Mk_UniqSet (UniqFM.UFM m) => m end.

Lemma Var_key_equal_complete (x y : Var) :
  Unique.getWordKey (Unique.getUnique x) =
  Unique.getWordKey (Unique.getUnique y) ->
  GHC.Base.op_zeze__ x y = true.
Proof.
  destruct x as [nx [ux] tx mx sx dx ix].
  destruct y as [ny [uy] ty my sy dy iy].
  change (ux = uy -> BinNat.N.eqb ux uy = true).
  intro Heq. subst uy. apply BinNat.N.eqb_refl.
Qed.

(* A lookup queries precisely the unique of its argument. No trie-WF or
   default payload is needed to recover query validity from key validity. *)
Lemma StrongValidVarSet_ValidVarSet :
  forall vs, StrongValidVarSet vs -> ValidVarSet vs.
Proof.
  intros [[m]] Hvalid v1 v2 Hlookup.
  apply Var_key_equal_complete.
  symmetry. exact (Hvalid _ _ Hlookup).
Qed.

Lemma ValidVarSet_iff_StrongValidVarSet :
  forall vs, ValidVarSet vs <-> StrongValidVarSet vs.
Proof.
  intro vs. split.
  - apply ValidVarSet_StrongValidVarSet.
  - apply StrongValidVarSet_ValidVarSet.
Qed.

Lemma VarSet_extensional_equal : forall vs1 vs2 : VarSet,
  IntMapProofs.WF (VarSet_IntMap vs1) ->
  IntMapProofs.WF (VarSet_IntMap vs2) ->
  ValidVarSet vs1 -> ValidVarSet vs2 ->
  (forall v, elemVarSet v vs1 = elemVarSet v vs2) ->
  GHC.Base.op_zeze__ (VarSet_IntMap vs1) (VarSet_IntMap vs2) = true.
Proof.
  intros vs1 vs2 W1 W2 V1 V2 members.
  pose proof (@ValidVarSet_StrongValidVarSet vs1 V1) as K1.
  pose proof (@ValidVarSet_StrongValidVarSet vs2 V2) as K2.
  destruct vs1 as [[m1]], vs2 as [[m2]].
  cbn in W1, W2, K1, K2 |- *.
  eapply (ContainerProofs.IntMap_equal_by_key_membership
    (fun v : Var => Unique.getWordKey (Unique.getUnique v))
    Var_key_equal_complete m1 m2 W1 W2 K1 K2).
  destruct W1 as [f1 S1], W2 as [f2 S2].
  intro k.
  rewrite (IntMapProofs.member_Sem S1) (IntMapProofs.member_Sem S2).
  pose proof (@IntMapProofs.lookup_Sem _ _ _ k S1) as L1.
  pose proof (@IntMapProofs.lookup_Sem _ _ _ k S2) as L2.
  destruct (f1 k) as [v1|] eqn:F1;
    destruct (f2 k) as [v2|] eqn:F2; try reflexivity.
  - pose proof (members v1) as E.
    change (Data.IntMap.Internal.member
      (Unique.getWordKey (Unique.getUnique v1)) m1 =
      Data.IntMap.Internal.member
      (Unique.getWordKey (Unique.getUnique v1)) m2) in E.
    pose proof (K1 k v1 L1) as KV.
    change (Unique.getWordKey (Unique.getUnique v1) = k) in KV.
    rewrite KV (IntMapProofs.member_Sem S1)
      (IntMapProofs.member_Sem S2) F1 F2 in E.
    discriminate.
  - pose proof (members v2) as E.
    change (Data.IntMap.Internal.member
      (Unique.getWordKey (Unique.getUnique v2)) m1 =
      Data.IntMap.Internal.member
      (Unique.getWordKey (Unique.getUnique v2)) m2) in E.
    pose proof (K2 k v2 L2) as KV.
    change (Unique.getWordKey (Unique.getUnique v2) = k) in KV.
    rewrite KV (IntMapProofs.member_Sem S1)
      (IntMapProofs.member_Sem S2) F1 F2 in E.
    discriminate.
Qed.


(********************************* *)
