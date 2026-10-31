(* Regression checks for the recovered invariant boundary. *)
From Coq Require Import NArith.
Require Import Core Exitify.
Require Import Proofs.ScopeInvariant Proofs.JoinPointInvariants Proofs.Exitify.
Require Proofs.ContainerContractCounterexamples Proofs.CoreSubst.
Require Proofs.Axioms Proofs.VarSetInvariant Proofs.VarSetFSet.
Require Proofs.VarSet Proofs.VarEnv.
Require Proofs.TrieMap.

(* Payload validity has two equivalent formulations, without trie-WF or
   default-value premises. Preserve the original one-way API as well. *)
Check (@Axioms.ValidVarSet_StrongValidVarSet :
  forall s : VarSet, Axioms.ValidVarSet s -> Axioms.StrongValidVarSet s).
Check (@Axioms.StrongValidVarSet_ValidVarSet :
  forall s : VarSet, Axioms.StrongValidVarSet s -> Axioms.ValidVarSet s).
Check (@Axioms.ValidVarSet_iff_StrongValidVarSet :
  forall s : VarSet, Axioms.ValidVarSet s <-> Axioms.StrongValidVarSet s).

(* Boolean structural equality still requires both sets' trie-WF and payload
   validity; raw membership equality alone supplies neither invariant. *)
Check (@Axioms.VarSet_extensional_equal : forall s t : VarSet,
  IntMapProofs.WF (Axioms.VarSet_IntMap s) ->
  IntMapProofs.WF (Axioms.VarSet_IntMap t) ->
  Axioms.ValidVarSet s -> Axioms.ValidVarSet t ->
  (forall v, elemVarSet v s = elemVarSet v t) ->
  GHC.Base.op_zeze__ (Axioms.VarSet_IntMap s) (Axioms.VarSet_IntMap t) = true).

(* Key-only specifications must not demand payload validity. *)
Check (@VarSetInvariant.isEmptyVarSet_spec : forall s : VarSet,
  IntMapProofs.WF (Axioms.VarSet_IntMap s) ->
  (isEmptyVarSet s = true <-> forall v, elemVarSet v s = false)).
Check (@VarSetInvariant.subVarSet_spec : forall s t : VarSet,
  IntMapProofs.WF (Axioms.VarSet_IntMap s) ->
  IntMapProofs.WF (Axioms.VarSet_IntMap t) ->
  (subVarSet s t = true <->
   forall v, elemVarSet v s = true -> elemVarSet v t = true)).
Check (@VarSetInvariant.disjointVarSet_spec : forall s t : VarSet,
  IntMapProofs.WF (Axioms.VarSet_IntMap s) ->
  IntMapProofs.WF (Axioms.VarSet_IntMap t) ->
  (disjointVarSet s t = true <->
   forall v, elemVarSet v s = true -> elemVarSet v t = false)).

Check (@VarSetFSet.VarSetFacts.subset_iff : forall s t : VarSet,
  VarSetFSet.VarSetFSet.WF s -> VarSetFSet.VarSetFSet.WF t ->
  (VarSetFSet.VarSetFSet.Subset s t <-> subVarSet s t = true)).
Check (@VarSetFSet.VarSetFacts.is_empty_iff : forall s : VarSet,
  VarSetFSet.VarSetFSet.WF s ->
  (VarSetFSet.VarSetFSet.Empty s <-> isEmptyVarSet s = true)).
Check (@VarSetFSet.VarSetFacts.disjoint_iff : forall s t : VarSet,
  VarSetFSet.VarSetFSet.WF s -> VarSetFSet.VarSetFSet.WF t ->
  (disjointVarSet s t = true <-> forall v,
   VarSetFSet.VarSetFSet.In v s -> ~ VarSetFSet.VarSetFSet.In v t)).

Check (@VarSet.subVarSet_refl : forall s : Core.VarSet,
  VarSetFSet.VarSetFSet.WF s -> subVarSet s s = true).
Check (@VarSet.subVarSet_trans : forall s t u : Core.VarSet,
  VarSetFSet.VarSetFSet.WF s -> VarSetFSet.VarSetFSet.WF t ->
  VarSetFSet.VarSetFSet.WF u ->
  subVarSet s t = true -> subVarSet t u = true -> subVarSet s u = true).
Check (@VarSet.disjointVarSet_iff : forall s t : Core.VarSet,
  VarSetFSet.VarSetFSet.WF s -> VarSetFSet.VarSetFSet.WF t ->
  (disjointVarSet s t = true <-> forall v,
   VarSetFSet.VarSetFSet.In v s -> ~ VarSetFSet.VarSetFSet.In v t)).
Check (@VarSetFSet.VarSetBasicFacts.filter_1 :
  forall (s : Core.VarSet) (x : Var) (f : Var -> bool),
  VarSetFSet.VarSetFSet.WF s ->
  VarSetFSet.VarSetFSet.In x (filterVarSet f s) -> VarSetFSet.VarSetFSet.In x s).
Check (@Proofs.VarEnv.elemVarSet_uniqAway : forall v iss s,
  VarSetFSet.VarSetFSet.WF s ->
  VarSetFSet.VarSetFSet.WF (getInScopeVars iss) ->
  subVarSet s (getInScopeVars iss) = true ->
  elemVarSet (uniqAway iss v) s = false).

(* This singleton has a sound trie but an unrelated payload unique. The
   key-only specifications must work even though payload validity is false. *)
Section KeyOnlyRegression.
  Variable v : Var.
  Let payload := setVarUnique v (Unique.MkUnique 1%N).
  Let query := setVarUnique v (Unique.MkUnique 0%N).
  Let s := UniqSet.Mk_UniqSet
    (UniqFM.UFM (Data.IntMap.Internal.Tip 0%N payload)).

  Lemma mismatched_singleton_WF : IntMapProofs.WF (Axioms.VarSet_IntMap s).
  Proof. apply IntMapProofs.singleton_WF. Qed.

  Lemma mismatched_singleton_not_valid : ~ Axioms.ValidVarSet s.
  Proof.
    intro V. pose proof (V query payload) as H.
    unfold query, payload, s in H. destruct v.
    specialize (H eq_refl). discriminate H.
  Qed.

  Lemma mismatched_singleton_key_specs :
    isEmptyVarSet s = false /\
    subVarSet s emptyVarSet = false /\
    disjointVarSet s emptyVarSet = true.
  Proof.
    assert (M : elemVarSet query s = true) by
      (unfold query, s; destruct v; reflexivity).
    split.
    - apply Bool.not_true_is_false. intro E.
      pose proof (proj1 (VarSetInvariant.isEmptyVarSet_spec s
        mismatched_singleton_WF) E query) as H.
      rewrite M in H. discriminate.
    - split.
      + apply Bool.not_true_is_false. intro E.
        pose proof (proj1 (VarSetInvariant.subVarSet_spec s emptyVarSet
          mismatched_singleton_WF VarSetInvariant.emptyVarSet_WF) E query M) as H.
        rewrite VarSetInvariant.elemVarSet_empty in H. discriminate.
      + apply (proj2 (VarSetInvariant.disjointVarSet_spec s emptyVarSet
          mismatched_singleton_WF VarSetInvariant.emptyVarSet_WF)).
        intros q _. apply VarSetInvariant.elemVarSet_empty.
  Qed.
End KeyOnlyRegression.

(* Generic helpers accept representation certificates, but the program-level
   theorem must discharge them internally and keep this exact contract. *)
Check (@exitifyProgram_WellScoped_JPV :
  forall pgm : CoreProgram,
  WellScopedProgram pgm ->
  isJoinPointsValidProgram pgm ->
  WellScopedProgram (exitifyProgram pgm) /\
  isJoinPointsValidProgram (exitifyProgram pgm)).

(* These declarations were refutable on the exposed raw datatypes, or by the
   boolean negation diagonal. Keep their names unavailable to future proofs. *)
Fail Check IntMapProofs.All_IntMaps_WF.
Fail Check Axioms.ValidVarSet_Axiom.
Fail Check Axioms.StrongValidVarSet_Axiom.
Fail Check IntMapProofs.deferredFix2_eq.

(* Raw map types do not satisfy the unconditional TrieMap laws. *)
Fail Check Proofs.TrieMap.TrieMapLaws__Map.
Fail Check Proofs.TrieMap.TrieMapLaws__IntMap.
Fail Check Proofs.TrieMap.TrieMapLaws__UniqFM.

(* The raw membership API must not grow the old dummy FSet operations or
   their unsupported interface laws back. Qualify names to avoid library
   operations such as List.fold or unrelated equality lemmas. *)
Fail Check VarSetFSet.VarSetFSet.choose.
Fail Check VarSetFSet.VarSetFSet.elements.
Fail Check VarSetFSet.VarSetFSet.partition.
Fail Check VarSetFSet.VarSetFSet.fold.
Fail Check VarSetFSet.VarSetFSet.equal.
Fail Check VarSetFSet.VarSetFSet.choose_1.
Fail Check VarSetFSet.VarSetFSet.elements_1.
Fail Check VarSetFSet.VarSetFSet.partition_1.
Fail Check VarSetFSet.VarSetFSet.fold_1.
Fail Check VarSetFSet.VarSetFSet.equal_1.
Fail Check VarSetFSet.VarSetFSet.equal_2.
Fail Check VarSetFSet.VarSetBasicFacts.choose_1.
Fail Check VarSetFSet.VarSetBasicFacts.elements_1.
Fail Check VarSetFSet.VarSetBasicFacts.partition_1.
Fail Check VarSetFSet.VarSetBasicFacts.fold_1.
Fail Check VarSetFSet.VarSetBasicFacts.equal_1.
Fail Check VarSetFSet.VarSetBasicFacts.equal_2.

Print Assumptions exitifyProgram_WellScoped_JPV.
Print Assumptions CoreSubst.WellScoped_substExpr.
