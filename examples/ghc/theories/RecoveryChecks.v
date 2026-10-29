(* Regression checks for the recovered invariant boundary. *)
Require Import Core Exitify.
Require Import Proofs.ScopeInvariant Proofs.JoinPointInvariants Proofs.Exitify.
Require Proofs.ContainerContractCounterexamples Proofs.CoreSubst.

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

Print Assumptions exitifyProgram_WellScoped_JPV.
Print Assumptions CoreSubst.WellScoped_substExpr.
