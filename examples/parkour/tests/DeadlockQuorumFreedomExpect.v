From Stdlib Require Import Lists.List Strings.String.
Require Import DeadlockLocal DeadlockState.
Require DeadlockSource DeadlockNetwork Main Parkour.Runtime Parkour.Symbol.
Require Choreography.Choreo2 Choreography.Network Control.Monad.Trans.Reader.
Import ListNotations.

(* Independent client expectation. Frozen before the corollary exists.
   No source WF premise: the library's client must prove that separately.
   No unconditional DF: even this client's local STM calls can block. *)
Definition quorum_deadlock_freedom_expected : Prop :=
  forall (E : Type -> Type) (Store Input : Type)
    (model : local_model Parkour.Runtime.IO E Parkour.Symbol.Symbol
      (Store * Input))
    (stores : Parkour.Symbol.Symbol -> Store) (input : Input),
  (forall tc s,
    DeadlockSource.crun (DeadlockState.shared_model model)
      [GHC.Base.hs_string__ "candidate"; GHC.Base.hs_string__ "voter1";
       GHC.Base.hs_string__ "voter2"; GHC.Base.hs_string__ "voter3"]
      (DeadlockSource.initial (@Main.quorumVoting) (stores, input)) tc s ->
    DeadlockSource.cfinal (DeadlockState.shared_model model)
      [GHC.Base.hs_string__ "candidate"; GHC.Base.hs_string__ "voter1";
       GHC.Base.hs_string__ "voter2"; GHC.Base.hs_string__ "voter3"] s \/
      exists ac s',
        DeadlockSource.cstep (DeadlockState.shared_model model)
          [GHC.Base.hs_string__ "candidate"; GHC.Base.hs_string__ "voter1";
           GHC.Base.hs_string__ "voter2"; GHC.Base.hs_string__ "voter3"] s ac s') ->
  forall tn n,
    DeadlockNetwork.run (DeadlockState.shared_model model)
      [GHC.Base.hs_string__ "candidate"; GHC.Base.hs_string__ "voter1";
       GHC.Base.hs_string__ "voter2"; GHC.Base.hs_string__ "voter3"]
      (DeadlockNetwork.initialize
        [GHC.Base.hs_string__ "candidate"; GHC.Base.hs_string__ "voter1";
         GHC.Base.hs_string__ "voter2"; GHC.Base.hs_string__ "voter3"]
        (fun p => Control.Monad.Trans.Reader.runReaderT
          (Choreography.Choreo2.unEpp
            (Choreography.Choreo2.epp (@Main.quorumVoting p)
              (@Parkour.Symbol.MkSSymbol p)))
          Choreography.Network.Root)
        (stores, input)) tn n ->
    DeadlockNetwork.nfinal (DeadlockState.shared_model model) n \/
      exists an n',
        DeadlockNetwork.nstep (DeadlockState.shared_model model)
          [GHC.Base.hs_string__ "candidate"; GHC.Base.hs_string__ "voter1";
           GHC.Base.hs_string__ "voter2"; GHC.Base.hs_string__ "voter3"] n an n'.
