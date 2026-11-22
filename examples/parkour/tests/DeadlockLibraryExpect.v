From Stdlib Require Import Lists.List.
Require Import DeadlockLocal DeadlockState DeadlockRuns.
Require DeadlockSource DeadlockNetwork DeadlockWellFormed.
Require Choreography.Choreo2 Choreography.Network Control.Monad.Trans.Reader.
Require Parkour.Symbol.

(* Independent contract, frozen before the library proofs. No theorem from
   DeadlockFreedom or DeadlockContract is imported here.
   Only the not-yet-implemented history/state matching relation is abstract.
   Supplying that relation is NOT supplying a simulation or progress proof. *)
Module DeadlockContract.
Section Expected.
Context (M E : Type -> Type) (Store Input : Type).
Variable model : local_model M E Parkour.Symbol.Symbol (Store * Input).
Variable stores : Parkour.Symbol.Symbol -> Store.
Variable input : Input.
Variable R : list Parkour.Symbol.Symbol.
Variable A : Parkour.Symbol.Symbol -> Type.
Variable c : forall p, Choreography.Choreo2.Choreo M p (A p).

(* Both initial machines use exactly the same state and shared_model.
   Source initial expands to Code [] (c p), state (stores,input), and [].
   Network initialize expands to one loaded endpoint per role in R, empty
   queues, and state (stores,input). The program is the actual Root runner. *)
Definition source_initial :
    @DeadlockSource.configuration M E
      ((Parkour.Symbol.Symbol -> Store) * Input) A :=
  DeadlockSource.initial c (stores, input).

Definition network_initial :
    @DeadlockNetwork.configuration M E
      ((Parkour.Symbol.Symbol -> Store) * Input) :=
  DeadlockNetwork.initialize R
    (fun p => Control.Monad.Trans.Reader.runReaderT
      (Choreography.Choreo2.unEpp
        (Choreography.Choreo2.epp (c p) (@Parkour.Symbol.MkSSymbol p)))
      Choreography.Network.Root)
    (stores, input).

(* The DF predicates are deliberately expanded: every finite trace and
   destination, and final OR an actual enabled action, on BOTH machines.
   No local totality, fairness, normalization, simulation, or target-progress
   hypothesis is accepted. NoDup and codec premises live only in well_formed. *)
Definition epp_preserves_deadlock_freedom : Prop :=
  DeadlockWellFormed.well_formed R M A c ->
  (forall tc s,
    @DeadlockSource.crun M E _
      (DeadlockState.shared_model model) R A source_initial tc s ->
    DeadlockSource.cfinal (DeadlockState.shared_model model) R s \/
      exists ac s',
        DeadlockSource.cstep (DeadlockState.shared_model model) R s ac s') ->
  forall tn n,
    DeadlockNetwork.run (DeadlockState.shared_model model) R
      network_initial tn n ->
    DeadlockNetwork.nfinal (DeadlockState.shared_model model) n \/
      exists an n',
        DeadlockNetwork.nstep (DeadlockState.shared_model model) R n an n'.

(* This interface mentions actual typed traces and machine configurations.
   In particular, it relates a given network history, not an unrelated run.
   The eventual real relation may close over these same common inputs. *)
Definition matches_interface : Type :=
  list (@DeadlockSource.source_action E
    ((Parkour.Symbol.Symbol -> Store) * Input)) ->
  @DeadlockSource.configuration M E
    ((Parkour.Symbol.Symbol -> Store) * Input) A ->
  list (@DeadlockNetwork.action E
    ((Parkour.Symbol.Symbol -> Store) * Input)) ->
  @DeadlockNetwork.configuration M E
    ((Parkour.Symbol.Symbol -> Store) * Input) -> Prop.

Variable matches : matches_interface.

Definition network_run_has_source : Prop :=
  DeadlockWellFormed.well_formed R M A c ->
  forall tn n,
    DeadlockNetwork.run (DeadlockState.shared_model model) R
      network_initial tn n ->
    exists tc s,
      @DeadlockSource.crun M E _
        (DeadlockState.shared_model model) R A source_initial tc s /\
      matches tc s tn n.

Definition matched_ready : Prop :=
  DeadlockWellFormed.well_formed R M A c ->
  forall tc s tn n,
    @DeadlockSource.crun M E _
      (DeadlockState.shared_model model) R A source_initial tc s ->
    DeadlockNetwork.run (DeadlockState.shared_model model) R
      network_initial tn n ->
    matches tc s tn n ->
    (DeadlockSource.cfinal (DeadlockState.shared_model model) R s \/
      exists ac s',
        DeadlockSource.cstep (DeadlockState.shared_model model) R s ac s') ->
    DeadlockNetwork.nfinal (DeadlockState.shared_model model) n \/
      exists an n',
        DeadlockNetwork.nstep (DeadlockState.shared_model model) R n an n'.

Definition deadlock_reflection : Prop :=
  DeadlockWellFormed.well_formed R M A c ->
  forall tn n,
    DeadlockNetwork.run (DeadlockState.shared_model model) R
      network_initial tn n ->
    (~ DeadlockNetwork.nfinal (DeadlockState.shared_model model) n /\
      forall an n',
        ~ DeadlockNetwork.nstep (DeadlockState.shared_model model) R n an n') ->
    exists tc s,
      @DeadlockSource.crun M E _
        (DeadlockState.shared_model model) R A source_initial tc s /\
      matches tc s tn n /\
      (~ DeadlockSource.cfinal (DeadlockState.shared_model model) R s /\
        forall ac s',
          ~ DeadlockSource.cstep (DeadlockState.shared_model model) R s ac s').
End Expected.
End DeadlockContract.

(* These are type definitions, not purported EPP theorems. Direct witnesses
   against real exports must be supplied in a SEPARATE file after matches and
   the library exist; do not instantiate matches with a fixture relation. *)
Check @DeadlockContract.epp_preserves_deadlock_freedom.
Check @DeadlockContract.network_run_has_source.
Check @DeadlockContract.matched_ready.
Check @DeadlockContract.deadlock_reflection.
