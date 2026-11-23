From Stdlib Require Import Lists.List.
From ParkourTheories.Semantics Require Import LocalEffects SharedState Runs.
From ParkourTheories Require Choreography.RoleSteps Choreography.Execution
  Network.Endpoints Network.Execution Choreography.WellFormedness.
Require Choreography.Choreo2 Choreography.Network Control.Monad.Trans.Reader.
Require Parkour.Symbol.

(* Independent contract, frozen before the library proofs. No theorem from
   Progress or RunAndProgressTypes is imported here.
   Only the not-yet-implemented history/state matching relation is abstract.
   Supplying that relation is NOT supplying a simulation or progress proof. *)
Module RunAndProgressTypes.
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
    @Choreography.Execution.configuration M E
      ((Parkour.Symbol.Symbol -> Store) * Input) A :=
  Choreography.Execution.initial c (stores, input).

Definition network_initial :
    @Network.Execution.configuration M E
      ((Parkour.Symbol.Symbol -> Store) * Input) :=
  Network.Execution.initialize R
    (fun p => Control.Monad.Trans.Reader.runReaderT
      (Choreography.Choreo2.unEpp
        (Choreography.Choreo2.epp (c p) (@Parkour.Symbol.MkSSymbol p)))
      Choreography.Network.Root)
    (stores, input).

(* The deadlock_free predicates are deliberately expanded: every finite trace
  and
   destination, and final OR an actual enabled action, on BOTH machines.
   No local totality, fairness, normalization, simulation, or target-progress
   hypothesis is accepted. NoDup and codec premises live only in well_formed. *)
Definition epp_preserves_deadlock_freedom : Prop :=
  WellFormedness.well_formed R M A c ->
  (forall tc s,
    @Choreography.Execution.run M E _
      (SharedState.shared_model model) R A source_initial tc s ->
    Choreography.Execution.final (SharedState.shared_model model) R
      s \/
      exists ac s',
        Choreography.Execution.step (SharedState.shared_model
          model) R s ac s') ->
  forall tn n,
    Network.Execution.run (SharedState.shared_model model) R
      network_initial tn n ->
    Network.Execution.final (SharedState.shared_model model) n \/
      exists an n',
        Network.Execution.step (SharedState.shared_model model) R n an
          n'.

(* This interface mentions actual typed traces and machine configurations.
   In particular, it relates a given network history, not an unrelated run.
   The eventual real relation may close over these same common inputs. *)
Definition matches_interface : Type :=
  list (@RoleSteps.source_action E
    ((Parkour.Symbol.Symbol -> Store) * Input)) ->
  @Choreography.Execution.configuration M E
    ((Parkour.Symbol.Symbol -> Store) * Input) A ->
  list (@Endpoints.action E
    ((Parkour.Symbol.Symbol -> Store) * Input)) ->
  @Network.Execution.configuration M E
    ((Parkour.Symbol.Symbol -> Store) * Input) -> Prop.

Variable matches : matches_interface.

Definition network_run_has_source : Prop :=
  WellFormedness.well_formed R M A c ->
  forall tn n,
    Network.Execution.run (SharedState.shared_model model) R
      network_initial tn n ->
    exists tc s,
      @Choreography.Execution.run M E _
        (SharedState.shared_model model) R A source_initial tc s /\
      matches tc s tn n.

Definition matched_ready : Prop :=
  WellFormedness.well_formed R M A c ->
  forall tc s tn n,
    @Choreography.Execution.run M E _
      (SharedState.shared_model model) R A source_initial tc s ->
    Network.Execution.run (SharedState.shared_model model) R
      network_initial tn n ->
    matches tc s tn n ->
    (Choreography.Execution.final (SharedState.shared_model model)
      R s \/
      exists ac s',
        Choreography.Execution.step (SharedState.shared_model
          model) R s ac s') ->
    Network.Execution.final (SharedState.shared_model model) n \/
      exists an n',
        Network.Execution.step (SharedState.shared_model model) R n an
          n'.

Definition deadlock_reflection : Prop :=
  WellFormedness.well_formed R M A c ->
  forall tn n,
    Network.Execution.run (SharedState.shared_model model) R
      network_initial tn n ->
    (~ Network.Execution.final (SharedState.shared_model model) n /\
      forall an n',
        ~ Network.Execution.step (SharedState.shared_model model) R n an
          n') ->
    exists tc s,
      @Choreography.Execution.run M E _
        (SharedState.shared_model model) R A source_initial tc s /\
      matches tc s tn n /\
      (~ Choreography.Execution.final (SharedState.shared_model
        model) R s /\
        forall ac s',
          ~ Choreography.Execution.step (SharedState.shared_model
            model) R s ac s').
End Expected.
End RunAndProgressTypes.

(* These are type definitions, not purported EPP theorems. Direct witnesses
   against real exports must be supplied in a SEPARATE file after matches and
   the library exist; do not instantiate matches with a fixture relation. *)
Check @RunAndProgressTypes.epp_preserves_deadlock_freedom.
Check @RunAndProgressTypes.network_run_has_source.
Check @RunAndProgressTypes.matched_ready.
Check @RunAndProgressTypes.deadlock_reflection.
