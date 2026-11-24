From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Semantics.LocalEffects Semantics.SharedState
  Projection.Matching.PrefixRelation Network.Scheduling.
From ParkourTheories.Projection.Matching Require RoleReadiness.
From ParkourTheories.Projection.Matching Require DeliveryAvailability.
From ParkourTheories Require Projection.Matching.MatchedReceiveSafety
  Choreography.WellFormedness.
From ParkourTheories Require Projection.Matching.ActionReflection
  Semantics.Runs.
From ParkourTheories Require Choreography.Execution Network.Execution
  Projection.Matching.CursorAlignment.
Require Choreography.Network Choreography.Choreo2 Parkour.Symbol.
Import ListNotations.

From ParkourTheories.Projection Require Import RunCorrespondence.

Section Preservation.
Context {M E : Type -> Type} {Store Input : Type}.
Variable model : local_model M E Parkour.Symbol.Symbol (Store * Input).
Variable stores : Parkour.Symbol.Symbol -> Store.
Variable input : Input.
Variable roster : list Parkour.Symbol.Symbol.
Variable A : Parkour.Symbol.Symbol -> Type.
Variable program : forall p, Choreography.Choreo2.Choreo M p (A p).

(* Returned endpoint values are the actual source values. A bare equality of
   mailboxes would not suffice to reflect finality. *)
Lemma matched_network_final source_trace source network_trace network :
  matches model stores input roster A program source_trace source
    network_trace network ->
  Network.Execution.final (shared_model model) network ->
    Choreography.Execution.final (shared_model model) roster source.
Proof.
  intros Match Final. split.
  - apply (proj2 (terminal_queues model stores input roster A program
    source_trace source network_trace network Match)).
    exact (proj2 Final).
  - destruct Match as [gs H].
    destruct (prefix_state model stores input roster A program source_trace
      source network_trace network gs H)
      as [_ [_ [f [Hroster Align]]]].
    destruct network as [es q st]. cbn in Hroster; subst es.
    apply (proj1 (all_returns (shared_model model) roster A f q st)) in Final.
    intros p member. destruct (proj1 Final p member) as [x Hx].
    exists x. destruct (Align p member) as [Ha].
    eapply CursorAlignment.aligned_returns; eassumption.
Qed.

Lemma matched_source_final source_trace source network_trace network :
  matches model stores input roster A program source_trace source
    network_trace network ->
  Choreography.Execution.final (shared_model model) roster source ->
    Network.Execution.final (shared_model model) network.
Proof.
  intros Match [Empty Done].
  pose proof (proj1 (terminal_queues model stores input roster A program
    source_trace source network_trace network Match)
    Empty) as Q.
  destruct Match as [gs H].
  destruct (prefix_state model stores input roster A program source_trace source
    network_trace network gs H)
    as [_ [_ [f [Hroster Align]]]].
  destruct network as [es q st]. cbn in Hroster; subst es.
  apply (proj2 (all_returns (shared_model model) roster A f q st)). split;
    [|exact Q].
  intros p member. destruct (Done p member) as [x Hx].
  exists x. destruct (Align p member) as [Ha].
  eapply RoleReadiness.source_return_is_network_return; eassumption.
Qed.

(* Safety at a receive site concerns the head and the actual decoder. It
   does not say there is a receive, or that any other action is enabled. *)
Definition inputs_available (source : @Choreography.Execution.configuration M E
    ((Parkour.Symbol.Symbol -> Store) * Input) A)
    (network : @Network.Execution.configuration M E
      ((Parkour.Symbol.Symbol -> Store) * Input)) :=
  DeliveryAvailability.inputs_available model roster A source network.

Lemma initial_inputs_available :
  inputs_available
    (@source_initial M E Store Input stores input A program)
    (@network_initial M E Store Input stores input roster A program).
Proof.
  intros p Hr.
  eexists; exists (CursorAlignment.generated_initial_alignment
    (shared_model model) Choreography.Network.Root p (A p) (program p)).
  split.
  - cbn. induction roster as [|r rs IH]; cbn in *; [contradiction|].
    destruct Hr as [->|Hr]; [now left|right; auto].
  - apply RoleReadiness.empty_delivery_available.
Qed.

Lemma matched_ready_from_inputs source_trace source network_trace network :
  matches model stores input roster A program source_trace source
    network_trace network ->
  inputs_available source network ->
  (Choreography.Execution.final (shared_model model) roster source \/
    exists a next_source,
      Choreography.Execution.step (shared_model model) roster source a
        next_source) ->
  Network.Execution.final (shared_model model) network \/ exists b next_network,
    Network.Execution.step (shared_model model) roster network b next_network.
Proof.
  intros Match Safe [Done | [a [next_source Act]]].
  - left; eapply matched_source_final; eassumption.
  - right. destruct Act as [p a next_source Hr Hstep Frame].
    destruct (Safe p Hr) as (t & h & Hin & Hinput).
    destruct Match as [gs H].
    destruct (prefix_state model stores input roster A program source_trace
      source network_trace network gs H)
      as [Hstore _].
    rewrite Hstore in Hstep.
    destruct (RoleReadiness.source_action_exposes_network_action
      (shared_model model) Choreography.Network.Root roster p (A p)
      _ t h _ _ _ _ _ _ _ Hinput Hstep)
      as (b & t' & q' & st' & live).
    destruct network as [es q st]; cbn in Hin,live. apply in_split_large in Hin.
    destruct Hin as (pre & post & ->). exists b. eexists.
    apply Network.Execution.Schedule. exact live.
Qed.
End Preservation.

(* Induction on a particular schedule uses only the receive facts of its
   matched prefixes. The structural proof must establish those facts for
   every reachable prefix. *)
Section Schedules.
Context {M E : Type -> Type} {Store Input : Type}.
Variable model : local_model M E Parkour.Symbol.Symbol (Store * Input).
Variable stores : Parkour.Symbol.Symbol -> Store.
Variable input : Input.
Variable roster : list Parkour.Symbol.Symbol.
Variable A : Parkour.Symbol.Symbol -> Type.
Variable program : forall p, Choreography.Choreo2.Choreo M p (A p).

Lemma preservation_from_frontiers :
  NoDup roster ->
  (forall source_trace source network_trace network gs,
    matched_prefix model stores input roster A program source_trace source
      network_trace network gs ->
    ActionReflection.safe_residuals model roster A source network gs) ->
  (forall source_trace source network_trace network,
    matches model stores input roster A program source_trace source
      network_trace network ->
    inputs_available model roster A source network) ->
  Runs.deadlock_free
    (@Choreography.Execution.step M E _ (shared_model model) roster A)
    (Choreography.Execution.final (shared_model model) roster)
    (@source_initial M E Store Input stores input A program) ->
  forall network_trace network,
    Network.Execution.run (shared_model model) roster
      (@network_initial M E Store Input stores input roster A program)
      network_trace network ->
    Runs.ready (Network.Execution.step (shared_model model) roster)
      (Network.Execution.final (shared_model model)) network.
Proof.
  intros ND Safe Available Source network_trace network Net.
  destruct (schedule_from_safe_receives model stores input roster A program ND
    Safe network_trace network Net) as (source_trace & source & Run & H).
  eapply matched_ready_from_inputs; [exact H | exact (Available _ _ _ _ H) |].
  exact (Source source_trace source Run).
Qed.

Lemma reflection_from_frontiers :
  NoDup roster ->
  (forall source_trace source network_trace network gs,
    matched_prefix model stores input roster A program source_trace source
      network_trace network gs ->
    ActionReflection.safe_residuals model roster A source network gs) ->
  (forall source_trace source network_trace network,
    matches model stores input roster A program source_trace source
      network_trace network ->
    inputs_available model roster A source network) ->
  forall network_trace network,
    Network.Execution.run (shared_model model) roster
      (@network_initial M E Store Input stores input roster A program)
      network_trace network ->
    Runs.stuck (Network.Execution.step (shared_model model) roster)
      (Network.Execution.final (shared_model model)) network ->
    exists source_trace source,
      Choreography.Execution.run (shared_model model) roster
        (@source_initial M E Store Input stores input A program)
        source_trace source /\
      matches model stores input roster A program
        source_trace source network_trace network /\
      Runs.stuck
        (@Choreography.Execution.step M E _ (shared_model model) roster A)
        (Choreography.Execution.final (shared_model model) roster) source.
Proof.
  intros ND Safe Available network_trace network Net Stuck.
  destruct (schedule_from_safe_receives model stores input roster A program ND
    Safe network_trace network Net) as (source_trace & source & Run & H).
  exists source_trace, source. split; [exact Run|]. split; [exact H|].
  eapply Runs.ready_stuck_reflection; [|exact Stuck].
  exact (matched_ready_from_inputs model stores input roster A program
    source_trace source network_trace network H
    (Available _ _ _ _ H)).
Qed.
End Schedules.

(* These public contracts have no frontier, realization, or receive-safety
   premise. Those facts come from the structural proof for the actual prefix. *)
Section Contracts.
Context {M E : Type -> Type} {Store Input : Type}.
Variable model : local_model M E Parkour.Symbol.Symbol (Store * Input).
Variable stores : Parkour.Symbol.Symbol -> Store.
Variable input : Input.
Variable roster : list Parkour.Symbol.Symbol.
Variable A : Parkour.Symbol.Symbol -> Type.
Variable program : forall p, Choreography.Choreo2.Choreo M p (A p).

Lemma well_formed_inputs_available :
  WellFormedness.well_formed roster M A program ->
  forall source_trace source network_trace network,
    matches model stores input roster A program source_trace source
      network_trace network ->
    inputs_available model roster A source network.
Proof.
  intros Formed source_trace source network_trace network [gs Prefix].
  exact (proj2 (MatchedReceiveSafety.matched_prefix_frontiers
    model stores input roster A program source_trace source network_trace
      network gs Formed Prefix)).
Qed.

Theorem matched_ready :
  WellFormedness.well_formed roster M A program ->
  forall source_trace source network_trace network,
    Choreography.Execution.run (shared_model model) roster
      (@source_initial M E Store Input stores input A program)
      source_trace source ->
    Network.Execution.run (shared_model model) roster
      (@network_initial M E Store Input stores input roster A program)
      network_trace network ->
    matches model stores input roster A program source_trace source
      network_trace network ->
    (Choreography.Execution.final (shared_model model) roster source \/
      exists a next_source,
        Choreography.Execution.step (shared_model model) roster source a
          next_source) ->
    Network.Execution.final (shared_model model) network \/
      exists b next_network,
        Network.Execution.step (shared_model model) roster
          network b next_network.
Proof.
  intros Formed source_trace source network_trace network Source Network Match
    Ready.
  eapply matched_ready_from_inputs.
  - exact Match.
  - exact (well_formed_inputs_available Formed source_trace source network_trace
    network Match).
  - exact Ready.
Qed.

Theorem epp_preserves_deadlock_freedom :
  WellFormedness.well_formed roster M A program ->
  (forall source_trace source,
    Choreography.Execution.run (shared_model model) roster
      (@source_initial M E Store Input stores input A program)
      source_trace source ->
    Choreography.Execution.final (shared_model model) roster source \/
      exists a next_source,
        Choreography.Execution.step (shared_model model) roster source a
          next_source) ->
  forall network_trace network,
    Network.Execution.run (shared_model model) roster
      (@network_initial M E Store Input stores input roster A program)
      network_trace network ->
    Network.Execution.final (shared_model model) network \/
      exists b next_network,
        Network.Execution.step (shared_model model) roster
          network b next_network.
Proof.
  intros Formed Source.
  apply preservation_from_frontiers.
  - exact (proj1 Formed).
  - exact (well_formed_safe_residuals model stores input roster A program
    Formed).
  - exact (well_formed_inputs_available Formed).
  - exact Source.
Qed.

Theorem deadlock_reflection :
  WellFormedness.well_formed roster M A program ->
  forall network_trace network,
    Network.Execution.run (shared_model model) roster
      (@network_initial M E Store Input stores input roster A program)
      network_trace network ->
    (~ Network.Execution.final (shared_model model) network /\
      forall b next_network,
        ~ Network.Execution.step (shared_model model) roster network b
          next_network) ->
    exists source_trace source,
      Choreography.Execution.run (shared_model model) roster
        (@source_initial M E Store Input stores input A program)
        source_trace source /\
      matches model stores input roster A program
        source_trace source network_trace network /\
      (~ Choreography.Execution.final (shared_model model) roster source /\
        forall a next_source,
          ~ Choreography.Execution.step (shared_model model) roster source a
            next_source).
Proof.
  intro Formed.
  apply reflection_from_frontiers.
  - exact (proj1 Formed).
  - exact (well_formed_safe_residuals model stores input roster A program
    Formed).
  - exact (well_formed_inputs_available Formed).
Qed.
End Contracts.
