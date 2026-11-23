From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Semantics.LocalEffects Semantics.SharedState
  Projection.Matching.PrefixRelation.
From ParkourTheories Require Projection.Matching.MatchedReceiveSafety
  Choreography.WellFormedness.
From ParkourTheories Require Projection.Matching.ActionReflection
  Semantics.Runs.
From ParkourTheories Require Choreography.Execution Network.Execution.
Require Choreography.Choreo2 Parkour.Symbol.
Import ListNotations.

Section RunCorrespondence.
Context {M E : Type -> Type} {Store Input : Type}.
Variable model : local_model M E Parkour.Symbol.Symbol (Store * Input).
Variable stores : Parkour.Symbol.Symbol -> Store.
Variable input : Input.
Variable roster : list Parkour.Symbol.Symbol.
Variable A : Parkour.Symbol.Symbol -> Type.
Variable program : forall p, Choreography.Choreo2.Choreo M p (A p).
Local Notation sem := (shared_model model).
Local Notation start_source := (@source_initial M E Store Input stores input A
  program).
Local Notation start_network := (@network_initial M E Store Input stores input
  roster A program).
Local Notation paired := (matches model stores input roster A program).
Local Notation prefix := (matched_prefix model stores input roster A program).
Local Notation network_step := (Network.Execution.step sem roster).
Local Notation WF := (WellFormedness.well_formed roster M A program).

Lemma empty_network_run_has_source network :
  Network.Execution.run sem roster start_network [] network ->
  exists source_trace source,
    Choreography.Execution.run sem roster start_source source_trace source /\
    paired source_trace source [] network.
Proof.
  intro H. inversion H; subst. exists [], start_source.
  split; [constructor | apply initial_matches].
Qed.

Lemma network_run_snoc_view initial trace reached :
  Network.Execution.run sem roster initial trace reached ->
  Runs.finite_run network_step initial trace reached.
Proof.
  intro H; induction H; [constructor|].
  apply Runs.run_cons_iff. eauto.
Qed.

Lemma schedule_from_safe_receives :
  NoDup roster ->
  (forall source_trace source network_trace network gs,
    prefix source_trace source network_trace network gs ->
    ActionReflection.safe_residuals model roster A source network gs) ->
  forall network_trace network,
    Network.Execution.run sem roster start_network network_trace network ->
    exists source_trace source,
      Choreography.Execution.run sem roster start_source source_trace source /\
      paired source_trace source network_trace network.
Proof.
  intros ND Safe network_trace network Run. apply network_run_snoc_view in Run.
  remember start_network as start eqn:From in Run.
  induction Run as [start |start tr x a y Run IH Step].
  - subst start. exists [], start_source.
    split; [constructor | apply initial_matches].
  - destruct (IH From) as (source_trace & source & Source & gs & Match).
    destruct (ActionReflection.matched_prefix_step model roster A stores input
      program source_trace source tr x gs a y ND Match (Safe _ _ _ _ _ Match)
      Step)
      as (sa & next_source & gs' & Next & Act).
    exists (source_trace ++ [sa]), next_source. split; [eapply Runs.RunSnoc;
      eassumption|].
    now exists gs'.
Qed.

Lemma well_formed_safe_residuals :
  WF ->
  forall source_trace source network_trace network gs,
    prefix source_trace source network_trace network gs ->
    ActionReflection.safe_residuals model roster A source network gs.
Proof.
  intros Formed source_trace source network_trace network gs Prefix.
  exact (proj1 (MatchedReceiveSafety.matched_prefix_frontiers
    model stores input roster A program source_trace source network_trace
      network gs Formed Prefix)).
Qed.

Theorem network_run_has_source :
  WF ->
  forall network_trace network,
    Network.Execution.run sem roster start_network network_trace network ->
    exists source_trace source,
      Choreography.Execution.run sem roster start_source source_trace source /\
      paired source_trace source network_trace network.
Proof.
  intro Formed.
  apply schedule_from_safe_receives.
  - exact (proj1 Formed).
  - exact (well_formed_safe_residuals Formed).
Qed.

End RunCorrespondence.
