From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Projection.Payloads.ReceiverCodec
  Projection.FIFO.Heads.LoggedPrefix Projection.CommunicationTree.Construction
  Projection.Matching.ReceiveConditions Projection.Matching.PrefixRelation
  Projection.Matching.ActionReflection Choreography.WellFormedness
  Projection.Matching.DeliveryAvailability Semantics.LocalEffects
  Semantics.SharedState Choreography.Execution.
Require Import Parkour.Symbol.
Import ListNotations.

Section Frontiers.
Context {M E Store Input} (model : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input : Input) (R : list Symbol) (A : Symbol ->
    Type)
  (c : forall p, Choreography.Choreo2.Choreo M p (A p)).

Theorem matched_receive_frontiers tc s tn n gs :
  well_formed R M A c ->
  matched_prefix model stores input R A c tc s tn n gs ->
  forall p, In p R ->
  source_head_paths (shared_model model) p (A p) (positions s p) gs /\
  source_originals (shared_model model) p (A p) (positions s p) gs.
Proof.
  intros WF Prefix p Member.
  assert (Head : source_head_paths (shared_model model) p (A p) (positions s p)
    gs).
  { eapply (source_head_paths_matched_from_tracked model stores input R A c tc s
    tn n gs);
      [exact (proj1 WF)|exact Prefix| |exact Member].
    intros past ar Archives cuts Own Nodes.
    eapply structural_root_layout; eassumption. }
  split; [exact Head|].
  exact (matched_source_originals_from_head model stores input R A c _ _ _ _ _
    WF Prefix p Member Head).
Qed.

Theorem matched_prefix_frontiers tc s tn n gs :
  well_formed R M A c ->
  matched_prefix model stores input R A c tc s tn n gs ->
  safe_residuals model R A s n gs /\
  inputs_available model R A s n.
Proof.
  intros WF Prefix. apply covered_residuals.
  - exact (prefix_state model stores input R A c _ _ _ _ _ Prefix).
  - exact (matched_receive_frontiers _ _ _ _ _ WF Prefix).
Qed.
End Frontiers.
