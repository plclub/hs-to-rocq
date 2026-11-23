From Stdlib Require Import Lists.List.
From ITree Require Import ITree.
From ParkourTheories Require Import Semantics.LocalEffects
  Choreography.PendingDeliveries Choreography.RoleSteps Network.Mailboxes
  Network.Endpoints Projection.Matching.CursorAlignment
  Projection.Matching.RoleReadiness Choreography.Observations
  Projection.EndpointRunner Projection.ConstructorEquations.
Require Import Control.Monad.Tree.
From ParkourTheories.Tests.Choreography Require CommunicationOrder
  AsynchronousSteps.
Require Choreography.Choreo2.
Import ListNotations.
Module F := CommunicationOrder.

Definition pure_app : Choreography.Choreo2.Choreo (itree F.request) F.B bool :=
  App (Pure (fun b : bool => b)) (Pure true).

(* Alignment removes the left branch first. The source return derivation
   below removes the right branch first. The actual target stays an App. *)
Lemma left_first_alignment :
  aligned F.model Choreography.Network.Root F.B bool (Code [] pure_app)
    (CApp (CPure (fun b : bool => b)) (CPure true)).
Proof.
  unfold pure_app.
  eapply AlignSilent; [apply SApp |].
  eapply AlignSilent; [apply SForkLeft; apply SPure |].
  eapply AlignSilent; [apply SForkRight; apply SPure |].
  eapply AlignSilent; [apply SJoin |].
  apply AlignReturned.
  eapply AdminApp with (g := fun b : bool => b) (x := true);
    apply AdminPure.
Qed.

Lemma right_first_source_return :
  RoleSteps.returns F.model (Code [] pure_app) true.
Proof.
  unfold pure_app.
  eapply ReturnsSilent; [apply SApp |].
  eapply ReturnsSilent; [apply SForkRight; apply SPure |].
  eapply ReturnsSilent; [apply SForkLeft; apply SPure |].
  eapply ReturnsSilent; [apply SJoin |].
  apply Returns.
Qed.

Lemma opposite_bookkeeping_return :
  Endpoints.returns F.model bool
    (load (runner pure_app Choreography.Network.Root)) true.
Proof.
  change (Endpoints.returns F.model bool
    (CApp (CPure (fun b : bool => b)) (CPure true)) true).
  eapply source_return_is_network_return.
  - exact left_first_alignment.
  - exact right_first_source_return.
Qed.

Lemma generated_parallel_exposes_real_action :
  exists a n' q' s',
    Endpoints.step F.model F.roles F.B bool
      (load (runner F.parallel Choreography.Network.Root))
      empty_queues 0 a n' q' s'.
Proof.
  destruct AsynchronousSteps.parallel_action as [c' Hs].
  eapply generated_source_action_exposes_network_action. exact Hs.
Qed.

Lemma generated_off_role_prefix_exposes_real_action :
  exists a n' q' s',
    Endpoints.step F.model F.roles F.B (Choreography.Choreo2.At bool F.B F.B)
      (load (runner (F.independent F.B) Choreography.Network.Root))
      empty_queues 0 a n' q' s'.
Proof.
  destruct AsynchronousSteps.independent_action as [c' Hs].
  eapply generated_source_action_exposes_network_action. exact Hs.
Qed.

Lemma resumed_local_exposes_real_action :
  exists a n' q' s',
    Endpoints.step F.model F.roles F.B (Choreography.Choreo2.At bool F.B F.B)
      (CBind (CLocal F.act) (fun x => CPure (here_at x)))
      empty_queues 0 a n' q' s'.
Proof.
  eapply source_action_exposes_network_action with
    (Ha := AlignLocal F.model Choreography.Network.Root F.B bool [] F.act)
    (sq := []).
  - exact I.
  - apply RLocal.
    eapply LocalStep with (e := F.Act) (x := true) (s' := 0).
    + apply ViewNow. reflexivity.
    + split; reflexivity.
Qed.

(* A typed source delivery alone is not a wire-delivery invariant. These two
   checks prevent the availability premise from being silently dropped. *)
Definition receive_true :=
  F.comm F.B F.A F.B (F.located true).

Lemma typed_receive_is_source_enabled :
  role_step F.model F.roles (Choreography.Choreo2.At bool F.B F.B)
    (Code [] receive_true) 0 [Pending bool DataDelivery [] F.A F.B true]
    (ReceiveAction bool [] F.A F.B true) (Returned (here_at true)) 0 [].
Proof.
  unfold receive_true, F.comm.
  eapply RReceive; [discriminate | constructor].
Qed.

Lemma empty_wire_receive_is_not_network_enabled :
  ~ possible F.model F.B
      (load (runner receive_true Choreography.Network.Root)) empty_queues 0.
Proof.
  unfold receive_true, F.comm.
  assert (neq : F.A <> F.B) by discriminate.
  rewrite (runner_comm_receiver (itree F.request) F.A F.B bool
    F.show_bool F.read_bool (Parkour.Symbol.known F.A) (Parkour.Symbol.known
      F.B)
    (F.located true) neq Choreography.Network.Root).
  cbn [load possible empty_queues].
  intros [Hfalse | [tag [_ [Hrecv | [x [_ Hfalse]]]]]]; try contradiction.
  destruct Hrecv as [w [ws [x [Hhead _]]]]. discriminate.
Qed.

Lemma occurrence_receive_skips_same_lane :
  role_step F.model F.roles (Choreography.Choreo2.At bool F.B F.B)
    (Code F.second_path (F.comm F.B F.A F.B (F.located false)))
    0 F.two_pending (ReceiveAction bool F.second_path F.A F.B false)
    (Returned (here_at false)) 0
    [Pending bool DataDelivery F.first_path F.A F.B true].
Proof.
  unfold F.comm, F.two_pending.
  eapply RReceive; [discriminate |].
  apply TakeAtOther, TakeAtHead.
Qed.

Lemma strong_fifo_still_rejects_second_delivery :
  forall sq', ~ take_first_on_source_channel DataDelivery F.second_path F.A F.B
    false F.two_pending sq'.
Proof. exact AsynchronousSteps.fifo. Qed.

(* Availability must inspect the occurrence-only source delivery too. A
   predicate still using take_first_on_source_channel would miss this enabled
     receive. *)
Lemma occurrence_availability_rejects_bad_wire_head :
  ~ delivery_available_at bool DataDelivery F.second_path F.A F.B F.read_bool
      Choreography.Network.Root
      (enqueue empty_queues (F.A,F.B,Choreography.Network.Root)
        [BinNat.N.of_nat 2]) F.two_pending.
Proof.
  intro Havailable.
  assert (Htake : take_at_occurrence DataDelivery F.second_path F.A F.B false
    F.two_pending
    [Pending bool DataDelivery F.first_path F.A F.B true]).
  { unfold F.two_pending. apply TakeAtOther, TakeAtHead. }
  destruct (Havailable false _ Htake) as [w [ws [y [Hhead Hread]]]].
  rewrite enqueue_same in Hhead. cbn [empty_queues] in Hhead.
  inversion Hhead; subst w ws. discriminate Hread.
Qed.

(* A different decodable payload does not obstruct readiness. No equality
   with the payload of the heterogeneous take_at_occurrence witness is
     extracted. *)
Lemma occurrence_availability_accepts_other_decodable_payload :
  delivery_available_at bool DataDelivery F.second_path F.A F.B F.read_bool
    Choreography.Network.Root
    (enqueue empty_queues (F.A,F.B,Choreography.Network.Root)
      (@Parkour.Codec.show bool F.show_bool true)) F.two_pending.
Proof.
  intros x sq' _.
  exists (@Parkour.Codec.show bool F.show_bool true), [], true.
  split; [rewrite enqueue_same; reflexivity | reflexivity].
Qed.
