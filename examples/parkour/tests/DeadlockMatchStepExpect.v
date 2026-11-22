From Stdlib Require Import Lists.List.
From ITree Require Import ITree.
Require Import DeadlockMatchStep DeadlockMatch DeadlockRoster DeadlockAlignment
  DeadlockSource DeadlockNetwork DeadlockMessages DeadlockOrder DeadlockState
  DeadlockLocal DeadlockProjectionExpect DeadlockProjection
  Parkour.Symbol Parkour.Codec Control.Monad.Tree.
Require Choreography.Choreo2.
Import ListNotations.

(* A genuine generated send and an actual scheduled initial network action.
   The source prefix and residual are obtained from the proved reflection,
   not supplied to it. No local-event or scheduling hypothesis is assumed. *)
Definition Identity (X : Type) := X.
Definition NoEvent (_ : Type) := Empty_set.
Definition pure_model : local_model Identity NoEvent role (unit * unit) :=
  {| interpret_local := fun _ x => Ret x;
     reply_local := fun _ _ _ _ _ _ => False |}.
Definition sender : role := [].
Definition receiver : role := [BinNums.N0].
Definition participants := [sender; receiver].
Definition result p := Choreography.Choreo2.At bool receiver p.
Definition located p : Choreography.Choreo2.At bool sender p :=
  Choreography.Choreo2.Mk_At (fun _ => true).
Definition choreography p : Choreography.Choreo2.Choreo Identity p (result p) :=
  Perf (@Choreography.Choreo2.Comm Identity p bool sender receiver
    show_bool read_bool (known sender) (known receiver) MkSSymbol (located p) MkSSymbol).
Definition stores (_ : role) := tt.
Definition controls p : @control Identity NoEvent (result p) :=
  load (runner (choreography p) Choreography.Network.Root).
Definition initial : @DeadlockNetwork.configuration Identity NoEvent
    ((role -> unit) * unit) :=
  DeadlockMatch.network_initial stores tt participants result choreography.
Definition sent : @action NoEvent ((role -> unit) * unit) :=
  Sent sender receiver Choreography.Network.Root (@show bool show_bool true).

Lemma participants_nodup : NoDup participants.
Proof.
  constructor.
  - intros [H|H]; [discriminate|contradiction].
  - constructor; [intro H; contradiction|constructor].
Qed.

Lemma distinct : receiver <> sender.
Proof. discriminate. Qed.

Lemma generated_sender_action :
  exists u, step (shared_model pure_model) participants sender (result sender)
    (controls sender) empty_queues (stores,tt) sent u
    (enqueue empty_queues (sender,receiver,Choreography.Network.Root)
      (@show bool show_bool true)) (stores,tt).
Proof.
  unfold controls, choreography.
  eexists.
  eapply StepContinue with (x := Choreography.Network.Root).
  - apply ReturnPure.
  - apply StepLeft. apply StepBind. apply StepSend.
Qed.

Example nonempty_actual_prefix :
  exists n' sa s' gs',
    nstep (shared_model pure_model) participants initial sent n' /\
    matched_prefix pure_model stores tt participants result choreography
      [sa] s' [sent] n' gs' /\
    cstep (shared_model pure_model) participants
      (DeadlockMatch.source_initial stores tt result choreography) sa s'.
Proof.
  destruct generated_sender_action as [u H].
  set (target := assembled participants result
    (set_control result controls sender u)
    (enqueue empty_queues (sender,receiver,Choreography.Network.Root)
      (@show bool show_bool true)) (stores,tt)).
  assert (Net : nstep (shared_model pure_model) participants initial sent target).
  { change (nstep (shared_model pure_model) participants
      (assembled participants result controls empty_queues (stores,tt)) sent target).
    apply schedule_role; [apply participants_nodup|now left|exact H]. }
  destruct (initial_prefix_step pure_model participants result stores tt choreography
    sent target participants_nodup Net) as (sa & s' & gs' & Prefix & Source).
  exists target, sa, s', gs'. auto.
Qed.

Example safety_does_not_require_readiness X kind o p r rd gs :
  receive_at X kind o p r rd empty_queues gs.
Proof. intros w ws x Head. discriminate. Qed.

Print Assumptions aligned_decorated_step.
Print Assumptions endpoint_decorated_step.
Print Assumptions state_step.
Print Assumptions matched_prefix_step.
Print Assumptions initial_prefix_step.
Print Assumptions nonempty_actual_prefix.
