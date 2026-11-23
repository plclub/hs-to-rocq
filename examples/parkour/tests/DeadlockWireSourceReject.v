From Stdlib Require Import Lists.List Strings.String.
Require Import DeadlockWireRunsExpect DeadlockLocal DeadlockSource DeadlockRuns
  DeadlockMatch DeadlockState DeadlockNetwork DeadlockWireQueueReject DeadlockWireValueExpect.
Import ListNotations.

Definition produced {E S} R (a : @source_action E S) : list pending :=
  match a with
  | SendAction X o p r x => [Pending X DataDelivery o p r x]
  | AnnounceAction X o p x => announcement R X o p x
  | _ => []
  end.

Definition consumed {E S} (a : @source_action E S) : list pending :=
  match a with
  | ReceiveAction X o p r x => [Pending X DataDelivery o p r x]
  | HearAction X o p r x => [Pending X ChoiceDelivery o p r x]
  | _ => []
  end.

Lemma take_at_preserves {X} k o p r (x : X) q q' P :
  take_at k o p r x q q' ->
  Forall P q -> P (Pending X k o p r x) /\ Forall P q'.
Proof.
  induction 1; intro F; inversion F; subst.
  - split; assumption.
  - destruct (IHtake_at H3) as [A B]. split; [exact A|].
    constructor; assumption.
Qed.

Lemma role_queue_guard {M E S} (m : local_model M E Parkour.Symbol.Symbol S)
    R p X t s q a t' s' q' P :
  @role_step M E S m R p X t s q a t' s' q' ->
  Forall P q -> Forall P (produced R a) ->
  Forall P q' /\ Forall P (consumed a).
Proof.
  induction 1; cbn [produced consumed]; intros F G;
    try solve [split; [assumption|constructor]];
    try solve [split; [apply Forall_app; split; assumption|constructor]];
    try solve [eapply IHrole_step; eassumption].
  - destruct (take_at_preserves _ _ _ _ _ _ _ _ H F) as [A B].
    split; [exact B|constructor; [exact A|constructor]].
  - destruct (take_at_preserves _ _ _ _ _ _ _ _ H F) as [A B].
    split; [exact B|constructor; [exact A|constructor]].
Qed.

Lemma step_queue_guard {M E S A} (m : local_model M E Parkour.Symbol.Symbol S)
    R (c c' : @DeadlockSource.configuration M E S A) a P :
  cstep m R c a c' ->
  Forall P (deliveries c) -> Forall P (produced R a) ->
  Forall P (deliveries c') /\ Forall P (consumed a).
Proof.
  intros H. destruct H. eapply role_queue_guard. eassumption.
Qed.

Lemma run_queue_guard {M E S A} (m : local_model M E Parkour.Symbol.Symbol S)
    R (c c' : @DeadlockSource.configuration M E S A) tr P :
  finite_run (cstep m R) c tr c' ->
  Forall P (deliveries c) ->
  Forall (fun a => Forall P (produced R a)) tr ->
  Forall P (deliveries c') /\
  Forall (fun a => Forall P (consumed a)) tr.
Proof.
  induction 1; intros F G; [split; [exact F|constructor]|].
  apply Forall_app in G. destruct G as [G Last].
  inversion Last; subst.
  destruct (IHfinite_run F G) as [Q C].
  destruct (step_queue_guard _ _ _ _ _ _ H0 Q H3) as [Q' C'].
  split; [exact Q'|]. apply Forall_app. split; [exact C|].
  constructor; [exact C'|constructor].
Qed.

Local Notation bad_path :=
  (Pending bool ChoiceDelivery [ChoiceBody] wire_A wire_B true).

Theorem reject_wrong_occurrence : wire_reject_wrong_occurrence.
Proof.
  intros s n [gs Match].
  pose proof (prefix_source_run wire_model wire_stores tt wire_roles
    (fun _ => bool) wire_choice _ _ _ _ _ Match) as Run.
  pose proof (run_queue_guard _ _ _ _ _ (fun v => v <> bad_path) Run) as Guard.
  specialize (Guard (Forall_nil _) ltac:(
    cbn [produced announcement wire_roles wire_A wire_B wire_C] ;
    repeat constructor; intro H; discriminate)).
  destruct Guard as [_ Guard].
  apply Forall_cons_iff in Guard; destruct Guard as [_ Guard].
  apply Forall_cons_iff in Guard; destruct Guard as [_ Guard].
  apply Forall_cons_iff in Guard; destruct Guard as [Guard _].
  cbn [consumed] in Guard.
  apply Forall_cons_iff in Guard; destruct Guard as [Guard _].
  exact (Guard eq_refl).
Qed.

(* A receive label records the actual head removed by StepRecv, including
   under Bind and App evaluation contexts. *)
Lemma target_receive_head {M E S} (m : local_model M E role S)
    R p X t q st a u q' st' :
  step m R p X t q st a u q' st' ->
  match a with
  | Received sender receiver sid w =>
      exists ws, q (sender, receiver, sid) = w :: ws
  | _ => True
  end.
Proof. induction 1; cbn; eauto. Qed.

Theorem reject_invented_bytes : wire_reject_invented_bytes.
Proof.
  intros s n [gs Match].
  pose proof (prefix_network_run wire_model wire_stores tt wire_roles
    (fun _ => bool) wire_choice _ _ _ _ _ Match) as Run.
  inversion Run as [|n0 a n1 tr n3 First Rest]; subst.
  inversion Rest as [|n1' a' n2 tr' n3' Second Rest']; subst.
  inversion Rest' as [|n2' a'' n3'' tr'' n4 Third Rest'']; subst.
  assert (Prefix : run (shared_model wire_model) wire_roles
    (DeadlockMatch.network_initial wire_stores tt wire_roles
      (fun _ => bool) wire_choice)
    [Announced wire_A Choreography.Network.Root (GHC.Base.hs_string__ "True");
     Sent wire_A wire_C Choreography.Network.Root (GHC.Base.hs_string__ "False")] n2).
  { econstructor; [exact First|]. econstructor; [exact Second|constructor]. }
  pose proof (observed_run_wires _ _ _ _ _ Prefix) as Queues.
  inversion Third as [pre post X p t t' q st a q' st' Step]; subst.
  destruct (target_receive_head _ _ _ _ _ _ _ _ _ _ _ Step) as [ws Head].
  cbn [mailboxes] in Queues.
  rewrite Queues in Head.
  discriminate Head.
Qed.

(* Hidden payload types permit transport along a hypothetical type loop.
   Consequently the value rejection cannot be proved from plain queue
   membership without assuming an additional type-equality principle. *)
Lemma hear_transport {E S} (X Y : Set) (e : X = Y) o p r (x : X) :
  @HearAction E S X o p r x =
  @HearAction E S Y o p r (eq_rect X (fun T => T) x Y e).
Proof. destruct e. reflexivity. Qed.

Theorem invented_value_transport_obstruction :
  forall e : bool = bool,
    eq_rect bool (fun T => T) true bool e = false ->
    wire_partial_delivery -> ~ wire_reject_invented_value.
Proof.
  intros e Flip [s [n [_ [_ [Match _]]]]] Reject.
  pose proof (@hear_transport wire_event ((Parkour.Symbol.Symbol -> unit) * unit)
    bool bool e [] wire_A wire_B true) as Equal.
  rewrite Flip in Equal.
  unfold wire_reject_invented_value in Reject.
  apply (Reject s n).
  rewrite <- Equal. exact Match.
Qed.

Print Assumptions reject_wrong_occurrence.
Print Assumptions invented_value_transport_obstruction.
Print Assumptions reject_invented_bytes.
