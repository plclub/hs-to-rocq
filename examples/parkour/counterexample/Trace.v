From Stdlib Require Import Lists.List.
From Counterexample Require Import Family Source Network Projection.
Require Import Choreography.Network Control.Monad.Tree Parkour.Codec.
Import ListNotations.

(* Classify just the derivations used by this schedule. The index is the
   operational proof itself; context steps inherit their premise's label. *)
Inductive classified (self : loc) : forall a (t : net Id a) q u r,
    ns self t q u r -> option event -> Prop :=
| unit_send q :
    classified self _ _ _ _ _
      (S_send Id roles local_effect self unit show_unit Root tt B q)
      (Some (Source.send tt))
| bool_broadcast q :
    classified self _ _ _ _ _
      (S_bcast Id roles local_effect self bool show_bool Root true q)
      (Some (announce true))
| bind_done a b v k q :
    classified self _ _ _ _ _
      (S_bind_done Id roles local_effect self a b v k q) None
| app_done a b f x q :
    classified self _ _ _ _ _
      (S_app_done Id roles local_effect self a b f x q) None
| under_bind a b t u k q r h e :
    classified self a t q u r h e ->
    classified self _ _ _ _ _
      (S_bind Id roles local_effect self a b t u k q r h) e
| under_left a b f g x q r h e :
    classified self _ f q g r h e ->
    classified self _ _ _ _ _
      (S_app_left Id roles local_effect self a b f g x q r h) e
| under_right a b f x y q r h e :
    classified self _ x q y r h e ->
    classified self _ _ _ _ _
      (S_app_right Id roles local_effect self a b f x y q r h) e.

Lemma quiet_preserves_queues self a t q u r h e :
  classified self a t q u r h e -> e = None -> q = r.
Proof. induction 1; intros Hnone; try discriminate; auto. Qed.

Inductive microstep : option event -> configuration -> configuration -> Prop :=
| micro_A x y q u r h e : classified A _ x q u r h e ->
    microstep e (Build_configuration x y q) (Build_configuration u y r)
| micro_B x y q u r h e : classified B _ y q u r h e ->
    microstep e (Build_configuration x y q) (Build_configuration x u r).

Lemma microstep_sound e c d : microstep e c d -> nstep c d.
Proof. destruct 1; [apply step_A | apply step_B]; assumption. Qed.

Lemma enqueue_changes q k w : q k <> enqueue q k w k.
Proof.
  unfold enqueue; rewrite put_same.
  induction (q k) as [|x xs IH]; cbn; intro H; [discriminate|].
  apply IH. exact (f_equal (@tl wire) H).
Qed.

Lemma classified_action_changes self a t q u r h e :
  classified self a t q u r h e -> (self = A \/ self = B) ->
  forall action, e = Some action -> exists k, q k <> r k.
Proof.
  induction 1; intros role action Hlabel; try discriminate.
  - eexists; apply enqueue_changes.
  - destruct role as [-> | ->].
    + exists (A,B,Root). apply enqueue_changes.
    + exists (B,A,Root). apply enqueue_changes.
  - eauto.
  - eauto.
  - eauto.
Qed.

Theorem microstep_queue_effect e c d : microstep e c d ->
  match e with
  | None => buffers c = buffers d
  | Some _ => exists k, buffers c k <> buffers d k
  end.
Proof.
  destruct 1; destruct e; simpl;
    [eapply classified_action_changes | eapply quiet_preserves_queues |
     eapply classified_action_changes | eapply quiet_preserves_queues]; eauto.
Qed.

Inductive schedule : list (option event) -> configuration -> configuration -> Prop :=
| stop c : schedule [] c c
| next e es c d f : microstep e c d -> schedule es d f ->
    schedule (e :: es) c f.

Definition bad_schedule :=
  [None; Some (Source.send tt); None; None; None; Some (announce true); None; None; None].

Theorem projected_schedule : schedule bad_schedule Projection.initial bad.
Proof.
  unfold bad_schedule, Projection.initial, bad.
  rewrite sender_actual, receiver_actual. unfold sender_shape, receiver_shape.
  eapply next; [eapply micro_A; apply under_right, bind_done |].
  eapply next; [eapply micro_A; apply under_right, under_left, under_bind, unit_send |].
  eapply next; [eapply micro_A; apply under_right, under_left, bind_done |].
  eapply next; [eapply micro_A; apply under_right, app_done |].
  eapply next; [eapply micro_A; apply under_left, under_bind, bind_done |].
  eapply next; [eapply micro_A; apply under_left, under_bind, bool_broadcast |].
  eapply next; [eapply micro_A; apply under_left, bind_done |].
  eapply next; [eapply micro_A; apply app_done |].
  eapply next; [eapply micro_B; apply under_bind, bind_done |].
  apply stop.
Qed.

Definition actions := flat_map (fun x : option event =>
  match x with Some e => [e] | None => [] end).

Theorem projected_action_history :
  schedule bad_schedule Projection.initial bad /\
  actions bad_schedule = [Source.send tt; announce true] /\
  empty_queues key <> queue1 key /\ queue1 key <> queue2 key.
Proof.
  split; [apply projected_schedule|]. repeat split; discriminate.
Qed.

Theorem final_queues_empty :
  (forall s, Source.final s -> pending_choice s = None /\ pending_data s = None) /\
  (forall c, network_final c -> forall k, buffers c k = []).
Proof.
  split; [intros s (x & y & ->); split; reflexivity | intros c [_ [_ H]]; exact H].
Qed.
