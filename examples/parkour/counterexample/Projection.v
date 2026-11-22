From Stdlib Require Import Lists.List.
From Counterexample Require Import Family Network.
Require Import Choreography.Choreo2 Control.Monad.Trans.Reader Parkour.Symbol.
Require Import Parkour.Codec Control.Monad.Tree.
Import ListNotations.

Definition endpoint (p : Symbol) :=
  runReaderT (unEpp (epp (program p) (@MkSSymbol p)))
    Choreography.Network.Root.

Definition sender_shape (v : At unit B A) : Network.Network Id (At unit B A) :=
  Tree.App
    (Tree.Bind
      (Tree.Bind (Tree.Pure Network.Root)
        (fun sid => Tree.Perf (Network.BCast sid true)))
      (fun _ => Tree.Pure (fun x : At unit B A => x)))
    (Tree.Bind (Tree.Pure Network.Root)
      (fun sid => Tree.App
        (Tree.Bind (Tree.Perf (Network.Send sid tt B))
          (fun _ => Tree.Pure (fun x : At unit B A => x)))
        (Tree.Pure v))).

Definition sender_normalization :
  {v : At unit B A | endpoint A = sender_shape v}.
Proof. eexists; reflexivity. Defined.
Definition sender_value := proj1_sig sender_normalization.
Lemma sender_actual : endpoint A = sender_shape sender_value.
Proof. exact (proj2_sig sender_normalization). Qed.

Definition receiver_shape : Network.Network Id (At unit B B) :=
  Tree.Bind
    (Tree.Bind (Tree.Pure Network.Root)
      (fun sid => Tree.Perf (@Network.Recv Id bool _ sid A)))
    (fun _ : bool =>
      Tree.Bind (Tree.Pure Network.Root)
        (fun sid => Tree.Bind (Tree.Perf (@Network.Recv Id unit _ sid A))
          (fun x => Tree.Pure (@Mk_At unit B B (fun _ => x))))).
Lemma receiver_actual : endpoint B = receiver_shape.
Proof. reflexivity. Qed.

Definition empty_queues : channel -> list wire := fun _ => [].
Definition key : channel := (A, B, Network.Root).
Definition unit_wire := @show unit show_unit tt.
Definition bool_wire := @show bool show_bool true.
Definition queue1 := put empty_queues key [unit_wire].
Definition queue2 := put queue1 key [unit_wire; bool_wire].
Definition local_effect (X : Type) (x : Id X) (v : X) := v = x.
Definition ns := @step Id roles (@local_effect).
Definition nr := @run Id roles (@local_effect).
Arguments ns self {a}.
Arguments nr self {a}.

Lemma sender_bad_run :
  nr A (endpoint A) empty_queues (Tree.Pure sender_value) queue2.
Proof.
  rewrite sender_actual. unfold sender_shape.
  eapply run_cons. { apply S_app_right. apply S_bind_done. }
  eapply run_cons.
  { apply S_app_right. apply S_app_left. apply S_bind. apply S_send. }
   eapply run_cons.
   { apply S_app_right. apply S_app_left. apply S_bind_done. }
   eapply run_cons. { apply S_app_right. apply S_app_done. }
   eapply run_cons. { apply S_app_left. apply S_bind. apply S_bind_done. }
   eapply run_cons. { apply S_app_left. apply S_bind. apply S_bcast. }
   eapply run_cons. { apply S_app_left. apply S_bind_done. }
   eapply run_cons. { apply S_app_done. }
   apply run_refl.
Qed.

Definition receiver_stuck : Network.Network Id (At unit B B) :=
  Tree.Bind (Tree.Perf (@Network.Recv Id bool _ Network.Root A))
    (fun _ : bool =>
      Tree.Bind (Tree.Pure Network.Root)
        (fun sid => Tree.Bind (Tree.Perf (@Network.Recv Id unit _ sid A))
          (fun x => Tree.Pure (@Mk_At unit B B (fun _ => x))))).

Lemma receiver_bookkeeping q :
  ns B (endpoint B) q receiver_stuck q.
Proof. rewrite receiver_actual. apply S_bind. apply S_bind_done. Qed.

Lemma queue_order : queue2 key = [unit_wire; bool_wire].
Proof. apply put_same. Qed.

Lemma bool_cannot_read_unit : @read bool read_bool unit_wire = None.
Proof. reflexivity. Qed.

Lemma receiver_disabled : ~ enabled B receiver_stuck queue2.
Proof.
  unfold receiver_stuck; cbn [enabled is_pure].
  intros [(w & ws & v & Hq & Hd) | H]; [|exact H].
  change (queue2 key = w :: ws) in Hq.
  rewrite queue_order in Hq. inversion Hq; subst.
  rewrite bool_cannot_read_unit in Hd. discriminate.
Qed.

Lemma sender_disabled : ~ @enabled Id _ A (Tree.Pure sender_value) queue2.
Proof. exact (fun H => H). Qed.

Record configuration := {
  at_A : Network.Network Id (At unit B A);
  at_B : Network.Network Id (At unit B B);
  buffers : queues
}.
Inductive nstep : configuration -> configuration -> Prop :=
| step_A : forall x y q x' q',
    ns A x q x' q' ->
    nstep {| at_A := x; at_B := y; buffers := q |}
      {| at_A := x'; at_B := y; buffers := q' |}
| step_B : forall x y q y' q',
    ns B y q y' q' ->
    nstep {| at_A := x; at_B := y; buffers := q |}
      {| at_A := x; at_B := y'; buffers := q' |}.
Inductive nrun : configuration -> configuration -> Prop :=
| nrun_refl : forall c, nrun c c
| nrun_cons : forall c d e, nstep c d -> nrun d e -> nrun c e.
Definition initial :=
  {| at_A := endpoint A; at_B := endpoint B; buffers := empty_queues |}.
Definition bad :=
  {| at_A := Tree.Pure sender_value; at_B := receiver_stuck; buffers := queue2 |}.
Definition network_final c :=
  final (at_A c) /\ final (at_B c) /\ (forall key, buffers c key = []).

Lemma lift_sender_run x q x' q' :
  nr A x q x' q' ->
  forall y y' q'', ns B y q' y' q'' ->
  nrun {| at_A := x; at_B := y; buffers := q |}
       {| at_A := x'; at_B := y'; buffers := q'' |}.
Proof.
  intros H. induction H; intros.
  - eapply nrun_cons. apply step_B; eassumption. apply nrun_refl.
  - eapply nrun_cons. apply step_A; eassumption. apply IHrun; assumption.
Qed.

Theorem actual_projected_bad_run : nrun initial bad.
Proof.
  eapply lift_sender_run.
  - exact sender_bad_run.
  - apply receiver_bookkeeping.
Qed.

Theorem no_network_step : forall c, ~ nstep bad c.
Proof.
  intros c H. inversion H; subst.
  - apply sender_disabled. eapply step_enabled; eassumption.
  - apply receiver_disabled. eapply step_enabled; eassumption.
Qed.

Theorem bad_not_final : ~ network_final bad.
Proof.
  intros [_ [[v H] _]]. discriminate H.
Qed.

Theorem actual_projected_counterexample :
  nrun initial bad /\ (forall c, ~ nstep bad c) /\
    ~ network_final bad /\ buffers bad key = [unit_wire; bool_wire].
Proof.
  split; [apply actual_projected_bad_run|].
  split; [apply no_network_step|].
  split; [apply bad_not_final|apply queue_order].
Qed.
