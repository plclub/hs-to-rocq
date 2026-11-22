From Stdlib Require Import Lists.List Strings.String.
From Counterexample Require Family Source Network Projection Local.
From ITree Require Import ITreeDefinition.
Import ListNotations.

(* Even counting every housekeeping step as enabled (a more permissive
   readiness test) cannot make this residual ready. *)
Definition network_ready n :=
  Projection.network_final n \/ exists n', Projection.nstep n n'.

Lemma identity_result X (x : Family.Id X) (v : X) :
  Projection.local_effect X x v <-> observe (Local.interpret x) = RetF v.
Proof.
  split; intro H.
  - unfold Projection.local_effect in H. subst. reflexivity.
  - cbn [Local.interpret] in H. injection H as H. symmetry; exact H.
Qed.

Lemma other_channels_empty k : k <> Projection.key ->
  Projection.buffers Projection.bad k = [].
Proof.
  intro H. change (Projection.queue2 k = []).
  unfold Projection.queue2, Projection.queue1.
  rewrite !Network.put_other by exact H. reflexivity.
Qed.

Theorem two_role_counterexample :
  (NoDup Family.roles /\ Source.well_formed Family.roles Family.B Family.program) /\
  (forall t s, Source.run t s -> Source.ready s) /\
  Projection.nrun Projection.initial Projection.bad /\
  ~ network_ready Projection.bad /\
  Projection.buffers Projection.bad Projection.key =
    [GHC.Base.hs_string__ "()"; GHC.Base.hs_string__ "True"].
Proof.
  split; [exact Source.program_well_formed|].
  split; [exact Source.source_deadlock_free|].
  split; [exact Projection.actual_projected_bad_run|].
  split; [|exact Projection.queue_order].
  intros [H | [n H]].
  - exact (Projection.bad_not_final H).
  - exact (Projection.no_network_step n H).
Qed.

Theorem preservation_fails :
  ~ ((forall t s, Source.run t s -> Source.ready s) ->
     forall n, Projection.nrun Projection.initial n -> network_ready n).
Proof.
  destruct two_role_counterexample as [_ [df [run [stuck _]]]].
  intro preserve. exact (stuck (preserve df _ run)).
Qed.

Theorem reflection_fails :
  ~ (forall n, Projection.nrun Projection.initial n -> ~ network_ready n ->
     exists t s, Source.run t s /\ ~ Source.ready s).
Proof.
  destruct two_role_counterexample as [_ [df [run [stuck _]]]].
  intro reflect. destruct (reflect _ run stuck) as [t [s [r h]]].
  exact (h (df t s r)).
Qed.
