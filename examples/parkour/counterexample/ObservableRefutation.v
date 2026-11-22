From Stdlib Require Import Lists.List Relations.Relation_Operators.
From Counterexample Require Import Family Network.
From Counterexample Require Source Projection Trace.
Import ListNotations.

Section Observations.
Variable L : Type.
Variable transition :
  Projection.configuration -> option L -> Projection.configuration -> Prop.

(* This is only finite closure, not another operative step relation.
   None denotes silence; Some denotes a genuine observation. Finality
   requires both Pure endpoints and empty FIFOs on every channel. *)
Definition silent_prefix :=
  clos_refl_trans_1n Projection.configuration (fun c d => transition c None d).
Definition observable_ready c :=
  exists d, silent_prefix c d /\
    (Projection.network_final d \/ exists label e, transition d (Some label) e).

Hypothesis erases :
  forall c label d, transition c label d -> Projection.nstep c d.

Lemma bad_silent_prefix d :
  silent_prefix Projection.bad d -> d = Projection.bad.
Proof.
  intro H; inversion H; subst; [reflexivity |].
  exfalso; eapply Projection.no_network_step.
  eapply erases; eassumption.
Qed.

Theorem bad_observably_stuck : ~ observable_ready Projection.bad.
Proof.
  intros [d [Hsilent Hready]].
  apply bad_silent_prefix in Hsilent; subst d.
  destruct Hready as [Hfinal | [label [e Hstep]]].
  - exact (Projection.bad_not_final Hfinal).
  - apply (Projection.no_network_step e).
    eapply erases; exact Hstep.
Qed.
End Observations.

Theorem no_stuck_source_witness :
  ~ (exists t s, Source.run t s /\ ~ Source.ready s).
Proof.
  intros [t [s [Hrun Hstuck]]].
  exact (Hstuck (Source.source_deadlock_free t s Hrun)).
Qed.

(* Universal labelling quantification is a stronger consequence of the
   all-microstep dead end, not a progress or simulation assumption on the
   choreography. It covers any full labelling whose steps erase to nstep;
   the incomplete classification in Trace is used only for its exact
   witness schedule, never as a definition of network deadlock freedom. *)
Theorem observable_two_role_counterexample :
  (NoDup roles /\ Source.well_formed roles B program) /\
  (forall t s, Source.run t s -> Source.ready s) /\
  Trace.schedule Trace.bad_schedule Projection.initial Projection.bad /\
  Projection.nrun Projection.initial Projection.bad /\
  (forall c, ~ Projection.nstep Projection.bad c) /\
  ~ Projection.network_final Projection.bad /\
  Projection.buffers Projection.bad Projection.key =
    [Projection.unit_wire; Projection.bool_wire] /\
  (forall (L : Type)
    (transition : Projection.configuration -> option L ->
      Projection.configuration -> Prop),
    (forall c label d, transition c label d -> Projection.nstep c d) ->
    ~ observable_ready L transition Projection.bad).
Proof.
  split; [exact Source.program_well_formed |].
  split; [exact Source.source_deadlock_free |].
  split; [exact Trace.projected_schedule |].
  split; [exact Projection.actual_projected_bad_run |].
  split; [exact Projection.no_network_step |].
  split; [exact Projection.bad_not_final |].
  split; [exact Projection.queue_order |].
  exact bad_observably_stuck.
Qed.
