From Stdlib Require Import Lists.List.
From Counterexample Require Import Source.
From Counterexample Require Trace Projection.
Import ListNotations.

(* A match preserving observable order cannot assign the network's first
   unit send to the continuation of a still-unannounced source choice. *)
Lemma source_first_action t s :
  run t s -> (t = [] /\ s = initial) \/ exists rest, t = announce true :: rest.
Proof.
  induction 1 as [|t s e s' prefix IH act].
  - left; auto.
  - right. destruct IH as [[-> ->] | [tail ->]].
    + inversion act; subst. exists []; reflexivity.
    + exists (tail ++ [e]); reflexivity.
Qed.

Theorem no_send_first tail s : ~ run (send tt :: tail) s.
Proof.
  intro H. destruct (source_first_action _ _ H) as [[bad _] | [? bad]];
    discriminate.
Qed.

Theorem generated_history_has_no_source :
  Trace.schedule Trace.bad_schedule Projection.initial Projection.bad /\
  ~ exists s, run (Trace.actions Trace.bad_schedule) s.
Proof.
  destruct Trace.projected_action_history as [sched [actions _]].
  split; [exact sched|]. rewrite actions.
  intros [s H]. exact (no_send_first _ _ H).
Qed.
