From Stdlib Require Import Lists.List Strings.String.
From ParkourTheories Require Import Tests.FIFO.ScheduledTraceContracts
  Network.Mailboxes Network.Endpoints Network.Execution
  Projection.FIFO.MessageRepresentation Projection.Matching.PrefixRelation
  Semantics.SharedState.
Import ListNotations.

(* For a fixed observed network trace, only the queues are deterministic.
   This calculation does not assume that an endpoint or a local effect is. *)
Definition update_wires {E S} rs q (a : @action E S) : queues :=
  match a with
  | Local _ => q
  | Announced p sid w => announce rs p sid w q
  | Sent p r sid w => enqueue q (p,r,sid) w
  | Received p r sid _ => replace_queue q (p,r,sid) (tl (q (p,r,sid)))
  end.

Lemma observed_update {M E S} (m : LocalEffects.local_model M E role S)
    rs p X t q st a u q' st' :
  Endpoints.step m rs p X t q st a u q' st' -> q' = update_wires rs q a.
Proof.
  induction 1; cbn [update_wires]; try reflexivity; try assumption.
  apply f_equal. exact (eq_sym (f_equal (@tl wire) H)).
Qed.

Lemma observed_run_wires {M E S} (m : LocalEffects.local_model M E role S)
    rs t tr t' :
  Network.Execution.run m rs t tr t' -> mailboxes t' = fold_left (update_wires
    rs) tr (mailboxes
    t).
Proof.
  induction 1; [reflexivity|]. cbn [fold_left].
  rewrite IHrun. f_equal. destruct H. cbn. eapply observed_update. eassumption.
Qed.

Local Notation arrival := [
  Announced wire_A Choreography.Network.Root (GHC.Base.hs_string__ "True");
  Sent wire_A wire_C Choreography.Network.Root (GHC.Base.hs_string__ "False");
  Received wire_A wire_B Choreography.Network.Root (GHC.Base.hs_string__
    "True")].
Local Notation key_c := (wire_A,wire_C,Choreography.Network.Root).

Lemma peer_queue tc s n :
  PrefixRelation.matches wire_model wire_stores tt wire_roles (fun _ => bool)
    wire_choice tc s arrival n ->
  mailboxes n key_c = [GHC.Base.hs_string__ "True"; GHC.Base.hs_string__
    "False"].
Proof.
  intros [gs P].
  rewrite (observed_run_wires _ _ _ _ _
    (prefix_network_run wire_model wire_stores tt wire_roles _ wire_choice _ _ _
      _ _ P)).
  reflexivity.
Qed.

Theorem reject_swapped_fifo : wire_reject_swapped_fifo.
Proof.
  intros s n Swapped Match. rewrite (peer_queue _ _ _ Match) in Swapped.
    discriminate.
Qed.

Theorem reject_lost_pending : wire_reject_lost_pending.
Proof.
  intros s n Empty Match. pose proof (peer_queue _ _ _ Match) as Nonempty.
  destruct Match as [gs P].
  destruct (prefix_state wire_model wire_stores tt wire_roles _ wire_choice _ _
    _ _ _ P)
    as [_ [[Pending Queues] _]].
  rewrite Empty in Pending. destruct gs; [|discriminate].
  rewrite Queues in Nonempty. discriminate.
Qed.
