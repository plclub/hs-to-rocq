From Stdlib Require Import Lists.List.
Require Import Parkour.Symbol.
From ParkourTheories.Choreography Require Import Occurrences.
Import ListNotations.

(* Typed payloads, not serialized bytes. Data and announcements have separate
   channels; source paths distinguish successive uses of a channel. *)
Inductive delivery_kind := DataDelivery | ChoiceDelivery.
Inductive pending : Type :=
| Pending : forall X, delivery_kind -> occurrence -> Symbol -> Symbol -> X ->
  pending.

(* FIFO selection cannot skip an earlier entry on the same directed channel.
   Independent recipients/channels can receive in either order. *)
Definition same_channel (k : delivery_kind) (o : occurrence)
    (s d : Symbol) (v : pending) : Prop :=
  match v with Pending _ k' o' s' d' _ =>
    k = k' /\ source_lane o = source_lane o' /\ s = s' /\ d = d'
  end.
#[universes(template)]
Inductive take_first_on_source_channel {X} k o s d (x : X) :
    list pending -> list pending -> Prop :=
| TakeHead q : take_first_on_source_channel k o s d x (Pending X k o s d x :: q)
  q
| TakeOther v q q' :
    ~ same_channel k o s d v ->
    take_first_on_source_channel k o s d x q q' ->
    take_first_on_source_channel k o s d x (v :: q) (v :: q').

(* Source receives select their own occurrence, not a transport frontier.
   Role-local cursors impose source order. The stronger
     take_first_on_source_channel relation
   above remains available to reason separately about FIFO correspondence. *)
#[universes(template)]
Inductive take_at_occurrence {X} k o s d (x : X) :
    list pending -> list pending -> Prop :=
| TakeAtHead q : take_at_occurrence k o s d x (Pending X k o s d x :: q) q
| TakeAtOther v q q' :
    take_at_occurrence k o s d x q q' ->
    take_at_occurrence k o s d x (v :: q) (v :: q').

Lemma take_pending_at {X} k o s d (x : X) q q' :
  take_first_on_source_channel k o s d x q q' -> take_at_occurrence k o s d x q
    q'.
Proof.
  induction 1; [apply TakeAtHead | apply TakeAtOther; assumption].
Qed.

Lemma take_at_split {X} k o s d (x : X) q q' :
  take_at_occurrence k o s d x q q' ->
  exists front back,
    q = front ++ Pending X k o s d x :: back /\ q' = front ++ back.
Proof.
  induction 1 as [q | v q q' Htake [front [back [Hq Hq']]]].
  - exists [], q. split; reflexivity.
  - exists (v :: front), back. subst. split; reflexivity.
Qed.
