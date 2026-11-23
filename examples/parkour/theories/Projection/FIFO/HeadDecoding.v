From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Choreography.Occurrences
  Choreography.PendingDeliveries Network.Mailboxes
  Projection.FIFO.MessageRepresentation Projection.SessionPaths
  Projection.Matching.ActionReflection Choreography.WellFormedness.
Require Import Parkour.Codec.
Import ListNotations.

(* Keep the transport order and the syntax of the original sender separate.
   Neither inspecting a Pending package nor inverting a universe equality is
   a valid way to recover the value at a particular receiver type. *)
Definition first_message_at_key k gs m :=
  exists pre post, gs = pre ++ m :: post /\
    Forall (fun g => message_key g <> k) pre /\ message_key m = k.

Lemma nonempty_channel_first k gs w ws :
  at_key k gs = w :: ws ->
  exists m, first_message_at_key k gs m /\ w = message_wire m.
Proof.
  induction gs as [|g gs IH]; cbn; [discriminate|].
  destruct (key_eq_dec (message_key g) k) as [Eq|Ne].
  - intros H. injection H as Ew Et. exists g. split; [|symmetry; exact Ew].
    exists [], gs. auto using Forall_nil.
  - intro H. destruct (IH H) as [m [[pre [post [-> [F K]]]] W]].
    exists m. split; [|exact W].
    exists (g :: pre), post. cbn. auto using Forall_cons.
Qed.

Definition pending_key (m : pending) : key :=
  match m with Pending _ _ o s d _ => (s,d,session_at o
    Choreography.Network.Root) end.

Lemma removal_has_key X kind o s d (x : X) ps ps' :
  take_at_occurrence kind o s d x ps ps' ->
  In (s,d,session_at o Choreography.Network.Root) (map pending_key ps).
Proof. induction 1; cbn; [now left|now right]. Qed.

Lemma queued_key_nonempty k gs :
  In k (map pending_key (map pending_of gs)) ->
  exists w ws, at_key k gs = w :: ws.
Proof.
  induction gs as [|g gs IH]; [contradiction|].
  destruct (key_eq_dec (message_key g) k) as [<-|Ne].
  - rewrite at_key_same. intros _. do 2 eexists; reflexivity.
  - rewrite at_key_other by exact Ne. intros [Eq|I]; [|now apply IH].
    destruct g. contradiction.
Qed.

Section Receive.
Context {X : Type} (kind : delivery_kind) (o : occurrence) (s d : role)
  (v : X) (sh : Show X) (rd : Read X) (q : queues) (gs : list message).
Let k := (s,d,session_at o Choreography.Network.Root).

(* The first hypothesis compares positions only. The second identifies the
   past producer's whole package at that position, including its own Show. *)
Hypothesis HeadPath : forall g, first_message_at_key k gs g -> message_path g =
  o.
Hypothesis Origin : forall g, In g gs -> message_key g = k -> message_path g = o
  ->
  g = Message X kind o s d v sh.
Hypothesis Wire : wire_law sh rd.
Hypothesis Rep : forall i, q i = at_key i gs.

Lemma head_bytes w ws :
  q k = w :: ws -> w = @show X sh v /\
  exists pre post, gs = pre ++ Message X kind o s d v sh :: post /\
    Forall (fun g => message_key g <> k) pre.
Proof.
  rewrite Rep. intro Q. destruct (nonempty_channel_first k gs w ws Q)
    as [g [First Bytes]]. pose proof (HeadPath g First) as Path.
  destruct First as [pre [post [List [Earlier Key]]]].
  assert (Member : In g gs) by (rewrite List; apply in_or_app; right; now left).
  specialize (Origin g Member Key Path) as E. subst g.
  split; [exact Bytes|eauto].
Qed.

Lemma exact_receive_at :
  receive_at X kind o s d rd q gs.
Proof.
  intros w ws x Head Decode.
  destruct (head_bytes w ws Head) as [-> [pre [post [G F]]]].
  unfold wire_law in Wire. rewrite Wire in Decode. injection Decode as <-.
  exists sh, pre, post. auto.
Qed.

Lemma source_removal_exposes_wire ps ps' (x : X) :
  map pending_of gs = ps -> take_at_occurrence kind o s d x ps ps' ->
  exists w ws (y : X), q k = w :: ws /\ @read X rd w = Some y.
Proof.
  intros <- H. apply removal_has_key in H.
  destruct (queued_key_nonempty k gs H) as [w [ws Bytes]].
  rewrite <- Rep in Bytes. destruct (head_bytes w ws Bytes) as [-> _].
  exists (@show X sh v), ws, v. auto.
Qed.
End Receive.
