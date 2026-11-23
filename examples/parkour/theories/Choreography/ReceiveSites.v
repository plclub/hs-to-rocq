From Stdlib Require Import Lists.List.
Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree.
Require Choreography.Choreo2.
From ParkourTheories.Choreography Require Import Occurrences PendingDeliveries
  RoleSteps Histories.CursorHistories Histories.TransitionArchive.
Import ListNotations.
Local Arguments ContextHole {M E p X}.
Local Arguments ContextSeq {M E p X Y Z} _ _ _.
Local Arguments ContextLeft {M E p X Y Z} _ _.
Local Arguments ContextRight {M E p X Y Z} _ _.
Local Arguments erased_cursor {M E Store model configured p A} _.
Local Arguments archive {M E Store model configured p A} _.
Local Notation Choreo := Choreography.Choreo2.Choreo.
Local Notation At := Choreography.Choreo2.At.
Local Notation Comm := Choreography.Choreo2.Comm.
Local Notation Cond := Choreography.Choreo2.Cond.

(* Source sites include the finite bookkeeping that an alignment witness
   may hide. They do not mention an endpoint, a wire head, or readiness. *)
Section Sites.
Context {M E : Type -> Type} {Store : Type}.
Variable model : LocalEffects.local_model M E Symbol Store.

Inductive receive_focus (p : Symbol) :
    forall A, @cursor M E p A ->
      forall X, delivery_kind -> occurrence -> Symbol -> Read X -> Prop :=
| FocusData X l o sh rd kl kd sl input sd (different : l <> p) :
    receive_focus p (At X p p)
      (Code o (Perf (@Comm M p X l p sh rd kl kd sl input sd)))
      X DataDelivery o l rd
| FocusChoice X A l o sh rd kl sl input (k : X -> Choreo M p A)
    (different : l <> p) :
    receive_focus p A
      (Code o (Perf (@Cond M p X l A sh rd kl sl input k)))
      X ChoiceDelivery o l rd.

Definition receive_site p A (c : @cursor M E p A)
    X kind path sender (decoder : Read X) : Prop :=
  exists B (C : @cursor_context M E p B A) focus,
    silent_prefix model c (plug C focus) /\
    receive_focus p B focus X kind path sender decoder.

Lemma silent_prefix_trans p A (t u v : @cursor M E p A) :
  silent_prefix model t u -> silent_prefix model u v ->
  silent_prefix model t v.
Proof.
  intros First. induction First; intro Last; [exact Last |].
  eapply PrefixCons; [exact H|now apply IHFirst].
Qed.

Lemma receive_site_now p A c X kind path sender decoder :
  receive_focus p A c X kind path sender decoder ->
  receive_site p A c X kind path sender decoder.
Proof.
  intro Focus. exists A, (@ContextHole M E p A), c.
  split; [constructor |exact Focus].
Qed.

Lemma receive_site_silent p A c u X kind path sender decoder :
  silent model A c u ->
  receive_site p A u X kind path sender decoder ->
  receive_site p A c X kind path sender decoder.
Proof.
  intros Step (B & C & focus & Prefix & Focus).
  exists B, C, focus. split; [eapply PrefixCons; eassumption |exact Focus].
Qed.

Lemma receive_site_prefix p A c u X kind path sender decoder :
  silent_prefix model c u ->
  receive_site p A u X kind path sender decoder ->
  receive_site p A c X kind path sender decoder.
Proof.
  intros Prefix (B & C & focus & More & Focus).
  exists B, C, focus. split; [eapply silent_prefix_trans; eassumption |exact
    Focus].
Qed.

Lemma receive_site_plug p A B (C : @cursor_context M E p A B)
    c X kind path sender decoder :
  receive_site p A c X kind path sender decoder ->
  receive_site p B (plug C c) X kind path sender decoder.
Proof.
  intros (D & Inner & focus & Prefix & Focus).
  exists D, (compose_context C Inner), focus. split; [|exact Focus].
  rewrite plug_compose. apply silent_prefix_plug. exact Prefix.
Qed.

Lemma returns_silent_prefix p A (t : @cursor M E p A) x :
  RoleSteps.returns model t x ->
  silent_prefix model t (Returned x).
Proof.
  induction 1; [constructor |eapply PrefixCons; eassumption].
Qed.

(* An actual returned prefix, including owner-local silent return, exposes
   its actual k x. No result for another role is requested. *)
Lemma receive_site_bind_body p A B root (t : @cursor M E p A)
    (k : A -> Choreo M p B) x X kind path sender decoder :
  RoleSteps.returns model t x ->
  receive_site p B (Code (child root BindBody) (k x)) X kind path sender decoder
    ->
  receive_site p B (Seq root t k) X kind path sender decoder.
Proof.
  intros Result Body.
  eapply receive_site_prefix.
  - apply (silent_prefix_plug model p A B
      (ContextSeq root k ContextHole) t (Returned x)).
    apply returns_silent_prefix. exact Result.
  - eapply receive_site_silent; [apply SSeq |exact Body].
Qed.

(* A source site is a genuine silently exposed focus in a persistent replay
   cut. In particular exposing a returned Bind prefix records PrimitiveBody
   in the extended archive, rather than looking up a nonexistent live Seq. *)
Theorem replay_receive_site roster p A start trace
    (cut : @annotated_cut M E Store model roster p A)
    X kind path sender decoder :
  cut_history model roster p start trace cut ->
  receive_site p A (erased_cursor cut) X kind path sender decoder ->
  exists next B (C : @cursor_context M E p B A) focus,
    cut_history model roster p start trace next /\
    erased_cursor next = plug C focus /\
    archive_extends model roster p (archive next) (archive cut) /\
    receive_focus p B focus X kind path sender decoder.
Proof.
  intros History (B & C & focus & Prefix & Focus).
  destruct (cut_after_silent_prefix model roster p A start trace cut
    (plug C focus) History Prefix) as (next & Hist & Erase & More).
  exists next, B, C, focus. auto.
Qed.
End Sites.
