From Stdlib Require Import Lists.List.
Require Import DeadlockSource DeadlockCoherence DeadlockReplay DeadlockHead
  DeadlockNetwork DeadlockMessages DeadlockOrder DeadlockAlignment
  DeadlockAlignmentProgress DeadlockMatchStep DeadlockWellFormed
  Parkour.Symbol Parkour.Codec Control.Monad.Tree.
Require Choreography.Choreo2 Choreography.Network DeadlockReadyInputs.
Import ListNotations.
Local Arguments ContextHole {M E p X}.
Local Arguments ContextSeq {M E p X Y Z} _ _ _.
Local Arguments ContextLeft {M E p X Y Z} _ _.
Local Arguments ContextRight {M E p X Y Z} _ _.
Local Arguments erased_cursor {M E Store model configured p A} _.
Local Arguments archive {M E Store model configured p A} _.
Local Arguments positions {M E Store A} _ _.
Local Notation Choreo := Choreography.Choreo2.Choreo.
Local Notation At := Choreography.Choreo2.At.
Local Notation Comm := Choreography.Choreo2.Comm.
Local Notation Cond := Choreography.Choreo2.Cond.

(* Source sites include the finite bookkeeping that an alignment witness
   may hide. They do not mention an endpoint, a wire head, or readiness. *)
Section Sites.
Context {M E : Type -> Type} {Store : Type}.
Variable model : DeadlockLocal.local_model M E Symbol Store.

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
    X kind o sender (rd : Read X) : Prop :=
  exists B (C : @cursor_context M E p B A) focus,
    silent_prefix model c (plug C focus) /\
    receive_focus p B focus X kind o sender rd.

Lemma silent_prefix_trans p A (t u v : @cursor M E p A) :
  silent_prefix model t u -> silent_prefix model u v ->
  silent_prefix model t v.
Proof.
  intros First. induction First; intro Last; [exact Last |].
  eapply PrefixCons; [exact H|now apply IHFirst].
Qed.

Lemma receive_site_now p A c X kind o sender rd :
  receive_focus p A c X kind o sender rd ->
  receive_site p A c X kind o sender rd.
Proof.
  intro Focus. exists A, (@ContextHole M E p A), c.
  split; [constructor |exact Focus].
Qed.

Lemma receive_site_silent p A c u X kind o sender rd :
  silent model A c u ->
  receive_site p A u X kind o sender rd ->
  receive_site p A c X kind o sender rd.
Proof.
  intros Step (B & C & focus & Prefix & Focus).
  exists B, C, focus. split; [eapply PrefixCons; eassumption |exact Focus].
Qed.

Lemma receive_site_prefix p A c u X kind o sender rd :
  silent_prefix model c u ->
  receive_site p A u X kind o sender rd ->
  receive_site p A c X kind o sender rd.
Proof.
  intros Prefix (B & C & focus & More & Focus).
  exists B, C, focus. split; [eapply silent_prefix_trans; eassumption |exact Focus].
Qed.

Lemma receive_site_plug p A B (C : @cursor_context M E p A B)
    c X kind o sender rd :
  receive_site p A c X kind o sender rd ->
  receive_site p B (plug C c) X kind o sender rd.
Proof.
  intros (D & Inner & focus & Prefix & Focus).
  exists D, (compose_context C Inner), focus. split; [|exact Focus].
  rewrite plug_compose. apply silent_prefix_plug. exact Prefix.
Qed.

Lemma returns_silent_prefix p A (t : @cursor M E p A) x :
  DeadlockSource.returns model t x ->
  silent_prefix model t (Returned x).
Proof.
  induction 1; [constructor |eapply PrefixCons; eassumption].
Qed.

(* An actual returned prefix, including owner-local silent return, exposes
   its actual k x. No result for another role is requested. *)
Lemma receive_site_bind_body p A B root (t : @cursor M E p A)
    (k : A -> Choreo M p B) x X kind o sender rd :
  DeadlockSource.returns model t x ->
  receive_site p B (Code (child root BindBody) (k x)) X kind o sender rd ->
  receive_site p B (Seq root t k) X kind o sender rd.
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
Theorem replay_receive_site configured p A start tr
    (cut : @annotated_cut M E Store model configured p A)
    X kind o sender rd :
  cut_history model configured p start tr cut ->
  receive_site p A (erased_cursor cut) X kind o sender rd ->
  exists next B (C : @cursor_context M E p B A) focus,
    cut_history model configured p start tr next /\
    erased_cursor next = plug C focus /\
    extends model configured p (archive next) (archive cut) /\
    receive_focus p B focus X kind o sender rd.
Proof.
  intros History (B & C & focus & Prefix & Focus).
  destruct (cut_after_silent_prefix model configured p A start tr cut
    (plug C focus) History Prefix) as (next & Hist & Erase & More).
  exists next, B, C, focus. auto.
Qed.
End Sites.

(* These are the remaining SOURCE-ONLY premises. Head paths concern transport
   order; original operands concern the shared source node and its codec.
   Neither premise contains receive_safety, delivery_available, or a future
   simulation/progress claim. No theorem deriving them for all WF cuts is
   asserted in this module. *)
Section SourceCoverage.
Context {M E : Type -> Type} {Store : Type}.
Variable model : DeadlockLocal.local_model M E Symbol Store.

Definition source_head_paths p A (c : @cursor M E p A) gs : Prop :=
  forall X kind o sender (rd : Read X),
    receive_site model p A c X kind o sender rd ->
    forall g,
      first_for (sender,p,session_at o Choreography.Network.Root) gs g ->
      message_path g = o.

Definition source_originals p A (c : @cursor M E p A) gs : Prop :=
  forall X kind o sender (rd : Read X),
    receive_site model p A c X kind o sender rd ->
    (exists g, first_for (sender,p,session_at o Choreography.Network.Root) gs g) ->
    exists (value : X) (sh : Show X),
      (forall g, In g gs ->
        message_key g = (sender,p,session_at o Choreography.Network.Root) ->
        message_path g = o ->
        g = Message X kind o sender p value sh) /\
      wire_law sh rd.

Lemma covered_site_receive_at p A c gs q X kind o sender rd :
  source_head_paths p A c gs ->
  source_originals p A c gs ->
  (forall k, q k = at_key k gs) ->
  receive_site model p A c X kind o sender rd ->
  receive_at X kind o sender p rd q gs.
Proof.
  intros Paths Original Rep Site w ws x Bytes Read.
  pose proof Bytes as AtKey. rewrite Rep in AtKey.
  destruct (nonempty_channel_first _ _ _ _ AtKey) as [g [First _]].
  destruct (Original _ _ _ _ _ Site (ex_intro _ g First)) as (value & sh & Origin & Wire).
  exact (exact_receive_at kind o sender p value sh rd q gs
    (Paths _ _ _ _ _ Site) Origin Wire Rep w ws x Bytes Read).
Qed.

Lemma covered_site_delivery_at p A c gs q sq X kind o sender rd :
  source_head_paths p A c gs ->
  source_originals p A c gs ->
  represents sq q gs ->
  receive_site model p A c X kind o sender rd ->
  delivery_available_at X kind o sender p rd
    (session_at o Choreography.Network.Root) q sq.
Proof.
  intros Paths Original [Pending Rep] Site x sq' Removal.
  pose proof (removal_has_key _ _ _ _ _ _ _ _ Removal) as Key.
  rewrite <- Pending in Key. destruct (queued_key_nonempty _ _ Key) as [w [ws Bytes]].
  destruct (nonempty_channel_first _ _ _ _ Bytes) as [g [First _]].
  destruct (Original _ _ _ _ _ Site (ex_intro _ g First)) as (value & sh & Origin & Wire).
  exact (source_removal_exposes_wire kind o sender p value sh rd q gs
    (Paths _ _ _ _ _ Site) Origin Wire Rep sq sq' x Pending Removal).
Qed.

(* The source-site lift follows the entire real alignment, not just currently
   visible Code cursors. AlignSeq's continuation is included precisely for
   values returned by its ACTUAL prefix. *)
Theorem aligned_cut_receive_safety p A c n
    (Ha : aligned model Choreography.Network.Root p A c n) q gs :
  source_head_paths p A c gs ->
  source_originals p A c gs ->
  (forall k, q k = at_key k gs) ->
  receive_safety model p A c n Ha q gs.
Proof.
  intros Paths Original Rep.
  assert (Safe : forall X kind o sender rd,
    receive_site model p A c X kind o sender rd ->
    receive_at X kind o sender p rd q gs).
  { intros. eapply covered_site_receive_at; eassumption. }
  clear Paths Original Rep.
  induction Ha; cbn [receive_safety]; try exact I.
  - apply IHHa. intros. apply Safe.
    eapply receive_site_silent; eassumption.
  - split.
    + apply IHHa. intros. apply Safe.
      exact (receive_site_plug model p X Y
        (ContextSeq o k ContextHole) _ _ _ _ _ _ H0).
    + intros x Returned. apply H. intros. apply Safe.
      eapply receive_site_bind_body; eassumption.
  - split.
    + apply IHHa1. intros. apply Safe.
      eapply receive_site_plug with (C := ContextLeft t ContextHole).
      eassumption.
    + apply IHHa2. intros. apply Safe.
      eapply receive_site_plug with (C := ContextRight f ContextHole).
      eassumption.
  - apply IHHa. exact Safe.
  - apply Safe. apply receive_site_now. apply FocusData. exact neq.
  - apply Safe. apply receive_site_now. apply FocusChoice. exact neq.
Qed.

Theorem aligned_cut_delivery_available p A c n
    (Ha : aligned model Choreography.Network.Root p A c n) q sq gs :
  source_head_paths p A c gs ->
  source_originals p A c gs ->
  represents sq q gs ->
  delivery_available model Choreography.Network.Root p A c n Ha q sq.
Proof.
  intros Paths Original Rep.
  assert (Available : forall X kind o sender rd,
    receive_site model p A c X kind o sender rd ->
    delivery_available_at X kind o sender p rd
      (session_at o Choreography.Network.Root) q sq).
  { intros. eapply covered_site_delivery_at; eassumption. }
  clear Paths Original Rep.
  induction Ha; cbn [delivery_available]; try exact I.
  - apply IHHa. intros. apply Available.
    eapply receive_site_silent; eassumption.
  - split.
    + apply IHHa. intros. apply Available.
      exact (receive_site_plug model p X Y
        (ContextSeq o k ContextHole) _ _ _ _ _ _ H0).
    + intros x Returned. apply H. intros. apply Available.
      eapply receive_site_bind_body; eassumption.
  - split.
    + apply IHHa1. intros. apply Available.
      eapply receive_site_plug with (C := ContextLeft t ContextHole).
      eassumption.
    + apply IHHa2. intros. apply Available.
      eapply receive_site_plug with (C := ContextRight f ContextHole).
      eassumption.
  - apply IHHa. exact Available.
  - apply Available. apply receive_site_now. apply FocusData. exact neq.
  - apply Available. apply receive_site_now. apply FocusChoice. exact neq.
Qed.
End SourceCoverage.

Section MatchedCuts.
Context {M E : Type -> Type} {Store Input : Type}.
Variable model : DeadlockLocal.local_model M E role (Store * Input).
Variable R : list role.
Variable A : role -> Type.
Local Notation sm := (DeadlockState.shared_model model).

Theorem covered_residuals s n gs :
  DeadlockMatch.state_match model R A s n gs ->
  (forall p, In p R ->
    source_head_paths sm p (A p) (positions s p) gs /\
    source_originals sm p (A p) (positions s p) gs) ->
  safe_residuals model R A s n gs /\
  DeadlockReadyInputs.inputs_available model R A s n.
Proof.
  intros [_ [Rep [f [Es Align]]]] Cover. split.
  - exists f. split; [exact Es|]. intros p Hin.
    destruct (Align p Hin) as [Ha]. exists Ha.
    destruct (Cover p Hin). eapply aligned_cut_receive_safety; try eassumption.
    exact (proj2 Rep).
  - intros p Hin. destruct (Align p Hin) as [Ha]. exists (f p), Ha. split.
    + refine (eq_ind_r (fun es => In (Endpoint (A p) p (f p)) es) _ Es).
      clear -Hin. induction R as [|r rest IH]; cbn in *; [contradiction|].
      destruct Hin as [->|Hin]; [now left|right; auto].
    + destruct (Cover p Hin). eapply aligned_cut_delivery_available; eassumption.
Qed.
End MatchedCuts.
