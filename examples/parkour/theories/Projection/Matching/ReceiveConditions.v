From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Choreography.RoleSteps
  Choreography.Execution Choreography.Histories.CursorHistories
  Choreography.ReceiveSites Projection.FIFO.HeadDecoding Network.Mailboxes
  Network.Endpoints Projection.FIFO.MessageRepresentation
  Projection.SessionPaths Projection.Matching.CursorAlignment
  Projection.Matching.RoleReadiness Projection.Matching.ActionReflection
  Choreography.WellFormedness.
Require Import Parkour.Symbol Parkour.Codec.
Require Choreography.Network.
From ParkourTheories.Projection.Matching Require DeliveryAvailability.
Import ListNotations.
Local Arguments ContextHole {M E p X}.
Local Arguments ContextSeq {M E p X Y Z} _ _ _.
Local Arguments ContextLeft {M E p X Y Z} _ _.
Local Arguments ContextRight {M E p X Y Z} _ _.
Local Arguments positions {M E Store A} _ _.

(* These premises relate source sites to the message history. Head paths concern
  transport
   order; original operands concern the shared source node and its codec.
   Neither premise contains receive_safety, delivery_available, or a future
   simulation/progress claim. No theorem deriving them for all WF cuts is
   asserted in this module. *)
Section SourceCoverage.
Context {M E : Type -> Type} {Store : Type}.
Variable model : LocalEffects.local_model M E Symbol Store.

Definition source_head_paths p A (c : @cursor M E p A) gs : Prop :=
  forall X kind o sender (rd : Read X),
    receive_site model p A c X kind o sender rd ->
    forall g,
      first_message_at_key (sender,p,session_at o Choreography.Network.Root) gs
        g ->
      message_path g = o.

Definition source_originals p A (c : @cursor M E p A) gs : Prop :=
  forall X kind o sender (rd : Read X),
    receive_site model p A c X kind o sender rd ->
    (exists g, first_message_at_key (sender,p,session_at o
      Choreography.Network.Root) gs g)
      ->
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
  destruct (Original _ _ _ _ _ Site (ex_intro _ g First)) as (value & sh &
    Origin & Wire).
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
  rewrite <- Pending in Key.
  destruct (queued_key_nonempty _ _ Key) as [w [ws Bytes]].
  destruct (nonempty_channel_first _ _ _ _ Bytes) as [g [First _]].
  destruct (Original _ _ _ _ _ Site (ex_intro _ g First)) as (value & sh &
    Origin & Wire).
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
Variable model : LocalEffects.local_model M E role (Store * Input).
Variable R : list role.
Variable A : role -> Type.
Local Notation sm := (SharedState.shared_model model).

Theorem covered_residuals s n gs :
  PrefixRelation.state_match model R A s n gs ->
  (forall p, In p R ->
    source_head_paths sm p (A p) (positions s p) gs /\
    source_originals sm p (A p) (positions s p) gs) ->
  safe_residuals model R A s n gs /\
  DeliveryAvailability.inputs_available model R A s n.
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
    + destruct (Cover p Hin).
    eapply aligned_cut_delivery_available; eassumption.
Qed.
End MatchedCuts.
