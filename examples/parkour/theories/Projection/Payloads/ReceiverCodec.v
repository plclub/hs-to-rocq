From Stdlib Require Import Lists.List Logic.Eqdep_dec.
From ParkourTheories Require Import Projection.Payloads.OwnedPackets
  Projection.RoleLogs.Families.RegionOwnership
  Projection.RoleLogs.Families.ChoicePartition
  Projection.RoleLogs.Families.BranchPartition
  Choreography.Results.CutFamilySoundness
  Choreography.Histories.SyntaxDecomposition Projection.Payloads.RootPackets
  Projection.RoleLogs.OccurrenceScope Projection.RoleLogs.ArchiveOrder
  Projection.Matching.ObservationArchive Choreography.ReceiveSites
  Projection.Matching.ReceiveConditions Choreography.Occurrences
  Choreography.PendingDeliveries Choreography.RoleSteps Choreography.Execution
  Network.Mailboxes Network.Endpoints Network.Execution
  Projection.FIFO.MessageRepresentation Projection.SessionPaths
  Semantics.LocalEffects Choreography.Histories.CursorHistories
  Choreography.Results.OperandObservations Choreography.Results.FiniteSelection
  Choreography.WellFormedness Projection.Matching.PayloadHistory
  Projection.Matching.PrefixRelation Semantics.SharedState.
Require Import Parkour.Symbol Parkour.Codec Choreography.Choreo2
  Control.Monad.Tree.
Import ListNotations.

(* This property talks only about exposed receivers. A Bind continuation
   contributes no receiver until its actual prefix has returned. *)
Section CursorContracts.
Context {M E : Type -> Type} {State : Type}
  (model : local_model M E Symbol State).
Variable G : Symbol -> occurrence -> forall X, delivery_kind -> Symbol -> Read X
  -> Prop.

Fixpoint cursor_readers p B (t : @cursor M E p B) : Prop :=
  match t with
  | Code o code => reader_contract code (G p o)
  | Seq _ prefix _ => cursor_readers p _ prefix
  | Fork f x => cursor_readers p _ f /\ cursor_readers p _ x
  | _ => True
  end.

Definition atomic_cursor p B (t : @cursor M E p B) : Prop :=
  match t with
  | Code _ (Pure _) => True
  | Code _ (Perf (Locally _ _)) => True
  | Code _ (Perf (Comm _ _ _)) => True
  | Returned _ | RoleSteps.Local _ _ => True
  | _ => False
  end.

Lemma atomic_silent p B t u :
  @silent M E State model p B t u ->
  atomic_cursor p B t /\ cursor_readers p B t ->
  atomic_cursor p B u /\ cursor_readers p B u.
Proof.
  destruct 1; cbn [atomic_cursor cursor_readers reader_contract]; tauto.
Qed.

Lemma atomic_role p R B t st q a u st' q' :
  @role_step M E State model R p B t st q a u st' q' ->
  atomic_cursor p B t /\ cursor_readers p B t ->
  atomic_cursor p B u /\ cursor_readers p B u.
Proof.
  induction 1; cbn [atomic_cursor cursor_readers reader_contract] in *;
    try tauto.
  intros Before. apply IHrole_step. eapply atomic_silent; eassumption.
Qed.

Lemma atomic_history p R B t actions u :
  @cursor_history M E State model R p B t actions u ->
  atomic_cursor p B t /\ cursor_readers p B t ->
  atomic_cursor p B u /\ cursor_readers p B u.
Proof.
  induction 1; intro Initial; [exact Initial| |].
  - eapply atomic_silent; [|exact (IHcursor_history Initial)].
    apply silent_plug. now apply primitive_is_silent.
  - eapply (atomic_role p R); [|exact (IHcursor_history Initial)].
    apply role_step_plug. apply primitive_is_role_step. exact H0.
Qed.

Lemma readers_focus p B D (C : @cursor_context M E p D B) t :
  cursor_readers p B (plug C t) -> cursor_readers p D t.
Proof.
  induction C; cbn [plug cursor_readers]; intros H;
    first [exact H|apply IHC; tauto].
Qed.

Lemma readers_receive p B t X kind o sender rd :
  receive_focus p B t X kind o sender rd ->
  cursor_readers p B t -> G p o X kind sender rd.
Proof.
  destruct 1; cbn [cursor_readers reader_contract]; auto.
Qed.
End CursorContracts.

Definition packet_codec (gs : list message) p o X kind sender (rd : Read X) :
  Prop :=
  (exists g, In g gs /\
    message_key g = (sender,p,session_at o Choreography.Network.Root) /\
    message_path g = o) ->
  exists (value : X) (writer : Show X),
    (forall g, In g gs ->
      message_key g = (sender,p,session_at o Choreography.Network.Root) ->
      message_path g = o -> g = Message X kind o sender p value writer) /\
    wire_law writer rd.

Section AllOrigins.
Context {M E Store Input} (model : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input : Input) (R : list Symbol)
  (A0 : Symbol -> Type) (c0 : forall p, Choreo M p (A0 p)).
Local Arguments cursor_at {M E Store Input model stores input R A c p B} _.
Variable tc : list (@source_action E ((Symbol -> Store) * Input)).
Variable s : @Choreography.Execution.configuration M E ((Symbol -> Store) *
  Input) A0.
Variable tn : list (@Endpoints.action E ((Symbol -> Store) * Input)).
Variable n : @Network.Execution.configuration M E ((Symbol -> Store) * Input).
Variable gs : list message.
Variable past : list payload_event.
Variable ar : actor_archive model stores input R A0 c0.
Hypothesis Archives :
  observed_archives model stores input R A0 c0 tc s tn n gs past ar.
Variable Laws : cut_family_laws (logged_cut model stores input R A0 c0)
  (at_node model stores input R A0 c0 past)
  (finished model stores input R A0 c0) past
  (owns_region model stores input R A0 c0 ar).

Lemma logged_atomic_readers p B o code
    (cut : logged_cut model stores input R A0 c0 p B) :
  @atomic_cursor M E p B (Code o code) ->
  at_node model stores input R A0 c0 past p B o code cut ->
  reader_contract code (packet_codec gs p o) ->
  cursor_readers (packet_codec gs) p B (cursor_at cut).
Proof.
  intros Atomic [Run _] Reader.
  destruct (actor_log_history model stores input R A0 c0 p B _ _ _ Run)
    as [actions Hist].
  exact (proj2 (atomic_history (shared_model model) (packet_codec gs)
    p R B _ actions _ Hist (conj Atomic Reader))).
Qed.

Theorem structural_logged_readers S A prog Q :
  structural R M S A prog Q ->
  forall active (inc : includes (fun p => In p active) S) o
    (cuts : family (logged_cut model stores input R A0 c0) A active),
  (forall p (x y : S p), x = y) ->
  NoDup active ->
  owns_region model stores input R A0 c0 ar A active o cuts ->
  family_at (logged_cut model stores input R A0 c0)
    (at_node model stores input R A0 c0 past) S A prog active inc o cuts ->
  forall p d, cursor_readers (packet_codec gs) p (A p)
    (cursor_at (cuts p d)).
Proof.
  intro WF.
  induction WF as
    [S A input0 prog Shape
    |S X l f prog Owner Shape
    |S X l r sh rd input0 prog Sender Receiver Codec Shape
    |S X l A sh rd input0 k K prog Owner Codec Branch IH Shape
    |S A B f x F X prog WFf IHf WFx IHx Shape
    |S A B t k P K prog WFt IHt Body IHbody Shape];
    intros active inc o cuts PI ND Own At.
  - intros p d. eapply logged_atomic_readers; [|apply At|].
    + rewrite Shape; exact I.
    + rewrite Shape; exact I.
  - intros p d. eapply logged_atomic_readers; [|apply At|].
    + rewrite Shape; exact I.
    + rewrite Shape; exact I.
  - intros p d. eapply logged_atomic_readers; [|apply At|].
    + rewrite Shape; exact I.
    + exact (owned_node_codec model stores input R A0 c0 tc s tn n gs past ar
        Archives S _ prog active inc o cuts Own At _
        (WFComm R M S X l r sh rd input0 prog Sender Receiver Codec Shape) p d).
  - assert (Head : family_at (logged_cut model stores input R A0 c0)
      (at_node model stores input R A0 c0 past) S A (fun p s =>
        Perf (@Cond M p X l (A p) (sh p s) (rd p s)
          (known l) MkSSymbol (input0 p s) (k p s))) active inc o cuts).
    { intros p d. rewrite <- Shape. apply At. }
    destruct (replay_cond_logged_strong model stores input R A0 c0 past ar
      tc s tn n gs S X l A sh rd input0 k active [] inc o cuts
      (fun p d => False_rect _ d) (fun p d => False_rect _ d)
      (observed_archives_history model stores input R A0 c0 _ _ _ _ _ _ _
        Archives)
      ND (NoDup_nil _) Own Head (fun p d => False_rect _ d))
      as (entered & inside & completed & choices & branch &
        NE & BranchOwn & Observe & BranchAt & BranchRet & Entered & Outside).
    assert (RootReader : forall p d,
      reader_contract (prog p (inc p d)) (packet_codec gs p o)).
    { intros p d. exact (owned_node_codec model stores input R A0 c0 tc s tn n
      gs past ar
        Archives S A prog active inc o cuts Own At _
        (WFCond R M S X l A sh rd input0 k K prog Owner Codec Branch Shape) p
          d). }
    destruct entered as [|first rest].
    + intros p d. rewrite (Outside p d (fun h => h)).
      cbn [cursor_readers]. rewrite <- Shape. apply RootReader.
    + destruct (entered_choices_agree model stores input R A0 c0
        tc s tn n gs past ar S A X l sh rd input0 k active inc o cuts
        (first :: rest) inside choices Archives Own Head Codec Observe
        ltac:(discriminate)) as [Present Common].
      set (a := unAt (input0 l (inc l Present)) eq_refl).
      fold a in Common.
      assert (BranchReaders : forall p d,
        cursor_readers (packet_codec gs) p (A p) (cursor_at (branch p d))).
      { eapply (IH a (first :: rest) (fun p d => inc p (inside p d))
          (child o ChoiceBody) branch PI NE BranchOwn).
        intros p d. rewrite <- (Common p d). apply BranchAt. }
      intros p d. destruct (in_dec role_eq_dec p (first :: rest)) as
        [Here|NotHere].
      * rewrite <- (roster_member_unique active ND p (inside p Here) d).
        rewrite Entered. apply BranchReaders.
      * rewrite (Outside p d NotHere). cbn [cursor_readers].
        rewrite <- Shape. apply RootReader.
  - assert (Head : family_at (logged_cut model stores input R A0 c0)
      (at_node model stores input R A0 c0 past) S B
        (fun p s => App (f p s) (x p s)) active inc o cuts).
    { intros p d. rewrite <- Shape. apply At. }
    destruct (logged_replay_app model stores input R A0 c0 past ar S A B
      f x active inc o cuts Own Head)
      as (fs & xs & FOwn & XOwn & FAt & XAt & CursorShape).
    pose proof (IHf active inc (child o AppFunction) fs PI ND FOwn FAt) as
      FReaders.
    pose proof (IHx active inc (child o AppArgument) xs PI ND XOwn XAt) as
      XReaders.
    intros p d. destruct (CursorShape p d)
      as [[Parent _]|[Parent|(g & a & FRet & XRet & Parent)]]; rewrite Parent;
      cbn [cursor_readers reader_contract]; auto.
  - assert (Head : family_at (logged_cut model stores input R A0 c0)
      (at_node model stores input R A0 c0 past) S B
        (fun p s => Bind (t p s) (k p s)) active inc o cuts).
    { intros p d. rewrite <- Shape. apply At. }
    destruct (logged_replay_bind model stores input R A0 c0 past ar S A B t k
      active [] inc o cuts (fun p d => False_rect _ d) (fun p d => False_rect _
        d)
      ND (NoDup_nil _) Own Head (fun p d => False_rect _ d))
      as (entered & inside & completed & prefix & x & body &
        NE & PrefixOwn & PrefixAt & PrefixRet & BodyOwn & BodyAt & BodyRet &
          CursorShape).
    assert (PrefixResult : P (fun p => In p entered) x).
    { eapply (structural_cut_family_results
        (logged_cut model stores input R A0 c0)
        (at_node model stores input R A0 c0 past)
        (finished model stores input R A0 c0) past
        (owns_region model stores input R A0 c0 ar)
      Laws
        R S A t P WFt active entered inc (child o BindPrefix) prefix x inside
        PI ND NE PrefixOwn PrefixAt PrefixRet). }
    pose proof (IHt active inc (child o BindPrefix) prefix PI ND PrefixOwn
      PrefixAt)
      as PrefixReaders.
    pose proof (IHbody (fun p => In p entered) x (fun p d => inc p (inside p d))
      PrefixResult entered (fun p d => d) (child o BindBody) body
      (roster_member_unique entered NE) NE BodyOwn BodyAt) as BodyReaders.
    intros p d. destruct (CursorShape p d)
      as [(here & Eq & Parent)|[[Parent _]|Parent]]; rewrite Parent;
      cbn [cursor_readers reader_contract]; auto.
Qed.
Theorem observed_source_originals_present :
  well_formed R M A0 c0 ->
  forall p, In p R -> forall X kind o sender rd,
  receive_site (shared_model model) p (A0 p) (positions s p)
    X kind o sender rd ->
  packet_codec gs p o X kind sender rd.
Proof.
  intros [NR [Q WF]] p Member X kind o sender rd Site.
  destruct (expose_logged_receivers model stores input R A0 c0 past ar
    tc s tn n gs p X kind o sender rd Archives NR Site)
    as (cuts & B & C & focus & Own & Nodes & Cursor & Focus).
  pose proof (structural_logged_readers _ _ _ _ WF R (fun p d => d)
    [] cuts (roster_member_unique R NR) NR Own Nodes p Member) as All.
  rewrite (Cursor Member) in All.
  exact (readers_receive (packet_codec gs) p B focus X kind o sender rd Focus
    (readers_focus (packet_codec gs) p (A0 p) B C focus All)).
Qed.
End AllOrigins.

From ParkourTheories.Projection.Matching Require Import ReturnedValues.

(* The public clause requires no family witness, no global cut assumption,
   and no result at every configured role. The observed archive and its
   concrete replay laws both come from this same matched execution. *)
Theorem matched_receiver_packet_codec {M E Store Input}
    (model : local_model M E Symbol (Store * Input))
    stores input R A c tc s tn n gs :
  well_formed R M A c ->
  matched_prefix model stores input R A c tc s tn n gs ->
  forall p, In p R -> forall X kind o sender rd,
  receive_site (shared_model model) p (A p) (positions s p)
    X kind o sender rd ->
  packet_codec gs p o X kind sender rd.
Proof.
  intros WF Prefix p Member X kind o sender rd Site.
  destruct (matched_has_observed_archives model stores input R A c
    _ _ _ _ _ Prefix) as (past & ar & Hist & Archives & Valid).
  exact (observed_source_originals_present model stores input R A c
    tc s tn n gs past ar Archives
    (actual_replay_laws model stores input R A c tc s tn n gs past ar Archives)
    WF p Member X kind o sender rd Site).
Qed.

(* A separate head theorem supplies the path of the first queued packet.
   Once it does, the requested source_originals clause follows directly. *)
Theorem matched_source_originals_from_head {M E Store Input}
    (model : local_model M E Symbol (Store * Input))
    stores input R A c tc s tn n gs :
  well_formed R M A c ->
  matched_prefix model stores input R A c tc s tn n gs ->
  forall p, In p R ->
  source_head_paths (shared_model model) p (A p) (positions s p) gs ->
  source_originals (shared_model model) p (A p) (positions s p) gs.
Proof.
  intros WF Prefix p Member Head X kind o sender rd Site [g First].
  apply (matched_receiver_packet_codec model stores input R A c tc s tn n gs
    WF Prefix p Member X kind o sender rd Site).
  exists g. split.
  - destruct First as (pre & post & Eq & Skip & Key).
    rewrite Eq. apply in_or_app; right; now left.
  - split.
    + destruct First as (pre & post & Eq & Skip & Key). exact Key.
    + exact (Head X kind o sender rd Site g First).
Qed.
