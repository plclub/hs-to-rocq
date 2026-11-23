From Stdlib Require Import Lists.List Logic.Eqdep_dec.
Require Import Choreography.Choreo2 Control.Monad.Tree Parkour.Symbol
  Parkour.Codec.
From ParkourTheories Require Import Choreography.Occurrences
  Choreography.PendingDeliveries Choreography.RoleSteps Choreography.Execution
  Network.Mailboxes Projection.FIFO.MessageRepresentation Semantics.LocalEffects
  Projection.Matching.PrefixRelation Projection.Matching.PayloadHistory
  Choreography.Histories.TransitionArchive Projection.Payloads.RootPackets
  Choreography.WellFormedness Semantics.SharedState
  Choreography.Histories.CursorHistories.
Import ListNotations.

(* Observe bytes of the whole packet. In particular, no injection on an
   existential payload type, and no injectivity of the continuation, is used. *)
Theorem root_choice_delivery_selected
    {M E Store Input}
    (model : local_model M E role (Store * Input)) stores input R A c
    tc s tn n gs past X l
    (sh : forall p, Show X) (rd : forall p, Read X)
    (value : forall p, At X l p)
    (k : forall p, X -> Choreo M p (A p)) p chosen w gs' :
  c l = Perf (@Cond M l X l (A l)
    (sh l) (rd l) (known l) MkSSymbol (value l) (k l)) ->
  (l <> p -> wire_law (sh l) (rd p)) ->
  payload_history model stores input R A c tc s tn n gs past ->
  l <> p ->
  delivery X ChoiceDelivery [] l p chosen (rd p) gs w gs' ->
  chosen = unAt (value l) eq_refl.
Proof.
  intros Shape Codec History Different Delivery.
  destruct Delivery as [dict pre post FIFO Decode].
  assert (Member : In (Message X ChoiceDelivery [] l p chosen dict)
    (pre ++ Message X ChoiceDelivery [] l p chosen dict :: post)).
  { apply in_or_app. right. now left. }
  pose proof (packet_from_root_program model stores input R A c
    tc s tn n _ past X ChoiceDelivery l p chosen dict History Member) as Packet.
  rewrite Shape in Packet. cbn [outgoing] in Packet.
  destruct (role_eq_dec l l) as [same|Impossible]; [|contradiction].
  rewrite (UIP_dec role_eq_dec same eq_refl) in Packet.
  pose proof (f_equal (fun msg =>
    match msg with Some m => message_wire m | None => [] end) Packet) as Bytes.
  cbn in Bytes.
  rewrite <- Bytes, (Codec Different) in Decode.
  now injection Decode.
Qed.

Section ObservationView.
Context {M E : Type -> Type} {S : Type}.
Variable model : local_model M E role S.
Variable R : list role.
Variable p : role.

Definition atomic_not_choice A (c : Choreo M p A) : Prop :=
  match c with
  | Perf (@Cond _ _ _ _ _ _ _ _ _ _ _) => False
  | _ => True
  end.

Lemma atomic_not_choice_correct A c :
  atomic p A c -> atomic_not_choice A c.
Proof. destruct 1; exact I. Qed.

Definition choice_observed_view A (before : @cursor M E p A)
    (action : @source_action E S) (after : @cursor M E p A) gs gs' : Prop :=
  match before in cursor _ B return cursor p B -> Prop with
  | Code o code =>
    match code in Tree _ B return cursor p B -> Prop with
    | Perf e =>
      match e in ChoreoSig _ _ B return cursor p B -> Prop with
      | @Cond _ _ X l Y sh rd kl sl v k => fun after =>
        exists chosen,
          after = Code (child o ChoiceBody) (k chosen) /\
          ((exists same : l = p,
              chosen = unAt v same /\
              action = AnnounceAction X o p chosen) \/
           (l <> p /\ action = HearAction X o l p chosen /\
             exists wire, delivery X ChoiceDelivery o l p chosen rd gs wire
               gs'))
      | _ => fun _ => True
      end
    | _ => fun _ => True
    end
  | _ => fun _ => True
  end after.

Lemma observed_choice_view A before st pending act after st' pending' net gs gs'
  ev :
  @observed M E S model R p A before st pending act after st' pending' net gs
    gs' ev ->
  choice_observed_view A before act after gs gs'.
Proof.
  destruct 1; cbn [choice_observed_view]; try exact I.
  - eexists. split; [reflexivity|]. left.
    exists eq_refl. split; reflexivity.
  - eexists. split; [reflexivity|]. right.
    split; [exact h|]. split; [reflexivity|]. eexists; eassumption.
  - pose proof (silent_shape_correct model p _ _ _ H) as Shape.
    destruct t as [B o code|B v|B o tree|B C o pre k|B C f arg];
      cbn [choice_observed_view]; try exact I.
    destruct code as [B e|B v|B C f arg|B C pre k];
      cbn [choice_observed_view]; try exact I.
    destruct e; cbn [choice_observed_view]; try exact I.
    exact (False_rect _ (atomic_not_choice_correct _ _ Shape)).
Qed.
End ObservationView.

Theorem observed_root_choice_selected
    {M E Store Input}
    (model : local_model M E role (Store * Input)) stores input R A c
    tc s tn n gs past X l
    (sh : forall p, Show X) (rd : forall p, Read X)
    (value : forall p, At X l p)
    (k : forall p, X -> Choreo M p (A p))
    p st pending act after st' pending' net gs' ev :
  c l = Perf (@Cond M l X l (A l)
    (sh l) (rd l) (known l) MkSSymbol (value l) (k l)) ->
  c p = Perf (@Cond M p X l (A p)
    (sh p) (rd p) (known l) MkSSymbol (value p) (k p)) ->
  (l <> p -> wire_law (sh l) (rd p)) ->
  payload_history model stores input R A c tc s tn n gs past ->
  @observed M E _ (shared_model model) R p (A p)
    (Code [] (c p)) st pending act after st' pending' net gs gs' ev ->
  after = Code [ChoiceBody] (k p (unAt (value l) eq_refl)) /\
  ((p = l /\ act = AnnounceAction X [] p (unAt (value l) eq_refl)) \/
   (l <> p /\ act = HearAction X [] l p (unAt (value l) eq_refl))).
Proof.
  intros Owner Peer Codec History Obs.
  rewrite Peer in Obs.
  destruct (observed_choice_view (shared_model model) R p _ _ _ _ _ _ _ _ _ _ _
    _ Obs)
    as (chosen & After & [(same & Value & Act)|(Different & Act & wire &
      Delivery)]).
  - destruct same. rewrite Value in After, Act.
  exact (conj After (or_introl (conj eq_refl Act))).
  - assert (Value : chosen = unAt (value l) eq_refl).
    { exact (root_choice_delivery_selected model stores input R A c
        tc s tn n gs past X l sh rd value k p chosen wire gs'
        Owner Codec History Different Delivery). }
    rewrite Value in After, Act.
    exact (conj After (or_intror (conj Different Act))).
Qed.

Section ArchivedRoot.
Context {M E : Type -> Type} {Store Input : Type}.
Variable model : local_model M E role (Store * Input).
Variable stores : role -> Store.
Variable input : Input.
Variable R : list role.
Variable A : role -> Type.
Variable c : forall p, Choreo M p (A p).
Variable X : Type.
Variable l : role.
Variable sh : forall p : role, Show X.
Variable rd : forall p : role, Read X.
Variable value : forall p, At X l p.
Variable k : forall p, X -> Choreo M p (A p).
Variable p : role.

Definition choice_action_selected (act : @source_action E ((role -> Store) *
  Input)) :=
  (p = l /\ act = AnnounceAction X [] p (unAt (value l) eq_refl)) \/
  (l <> p /\ act = HearAction X [] l p (unAt (value l) eq_refl)).

Definition root_choice_contract B (code : Choreo M p B) :=
  forall tc s tn n gs past st pending act (after : @cursor M E p B)
    st' pending' net gs' ev,
  payload_history model stores input R A c tc s tn n gs past ->
  @observed M E _ (shared_model model) R p B
    (Code [] code) st pending act after st' pending' net gs gs' ev ->
  existT (fun T => @cursor M E p T) B after =
    existT (fun T => @cursor M E p T) (A p)
      (Code [ChoiceBody] (k p (unAt (value l) eq_refl))) /\
  choice_action_selected act.

(* The archive supplies the original-code contract without injecting its
   existential result type. The observation supplies the real earlier ghost
   queue and decoder. Neither an equal endpoint nor a constant k supplies it. *)
Theorem archived_actual_root_choice_selected
    tr (cut : annotated_cut (shared_model model) R p (A p))
    B (code : Choreo M p B) after st pending act st' pending'
    (prim : primitive_action (shared_model model) R B
      (Code [] code) st pending act after st' pending')
    tc s tn n gs past net gs' ev :
  c l = Perf (@Cond M l X l (A l)
    (sh l) (rd l) (known l) MkSSymbol (value l) (k l)) ->
  c p = Perf (@Cond M p X l (A p)
    (sh p) (rd p) (known l) MkSSymbol (value p) (k p)) ->
  (l <> p -> wire_law (sh l) (rd p)) ->
  cut_history (shared_model model) R p (Code [] (c p)) tr cut ->
  In (ActionEvent (shared_model model) R p B
      (Code [] code) after st pending act st' pending' prim)
    (lookup (shared_model model) R p [] (archive (shared_model model) R p cut))
      ->
  payload_history model stores input R A c tc s tn n gs past ->
  @observed M E _ (shared_model model) R p B
    (Code [] code) st pending act after st' pending' net gs gs' ev ->
  existT (fun T => @cursor M E p T) B after =
    existT (fun T => @cursor M E p T) (A p)
      (Code [ChoiceBody] (k p (unAt (value l) eq_refl))) /\
  choice_action_selected act.
Proof.
  intros Owner Peer Codec Archived Member History Obs.
  assert (Original : root_choice_contract (A p) (c p)).
  { intros tc0 s0 tn0 n0 gs0 past0 st0 pending0 act0 after0 st1 pending1
      net0 gs1 ev0 Hist0 Obs0.
    destruct (observed_root_choice_selected model stores input R A c
      tc0 s0 tn0 n0 gs0 past0 X l sh rd value k p st0 pending0 act0 after0
      st1 pending1 net0 gs1 ev0 Owner Peer Codec Hist0 Obs0) as [After Action].
    subst after0. split; [reflexivity|exact Action]. }
  pose proof (archived_root (shared_model model) R p root_choice_contract
    (A p) _ tr cut Archived (fun _ => Original)) as [_ Events].
  specialize (Events [] _ Member).
  cbn [event_ok root_ok] in Events.
  exact (Events eq_refl tc s tn n gs past st pending act after st' pending'
    net gs' ev History Obs).
Qed.
End ArchivedRoot.

Section ActorInvariant.
Context {M E : Type -> Type} {Store Input : Type}.
Variable model : local_model M E role (Store * Input).
Variable stores : role -> Store.
Variable input : Input.
Variable R : list role.
Variable A : role -> Type.
Variable c : forall p, Choreo M p (A p).
Variable X : Type.
Variable l : role.
Variable sh : forall p : role, Show X.
Variable rd : forall p : role, Read X.
Variable value : forall p, At X l p.
Variable k : forall p, X -> Choreo M p (A p).
Local Notation sm := (shared_model model).
Local Notation SC := (@Choreography.Execution.configuration M E ((role -> Store)
  *
  Input) A).
Local Arguments positions {M E Store A} _ _.

Definition selected_origin p : @cursor M E p (A p) :=
  Code [ChoiceBody] (k p (unAt (value l) eq_refl)).

(* The witness records a REAL first transition at an earlier global prefix,
   together with the ordered suffix of this actor's actions. Its start is
   fixed even when its current erased cursor lies deep in a later branch. *)
Definition choice_started p tc (s : SC) : Prop :=
  exists tc0 s0 tn0 n0 gs0 past0 first s1 net n1 gs1 ev suffix,
    payload_history model stores input R A c tc0 s0 tn0 n0 gs0 past0 /\
    actor_actions p tc0 = [] /\
    positions s0 p = Code [] (c p) /\
    paired_observed model R A s0 n0 gs0 first s1 net n1 gs1 ev /\
    @observed M E _ sm R p (A p) (Code [] (c p))
      (Choreography.Execution.shared_store s0) (deliveries s0) first
        (selected_origin p)
      (Choreography.Execution.shared_store s1) (deliveries s1) net gs0 gs1 ev /\
    actor_actions p tc = first :: suffix /\
    cursor_history sm R (selected_origin p) suffix (positions s p).

Lemma choice_started_frame p tc (s s' : SC) :
  positions s p = positions s' p ->
  choice_started p tc s -> choice_started p tc s'.
Proof.
  intros Frame (tc0 & s0 & tn0 & n0 & gs0 & past0 & first & s1 & net &
    n1 & gs1 & ev & suffix & Hist & Empty & Root & Pair & Obs & Trace & Run).
  exists tc0, s0, tn0, n0, gs0, past0, first, s1, net, n1, gs1, ev, suffix.
  repeat split; try assumption. now rewrite <- Frame.
Qed.

Lemma choice_started_actor_step p tc (s s' : SC) act :
  role_step sm R (A p) (positions s p) (Choreography.Execution.shared_store s)
    (deliveries s) act (positions s' p) (Choreography.Execution.shared_store s')
    (deliveries s') ->
  choice_started p tc s -> choice_started p (tc ++ [act]) s'.
Proof.
  intros Step (tc0 & s0 & tn0 & n0 & gs0 & past0 & first & s1 & net &
    n1 & gs1 & ev & suffix & Hist & Empty & Root & Pair & Obs & Trace & Run).
  exists tc0, s0, tn0, n0, gs0, past0, first, s1, net, n1, gs1, ev,
    (suffix ++ [act]).
  repeat split; try assumption.
  - rewrite actor_actions_snoc, (role_step_actor sm R _ _ _ _ _ _ _ _ _ Step).
    destruct (List.list_eq_dec BinNat.N.eq_dec p p); [|contradiction].
    now rewrite Trace.
  - eapply history_after_role_step; eassumption.
Qed.

Theorem root_choice_actor_invariant tc s tn n gs past :
  In l R ->
  (forall p, In p R -> c p = Perf (@Cond M p X l (A p)
    (sh p) (rd p) (known l) MkSSymbol (value p) (k p))) ->
  (forall p, In p R -> l <> p -> wire_law (sh l) (rd p)) ->
  payload_history model stores input R A c tc s tn n gs past ->
  forall p, In p R ->
    (actor_actions p tc = [] /\ positions s p = Code [] (c p)) \/
    choice_started p tc s.
Proof.
  intros Owner Shape Codec History.
  induction History as
    [|tc s tn n gs past act s' net n' gs' ev Hist IH Pair State];
    intros p Member.
  - left. split; reflexivity.
  - pose proof Pair as ActualPair.
    destruct Pair as
      [r pre post t t' s' n' act net gs' ev InR Before After Obs Frame NetStep].
    pose proof (observed_decorated sm R r (A r)
      (positions s r) (Choreography.Execution.shared_store s) (deliveries s) act
      (positions s' r) (Choreography.Execution.shared_store s') (deliveries s')
      net gs gs' ev Obs) as Decorated.
    pose proof (decorated_source sm R r (A r)
      (positions s r) (Choreography.Execution.shared_store s) (deliveries s) act
      (positions s' r) (Choreography.Execution.shared_store s') (deliveries s')
      net gs gs' Decorated) as Step.
    pose proof (role_step_actor sm R _ _ _ _ _ _ _ _ _ Step) as Actor.
    destruct (List.list_eq_dec BinNat.N.eq_dec r p) as [Same|Other].
    + clear Actor. subst r.
      pose proof (role_step_actor sm R _ _ _ _ _ _ _ _ _ Step) as Actor.
      destruct (IH p Member) as [[Empty Root]|Started].
      * assert (Selected : positions s' p = selected_origin p).
        { unfold selected_origin.
          pose proof Obs as RootObs. rewrite Root in RootObs.
          exact (proj1 (observed_root_choice_selected model stores input R A c
            tc s tn n gs past X l sh rd value k p
            (Choreography.Execution.shared_store s) (deliveries s) act
              (positions s' p)
            (Choreography.Execution.shared_store s') (deliveries s') net gs' ev
            (Shape l Owner) (Shape p Member)
            (Codec p Member) Hist RootObs)). }
        right. unfold choice_started.
        exists tc, s, tn, n, gs, past, act, s', net, n', gs', ev, [].
        split; [exact Hist|]. split; [exact Empty|]. split; [exact Root|].
        split; [exact ActualPair|]. split.
        -- rewrite <- Selected, <- Root. exact Obs.
        -- split.
           ++ rewrite actor_actions_snoc, Actor.
              destruct (List.list_eq_dec BinNat.N.eq_dec p p); [|contradiction].
              now rewrite Empty.
           ++ rewrite Selected. constructor.
      * right. eapply choice_started_actor_step; eassumption.
    + assert (Trace : actor_actions p (tc ++ [act]) = actor_actions p tc).
      { rewrite actor_actions_snoc, Actor.
        destruct (List.list_eq_dec BinNat.N.eq_dec r p); [contradiction|].
        apply app_nil_r. }
      destruct (IH p Member) as [[Empty Root]|Started].
      * left. split; [now rewrite Trace|].
        rewrite <- Frame; [exact Root|congruence].
      * right. unfold choice_started in *.
        rewrite Trace. eapply choice_started_frame; [|exact Started].
        apply Frame. congruence.
Qed.
End ActorInvariant.
