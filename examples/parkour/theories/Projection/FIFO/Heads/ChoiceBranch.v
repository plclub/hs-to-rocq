From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Choreography.Occurrences
  Choreography.PendingDeliveries Choreography.RoleSteps Choreography.Execution
  Network.Mailboxes Projection.Matching.PrefixRelation
  Projection.FIFO.MessageRepresentation Projection.FIFO.ChannelLedger
  Projection.FIFO.ConsumedOccurrences Projection.FIFO.Heads.RootOccurrence
  Projection.FIFO.FirstEmission Projection.Occurrences.SubtreeGuards
  Projection.Occurrences.SenderBarrier Projection.FIFO.Heads.StaticPath
  Projection.Payloads.SelectedBranch Projection.Payloads.ChoiceSelection
  Projection.Occurrences.EnteredCode Projection.Payloads.StaticPackets
  Projection.Occurrences.PossiblePaths Projection.Payloads.RootPackets
  Choreography.ReceiveSites Choreography.WellFormedness Semantics.LocalEffects
  Semantics.SharedState Choreography.Results.OperandObservations
  Projection.Matching.PayloadHistory Choreography.Histories.CursorHistories
  Choreography.Histories.RoleChronology Projection.SessionPaths
  Projection.FIFO.HeadDecoding.
Require Import Choreography.Choreo2 Control.Monad.Tree Parkour.Codec
  Parkour.Symbol.
Import ListNotations.
Local Arguments positions {M E Store A} _ _.

(* A live guard singles out a session even inside a dynamically entered
   subtree. A different live App branch has a different generated session. *)
Lemma guarded_action_session {M E S} (m : local_model M E role S)
    R sending p peer site A t st q a u st' q' root :
  @role_step M E S m R p A t st q a u st' q' ->
  mandatory_guard R sending p peer site t -> scoped root t ->
  session_at (action_path a) Choreography.Network.Root =
    session_at site Choreography.Network.Root ->
  action_path a = site.
Proof.
  intro Step. revert root. induction Step; intros root Guard Scope Session;
    cbn [mandatory_guard] in Guard; try contradiction.
  all: try solve [
    match type of Scope with scoped _ (Code ?o (Perf ?sig)) =>
      destruct (@mandatory_perf M E R sending p peer site _ o sig Guard) as [Eq
        _];
      cbn [action_path]; symmetry; exact Eq
    end].
  - cbn [scoped] in Scope. destruct Scope as [_ Scope].
    eapply IHStep; eassumption.
  - cbn [scoped] in Scope. destruct Scope as (v & Bound & Sf & Sx).
    destruct Guard as [Guard|Guard].
    + eapply IHStep; eassumption.
    + exfalso. eapply (scoped_fork_disjoint p _ _ root f x
        (action_path a) site Choreography.Network.Root).
      * exists v; auto.
      * exact (proj2 (role_future _ _ _ _ _ _ _ _ _ _ _ Step)).
      * eapply mandatory_future; exact Guard.
      * exact Session.
  - cbn [scoped] in Scope. destruct Scope as (v & Bound & Sf & Sx).
    destruct Guard as [Guard|Guard].
    + exfalso. eapply (scoped_fork_disjoint p _ _ root f x
        site (action_path a) Choreography.Network.Root).
      * exists v; auto.
      * eapply mandatory_future; exact Guard.
      * exact (proj2 (role_future _ _ _ _ _ _ _ _ _ _ _ Step)).
      * symmetry; exact Session.
    + eapply IHStep; eassumption.
  - eapply IHStep.
    + eapply mandatory_silent; eassumption.
    + eapply silent_scoped; eassumption.
    + exact Session.
Qed.

Lemma mandatory_action_session {E S} sending R p peer site z
    (a : @source_action E S) :
  In z (mandatory_ledger sending R p peer site a) ->
  session_at (action_path a) Choreography.Network.Root =
    session_at site Choreography.Network.Root.
Proof.
  destruct sending; cbn [mandatory_ledger].
  - destruct a; cbn [emits action_path]; try contradiction.
    + destruct (key_eq_dec _ _) as [Eq|Ne]; [|contradiction].
      inversion Eq; reflexivity.
    + unfold key_paths, announcement_messages.
      intro Member. apply in_map_iff in Member.
      destruct Member as (g & Eq & Member). apply filter_In in Member.
      destruct Member as [Member Key]. apply in_map_iff in Member.
      destruct Member as (r & <- & _). cbn [message_key] in Key.
      destruct (key_eq_dec _ _) as [K|Ne]; [inversion K;
        reflexivity|discriminate].
  - destruct a; cbn [receives action_path]; try contradiction.
    all: destruct (key_eq_dec _ _) as [Eq|Ne]; [inversion Eq;
      reflexivity|contradiction].
Qed.

(* This ledger is the exact enclosing role trace of the entered body, not
   an independently reconstructed traversal of the same source syntax. *)
Lemma guarded_history_front {M E S} (m : local_model M E role S)
    R sending p peer site A (start finish : @cursor M E p A) tr root :
  cursor_history m R start tr finish ->
  mandatory_guard R sending p peer site start -> scoped root start ->
  (flat_map (mandatory_ledger sending R p peer site) tr = [] /\
    mandatory_guard R sending p peer site finish) \/
  exists tail, flat_map (mandatory_ledger sending R p peer site) tr = site ::
    tail.
Proof.
  intro Hist. induction Hist as [|tr B C before after Hist IHHist Prim|
      tr B C before after st sq act st' sq' Hist IHHist Prim];
    intros Guard Scope.
  - left; auto.
  - destruct (IHHist Guard Scope) as [[Empty Now]|Issued]; [left|right; exact
    Issued].
    split; [exact Empty|]. eapply mandatory_silent;
      [apply silent_plug; apply primitive_is_silent; exact Prim|exact Now].
  - rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r.
    destruct (IHHist Guard Scope) as [[Empty Now]|[tail Issued]].
    + rewrite Empty. cbn [app].
      assert (Step : role_step m R A (plug C before) st sq act (plug C after)
        st' sq').
      { apply role_step_plug. apply primitive_is_role_step. exact Prim. }
      destruct (mandatory_ledger sending R p peer site act) as [|head tail]
        eqn:Batch.
      * left; split; [reflexivity|].
        destruct (mandatory_step m R sending p peer site _ _ _ _ _ _ _ _
          Step Now) as [InBatch|Next]; [rewrite Batch in InBatch;
            contradiction|exact Next].
      * right. exists tail. f_equal.
        assert (Member : In head (mandatory_ledger sending R p peer site act))
          by (rewrite Batch; now left).
        rewrite (mandatory_ledger_path _ _ _ _ _ _ _ Member).
        eapply guarded_action_session; [exact Step|exact Now| |].
        -- eapply cursor_history_scoped; eassumption.
        -- eapply mandatory_action_session; exact Member.
    + right. rewrite Issued. eexists; reflexivity.
Qed.

Lemma actor_flat_map {E S B} p (F : @source_action E S -> list B) tc :
  (forall a, action_actor a <> p -> F a = []) ->
  flat_map F (actor_actions p tc) = flat_map F tc.
Proof.
  intro Other. unfold actor_actions. induction tc as [|a tc IH]; [reflexivity|].
  cbn [filter flat_map]. destruct (list_eq_dec BinNat.N.eq_dec (action_actor a)
    p)
    as [Eq|Ne]; cbn [flat_map]; rewrite IH; [reflexivity|].
  now rewrite Other by exact Ne.
Qed.

Lemma announcement_one R sender receiver sid :
  NoDup R -> In receiver R -> sender <> receiver ->
  key_paths (sender,receiver,sid)
    (announcement_messages unit [] sender tt show_unit R) =
  if key_eq_dec (sender,receiver,Choreography.Network.Root)
       (sender,receiver,sid) then [[]] else [].
Proof.
  intros ND Member Ne.
  unfold announcement_messages.
  induction R as [|r rs IH]; [contradiction|].
  inversion ND as [|? ? NotIn Rest]; subst.
  cbn [filter]. destruct (role_eq_dec r sender) as [->|Different].
  - apply IH; [exact Rest|]. destruct Member; [congruence|assumption].
  - cbn [map].
    destruct (role_eq_dec r receiver) as [->|NotReceiver].
    + assert (Absent : Forall
        (fun g => message_key g <> (sender,receiver,sid))
        (map (fun peer => Message unit ChoiceDelivery [] sender peer tt
          show_unit)
          (filter (fun peer => if role_eq_dec peer sender then false else true)
            rs))).
      { apply Forall_forall. intros g InG. apply in_map_iff in InG.
        destruct InG as (peer & <- & InPeer). apply filter_In in InPeer.
        cbn [message_key]. intro Eq. inversion Eq; subst. tauto. }
      destruct (key_eq_dec (sender,receiver,Choreography.Network.Root)
        (sender,receiver,sid)) as [Eq|N].
      * inversion Eq; subst sid.
        rewrite (key_paths_same
          (Message unit ChoiceDelivery [] sender receiver tt show_unit)).
        cbn [message_path message_key session_at].
        rewrite (key_paths_absent _ _ Absent). reflexivity.
      * rewrite key_paths_other by exact N.
      apply key_paths_absent; exact Absent.
    + rewrite key_paths_other.
      * apply IH; [exact Rest|]. destruct Member; [congruence|assumption].
      * cbn [message_key]. intro Eq; inversion Eq; contradiction.
Qed.

Lemma root_choice_balance {E S X} R l sender receiver sid
    (chosen : X) (send receive : @source_action E S) :
  NoDup R -> In receiver R -> sender <> receiver ->
  ((sender = l /\ send = AnnounceAction X [] sender chosen) \/
    (l <> sender /\ send = HearAction X [] l sender chosen)) ->
  ((receiver = l /\ receive = AnnounceAction X [] receiver chosen) \/
    (l <> receiver /\ receive = HearAction X [] l receiver chosen)) ->
  emits R (sender,receiver,sid) send = receives (sender,receiver,sid) receive.
Proof.
  intros ND Member Ne [[-> ->]|[Ns ->]] [[-> ->]|[Nr ->]];
    cbn [emits receives]; try contradiction; try reflexivity.
  - apply announcement_one; assumption.
  - destruct (key_eq_dec _ _) as [Eq|N]; [inversion Eq;
    contradiction|reflexivity].
Qed.

Lemma focus_ready {M E} p B (t : @cursor M E p B) Y kind o sender rd :
  receive_focus p B t Y kind o sender rd ->
  match t with Code _ code => receiver_node code sender | _ => False end.
Proof. destruct 1; cbn [receiver_node]; auto. Qed.

Section SelectedHead.
Context {M E Store Input} (model : local_model M E role (Store * Input))
  (stores : role -> Store) (input : Input) (R : list role) (A : role -> Type)
  (c : forall p, Choreo M p (A p)).
Local Notation sm := (shared_model model).
Local Notation prefix := (matched_prefix model stores input R A c).
Variable X : Type.
Variable l : role.
Variables (sh : forall p : role, Show X) (rd : forall p : role, Read X)
  (arg : forall p, At X l p) (k : forall p, X -> Choreo M p (A p)).
Let chosen := unAt (arg l) eq_refl.
Let body p := k p chosen.
Hypothesis Owner : In l R.
Hypothesis Shape : forall p, In p R ->
  c p = Perf (@Cond M p X l (A p) (sh p) (rd p)
    (known l) MkSSymbol (arg p) (k p)).
Hypothesis Law : forall p, In p R -> l <> p -> wire_law (sh l) (rd p).

Lemma choice_actor_body tc s tn n gs p :
  prefix tc s tn n gs -> In p R ->
  (actor_actions p tc = [] /\ positions s p = Code [] (c p)) \/
  exists first suffix,
    ((p = l /\ first = AnnounceAction X [] p chosen) \/
      (l <> p /\ first = HearAction X [] l p chosen)) /\
    actor_actions p tc = first :: suffix /\
    cursor_history sm R (Code [ChoiceBody] (body p)) suffix (positions s p).
Proof.
  intros Run Member.
  destruct (matched_payload_history model stores input R A c _ _ _ _ _ Run) as
    [past Hist].
  destruct (root_choice_actor_invariant model stores input R A c X l sh rd arg k
    _ _ _ _ _ _ Owner Shape Law Hist p Member) as [Waiting|Started]; [now
      left|].
  right. destruct Started as (tc0 & s0 & tn0 & n0 & gs0 & past0 & first &
    s1 & net & n1 & gs1 & ev & suffix & Earlier & Empty & Root & Pair & Obs &
      Trace & BodyHist).
  exists first, suffix. split; [|now split].
  exact (proj2 (observed_root_choice_selected model stores input R A c
    tc0 s0 tn0 n0 gs0 past0 X l sh rd arg k p
    (Choreography.Execution.shared_store s0) (deliveries s0) first
    (selected_origin A X l arg k p) (Choreography.Execution.shared_store s1)
    (deliveries s1) net gs1 ev (Shape l Owner) (Shape p Member)
    (Law p Member) Earlier Obs)).
Qed.

Lemma choice_body_entry tc s tn n gs :
  prefix tc s tn n gs -> forall p, In p R ->
  entered_body_or_waiting model R A c X l arg k s p.
Proof.
  intros Run p Member.
  destruct (choice_actor_body _ _ _ _ _ _ Run Member) as [[_ Wait]|(first &
    suffix & _ & _ & Hist)].
  - left; exact Wait.
  - right; now exists suffix.
Qed.

Theorem choice_body_head_paths tc s tn n gs p :
  well_formed R M A body -> prefix tc s tn n gs -> In p R ->
  forall Y kind path sender reader, static_path path ->
  receive_site sm p (A p) (positions s p) Y kind (ChoiceBody :: path) sender
    reader ->
  forall g, first_message_at_key (sender,p,session_at (ChoiceBody :: path)
    Choreography.Network.Root) gs g ->
    message_path g = ChoiceBody :: path.
Proof.
  intros [ND [Q WF]] Run Member Y kind path sender reader Static Site g Head.
  set (site := ChoiceBody :: path).
  set (key := (sender,p,session_at site Choreography.Network.Root)).
  pose proof (receive_site_future sm p (A p) _ Y kind _ _ _ Site) as Future.
  assert (Ne : sender <> p).
  { destruct Site as (B & C & focus & Sil & Focus). destruct Focus; assumption.
  }
  assert (ReceiverNode : exists B (code : Choreo M p B),
    choreo_at_static_path path (body p) = Some (existT _ B code) /\
      receiver_node code
      sender).
  { destruct Site as (B & C & focus & Sil & Focus).
    destruct (focus_reader _ _ _ _ _ _ Focus) as (code & -> & Reads).
    pose proof (select_inner_code model stores input R A c X l sh rd arg k
      Shape choice_body_entry _ _ _ _ _ _ _ C code path Run Member Static Sil)
        as Desc.
    exists B, code. split; [exact Desc|].
    exact (focus_ready _ _ _ _ _ _ _ _ Focus). }
  destruct ReceiverNode as (B & code & Desc & ReadyReceiver).
  assert (SenderNode : exists v sw, In sender R /\
    outgoing_from_lookup (choreo_at_static_path path (body sender)) site p =
      Some (Message Y kind site
      sender p v sw) /\
    wire_law sw reader).
  { destruct Site as (D & C & focus & Sil & Focus).
    destruct (focus_reader _ _ _ _ _ _ Focus) as (actual & -> & Reads).
    pose proof (select_inner_code model stores input R A c X l sh rd arg k
      Shape choice_body_entry _ _ _ _ _ _ _ C actual path Run Member Static Sil)
        as ActualDesc.
    change (choreo_at_static_path path (body p) = Some (existT _ D actual)) in
      ActualDesc.
    pose proof (family_static_reader WF path site p Member (fun r h => h)
      (fun r _ => outgoing_from_lookup (choreo_at_static_path path (body r))
        site p) (fun _ _ => eq_refl))
        as Rdr.
    cbn beta in Rdr. rewrite ActualDesc in Rdr.
    destruct (Reads _ Rdr) as (value & dict & InS & Out & Wire).
    exists value,dict; auto. }
  destruct SenderNode as (v & sw & SenderMember & Output & Codec).
  assert (ReceiverGuard : @mandatory_guard M E R false p sender site _ (Code
    [ChoiceBody] (body p))).
  { exists path. split; [reflexivity|].
    cbn [mandatory_packed mandatory_ready]. rewrite Desc. exact ReadyReceiver. }
  assert (SenderGuard : @mandatory_guard M E R true sender p site _ (Code
    [ChoiceBody] (body sender))).
  { exists path. split; [reflexivity|].
    cbn [mandatory_packed mandatory_ready].
    exact (outgoing_from_lookup_sender R p _ Y kind site v sw Member Ne Output).
      }
  destruct (choice_actor_body _ _ _ _ _ p Run Member) as [[_ Waiting]|(recv &
    rsuffix & RFirst & RTrace & RHist)].
  { exfalso. destruct Site as (D & C & focus & Sil & Focus).
    destruct (focus_reader _ _ _ _ _ _ Focus) as (actual & -> & Reads).
    rewrite Waiting, (Shape p Member) in Sil.
    pose proof (before_choice_no_child sm p X l (A p) (sh p) (rd p) (known l)
      MkSSymbol (arg p) (k p) [] D C (ChoiceBody :: path) actual Sil).
    discriminate. }
  assert (ReceiveFactor : received key tc = receives key recv ++ received key
    rsuffix).
  { unfold received. rewrite <- (actor_flat_map p (receives key) tc).
    - rewrite RTrace. reflexivity.
    - apply receives_other_actor. }
  assert (ReceivedBody : received key rsuffix = []).
  { destruct (guarded_history_front sm R false p sender site _ _ _ rsuffix
      [ChoiceBody] RHist ReceiverGuard (path_prefix_refl _)) as [[Empty _]|[tail
        Nonempty]];
      [exact Empty|].
    exfalso. apply (matched_future_unreceived model stores input R A c
      _ _ _ _ _ sender p (session_at site Choreography.Network.Root) site Run
        Future).
    change (In site (received key tc)).
    rewrite ReceiveFactor. apply in_or_app; right.
    change (received key rsuffix = site :: tail) in Nonempty.
    rewrite Nonempty. now left. }
  destruct (choice_actor_body _ _ _ _ _ sender Run SenderMember)
    as [[NoActions _]|(send & ssuffix & SFirst & STrace & SHist)].
  { pose proof (actor_flat_map sender (emits R key) tc
      (emits_other_actor R sender p (session_at site
        Choreography.Network.Root))) as Factor.
    rewrite NoActions in Factor. cbn [flat_map] in Factor.
    pose proof (prefix_ledger model stores input R A c _ _ _ _ _ key Run) as
      Ledger.
    change ([] = sent R key tc) in Factor. rewrite <- Factor in Ledger.
    symmetry in Ledger. apply app_eq_nil in Ledger as [_ Empty].
    destruct (head_key_path _ _ _ Head) as [tail Pending].
    change (key_paths key gs = message_path g :: tail) in Pending. congruence. }
  assert (SendFactor : sent R key tc = emits R key send ++ sent R key ssuffix).
  { unfold sent. rewrite <- (actor_flat_map sender (emits R key) tc).
    - rewrite STrace. reflexivity.
    - apply emits_other_actor. }
  assert (Balance : emits R key send = receives key recv).
  { unfold key. eapply root_choice_balance; eassumption. }
  pose proof (prefix_ledger model stores input R A c _ _ _ _ _ key Run) as
    Ledger.
  rewrite SendFactor, ReceiveFactor, ReceivedBody, Balance in Ledger.
  cbn [app] in Ledger. rewrite <- app_assoc in Ledger.
  apply app_inv_head in Ledger.
  destruct (head_key_path _ _ _ Head) as [tail Pending].
  change (key_paths key gs = message_path g :: tail) in Pending.
  destruct (guarded_history_front sm R true sender p site _ _ _ ssuffix
    [ChoiceBody] SHist SenderGuard (path_prefix_refl _)) as [[Empty _]|[rest
      Nonempty]].
  - change (sent R key ssuffix = []) in Empty.
  rewrite Empty, Pending in Ledger; discriminate.
  - change (sent R key ssuffix = site :: rest) in Nonempty.
    rewrite Nonempty, Pending in Ledger. now injection Ledger as <- _.
Qed.
End SelectedHead.

(* The public theorem needs no entry, body-WF, or codec premises beyond the
   original WF certificate and the given matched prefix. *)
Theorem source_head_paths_choice_static {M E Store Input}
    (model : local_model M E role (Store * Input)) stores input R A c tc s tn n
      gs :
  well_formed R M A c -> matched_prefix model stores input R A c tc s tn n gs ->
  forall p, In p R -> forall Y kind path sender reader, static_path path ->
  receive_site (shared_model model) p (A p) (positions s p)
    Y kind (ChoiceBody :: path) sender reader ->
  forall g, first_message_at_key (sender,p,session_at (ChoiceBody :: path)
    Choreography.Network.Root) gs g ->
    message_path g = ChoiceBody :: path.
Proof.
  intros [ND [Q WF]] Run p Member Y kind path sender reader Static Site g Head.
  assert (Root : root_condition (c p)).
  { destruct Site as (B & C & focus & Sil & F).
    assert (Hit : exists code, focus = Code (ChoiceBody :: path) code /\
      possible_path [] code)
      by (destruct F; eexists; split; [reflexivity|exact I|reflexivity|exact
        I]).
    destruct Hit as (code & -> & Hit).
    assert (Possible : possible_path (ChoiceBody :: path) (c p)).
    { eapply reached_action_path; [|exact Sil|exact Hit].
      eapply run_follows; [exact (prefix_source_run model stores input R A c _ _
        _ _ _ Run)|].
      intros tail T; exact T. }
    destruct (c p); cbn [root_condition possible_path] in *; try contradiction.
    match goal with e : ChoreoSig _ _ _ |- _ => destruct e; exact Possible end.
    }
  destruct (invert_root_condition _ _ _ _ _ _ WF p Member Root)
    as (X & l & sh & rd & arg & k & K & Owner & Law & Shape & Branch).
  pose (v0 := unAt (arg l Owner) eq_refl).
  pose (shows := on_roster R sh (fun _ => sh l Owner)).
  pose (reads := on_roster R rd (fun _ => rd l Owner)).
  pose (args := on_roster R arg (fun r => @Mk_At X l r (fun _ => v0))).
  pose (cont := on_roster R k (fun r _ => c r)).
  pose proof (on_roster_member R arg (fun r => @Mk_At X l r (fun _ => v0)) l
    Owner ND) as Base.
  change (args l = arg l Owner) in Base.
  refine (choice_body_head_paths model stores input R A c X l shows reads args
    cont
    Owner _ _ tc s tn n gs p _ Run Member Y kind path sender reader Static Site
      g Head).
  - intros r h. unfold shows,reads,args,cont.
    rewrite !(on_roster_member _ _ _ _ h ND). exact (Shape r h).
  - intros r h Ne. unfold shows,reads.
    rewrite (on_roster_member _ _ _ _ Owner ND), (on_roster_member _ _ _ _ h
      ND).
    apply Law. congruence.
  - split; [exact ND|]. exists (K v0).
  eapply structural_pointwise; [exact (Branch v0)|].
    intros r h. rewrite Base. unfold cont.
    rewrite (on_roster_member _ _ _ _ h ND). reflexivity.
Qed.
