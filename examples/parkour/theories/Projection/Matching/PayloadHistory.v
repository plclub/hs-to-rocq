From Stdlib Require Import Lists.List Logic.Eqdep_dec.
From ParkourTheories Require Import Projection.Matching.PrefixRelation
  Projection.FIFO.MessageRepresentation Choreography.Occurrences
  Choreography.PendingDeliveries Choreography.RoleSteps Choreography.Execution
  Network.Mailboxes Network.Endpoints Network.Execution Semantics.SharedState
  Semantics.LocalEffects Choreography.Results.OperandObservations
  Choreography.Histories.CursorHistories
  Choreography.Histories.TransitionArchive.
Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree.
Require Choreography.Choreo2.
Import ListNotations.
Import Choreography.Choreo2 (At, unAt, Choreo, Comm, Cond).
Arguments ContextHole {M E p X}.
Arguments ContextSeq {M E p X Y Z} _ _ _.
Arguments ContextLeft {M E p X Y Z} _ _.
Arguments ContextRight {M E p X Y Z} _ _.
Arguments erased_cursor {M E Store} model configured p {A} _.
Arguments archive {M E Store} model configured p {A} _.

Definition produced_message (m : message) : payload_event :=
  match m with Message X k o s d x sh => Produced k o s d (Operand X sh x) end.
Definition consumed_message (m : message) : payload_event :=
  match m with Message X k o s d x sh => Consumed k o s d (@show X sh x) end.

Section Observations.
Context {M E : Type -> Type} {S : Type}.
Variable model : local_model M E role S.
Variable R : list role.

(* The event batch is indexed by the actual source and network transitions.
   Only these constructors can introduce Produced, and their dictionaries and
   operands are precisely the ones in the exposed source syntax. *)
Inductive observed {p} :
    forall X, @cursor M E p X -> S -> list pending ->
      @source_action E S -> @cursor M E p X -> S -> list pending ->
      @action E S -> list message -> list message -> list payload_event -> Prop
        :=
| OLocal X o t s a t' s' ps gs :
    local_step (reply_local _ _ _ _ model) p t s a t' s' ->
    observed (At X p p) (RoleSteps.Local o t) s ps (LocalAction o
      a)
      (RoleSteps.Local o t') s' ps (Endpoints.Local a) gs
        gs []
| OSend X d o sh rd kl kd sl v sd (h : d <> p) s gs :
    observed (At X d p)
      (Code o (Perf (@Comm M p X p d sh rd kl kd sl v sd)))
      s (map pending_of gs) (SendAction X o p d (unAt v eq_refl))
      (Returned (off_at h)) s
      (map pending_of (gs ++ [Message X DataDelivery o p d (unAt v eq_refl)
        sh]))
      (Sent p d (SessionPaths.session_at o Choreography.Network.Root)
        (@show X sh (unAt v eq_refl)))
      gs (gs ++ [Message X DataDelivery o p d (unAt v eq_refl) sh])
      [Produced DataDelivery o p d (Operand X sh (unAt v eq_refl))]
| OReceive X l o sh rd kl kd sl v sd (h : l <> p) s gs gs' x w :
    delivery X DataDelivery o l p x rd gs w gs' ->
    observed (At X p p)
      (Code o (Perf (@Comm M p X l p sh rd kl kd sl v sd)))
      s (map pending_of gs) (ReceiveAction X o l p x)
      (Returned (here_at x)) s (map pending_of gs')
      (Received l p (SessionPaths.session_at o Choreography.Network.Root) w) gs
        gs'
      [Consumed DataDelivery o l p w]
| OAnnounce X Y o sh rd kl sl v (k : X -> Choreo M p Y) s gs :
    observed Y (Code o (Perf (@Cond M p X p Y sh rd kl sl v k)))
      s (map pending_of gs) (AnnounceAction X o p (unAt v eq_refl))
      (Code (child o ChoiceBody) (k (unAt v eq_refl))) s
      (map pending_of (gs ++ announcement_messages X o p (unAt v eq_refl) sh R))
      (Announced p (SessionPaths.session_at o Choreography.Network.Root)
        (@show X sh (unAt v eq_refl)))
      gs (gs ++ announcement_messages X o p (unAt v eq_refl) sh R)
      (map produced_message (announcement_messages X o p (unAt v eq_refl) sh R))
| OHear X Y l o sh rd kl sl v (k : X -> Choreo M p Y)
    (h : l <> p) s gs gs' x w :
    delivery X ChoiceDelivery o l p x rd gs w gs' ->
    observed Y (Code o (Perf (@Cond M p X l Y sh rd kl sl v k)))
      s (map pending_of gs) (HearAction X o l p x)
      (Code (child o ChoiceBody) (k x)) s (map pending_of gs')
      (Received l p (SessionPaths.session_at o Choreography.Network.Root) w) gs
        gs'
      [Consumed ChoiceDelivery o l p w]
| OSeq X Y o t t' (k : X -> Choreo M p Y) s ps a s' ps' na gs gs' ev :
    observed X t s ps a t' s' ps' na gs gs' ev ->
    observed Y (Seq o t k) s ps a (Seq o t' k) s' ps' na gs gs' ev
| OLeft X Y (f f' : @cursor M E p (X -> Y)) t s ps a s' ps' na gs gs' ev :
    observed (X -> Y) f s ps a f' s' ps' na gs gs' ev ->
    observed Y (Fork f t) s ps a (Fork f' t) s' ps' na gs gs' ev
| ORight X Y (f : @cursor M E p (X -> Y)) t t' s ps a s' ps' na gs gs' ev :
    observed X t s ps a t' s' ps' na gs gs' ev ->
    observed Y (Fork f t) s ps a (Fork f t') s' ps' na gs gs' ev
| OSilent X t u t' s ps a s' ps' na gs gs' ev :
    silent model X t u ->
    observed X u s ps a t' s' ps' na gs gs' ev ->
    observed X t s ps a t' s' ps' na gs gs' ev.

Theorem decorated_observed p X t s ps a t' s' ps' na gs gs' :
  @decorated M E S model R p X t s ps a t' s' ps' na gs gs' ->
  exists ev, @observed p X t s ps a t' s' ps' na gs gs' ev.
Proof.
  induction 1.
  - exists []. constructor. assumption.
  - eexists. apply OSend.
  - eexists. apply OReceive; eassumption.
  - eexists. apply OAnnounce.
  - eexists. eapply OHear; eassumption.
  - destruct IHdecorated as [ev Obs]. exists ev. apply OSeq. exact Obs.
  - destruct IHdecorated as [ev Obs]. exists ev. apply OLeft. exact Obs.
  - destruct IHdecorated as [ev Obs]. exists ev. apply ORight. exact Obs.
  - destruct IHdecorated as [ev O]. exists ev. eapply OSilent; eassumption.
Qed.

Theorem observed_decorated p X t s ps a t' s' ps' na gs gs' ev :
  @observed p X t s ps a t' s' ps' na gs gs' ev ->
  decorated model R X t s ps a t' s' ps' na gs gs'.
Proof.
  induction 1.
  - apply DLocal. assumption.
  - apply DSend.
  - eapply DReceive; eassumption.
  - apply DAnnounce.
  - eapply DHear; eassumption.
  - apply DSeq. assumption.
  - apply DLeft. assumption.
  - apply DRight. assumption.
  - eapply DSilent; eassumption.
Qed.

(* A source-syntax certificate at the actual primitive sender focus. *)
Inductive sender_site {p} :
    forall X, payload_event -> @cursor M E p X -> Prop :=
| SendSite X d o sh rd kl kd sl v sd :
    sender_site (At X d p)
      (Produced DataDelivery o p d (Operand X sh (unAt v eq_refl)))
      (Code o (Perf (@Comm M p X p d sh rd kl kd sl v sd)))
| AnnounceSite X Y o sh rd kl sl v (k : X -> Choreo M p Y) peer :
    In peer (filter (fun r => if role_eq_dec r p then false else true) R) ->
    sender_site Y
      (Produced ChoiceDelivery o p peer (Operand X sh (unAt v eq_refl)))
      (Code o (Perf (@Cond M p X p Y sh rd kl sl v k))).

Lemma sender_site_operand p X kind o sender recipient operand before :
  @sender_site p X (Produced kind o sender recipient operand) before ->
  sender = p /\
  exists code, before = Code o code /\ sender_operand code = Some operand.
Proof.
  intro Site. remember (Produced kind o sender recipient operand) as ev eqn:Eq
    in Site.
  destruct Site; inversion Eq; subst; split; [reflexivity| |reflexivity|].
  - eexists. split; [reflexivity|apply comm_sender_operand].
  - eexists. split; [reflexivity|].
    cbn [sender_operand].
    destruct (list_eq_dec BinNat.N.eq_dec sender sender) as [same|Ne];
      [|contradiction].
    rewrite (UIP_dec (list_eq_dec BinNat.N.eq_dec) same eq_refl). reflexivity.
Qed.

Definition production_focus p X t s ps a t' s' ps'
    (event : payload_event) : Prop :=
  exists Y (C : @cursor_context M E p Y X) before after,
    silent_prefix model t (plug C before) /\
    @primitive_action M E S model R p Y before s ps a after s' ps' /\
    t' = plug C after /\ sender_site Y event before.

Theorem observed_production_focus p X t s ps a t' s' ps' na gs gs' ev :
  @observed p X t s ps a t' s' ps' na gs gs' ev ->
  forall kind o sender recipient operand,
    In (Produced kind o sender recipient operand) ev ->
    production_focus p X t s ps a t' s' ps'
      (Produced kind o sender recipient operand).
Proof.
  induction 1; intros kind path sender recipient operand InEvent.
  - contradiction.
  - destruct InEvent as [Eq|No]; [|contradiction]. inversion Eq; subst.
    exists (At X recipient sender), ContextHole. do 2 eexists.
    split; [apply PrefixRefl|]. split.
    + rewrite map_app. cbn. apply PrimitiveSend.
    + split; [reflexivity|apply SendSite].
  - destruct InEvent as [Eq|No]; [discriminate|contradiction].
  - apply in_map_iff in InEvent. destruct InEvent as [m [Eq InM]].
    unfold announcement_messages in InM.
    apply in_map_iff in InM. destruct InM as [peer [Em InPeer]]. subst m.
    cbn in Eq. inversion Eq; subst.
    exists Y, ContextHole. do 2 eexists.
    split; [apply PrefixRefl|]. split.
    + rewrite map_app, announcement_pending. apply PrimitiveAnnounce.
    + split; [reflexivity|apply AnnounceSite; exact InPeer].
  - destruct InEvent as [Eq|No]; [discriminate|contradiction].
  - destruct (IHobserved _ _ _ _ _ InEvent) as (U & C & before & after & Sil &
    Act & Eq & Site).
    exists U, (ContextSeq o k C), before, after.
    split.
    + apply (silent_prefix_plug model p _ _ (ContextSeq o k ContextHole)).
    exact Sil.
    + split; [exact Act|]. split; [cbn; now rewrite Eq|exact Site].
  - destruct (IHobserved _ _ _ _ _ InEvent) as (U & C & before & after & Sil &
    Act & Eq & Site).
    exists U, (ContextLeft t C), before, after.
    split.
    + apply (silent_prefix_plug model p _ _ (ContextLeft t ContextHole)).
    exact Sil.
    + split; [exact Act|]. split; [cbn; now rewrite Eq|exact Site].
  - destruct (IHobserved _ _ _ _ _ InEvent) as (U & C & before & after & Sil &
    Act & Eq & Site).
    exists U, (ContextRight f C), before, after.
    split.
    + apply (silent_prefix_plug model p _ _ (ContextRight f ContextHole)).
    exact Sil.
    + split; [exact Act|]. split; [cbn; now rewrite Eq|exact Site].
  - destruct (IHobserved _ _ _ _ _ InEvent) as (U & C & before & after & Sil &
    Act & Eq & Site).
    exists U, C, before, after. split; [eapply PrefixCons; eassumption|].
    auto.
Qed.

Theorem observed_consumption p X t s ps a t' s' ps' na gs gs' ev :
  @observed p X t s ps a t' s' ps' na gs gs' ev ->
  forall kind o sender recipient w,
    In (Consumed kind o sender recipient w) ev ->
    recipient = p /\
    na = Received sender recipient
      (SessionPaths.session_at o Choreography.Network.Root) w /\
    exists Y (x : Y),
      (kind = DataDelivery /\ a = ReceiveAction Y o sender recipient x) \/
      (kind = ChoiceDelivery /\ a = HearAction Y o sender recipient x).
Proof.
  induction 1; intros kind path sender recipient wire InEvent; try (eapply
    IHobserved; exact InEvent).
  - contradiction.
  - destruct InEvent as [Eq|No]; [discriminate|contradiction].
  - destruct InEvent as [Eq|No]; [|contradiction]. inversion Eq; subst.
    repeat split; try reflexivity. exists X, x. left. auto.
  - apply in_map_iff in InEvent. destruct InEvent as [m [Eq _]].
    destruct m. discriminate.
  - destruct InEvent as [Eq|No]; [|contradiction]. inversion Eq; subst.
    repeat split; try reflexivity. exists X, x. right. auto.
Qed.

Theorem production_focus_sender p X t s ps a t' s' ps'
    kind o sender recipient operand :
  production_focus p X t s ps a t' s' ps'
    (Produced kind o sender recipient operand) ->
  sender = p /\
  exists Y (C : @cursor_context M E p Y X) code after,
    silent_prefix model t (plug C (Code o code)) /\
    primitive_action model R Y (Code o code) s ps a after s' ps' /\
    t' = plug C after /\ sender_operand code = Some operand.
Proof.
  intros (Y & C & before & after & Sil & Act & End & Site).
  destruct (sender_site_operand _ _ _ _ _ _ _ _ Site)
    as [Owner [code [Before Operand]]].
  split; [exact Owner|]. exists Y, C, code, after. subst before. auto.
Qed.

(* Replay can persist the very same sender focus. The archived event retains
   its actual primitive proof and the original dictionary-bearing syntax. *)
Theorem production_recorded_in_replay p X t s ps a t' s' ps'
    kind o sender recipient operand start tr cut :
  production_focus p X t s ps a t' s' ps'
    (Produced kind o sender recipient operand) ->
  cut_history model R p start tr cut ->
  erased_cursor model R p cut = t ->
  exists next,
    cut_history model R p start (tr ++ [a]) next /\
    erased_cursor model R p next = t' /\
    exists Y (C : @cursor_context M E p Y X) code after
      (Prim : primitive_action model R Y (Code o code) s ps a after s' ps'),
      sender_operand code = Some operand /\
      In (ActionEvent model R p Y (Code o code) after s ps a s' ps' Prim)
        (lookup model R p o (archive model R p next)).
Proof.
  intros Focus Hist Erase.
  destruct (production_focus_sender _ _ _ _ _ _ _ _ _ _ _ _ _ _ Focus)
    as [_ (Y & C & code & after & Sil & Prim & End & Operand)].
  rewrite <- Erase in Sil.
  destruct (cut_after_silent_prefix model R p _ _ _ _ _ Hist Sil)
    as ([u tree] & Mid & EU & Ext).
  cbn in EU. subst u. cbn in Mid.
  eexists. split.
  - eapply CutAction with (step := Prim). exact Mid.
  - split.
    + cbn. symmetry. exact End.
    + exists Y, C, code, after, Prim. split; [exact Operand|].
      cbn [archive event_route position]. apply insert_here.
Qed.
End Observations.

(* Queue conservation, independent of machine syntax. The observation theorem
   below establishes this summary from actual decorated transitions. *)
Inductive payload_change : list message -> list message -> list payload_event ->
  Prop :=
| ChangeNone gs : payload_change gs gs []
| ChangeProduce gs added :
    payload_change gs (gs ++ added) (map produced_message added)
| ChangeConsume pre m post :
    payload_change (pre ++ m :: post) (pre ++ post) [consumed_message m].

Lemma observed_change {M E S} model R p X t s ps a t' s' ps' na gs gs' ev :
  @observed M E S model R p X t s ps a t' s' ps' na gs gs' ev ->
  payload_change gs gs' ev.
Proof.
  induction 1; try assumption.
  - apply ChangeNone.
  - exact (ChangeProduce gs [Message X DataDelivery o p d (unAt v eq_refl) sh]).
  - destruct H. apply (ChangeConsume pre (Message X DataDelivery o l p x sh0)
    post).
  - apply ChangeProduce.
  - destruct H. apply (ChangeConsume pre (Message X ChoiceDelivery o l p x sh0)
    post).
Qed.

Definition past_ok (past : list payload_event) (gs : list message) : Prop :=
  (forall m, In m gs -> In (produced_message m) past) /\
  forall kind o sender receiver w, In (Consumed kind o sender receiver w) past
    ->
    past_receive past kind o sender receiver w.

Lemma past_receive_append past extra kind o sender receiver w :
  past_receive past kind o sender receiver w ->
  past_receive (past ++ extra) kind o sender receiver w.
Proof.
  intros (a & before & between & after & Eq & Wire).
  exists a, before, between, (after ++ extra). split; [|exact Wire].
  rewrite Eq. rewrite <- !app_assoc. cbn [List.app].
  repeat rewrite <- app_assoc. reflexivity.
Qed.

Lemma produced_last past m :
  In (produced_message m) past ->
  match consumed_message m with Consumed kind o sender receiver w =>
    past_receive (past ++ [consumed_message m]) kind o sender receiver w
  | _ => True end.
Proof.
  destruct m as [X kind o sender receiver x sh]. cbn.
  intro H. apply in_split in H. destruct H as [before [between Eq]].
  exists (Operand X sh x), before, between, []. split; [|reflexivity].
  rewrite Eq. rewrite <- !app_assoc. cbn [List.app].
  repeat rewrite <- app_assoc. reflexivity.
Qed.

Theorem change_preserves_past past gs gs' ev :
  past_ok past gs -> payload_change gs gs' ev -> past_ok (past ++ ev) gs'.
Proof.
  intros [Pending Receives] Change. destruct Change.
  - rewrite app_nil_r. split; assumption.
  - split.
    + intros m H. apply in_app_or in H. apply in_or_app.
      destruct H as [Old|New]; [left; apply Pending; exact Old|].
      right. apply in_map. exact New.
    + intros kind o sender receiver w H.
      apply in_app_or in H. destruct H as [Old|New].
      * apply past_receive_append. apply Receives. exact Old.
      * apply in_map_iff in New. destruct New as [m [Eq _]]. destruct m.
      discriminate.
  - split.
    + intros g H. apply in_or_app. left. apply Pending.
      apply in_app_or in H. apply in_or_app. destruct H as [Pre|Post].
      * now left.
      * right. now right.
    + intros kind o sender receiver w H.
      apply in_app_or in H. destruct H as [Old|New].
      * apply past_receive_append. apply Receives. exact Old.
      * destruct New as [Eq|No]; [|contradiction].
        destruct m as [X k path s d x sh]. cbn in Eq.
        inversion Eq; subst.
        apply (produced_last past (Message X kind o sender receiver x sh)).
        apply Pending. apply in_or_app. right. now left.
Qed.

Section History.
Context {M E : Type -> Type} {Store Input : Type}.
Variable model : local_model M E role (Store * Input).
Variable stores : role -> Store.
Variable input : Input.
Variable R : list role.
Variable A : role -> Type.
Variable c : forall p, Choreo M p (A p).

(* Same scheduled-role and typed-step indices as paired_step, with the
   payload batch attached to that very operational transition. *)
Inductive paired_observed
    (s : @Choreography.Execution.configuration M E ((role -> Store) * Input) A)
    (n : @Network.Execution.configuration M E ((role -> Store) * Input)) gs :
    @source_action E ((role -> Store) * Input) ->
    @Choreography.Execution.configuration M E ((role -> Store) * Input) A ->
    @action E ((role -> Store) * Input) ->
    @Network.Execution.configuration M E ((role -> Store) * Input) ->
    list message -> list
      payload_event -> Prop :=
| ObservedPair p pre post t t' s' n' a na gs' ev :
    In p R ->
    endpoints n = pre ++ Endpoint (A p) p t :: post ->
    endpoints n' = pre ++ Endpoint (A p) p t' :: post ->
    observed (shared_model model) R (A p) (positions s p)
      (Choreography.Execution.shared_store s)
      (deliveries s) a (positions s' p) (Choreography.Execution.shared_store s')
      (deliveries s') na gs gs' ev ->
    (forall r, r <> p -> positions s r = positions s' r) ->
    Endpoints.step (shared_model model) R p (A p) t (mailboxes n)
      (Network.Execution.shared_store
      n)
      na t' (mailboxes n') (Network.Execution.shared_store n') ->
    paired_observed s n gs a s' na n' gs' ev.

Lemma paired_has_observation s n gs a s' na n' gs' :
  paired_step model R A s n gs a s' na n' gs' ->
  exists ev, paired_observed s n gs a s' na n' gs' ev.
Proof.
  destruct 1.
  match goal with
  | D : @decorated ?m ?e ?st ?md ?rs ?p ?X ?t ?s ?ps ?a ?u ?s1 ?ps1 ?na ?gs ?gs1
    |- _ =>
    destruct (decorated_observed md rs p X t s ps a u s1 ps1 na gs gs1 D) as [ev
      Obs]
  end.
  exists ev. econstructor; eassumption.
Qed.

Lemma observation_is_paired s n gs a s' na n' gs' ev :
  paired_observed s n gs a s' na n' gs' ev ->
  paired_step model R A s n gs a s' na n' gs'.
Proof.
  destruct 1. econstructor; try eassumption.
  eapply observed_decorated. eassumption.
Qed.

Inductive payload_history :
    list (@source_action E ((role -> Store) * Input)) ->
    @Choreography.Execution.configuration M E ((role -> Store) * Input) A ->
    list (@action E ((role -> Store) * Input)) ->
    @Network.Execution.configuration M E ((role -> Store) * Input) ->
    list message -> list payload_event -> Prop :=
| PayloadInitial :
    payload_history [] (PrefixRelation.source_initial stores input A c)
      [] (PrefixRelation.network_initial stores input R A c) [] []
| PayloadSnoc tc s tn n gs past a s' na n' gs' ev :
    payload_history tc s tn n gs past ->
    paired_observed s n gs a s' na n' gs' ev ->
    state_match model R A s' n' gs' ->
    payload_history (tc ++ [a]) s' (tn ++ [na]) n' gs' (past ++ ev).

Theorem matched_payload_history tc s tn n gs :
  matched_prefix model stores input R A c tc s tn n gs ->
  exists past, payload_history tc s tn n gs past.
Proof.
  induction 1.
  - exists []. constructor.
  - destruct IHmatched_prefix as [past Hist].
    destruct (paired_has_observation _ _ _ _ _ _ _ _ H0) as [ev Obs].
    exists (past ++ ev). eapply PayloadSnoc; eassumption.
Qed.

Theorem history_is_matched tc s tn n gs past :
  payload_history tc s tn n gs past ->
  matched_prefix model stores input R A c tc s tn n gs.
Proof.
  induction 1; [constructor|].
  eapply PrefixSnoc; [exact IHpayload_history| |eassumption].
  eapply observation_is_paired. eassumption.
Qed.

Theorem history_past_ok tc s tn n gs past :
  payload_history tc s tn n gs past -> past_ok past gs.
Proof.
  induction 1.
  - split; intros; contradiction.
  - eapply change_preserves_past; [exact IHpayload_history|].
    destruct H0. eapply observed_change. eassumption.
Qed.

(* A past production is justified by an actual earlier matched machine
   prefix and its actual next paired step, not an arbitrary Produced list. *)
Definition actual_production (event : payload_event) : Prop :=
  exists tc s tn n gs a s' na n' gs' ev,
    matched_prefix model stores input R A c tc s tn n gs /\
    paired_observed s n gs a s' na n' gs' ev /\ In event ev.

Theorem history_production tc s tn n gs past :
  payload_history tc s tn n gs past ->
  forall kind o sender recipient operand,
    In (Produced kind o sender recipient operand) past ->
    actual_production (Produced kind o sender recipient operand).
Proof.
  induction 1; intros kind o sender recipient operand Member; [contradiction|].
  apply in_app_or in Member. destruct Member as [Old|New].
  - eapply IHpayload_history. exact Old.
  - do 11 eexists. split.
    + eapply history_is_matched. exact H.
    + split; eassumption.
Qed.

Theorem actual_production_focus kind o sender recipient operand :
  actual_production (Produced kind o sender recipient operand) ->
  exists tc s tn n gs a s' na n' gs' ev p,
    matched_prefix model stores input R A c tc s tn n gs /\
    paired_observed s n gs a s' na n' gs' ev /\
    In p R /\
    production_focus (shared_model model) R p (A p) (positions s p)
      (Choreography.Execution.shared_store
      s)
      (deliveries s) a (positions s' p) (Choreography.Execution.shared_store s')
        (deliveries s')
      (Produced kind o sender recipient operand).
Proof.
  intros (tc & s & tn & n & gs & a & s' & na & n' & gs' & ev & Prefix & Obs &
    Member).
  exists tc, s, tn, n, gs, a, s', na, n', gs', ev.
  destruct Obs.
  eexists. split; [exact Prefix|]. split.
  - econstructor; eassumption.
  - split; [eassumption|]. eapply observed_production_focus; eassumption.
Qed.

Theorem matched_has_actual_past tc s tn n gs :
  matched_prefix model stores input R A c tc s tn n gs ->
  exists past,
    payload_history tc s tn n gs past /\
    (forall kind o sender receiver w,
      In (Consumed kind o sender receiver w) past ->
      past_receive past kind o sender receiver w) /\
    (forall m, In m gs -> In (produced_message m) past) /\
    (forall kind o sender receiver operand,
      In (Produced kind o sender receiver operand) past ->
      actual_production (Produced kind o sender receiver operand)).
Proof.
  intro Prefix. destruct (matched_payload_history _ _ _ _ _ Prefix) as [past
    Hist].
  exists past. split; [exact Hist|].
  destruct (history_past_ok _ _ _ _ _ _ Hist) as [Pending Receives].
  split; [exact Receives|]. split; [exact Pending|].
  eapply history_production. exact Hist.
Qed.
End History.
