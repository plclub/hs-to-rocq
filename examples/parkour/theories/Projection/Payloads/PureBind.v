From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Choreography.Occurrences
  Choreography.RoleSteps Choreography.Execution Network.Mailboxes
  Projection.Matching.PrefixRelation Projection.FIFO.MessageRepresentation
  Choreography.ReceiveSites Projection.Payloads.StaticPackets
  Projection.Occurrences.EnteredCode Projection.Payloads.RootPackets
  Choreography.WellFormedness Semantics.LocalEffects Semantics.SharedState
  Choreography.Results.OperandObservations Projection.Matching.PayloadHistory
  Choreography.Histories.CursorHistories Projection.SessionPaths
  Choreography.Histories.SyntaxDecomposition
  Choreography.Histories.PureBindDescent Projection.Payloads.SelectedBranch
  Choreography.Results.FiniteSelection Choreography.Histories.TransitionArchive.
Require Import Choreography.Choreo2 Control.Monad.Tree Parkour.Codec
  Parkour.Symbol.
Import ListNotations.
Local Arguments positions {M E Store A} _ _.

Section SyntaxAnchor.
Context {M E : Type -> Type} {S : Type}.
Variable m : local_model M E role S.
Variable R : list role.
Variable p : role.
Variable A : Type.
Variable base : occurrence.
Variable body : Choreo M p A.

Lemma relative_cursor_history B start tr t :
  cursor_history m R start tr t ->
  @relative_cursor M E p A base body B start ->
  relative_cursor p A base body t.
Proof.
  induction 1; intro Good; [exact Good| |].
  - eapply relative_silent; [apply silent_plug; eapply primitive_is_silent;
    exact H0|auto].
  - eapply relative_step; [apply role_step_plug; eapply primitive_is_role_step;
    exact H0|auto].
Qed.

Lemma syntax_relative_cursor B o code t :
  syntax_cut m R p B o code t ->
  relative_node p A base body o code -> relative_cursor p A base body t.
Proof.
  intro Cut. induction Cut; intro Good; cbn [relative_cursor]; try exact I.
  - exact Good.
  - eapply relative_cursor_history; [exact H0|exact Good].
  - pose proof (relative_silent m p A base body _ _ _
      (SApp m _ _ _ _ _) Good) as Children.
    cbn [relative_cursor] in Children.
    split; [apply IHCut1|apply IHCut2]; tauto.
  - pose proof (relative_silent m p A base body _ _ _
      (SBind m _ _ _ _ _) Good) as Prefix.
    cbn [relative_cursor] in Prefix. split; [tauto|apply IHCut; tauto].
  - apply IHCut2. eapply relative_child; [auto|].
    eapply relative_prefix; exact Good.
  - apply IHCut. eapply relative_child; [auto|].
    eapply relative_prefix; exact Good.
Qed.
End SyntaxAnchor.

Section PureFocus.
Context {M E : Type -> Type} {S : Type}.
Variable m : local_model M E role S.
Variable R : list role.
Variable p : role.
Variable X A : Type.
Variable value : X.
Variable k : X -> Choreo M p A.

Fixpoint pure_body_codes {B} (t : @cursor M E p B) : Prop :=
  match t with
  | Code o code => forall path, o = BindBody :: path -> static_path path ->
      choreo_at_static_path path (k value) = Some (existT _ _ code)
  | Seq _ t _ => pure_body_codes t
  | Fork f x => pure_body_codes f /\ pure_body_codes x
  | _ => True
  end.

Lemma relative_body_codes B (t : @cursor M E p B) :
  relative_cursor p A [BindBody] (k value) t -> pure_body_codes t.
Proof.
  induction t; cbn [relative_cursor pure_body_codes]; try tauto.
  intros (path & Eq & Origin) rest Same Static.
  cbn in Eq. rewrite Eq in Same. injection Same as Same. subst rest.
  specialize (Origin []). rewrite app_nil_r in Origin.
  exact (eq_sym (Origin Static)).
Qed.

Lemma pure_body_codes_focus B Y (C : @cursor_context M E p B Y) t :
  pure_body_codes (plug C t) -> pure_body_codes t.
Proof. induction C; cbn; intros Good; first [exact Good|apply IHC; tauto]. Qed.

Lemma pure_bind_syntax_codes t :
  syntax_cut m R p A [] (Bind (Pure value) k) t -> pure_body_codes t.
Proof.
  intro Cut.
  destruct (syntax_cut_decomposition m R p _ _ _ _ Cut)
    as [Initial|[(pre & Prefix & Waiting)|(x & b & Prefix & Body & End)]].
  - subst t. cbn [pure_body_codes]. discriminate.
  - subst t. cbn [pure_body_codes].
    destruct (pure_cut_shape m R p X [BindPrefix] _ pre Prefix) as
      [Initial|Done].
    + subst pre. cbn [pure_body_codes]. discriminate.
    + subst pre. exact I.
  - subst t.
    assert (Value : x = value).
    { eapply pure_cut_returned; [exact Prefix|reflexivity]. }
    subst x. apply relative_body_codes.
    eapply syntax_relative_cursor; [exact Body|].
    exists []; cbn. split; [reflexivity|]. intros; reflexivity.
Qed.

Lemma pure_bind_focus_original B (C : @cursor_context M E p B A) code path tr t
  :
  cursor_history m R (Code [] (Bind (Pure value) k)) tr t ->
  silent_prefix m t (plug C (Code (BindBody :: path) code)) ->
  static_path path ->
  choreo_at_static_path path (k value) = Some (existT _ B code).
Proof.
  intros History Silent Static.
  pose proof (history_after_silent_prefix m R p A _ _ _ _ History Silent) as
    Full.
  pose proof (code_history_has_syntax_cut m R p A _ _ _ _ Full) as Cut.
  pose proof (pure_bind_syntax_codes _ Cut) as Good.
  exact (pure_body_codes_focus _ _ C _ Good path eq_refl Static).
Qed.
End PureFocus.

Section Originals.
Context {M E Store Input} (model : local_model M E role (Store * Input))
  (stores : role -> Store) (input : Input) (R : list role) (A : role -> Type)
  (c body : forall p, Choreo M p (A p)).
Local Notation sm := (shared_model model).
Hypothesis Shape : forall p, In p R ->
  exists X (value : X) (k : X -> Choreo M p (A p)),
    c p = Bind (Pure value) k /\ body p = k value.

Lemma pure_bind_inner_code tc s tn n gs p B (C : @cursor_context M E p B (A p))
    code path :
  matched_prefix model stores input R A c tc s tn n gs -> In p R ->
  static_path path ->
  silent_prefix sm (positions s p) (plug C (Code (BindBody :: path) code)) ->
  choreo_at_static_path path (body p) = Some (existT _ B code).
Proof.
  intros Prefix Member Static Silent.
  destruct (Shape p Member) as (X & value & k & Root & Body).
  pose proof (initial_actor_history sm R A c (stores,input) tc s
    (prefix_source_run model stores input R A c _ _ _ _ _ Prefix) p) as History.
  rewrite Root in History. rewrite Body.
  eapply pure_bind_focus_original; eassumption.
Qed.

Lemma pure_bind_inner_packet tc s tn n gs past Y kind path sender recipient
    (v : Y) dict :
  payload_history model stores input R A c tc s tn n gs past ->
  In (Message Y kind (BindBody :: path) sender recipient v dict) gs ->
  static_path path ->
  outgoing_from_lookup (choreo_at_static_path path (body sender)) (BindBody ::
    path) recipient =
    Some (Message Y kind (BindBody :: path) sender recipient v dict).
Proof.
  intros History Member Static.
  destruct (actual_production_focus model stores input R A c _ _ _ _ _
    (history_production model stores input R A c _ _ _ _ _ _ History kind
      (BindBody :: path) sender recipient (Operand Y dict v)
      (proj1 (history_past_ok model stores input R A c _ _ _ _ _ _ History) _
        Member)))
    as (tc0 & s0 & tn0 & n0 & gs0 & a & s1 & na & n1 & gs1 & ev & who &
      Prefix & Pair & InR & Focus).
  destruct (production_focus_sender _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Focus) as
    [Eq _].
  subst who. destruct Focus as (B & C & before & after & Silent & Prim & End &
    Site).
  pose proof (focus_packet _ _ _ _ _ Site) as Packet.
  destruct (sender_site_operand _ _ _ _ _ _ _ _ _ Site) as [_ [code [-> _]]].
  rewrite (pure_bind_inner_code _ _ _ _ _ _ _ C code path Prefix InR Static
    Silent).
  exact Packet.
Qed.

Theorem pure_bind_body_originals tc s tn n gs p :
  well_formed R M A body ->
  matched_prefix model stores input R A c tc s tn n gs -> In p R ->
  forall Y kind path sender reader, static_path path ->
  receive_site sm p (A p) (positions s p) Y kind (BindBody :: path) sender
    reader ->
  exists (v : Y) (dict : Show Y),
    (forall g, In g gs ->
      message_key g = (sender,p,session_at (BindBody :: path)
        Choreography.Network.Root) ->
      message_path g = BindBody :: path ->
      g = Message Y kind (BindBody :: path) sender p v dict) /\
    wire_law dict reader.
Proof.
  intros [_ [Q WF]] Prefix Member Y kind path sender reader Static
    (B & C & focus & Silent & Site).
  destruct (focus_reader _ _ _ _ _ _ Site) as (code & -> & Reads).
  pose proof (pure_bind_inner_code _ _ _ _ _ _ _ C code path Prefix Member
    Static Silent)
    as Receiver.
  pose proof (family_static_reader WF path (BindBody :: path) p Member (fun r h
    => h)
    (fun r _ => outgoing_from_lookup (choreo_at_static_path path (body r))
      (BindBody :: path) p)
    (fun _ _ => eq_refl)) as Reader.
  cbn beta in Reader. rewrite Receiver in Reader.
  destruct (Reads _ Reader) as (v & dict & InS & Origin & Law).
  exists v, dict. split; [|exact Law].
  intros [T jk b from dest x sw] InG Key Path.
  cbn [message_key message_path] in Key, Path. subst b; injection Key as -> ->.
  destruct (matched_payload_history model stores input R A c _ _ _ _ _ Prefix)
    as [past History].
  pose proof (pure_bind_inner_packet _ _ _ _ _ _ T jk path sender p x sw
    History InG Static). congruence.
Qed.
End Originals.

Definition root_pure {M p B} (code : Choreo M p B) : Prop :=
  match code with Pure _ => True | _ => False end.

Definition root_pure_bind {M p B} (code : Choreo M p B) : Prop :=
  match code with Bind t _ => root_pure t | _ => False end.

Lemma invert_root_pure R M S A family Q :
  structural R M S A family Q ->
  forall p mem, root_pure (family p mem) ->
  exists value : values A S,
    (forall r s, family r s = Pure (value r s)) /\ Q = pure_results value.
Proof.
  destruct 1; intros peer mem Root;
    match goal with Shape : forall p s, ?prog p s = _ |- _ =>
      rewrite (Shape peer mem) in Root end;
    cbn [root_pure] in Root; try contradiction.
  exists x. auto.
Qed.

Lemma invert_root_pure_bind R M S B family Q :
  structural R M S B family Q ->
  forall p mem, root_pure_bind (family p mem) ->
  exists A (value : values A S)
    (k : forall r, S r -> A r -> Choreo M r (B r)) K,
    (forall r s, family r s = Bind (Pure (value r s)) (k r s)) /\
    (forall D (x : values A D) (inc : includes D S),
      pure_results value D x ->
      structural R M D B (fun r d => k r (inc r d) (x r d)) (K D x)).
Proof.
  destruct 1; intros peer mem Root;
    match goal with Shape : forall p s, ?prog p s = _ |- _ =>
      rewrite (Shape peer mem) in Root end;
    cbn [root_pure_bind] in Root; try contradiction.
  destruct (invert_root_pure _ _ _ _ _ _ H peer mem Root)
    as (value & Pure & Result).
  subst P. exists A,value,k,K.
  split; [intros; rewrite H1, Pure; reflexivity|exact H0].
Qed.

(* The hypothesis only identifies this concrete dynamic case. It does not
   impose a result-family, entry, replay, or completion premise on the caller.
   *)
Theorem source_originals_pure_bind_static {M E Store Input}
    (model : local_model M E role (Store * Input)) stores input R A c tc s tn n
      gs :
  well_formed R M A c ->
  matched_prefix model stores input R A c tc s tn n gs ->
  forall p, In p R -> root_pure_bind (c p) ->
  forall Y kind path sender reader, static_path path ->
  receive_site (shared_model model) p (A p) (positions s p)
    Y kind (BindBody :: path) sender reader ->
  exists (v : Y) (dict : Show Y),
    (forall g, In g gs ->
      message_key g = (sender,p,session_at (BindBody :: path)
        Choreography.Network.Root) ->
      message_path g = BindBody :: path ->
      g = Message Y kind (BindBody :: path) sender p v dict) /\
    wire_law dict reader.
Proof.
  intros [ND [Q WF]] Prefix p Member Root.
  destruct (invert_root_pure_bind _ _ _ _ _ _ WF p Member Root)
    as (B & value & k & K & Shape & Branch).
  pose (body := on_roster R (fun r d => k r d (value r d)) c).
  assert (Body : well_formed R M A body).
  { split; [exact ND|]. exists (K (fun r => In r R) value).
    eapply structural_pointwise.
    - apply (Branch (fun r => In r R) value (fun r d => d)).
      split; [intros r d; exact d|].
      intros r d e. now rewrite (roster_member_unique R ND r d e).
    - intros r d. unfold body. rewrite (on_roster_member _ _ _ _ d ND).
    reflexivity. }
  eapply (pure_bind_body_originals model stores input R A c body); try
    eassumption.
  intros r d. exists (B r), (value r d), (k r d).
  split; [exact (Shape r d)|].
  unfold body.
  exact (@on_roster_member (fun r => Choreo M r (A r)) R
    (fun r d => k r d (value r d)) c r d ND).
Qed.

Print Assumptions source_originals_pure_bind_static.
