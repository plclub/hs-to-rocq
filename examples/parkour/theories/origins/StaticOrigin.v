From Stdlib Require Import Lists.List.
Require Import DeadlockRootOrigin DeadlockCutSafety DeadlockSameHistory
  DeadlockPast
  DeadlockState DeadlockSource DeadlockNetwork DeadlockReplay DeadlockCoherence
  DeadlockMatch DeadlockMessages DeadlockLocal DeadlockWellFormed DeadlockOrder
    DeadlockPlayedValues
  Control.Monad.Tree Choreography.Choreo2 Parkour.Symbol Parkour.Codec.
Import ListNotations.

Definition static_path (path : occurrence) :=
  ~ In ChoiceBody path /\ ~ In BindBody path.

Definition packed M p := { A : Type & Choreo M p A }.
Fixpoint descend {M p A} (path : occurrence) (c : Choreo M p A) :
    option (packed M p) :=
  match path with
  | [] => Some (existT _ A c)
  | e :: rest =>
    match e, c with
    | AppFunction, App f _ => descend rest f
    | AppArgument, App _ t | BindPrefix, Bind t _ => descend rest t
    | _, _ => None end
  end.

Section Static.
Context {M E : Type -> Type} {S : Type}.
Variable m : local_model M E role S.
Variable R : list role.
Variable p : role.
Variable result : Type.
Variable original : Choreo M p result.

Definition anchored {B} o (c : Choreo M p B) :=
  forall rest, static_path (o ++ rest) ->
    descend rest c = descend (o ++ rest) original.

Fixpoint anchored_cursor {B} (t : @cursor M E p B) :=
  match t with
  | Code o c => anchored o c
  | Seq _ u _ => anchored_cursor u
  | Fork f x => anchored_cursor f /\ anchored_cursor x
  | _ => True end.

Lemma dynamic_child e o B (c : Choreo M p B) :
  (e = BindBody \/ e = ChoiceBody) -> anchored (child o e) c.
Proof.
  intros D rest [C Bdy]. exfalso. destruct D as [D|D]; subst e;
    [apply Bdy|apply C]; unfold child; rewrite <- app_assoc;
    apply in_or_app; right; now left.
Qed.

Lemma silent_anchor B t u : @silent M E S m p B t u ->
  anchored_cursor t -> anchored_cursor u.
Proof.
  induction 1; cbn [anchored_cursor]; try tauto.
  - intros Root rest. unfold child; rewrite <- app_assoc.
    apply (Root (BindPrefix :: rest)).
  - intro Root. split; intros rest; unfold child; rewrite <- app_assoc.
    + apply (Root (AppFunction :: rest)).
    + apply (Root (AppArgument :: rest)).
  - intros _. apply dynamic_child; auto.
Qed.

Lemma step_anchor B t st q a u st' q' :
  @role_step M E S m R p B t st q a u st' q' ->
  anchored_cursor t -> anchored_cursor u.
Proof.
  induction 1; cbn [anchored_cursor]; try tauto;
    try (intros _; apply dynamic_child; auto).
  intro Ht. apply IHrole_step. eapply silent_anchor; eassumption.
Qed.

Lemma anchored_focus B A (C : @cursor_context M E p B A) t :
  anchored_cursor (plug C t) -> anchored_cursor t.
Proof. induction C; cbn; intros H; first [exact H|apply IHC; tauto]. Qed.

Lemma run_anchor A start tc finish :
  @DeadlockSource.crun M E S m R A start tc finish ->
  anchored_cursor (DeadlockSource.positions start p) ->
  anchored_cursor (DeadlockSource.positions finish p).
Proof.
  induction 1; intro Init; [exact Init|].
  destruct H0 as [r act u Hr Step Frame]. destruct (role_eq_dec r p) as [->|Ne].
  - eapply step_anchor; [exact Step|auto].
  - rewrite <- Frame by congruence; auto.
Qed.

Lemma at_static_focus B A o (code : Choreo M p B) (C : @cursor_context M E p B
  A) t :
  anchored_cursor t -> silent_prefix m t (plug C (Code o code)) ->
  static_path o -> descend o original = Some (existT _ B code).
Proof.
  intros Good Sil Static.
  assert (End : anchored_cursor (plug C (Code o code))).
  { clear -Good Sil. induction Sil; [exact Good|].
  apply IHSil; eapply silent_anchor; eassumption. }
  specialize (anchored_focus _ _ C _ End []) as At.
  rewrite app_nil_r in At. exact (eq_sym (At Static)).
Qed.
End Static.

Definition output {M p} (t : option (packed M p)) o recipient :=
  match t with Some (existT _ _ code) => outgoing code o recipient | None =>
    None end.

Lemma syntactic_packet {M E Store Input}
    (model : local_model M E role (Store * Input)) stores input R A c tc s tn n
      gs past
    X kind path sender recipient (x : X) sh :
  payload_history model stores input R A c tc s tn n gs past ->
  In (Message X kind path sender recipient x sh) gs -> static_path path ->
  output (descend path (c sender)) path recipient =
    Some (Message X kind path sender recipient x sh).
Proof.
  intros H Member Static. pose proof (history_production model stores input R A
    c
    _ _ _ _ _ _ H kind path sender recipient (Operand X sh x)
    (proj1 (history_past_ok model stores input R A c _ _ _ _ _ _ H) _ Member))
      as Past.
  destruct (actual_production_focus model stores input R A c _ _ _ _ _ Past)
    as (tc0 & s0 & tn0 & n0 & gs0 & a & s1 & na & n1 & gs1 & ev & who & Prefix &
      Pair & Hin & Focus).
  destruct (production_focus_sender _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Focus) as
    [Eq _].
  subst who. destruct Focus as (Y & C & before & after & Sil & Prim & End &
    Site).
  pose proof (focus_packet _ _ _ _ _ Site) as Packet.
  destruct (sender_site_operand _ _ _ _ _ _ _ _ _ Site) as [_ [code [-> _]]].
  pose proof (prefix_source_run model stores input R A c _ _ _ _ _ Prefix) as
    Run.
  pose proof (run_anchor (shared_model model) R sender _ (c sender) _ _ _ _ Run
    (fun _ _ => eq_refl)) as Init.
  rewrite (at_static_focus (shared_model model) sender _ (c sender)
    _ _ _ _ _ _ Init Sil Static). exact Packet.
Qed.

Definition read_at {M p} (t : option (packed M p))
    (G : forall X, delivery_kind -> role -> Read X -> Prop) :=
  match t with Some (existT _ _ code) => reader_contract code G | None => True
    end.

(* On these paths descent only needs the source family supplied to structural:
   App contributes both children, Bind its prefix. No prefix return or choice
   is guessed, and the occurrence carried by the message stays absolute. *)
Lemma family_static_reader {M R S A c Q} :
  structural R M S A c Q ->
  forall path absolute peer (member : S peer) (all : forall r, In r R -> S r)
    (emit : forall r, S r -> option message),
    (forall r s, output (descend path (c r s)) absolute peer = emit r s) ->
    read_at (descend path (c peer member)) (fun X kind l rd =>
      exists (v : X) (sh : Show X) (s : S l),
        emit l s = Some (Message X kind absolute l peer v sh) /\ wire_law sh
          rd).
Proof.
  induction 1; intros [|edge path] absolute peer mem all emit Sender;
    match goal with F : forall p s, _ p s = _ |- _ =>
      rewrite (F peer mem); pose proof (fun r s =>
        eq_ind _ (fun code => output (descend _ code) absolute peer = emit r s)
          (Sender r s) _ (F r s)) as Here end;
    cbn [descend read_at reader_contract] in *; try exact I;
    try (destruct edge; cbn [descend read_at] in *; try exact I;
         solve [eauto]).
  - intros <- Ne. specialize (all l H) as atL.
    exists (Choreography.Choreo2.unAt (x l atL) eq_refl), (sh l atL), atL.
    rewrite <- Here. cbn [output outgoing].
    destruct (role_eq_dec l l) as [e|N]; [|contradiction].
    rewrite (Eqdep_dec.UIP_dec role_eq_dec e eq_refl).
    split; [reflexivity|now apply H1].
  - intro Ne. specialize (all l H) as atL.
    exists (Choreography.Choreo2.unAt (x l atL) eq_refl), (sh l atL), atL.
    rewrite <- Here. cbn [output outgoing].
    destruct (role_eq_dec l l) as [e|N]; [|contradiction].
    rewrite (Eqdep_dec.UIP_dec role_eq_dec e eq_refl).
    split; [reflexivity|now apply H0].
Qed.

Lemma focus_reader {M E p B} (focus : @cursor M E p B) X kind o l rd :
  receive_focus p B focus X kind o l rd ->
  exists code, focus = Code o code /\
    forall G, reader_contract code G -> G X kind l rd.
Proof.
  destruct 1; eexists; split; [reflexivity| |reflexivity|];
    cbn [reader_contract]; auto.
Qed.

Theorem receiver_selects_sender {M E Store Input}
    (model : local_model M E role (Store * Input)) stores input R A c tc s tn n
      gs :
  well_formed R M A c ->
  matched_prefix model stores input R A c tc s tn n gs ->
  forall p, In p R -> forall X kind o l rd, static_path o ->
    receive_site (shared_model model) p (A p) (positions s p) X kind o l rd ->
    exists (v : X) (sh : Show X),
      output (descend o (c l)) o p = Some (Message X kind o l p v sh) /\
      wire_law sh rd.
Proof.
  intros [_ [Q WF]] Prefix p Member X kind o l rd Static
    (B & C & focus & Silent & Site).
  destruct (focus_reader _ _ _ _ _ _ Site) as (code & -> & Reads).
  pose proof (prefix_source_run model stores input R A c _ _ _ _ _ Prefix) as
    Run.
  pose proof (run_anchor (shared_model model) R p _ (c p) _ _ _ _ Run
    (fun _ _ => eq_refl)) as Init.
  pose proof (at_static_focus (shared_model model) p _ (c p) _ _ _ _ _ _
    Init Silent Static) as Receiver.
  pose proof (family_static_reader WF o o p Member (fun r h => h)
    (fun r _ => output (descend o (c r)) o p) (fun _ _ => eq_refl)) as Reader.
  cbn beta in Reader. rewrite Receiver in Reader.
  destruct (Reads _ Reader) as (v & sh & Inside & Origin & Law).
  exists v, sh; auto.
Qed.

Theorem source_originals_static {M E Store Input}
    (model : local_model M E role (Store * Input)) stores input R A c tc s tn n
      gs :
  well_formed R M A c ->
  matched_prefix model stores input R A c tc s tn n gs ->
  forall p, In p R -> forall X kind o l rd, static_path o ->
    receive_site (shared_model model) p (A p) (positions s p) X kind o l rd ->
    exists (v : X) (sh : Show X),
      (forall g, In g gs ->
        message_key g = (l,p,session_at o Choreography.Network.Root) ->
        message_path g = o -> g = Message X kind o l p v sh) /\
      wire_law sh rd.
Proof.
  intros WF Prefix p Member X kind o l rd Static Site.
  destruct (receiver_selects_sender model stores input R A c _ _ _ _ _ WF Prefix
    p
    Member X kind o l rd Static Site) as (v & sh & Origin & Law).
  exists v, sh. split; [|exact Law]. intros [Y k path s0 d0 x sh'] InG Key Path.
  cbn [message_key message_path] in Key, Path. subst path.
  injection Key as -> ->.
  destruct (matched_payload_history model stores input R A c _ _ _ _ _ Prefix)
    as [past Hist].
  pose proof (syntactic_packet model stores input R A c _ _ _ _ _ _ Y k o l p x
    sh'
    Hist InG Static) as Actual. congruence.
Qed.
