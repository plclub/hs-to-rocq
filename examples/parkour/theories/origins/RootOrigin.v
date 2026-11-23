From Stdlib Require Import Lists.List.
Require Import DeadlockCoherence DeadlockSource DeadlockNetwork DeadlockReplay
  DeadlockLocal DeadlockPast DeadlockPlayedValues DeadlockSameHistory
  DeadlockState Parkour.Symbol.
Require Choreography.Choreo2.
Require Import DeadlockCutSafety DeadlockWellFormed DeadlockMessages
  DeadlockOrder Parkour.Codec.
Import ListNotations.
Local Notation Choreo := Choreography.Choreo2.Choreo.

(* The original syntax of a root event can be recovered without comparing
   existential payload types. Carry any predicate on the whole typed program. *)
Section Root.
Context {M E : Type -> Type} {S : Type}.
Variable m : local_model M E role S.
Variable R : list role.
Variable p : role.
Variable P : forall X, Choreo M p X -> Prop.

Fixpoint root_ok {X} (t : @cursor M E p X) : Prop :=
  match t with
  | Code o c => o = [] -> P _ c
  | Fork f x => root_ok f /\ root_ok x
  | Seq _ u _ => root_ok u
  | _ => True
  end.

Lemma child_nonempty o e : child o e <> [].
Proof. unfold child; destruct o; discriminate. Qed.

Lemma silent_root X t u : @silent M E S m p X t u -> root_ok t -> root_ok u.
Proof.
  induction 1; cbn [root_ok]; intuition eauto; exfalso; eapply child_nonempty;
    eassumption.
Qed.

Lemma step_root X t st q a u st' q' :
  @role_step M E S m R p X t st q a u st' q' -> root_ok t -> root_ok u.
Proof.
  induction 1; cbn [root_ok]; intuition eauto using silent_root;
    exfalso; eapply child_nonempty; eassumption.
Qed.

Lemma root_focus X A (C : @cursor_context M E p X A) t :
  root_ok (plug C t) -> root_ok t.
Proof. induction C; cbn; intros H; first [exact H|apply IHC; tauto]. Qed.

Definition event_ok (event : replay_event m R p) :=
  match event with
  | SilentEvent _ _ _ _ before _ _ | ActionEvent _ _ _ _ before _ _ _ _ _ _ _ =>
      root_ok before
  end.

Local Arguments lookup {M E Store model configured p} _ _.
Local Arguments insert {M E Store model configured p} _ _ _.
Local Arguments event_route {M E p X A} _ _.

Lemma insert_members path (event : replay_event m R p) tree o e :
  In e (lookup o (insert path event tree)) ->
  event = e \/ In e (lookup o tree).
Proof.
  revert tree o. induction path as [|edge path IH]; intros tree [|f o]; cbn.
  - tauto.
  - destruct f; tauto.
  - destruct edge; cbn; tauto.
  - destruct edge, f; cbn; intros H; first [now apply IH|tauto].
Qed.

Theorem archived_root X start tr cut :
  @cut_history M E S m R p X start tr cut -> root_ok start ->
  root_ok (erased_cursor m R p cut) /\
  forall o event, In event (lookup o (archive m R p cut)) -> event_ok event.
Proof.
  intro Hist. induction Hist; intro Good.
  - split; [exact Good|]. intros o event H. cbn in H.
    induction o; cbn in H; [contradiction|exact (IHo H)].
  - destruct (IHHist Good) as [Before Old]. split.
    + cbn. eapply silent_root; [eapply silent_plug; apply primitive_is_silent;
      exact step|exact Before].
    + intros o event Member. apply insert_members in Member.
      destruct Member as [<-|I]; [exact (root_focus _ _ C _ Before)|exact (Old _
        _ I)].
  - destruct (IHHist Good) as [Before Old]. split.
    + cbn. eapply step_root; [eapply role_step_plug; apply
      primitive_is_role_step; exact step|exact Before].
    + intros o event Member. apply insert_members in Member.
      destruct Member as [<-|I]; [exact (root_focus _ _ C _ Before)|exact (Old _
        _ I)].
Qed.
End Root.

Definition outgoing {M p A} (c : Choreo M p A) o peer : option
  DeadlockMessages.message :=
  match c with
  | Control.Monad.Tree.Perf (@Choreography.Choreo2.Comm _ _ X l d sh _ _ _ _ v
    _) =>
    match role_eq_dec l p with
    | left e => Some (DeadlockMessages.Message X DataDelivery o p d
        (Choreography.Choreo2.unAt v e) sh)
    | right _ => None end
  | Control.Monad.Tree.Perf (@Choreography.Choreo2.Cond _ _ X l _ sh _ _ _ v _)
    =>
    match role_eq_dec l p with
    | left e => Some (DeadlockMessages.Message X ChoiceDelivery o p peer
        (Choreography.Choreo2.unAt v e) sh)
    | right _ => None end
  | _ => None end.

Definition event_packet (event : payload_event) :=
  match event with
  | Produced kind o s d (Operand X sh x) =>
      Some (DeadlockMessages.Message X kind o s d x sh)
  | _ => None end.

Lemma focus_packet {M E} R p B ev (t : @cursor M E p B) :
  sender_site R B ev t ->
  match t, ev with
  | Code o code, Produced _ _ _ d _ => outgoing code o d = event_packet ev
  | _, _ => False
  end.
Proof.
  destruct 1; cbn [outgoing event_packet].
  all: destruct (role_eq_dec p p) as [e|Ne]; [|contradiction];
    rewrite (Eqdep_dec.UIP_dec role_eq_dec e eq_refl); reflexivity.
Qed.

Lemma prefix_root_ok {M E S} (m : local_model M E role S) R p A
    (P : forall B, Choreo M p B -> Prop) start tc finish :
  @DeadlockSource.crun M E S m R A start tc finish ->
  root_ok p P (DeadlockSource.positions start p) ->
  root_ok p P (DeadlockSource.positions finish p).
Proof.
  induction 1; intro Init; [exact Init|].
  destruct H0 as [r act u Hr Step Frame].
  destruct (role_eq_dec r p) as [->|Ne].
  - eapply step_root; [exact Step|auto].
  - rewrite <- Frame by congruence. auto.
Qed.

Theorem packet_from_root_program {M E Store Input}
    (model : local_model M E role (Store * Input)) stores input R A c
    tc s tn n gs past X kind sender recipient (v : X) sh :
  payload_history model stores input R A c tc s tn n gs past ->
  In (DeadlockMessages.Message X kind [] sender recipient v sh) gs ->
  outgoing (c sender) [] recipient =
    Some (DeadlockMessages.Message X kind [] sender recipient v sh).
Proof.
  intros Hist Member. pose proof (history_production model stores input R A c
    _ _ _ _ _ _ Hist kind [] sender recipient (Operand X sh v)
    (proj1 (history_past_ok model stores input R A c _ _ _ _ _ _ Hist) _
      Member)) as Past.
  destruct (actual_production_focus model stores input R A c _ _ _ _ _ Past)
    as (tc0 & s0 & tn0 & n0 & gs0 & a & s1 & na & n1 & gs1 & ev & who & Prefix &
      Pair & Hin & Focus).
  pose proof (production_focus_sender _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Focus) as
    [Eq _].
  subst who. destruct Focus as (Y & C & before & after & Sil & Prim & End &
    Site).
  pose proof (focus_packet _ _ _ _ _ Site) as Packet.
  destruct (sender_site_operand _ _ _ _ _ _ _ _ _ Site)
    as [_ [code [-> _]]]. cbn [event_packet] in Packet.
  pose (P := fun B (t : Choreo M sender B) =>
    outgoing t [] recipient = outgoing (c sender) [] recipient).
  pose proof (prefix_root_ok _ R sender A P _ _ _
    (DeadlockMatch.prefix_source_run model stores input R A c _ _ _ _ _ Prefix)
    (fun _ => eq_refl)) as Good.
  assert (Root : root_ok sender P (plug C (Code [] code))).
  { clear -Good Sil. induction Sil; [exact Good|].
    apply IHSil. eapply silent_root; eassumption. }
  pose proof (root_focus sender P _ _ C _ Root eq_refl) as Orig.
  unfold P in Orig. now rewrite <- Orig.
Qed.

(* A queued packet at the source root identifies the original sender operand
   (type, dictionary, and value together), even if that sender has since
   entered a continuation and the original Code cursor is gone. *)
Theorem root_queued_operand {M E Store Input}
    (model : local_model M E role (Store * Input)) stores input R A c
    tc s tn n gs past X kind sender recipient (v : X) sh :
  payload_history model stores input R A c tc s tn n gs past ->
  In (DeadlockMessages.Message X kind [] sender recipient v sh) gs ->
  sender_operand (c sender) = Some (Operand X sh v).
Proof.
  intros Hist Member.
  pose proof (production_at_current_sender model stores input R A c _ _ _ _ _ _
    Hist
    kind [] sender recipient (Operand X sh v)
    (proj1 (history_past_ok model stores input R A c _ _ _ _ _ _ Hist) _
      Member))
    as (cut & HC & _ & Y & code & after & st & sq & a & st' & sq' & prim &
      Operand & Seen).
  pose (P := fun B (t : Choreo M sender B) => sender_operand t = sender_operand
    (c sender)).
  pose proof (archived_root (shared_model model) R sender P _ _ _ _ HC
    (fun _ => eq_refl)) as [_ Good].
  specialize (Good _ _ Seen). cbn [event_ok root_ok] in Good.
  unfold P in Good. rewrite <- (Good eq_refl). exact Operand.
Qed.

(* Traverse the receiver term before choosing a result type. Thus the
   decoder and the sender's operand meet at the WF constructor's actual
   hidden type, without dependent-pair injection. *)
Definition reader_contract {M p A} (c : Choreo M p A)
    (G : forall X, delivery_kind -> role -> Read X -> Prop) : Prop :=
  match c with
  | Control.Monad.Tree.Perf (@Choreography.Choreo2.Comm _ _ X l d _ rd _ _ _ _
    _) =>
    d = p -> l <> p -> G X DataDelivery l rd
  | Control.Monad.Tree.Perf (@Choreography.Choreo2.Cond _ _ X l _ _ rd _ _ _ _)
    =>
    l <> p -> G X ChoiceDelivery l rd
  | _ => True end.

Lemma coherent_root_reader {M R S A c Q} :
  structural R M S A c Q ->
  forall p (d : S p), (forall l, In l R -> S l) ->
    reader_contract (c p d) (fun X kind l rd =>
      exists (v : X) (sh : Show X) (s : S l),
      outgoing (c l s) [] p = Some (Message X kind [] l p v sh) /\ wire_law sh
        rd).
Proof.
  destruct 1; intros peer mem all.
  all: match goal with H : forall p s, _ p s = _ |- _ => rewrite (H peer mem)
    end;
    cbn [reader_contract]; try exact I.
  - intros <- Ne. specialize (all l H) as here.
    exists (Choreography.Choreo2.unAt (x l here) eq_refl), (sh l here), here.
    rewrite H2; cbn [outgoing].
    destruct (role_eq_dec l l) as [e|N]; [|contradiction].
    rewrite (Eqdep_dec.UIP_dec role_eq_dec e eq_refl).
    split; [reflexivity|now apply H1].
  - intros Ne. specialize (all l H) as here.
    exists (Choreography.Choreo2.unAt (x l here) eq_refl), (sh l here), here.
    match goal with F : forall p s, c p s = _ |- _ => rewrite (F l here) end.
    cbn [outgoing]. destruct (role_eq_dec l l) as [e|N]; [|contradiction].
    rewrite (Eqdep_dec.UIP_dec role_eq_dec e eq_refl).
    split; [reflexivity|now apply H0].
Qed.

Lemma root_site_contract {M E S} (m : local_model M E role S) R p A
    (c : forall p, Choreo M p (A p)) st tc finish X kind sender rd G :
  @DeadlockSource.crun M E S m R A (DeadlockSource.initial c st) tc finish ->
  receive_site m p (A p) (DeadlockSource.positions finish p) X kind [] sender rd
    ->
  reader_contract (c p) G -> G X kind sender rd.
Proof.
  intros Run (B & C & focus & Silent & Site) Reader.
  pose (P := fun Y (t : Choreo M p Y) => reader_contract t G).
  pose proof (prefix_root_ok m R p A P _ _ _ Run (fun _ => Reader)) as Root.
  assert (Good : root_ok p P (plug C focus)).
  { clear -Silent Root. induction Silent; [exact Root|].
    apply IHSilent; eapply silent_root; eassumption. }
  pose proof (root_focus p P _ _ C _ Good) as F.
  remember (@nil source_edge) as where_ in Site.
  destruct Site; subst; cbn [root_ok] in F;
    specialize (F eq_refl); unfold P, reader_contract in F; auto.
Qed.

Theorem source_originals_root {M E Store Input}
    (model : local_model M E role (Store * Input)) stores input R A c
    tc s tn n gs :
  well_formed R M A c ->
  DeadlockMatch.matched_prefix model stores input R A c tc s tn n gs ->
  forall p, In p R -> forall X kind sender rd,
    receive_site (shared_model model) p (A p) (DeadlockSource.positions s p)
      X kind [] sender rd ->
    exists (v : X) (sh : Show X),
      (forall g, In g gs ->
        message_key g = (sender,p,session_at [] Choreography.Network.Root) ->
        message_path g = [] -> g = Message X kind [] sender p v sh) /\
      wire_law sh rd.
Proof.
  intros [_ [Q WF]] Prefix p Member X kind sender rd Site.
  pose proof (coherent_root_reader WF p Member (fun r h => h)) as Reader.
  pose proof (DeadlockMatch.prefix_source_run model stores input R A c
    _ _ _ _ _ Prefix) as Run.
  destruct (root_site_contract (shared_model model) R p A c (stores,input)
    tc s X kind sender rd _ Run Site Reader)
    as (v & sh & inside & Origin & Codec).
  exists v, sh. split; [|exact Codec].
  destruct (matched_payload_history model stores input R A c _ _ _ _ _ Prefix)
    as [past Hist].
  intros [B k path a b value dict] InG Key Path.
  cbn [message_key message_path] in Key, Path. subst path.
  injection Key as -> ->.
  pose proof (packet_from_root_program model stores input R A c tc s tn n gs
    past
    B k sender p value dict Hist InG) as Produced.
  cbn beta in Origin. congruence.
Qed.
