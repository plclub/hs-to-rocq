From Stdlib Require Import Lists.List Logic.Eqdep_dec.
Require Import DeadlockRootOrigin DeadlockWellFormed DeadlockNetwork
  DeadlockMessages
  DeadlockFamilyLog DeadlockObservedCut DeadlockPlayedValues DeadlockPast
    DeadlockCoherence
  DeadlockLocal DeadlockSource DeadlockMatch DeadlockState DeadlockChronology
    Parkour.Codec
  DeadlockLogScope DeadlockPlayedFamily DeadlockPartialValues
  Parkour.Symbol Choreography.Choreo2 Control.Monad.Tree.
Import ListNotations.

(* A Bind body can be well-formed on only the roles that have entered.
   Its reader needs no value at an absent sender. If a packet exists there,
   the same execution archive supplies the sender membership witness. *)
Lemma partial_node_reader {M R S A c Q} :
  structural R M S A c Q ->
  forall p (member : S p) o,
  reader_contract (c p member) (fun X kind l reader =>
    forall here : S l, exists (value : X) (writer : Show X),
      outgoing (c l here) o p = Some (Message X kind o l p value writer) /\
      wire_law writer reader).
Proof.
  destruct 1; intros peer mem o;
    match goal with Shape : forall p s, _ p s = _ |- _ =>
      rewrite (Shape peer mem) end;
    cbn [reader_contract]; try exact I.
  - intros <- Ne here. exists (Choreography.Choreo2.unAt (x l here) eq_refl),
    (sh l here).
    rewrite H2; cbn [outgoing].
    destruct (role_eq_dec l l) as [e|N]; [|contradiction].
    rewrite (UIP_dec role_eq_dec e eq_refl). split; [reflexivity|now apply H1].
  - intros Ne here. exists (Choreography.Choreo2.unAt (x l here) eq_refl), (sh l
    here).
    match goal with F : forall p s, c p s = _ |- _ => rewrite (F l here) end.
    cbn [outgoing]. destruct (role_eq_dec l l) as [e|N]; [|contradiction].
    rewrite (UIP_dec role_eq_dec e eq_refl). split; [reflexivity|now apply H0].
Qed.

Section Provenance.
Context {M E Store Input} (model : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input : Input) (R : list Symbol) (A : Symbol ->
    Type)
  (c : forall p, Choreo M p (A p)).
Local Notation Cut := (logged_cut model stores input R A c).
Local Notation tokens_at := (tokens model stores input R A c).
Local Notation batch_of := (entry_batch model stores input R A c).

Theorem produced_in_owner_log tc s tn n gs past ar F active o
    (cuts : forall p, In p active -> Cut p (F p)) kind sender recipient op :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  owns_region model stores input R A c ar F active o cuts ->
  In (Produced kind o sender recipient op) past ->
  exists (here : In sender active) token,
    In token (tokens_at sender (F sender) (cuts sender here)) /\
    In (Produced kind o sender recipient op) (batch_of sender token).
Proof.
  intros Archives [ND [Cover Exact]] Member.
  destruct (observed_past_event_archived model stores input R A c
    _ _ _ _ _ _ _ Archives _ Member) as (p & path & token & Seen & Batch).
  destruct (entry_produced_site model stores input R A c p token _ _ _ _ _
    Batch) as [Eq Site].
  subst sender.
  destruct (observed_archives_valid model stores input R A c _ _ _ _ _ _ _
    Archives p path token Seen)
    as [Route Stamp].
  assert (Within : in_region model stores input R A c ar p o token).
  { split; [now rewrite <- Route|rewrite Site; apply extends_refl]. }
  specialize (Cover p token Within) as Here. exists Here,token.
  split; [now apply Exact|exact Batch].
Qed.

Theorem queued_in_owner_log tc s tn n gs past ar F active o
    (cuts : forall p, In p active -> Cut p (F p))
    X kind sender recipient (x : X) sh :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  owns_region model stores input R A c ar F active o cuts ->
  In (Message X kind o sender recipient x sh) gs ->
  exists (here : In sender active) token,
    In token (tokens_at sender (F sender) (cuts sender here)) /\
    In (Produced kind o sender recipient (Operand X sh x)) (batch_of sender
      token).
Proof.
  intros Archives Own Pending.
  eapply produced_in_owner_log; [exact Archives|exact Own|].
  pose proof (observed_archives_history model stores input R A c _ _ _ _ _ _ _
    Archives) as H.
  exact (proj1 (history_past_ok model stores input R A c _ _ _ _ _ _ H) _
    Pending).
Qed.
End Provenance.

Section OwnedNode.
Context {M E Store Input} (model : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input : Input) (R : list Symbol) (A : Symbol ->
    Type)
  (c : forall p, Choreo M p (A p)).
Local Notation Cut := (logged_cut model stores input R A c).
Local Notation atc := (at_node model stores input R A c).
Variable tc : list (@source_action E ((Symbol -> Store) * Input)).
Variables (s : @DeadlockSource.configuration M E ((Symbol -> Store) * Input) A)
  (tn : list (@action E ((Symbol -> Store) * Input))) (n :
    @DeadlockNetwork.configuration M E ((Symbol -> Store) * Input)).
Variable gs : list message.
Variable past : list payload_event.
Variable ar : actor_archive model stores input R A c.
Hypothesis Archives : observed_archives model stores input R A c tc s tn n gs
  past ar.
Variables (S : roles) (F : Symbol -> Type) (prog : programs M F S) (active :
  list Symbol)
  (inc : includes (fun p => In p active) S) (root : occurrence)
  (cuts : family Cut F active).
Hypothesis Own : owns_region model stores input R A c ar F active root cuts.
Hypothesis Nodes : family_at Cut (atc past) S F prog active inc root cuts.

Theorem owned_original_operand p (d : In p active) kind recipient op :
  sender_operand (prog p (inc p d)) = Some op ->
  original_operand past kind root p recipient op.
Proof.
  intros Expected other Produced.
  destruct (produced_in_owner_log model stores input R A c _ _ _ _ _ _ _ _ _ _ _
    kind p recipient other Archives Own Produced) as (h & token & Member &
      Batch).
  pose proof (roster_member_unique _ (proj1 Own) p h d) as Eq; subst h.
  destruct (Nodes p d) as [Log _].
  destruct (actor_log_produced_here model stores input R A c
    p (F p) root _ _ _ _ kind recipient other Log Member Batch) as [Origin _].
  congruence.
Qed.

Lemma owned_outgoing_packet X kind sender recipient (value : X) writer :
  In (Message X kind root sender recipient value writer) gs ->
  exists h : In sender active,
    forall d : In sender active,
      outgoing (prog sender (inc sender d)) root recipient =
        Some (Message X kind root sender recipient value writer).
Proof.
  intro Member.
  destruct (queued_in_owner_log model stores input R A c _ _ _ _ _ _ _ _ _ _ _
    X kind sender recipient value writer Archives Own Member) as (h & token &
      Seen & Batch).
  exists h. intro d. pose proof (roster_member_unique _ (proj1 Own) sender h d)
    as Eq; subst h.
  destruct (Nodes sender d) as [Log _].
  exact (proj2 (actor_log_produced_here model stores input R A c
    sender (F sender) root _ _ _ _ kind recipient (Operand X writer value) Log
      Seen Batch)).
Qed.

(* A receiver and a queued packet in the same realized WF node share the
   actual typed operand and dictionary. The initial packet witnesses that
   its sender is in the partial domain at this node. *)
Theorem owned_node_codec Q :
  structural R M S F prog Q ->
  forall p (d : In p active), reader_contract (prog p (inc p d))
    (fun X kind sender rd =>
      (exists g, In g gs /\ message_key g = (sender,p,DeadlockOrder.session_at
        root Choreography.Network.Root) /\
        message_path g = root) ->
      exists (v : X) (sh : Show X),
        (forall g, In g gs -> message_key g = (sender,p,DeadlockOrder.session_at
          root Choreography.Network.Root) ->
          message_path g = root -> g = Message X kind root sender p v sh) /\
            wire_law sh rd).
Proof.
  intros WF p d. pose proof (partial_node_reader WF p (inc p d) root) as Reader.
  assert (Map : forall B (t : Choreo M p B) (P Q : forall X, delivery_kind ->
    role -> Read X -> Prop),
    reader_contract t P -> (forall X kind l rd, P X kind l rd -> Q X kind l rd)
      -> reader_contract t Q).
  { intros B t P Z. destruct t; cbn; try tauto.
    destruct c0; cbn [reader_contract]; eauto. }
  eapply Map; [exact Reader|].
  intros X jk sender rd Sender ([T k0 o0 s0 d0 x dict] & Member & Key & Path).
  cbn [message_path message_key] in Key, Path. subst o0; injection Key as -> ->.
  destruct (owned_outgoing_packet _ _ _ _ _ _ Member) as [here At].
  destruct (Sender (inc _ here)) as (value & writer & Original & Law).
  exists value,writer. split; [|exact Law].
  intros [U k1 o1 s1 d1 y sh] Seen Key1 Path1.
  cbn [message_path message_key] in Key1, Path1; subst o1; injection Key1 as ->
    ->.
  destruct (owned_outgoing_packet _ _ _ _ _ _ Seen) as [_ All].
  specialize (All here); congruence.
Qed.
End OwnedNode.

(* The roles that have already entered a choice body agree on the selected
   argument. No witness is required when no role has entered. In particular
   this works for a partially entered Bind and an uninhabited choice type. *)
Theorem entered_choices_agree {M E Store Input}
    (model : local_model M E Symbol (Store * Input)) stores input R A c
    tc s tn n gs past ar S F X l (sh : forall p, S p -> Show X)
    (rd : forall p, S p -> Read X) (arg : values (fun p => At X l p) S)
    (k : forall p, S p -> X -> Choreo M p (F p))
    active (inc : includes (fun p => In p active) S) o cuts entered
    (inside : includes (fun p => In p entered) (fun p => In p active))
    (choices : values (fun _ => X) (fun p => In p entered)) :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  owns_region model stores input R A c ar F active o cuts ->
  family_at _ (at_node model stores input R A c past) S F (fun p s =>
    Perf (@Cond M p X l (F p) (sh p s) (rd p s) (known l) MkSSymbol (arg p s) (k
      p s)))
    active inc o cuts ->
  (forall p (s : S l) (t : S p), p <> l -> wire_law (sh l s) (rd p t)) ->
  (forall p d, choice_observation past X l p (rd p (inc p (inside p d)))
    (arg p (inc p (inside p d))) o (choices p d)) ->
  entered <> [] ->
  exists h : In l active,
    forall p d, choices p d = unAt (arg l (inc l h)) eq_refl.
Proof.
  intros Archives Own Nodes Codec Observed Nonempty.
  assert (Owner : In l active).
  { destruct entered as [|r rs]; [contradiction|].
    specialize (Observed r (or_introl eq_refl)) as [(Same & Chosen)|(Ne & w &
      Past & Read)].
    - rewrite Same. apply inside. now left.
    - eapply owns_sender_present; eassumption. }
  exists Owner. intros p d. destruct (Observed p d) as [(Eq & Chosen)|(Ne & w &
    Past & Read)].
  - destruct Eq. rewrite Chosen.
  now rewrite (roster_member_unique _ (proj1 Own) l (inside l d) Owner).
  - eapply (choice_observed_value X l p S arg sh rd (inc l Owner) (inc p (inside
    p d))
      past o w (choices p d)); [congruence|apply Codec; congruence| |exact
        Past|exact Read].
    eapply (owned_original_operand model stores input R A c _ _ _ _ _ _ _
      Archives
      S F _ active inc o cuts Own Nodes l Owner ChoiceDelivery p).
    cbn [sender_operand]. destruct (list_eq_dec BinNat.N.eq_dec l l) as [h|H];
      [|contradiction].
    rewrite (UIP_dec (list_eq_dec BinNat.N.eq_dec) h eq_refl). reflexivity.
Qed.
