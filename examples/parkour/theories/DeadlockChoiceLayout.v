From Stdlib Require Import Lists.List.
Require Import DeadlockFamilyChoice DeadlockFamilyOrigin DeadlockFamilyLog
  DeadlockAllOrigins DeadlockRootOrigin DeadlockRealized DeadlockLayoutOrder DeadlockCoverage
  DeadlockPlayedFamily DeadlockPlayedActual DeadlockObservedCut DeadlockLocalLog
  DeadlockSource DeadlockLocal DeadlockCoherence DeadlockPlayedValues
  DeadlockWellFormed DeadlockPartialValues DeadlockState DeadlockOrder
  DeadlockCutSafety DeadlockPast DeadlockNetwork DeadlockMessages
  Parkour.Symbol Parkour.Codec Choreography.Choreo2 Control.Monad.Tree.
Import ListNotations.
Local Arguments cursor_at {M E Store Input} model stores input R A c {p B} _.
Local Arguments tokens {M E Store Input} model stores input R A c {p B} _.

Section ChoiceLayout.
Context {M E Store Input} (model : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input0 : Input) (R : list Symbol)
  (A0 : Symbol -> Type) (c0 : forall p, Choreo M p (A0 p)).
Local Notation Cut := (logged_cut model stores input0 R A0 c0).
Local Notation cur := (cursor_at model stores input0 R A0 c0).
Local Notation tok := (tokens model stores input0 R A0 c0).
Local Notation entry := (observed_entry model stores input0 R A0 c0).
Local Notation node := (at_node model stores input0 R A0 c0).
Local Notation good := (owns_region model stores input0 R A0 c0).
Local Notation tracked := (tracked_realization model stores input0 R A0 c0).
Local Notation receive := (cut_receive model stores input0 R A0 c0).
Local Notation ret := (finished model stores input0 R A0 c0).
Local Notation covered := (cut_covered model stores input0 R A0 c0).
Local Notation stamp := (stamped model stores input0 R A0 c0).

Lemma initial_cond_receive p X B owner root sh rd kl sl v k
    (cut : Cut p B) Y kind o sender reader :
  cur cut = Code root (Perf (@Cond M p X owner B sh rd kl sl v k)) ->
  receive p B cut Y kind o sender reader ->
  kind = ChoiceDelivery /\ o = root /\ sender = owner /\ owner <> p.
Proof.
  intros Eq (Z & C & focus & Cursor & Focus).
  set (G := fun (p : Symbol) (o : occurrence) (X : Type)
    (kind : delivery_kind) (sender : Symbol) (rd : Read X) =>
      kind = ChoiceDelivery /\ o = root /\ sender = owner /\ owner <> p).
  assert (Root : cursor_readers G p B (cur cut)).
  { rewrite Eq. cbn [cursor_readers reader_contract]. unfold G. auto. }
  rewrite Cursor in Root.
  exact (readers_receive G p Z focus Y kind o sender reader Focus
    (readers_focus G p B Z C focus Root)).
Qed.

Lemma tracked_empty F root (cuts : family Cut F []) tree :
  tracked F [] root cuts tree.
Proof.
  constructor.
  - constructor; intros p d; contradiction.
  - intros p d; contradiction.
Qed.

Theorem logged_choice_layout tc s tn n gs past ar S X owner F
    (sh : forall p, S p -> Show X) (rd : forall p, S p -> Read X)
    (input : values (fun p => At X owner p) S)
    (k : forall p, S p -> X -> Choreo M p (F p))
    active inc root (cuts : family Cut F active) :
  payload_history model stores input0 R A0 c0 tc s tn n gs past ->
  NoDup active ->
  good ar F active root cuts ->
  family_at Cut (node past) S F (fun p s => Perf (@Cond M p X owner (F p)
    (sh p s) (rd p s) (known owner) MkSSymbol (input p s) (k p s)))
    active inc root cuts ->
  exists entered
    (inside : includes (fun p => In p entered) (fun p => In p active))
    (choices : values (fun _ => X) (fun p => In p entered))
    (bodies : family Cut F entered),
    NoDup entered /\
    good ar F entered (child root ChoiceBody) bodies /\
    (forall p d, choice_observation past X owner p (rd p (inc p (inside p d)))
      (input p (inc p (inside p d))) root (choices p d)) /\
    (forall p d, node past p _ (child root ChoiceBody)
      (k p (inc p (inside p d)) (choices p d)) (bodies p d)) /\
    (forall tree, tracked F entered (child root ChoiceBody) bodies tree ->
      tracked F active root cuts (Choice owner tree)).
Proof.
  intros Hist ND Own Nodes.
  destruct (replay_cond_logged_partition model stores input0 R A0 c0 past ar
    tc s tn n gs S X owner F sh rd input k active [] inc root cuts
    (fun p d => False_rect _ d) (fun p d => False_rect _ d)
    Hist ND (NoDup_nil _) Own Nodes (fun p d => False_rect _ d))
    as (entered & inside & completed & choices & bodies &
      NE & BodyOwn & Observe & BodyAt & BodyRet & Entered & Outside & Headers & Absent).
  exists entered,inside,choices,bodies.
  split; [exact NE|]. split; [exact BodyOwn|]. split; [exact Observe|].
  split; [exact BodyAt|]. intros tree BodyLayout.
  assert (HeaderCoverage : forall p d (here : In p entered) peer,
    owner <> peer -> (p = owner \/ p = peer) ->
    covered p (F p) (cuts p d) ChoiceDelivery root owner peer).
  { intros p d here peer Ne Peer.
    destruct (Headers p here) as (header & Tokens & Site & Stamp).
    exists header. split.
    - rewrite <- (roster_member_unique active ND p (inside p here) d).
      rewrite Tokens; now left.
    - exact (DeadlockRealized.stamped_choice_header model stores input0 R A0 c0
        p X (F p) owner root _ _ _ _ _ _ header _ Stamp peer Ne Peer). }
  eapply (tracked_choice model stores input0 R A0 c0 F active entered
    root owner cuts bodies tree BodyLayout).
  - intros p d e Member.
    destruct (in_dec role_eq_dec p entered) as [here|NotHere].
    + destruct (Headers p here) as (header & Tokens & Site & Stamp).
      rewrite <- (roster_member_unique active ND p (inside p here) d) in Member.
      rewrite Tokens in Member. destruct Member as [<-|Member].
      * left. split; [exact Site|]. intros ev Event.
        exact (stamped_choice_header_batch model stores input0 R A0 c0
          p X (F p) owner root _ _ _ _ _ _ header _ Stamp ev Event).
      * right. now exists here.
    + rewrite (Absent p d NotHere) in Member. contradiction.
  - intros p d here e Member.
    destruct (Headers p here) as (header & Tokens & Site & Stamp).
    rewrite <- (roster_member_unique active ND p (inside p here) d).
    rewrite Tokens; now right.
  - intros p d value Return.
    destruct (in_dec role_eq_dec p entered) as [here|NotHere].
    + exists here,value. split.
      * unfold finished in *. rewrite <-
          (roster_member_unique active ND p (inside p here) d) in Return.
        rewrite (Entered p here) in Return. exact Return.
      * exact (HeaderCoverage p d here).
    + unfold finished in Return. rewrite (Outside p d NotHere) in Return.
      contradiction.
  - intros p d Y kind o sender reader Recv.
    destruct (in_dec role_eq_dec p entered) as [here|NotHere].
    + right. exists here.
      destruct Recv as (Z & C & focus & Cursor & Focus).
      exists Z,C,focus. split; [|exact Focus].
      rewrite <- (Entered p here).
      now rewrite (roster_member_unique active ND p (inside p here) d).
    + left. exact (initial_cond_receive p X (F p) owner root
        (sh p (inc p d)) (rd p (inc p d)) (known owner) MkSSymbol
        (input p (inc p d)) (k p (inc p d)) (cuts p d)
        Y kind o sender reader (Outside p d NotHere) Recv).
  - exact HeaderCoverage.
Qed.

Theorem coherent_choice_layout tc s tn n gs past ar S X owner F
    (sh : forall p, S p -> Show X) (rd : forall p, S p -> Read X)
    (input : values (fun p => At X owner p) S)
    (k : forall p, S p -> X -> Choreo M p (F p))
    active inc root (cuts : family Cut F active) :
  observed_archives model stores input0 R A0 c0 tc s tn n gs past ar ->
  NoDup active ->
  good ar F active root cuts ->
  family_at Cut (node past) S F (fun p s => Perf (@Cond M p X owner (F p)
    (sh p s) (rd p s) (known owner) MkSSymbol (input p s) (k p s)))
    active inc root cuts ->
  (forall p (s : S owner) (t : S p), p <> owner ->
    wire_law (sh owner s) (rd p t)) ->
  tracked F active root cuts (Choice owner Leaf) \/
  exists entered
    (inside : includes (fun p => In p entered) (fun p => In p active))
    (chosen : X) (bodies : family Cut F entered),
    NoDup entered /\
    good ar F entered (child root ChoiceBody) bodies /\
    (forall p d, node past p _ (child root ChoiceBody)
      (k p (inc p (inside p d)) chosen) (bodies p d)) /\
    (forall tree, tracked F entered (child root ChoiceBody) bodies tree ->
      tracked F active root cuts (Choice owner tree)).
Proof.
  intros Archives ND Own Nodes Codec.
  destruct (logged_choice_layout tc s tn n gs past ar S X owner F sh rd input k
    active inc root cuts
    (observed_archives_history model stores input0 R A0 c0 _ _ _ _ _ _ _ Archives)
    ND Own Nodes)
    as (entered & inside & choices & bodies & NE & BodyOwn & Observe & BodyAt & Assemble).
  destruct entered as [|first rest].
  - left. apply Assemble. apply tracked_empty.
  - destruct (entered_choices_agree model stores input0 R A0 c0
      tc s tn n gs past ar S F X owner sh rd input k active inc root cuts
      (first :: rest) inside choices Archives Own Nodes Codec Observe
      ltac:(discriminate)) as [here Common].
    right. exists (first :: rest),inside,(unAt (input owner (inc owner here)) eq_refl),bodies.
    split; [exact NE|]. split; [exact BodyOwn|]. split; [|exact Assemble].
    intros p d. rewrite <- (Common p d). apply BodyAt.
Qed.
End ChoiceLayout.

Print Assumptions logged_choice_layout.
Print Assumptions coherent_choice_layout.
