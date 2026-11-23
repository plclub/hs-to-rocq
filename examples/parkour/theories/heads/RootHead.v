From Stdlib Require Import Lists.List.
Require Import DeadlockSource DeadlockNetwork DeadlockCoherence
  DeadlockChronology
  DeadlockMatch DeadlockHead DeadlockFrontiers DeadlockFrontierCoverage
    DeadlockCutSafety
  DeadlockRootOrigin DeadlockFirstSend DeadlockWellFormed DeadlockMessages
    DeadlockOrder
  DeadlockState Parkour.Symbol Parkour.Codec Control.Monad.Tree.
Import ListNotations.
Local Arguments positions {M E Store A} _ _.
Local Notation Choreo := Choreography.Choreo2.Choreo.
Local Notation Comm := Choreography.Choreo2.Comm.
Local Notation Cond := Choreography.Choreo2.Cond.

Definition sender_ready {M p A} R (c : Choreo M p A) receiver : Prop :=
  match c with
  | Perf (@Comm _ _ _ l d _ _ _ _ _ _ _) =>
      l = p /\ d = receiver /\ p <> receiver
  | Perf (@Cond _ _ _ l _ _ _ _ _ _ _) =>
      l = p /\ p <> receiver /\ In receiver R
  | _ => False
  end.

Definition receiver_ready {M p A} (c : Choreo M p A) sender : Prop :=
  match c with
  | Perf (@Comm _ _ _ l d _ _ _ _ _ _ _) =>
      l = sender /\ d = p /\ l <> p
  | Perf (@Cond _ _ _ l _ _ _ _ _ _ _) =>
      l = sender /\ l <> p
  | _ => False
  end.

Lemma announcement_root_nonempty R sender receiver :
  In receiver R -> sender <> receiver ->
  exists tail, key_paths (sender,receiver,Choreography.Network.Root)
    (announcement_messages unit [] sender tt show_unit R) = [] :: tail.
Proof.
  unfold announcement_messages.
  intros Member Ne. induction R as [|r rs IH]; [contradiction|].
  cbn [filter]. destruct (role_eq_dec r sender) as [->|Different].
  - apply IH. destruct Member; [congruence|assumption].
  - cbn [map]. destruct (key_eq_dec
      (sender,r,Choreography.Network.Root)
      (sender,receiver,Choreography.Network.Root)) as [Eq|N].
    + inversion Eq; subst r.
      rewrite (key_paths_same
        (Message unit ChoiceDelivery [] sender receiver tt show_unit)).
      eauto.
    + rewrite key_paths_other by exact N. apply IH.
      destruct Member; [subst; contradiction|assumption].
Qed.

Section RootSteps.
Context {M E : Type -> Type} {S : Type}.
Variable m : DeadlockLocal.local_model M E role S.
Variable R : list role.

Definition sender_cursor {p A} (t : @cursor M E p A) receiver :=
  match t with Code o c => o = [] /\ sender_ready R c receiver | _ => False end.
Definition receiver_cursor {p A} (t : @cursor M E p A) sender :=
  match t with Code o c => o = [] /\ receiver_ready c sender | _ => False end.

Lemma sender_no_silent p A (t u : @cursor M E p A) receiver :
  silent m A t u -> sender_cursor t receiver -> False.
Proof.
  destruct 1; cbn [sender_cursor sender_ready]; intuition congruence.
Qed.

Lemma receiver_no_silent p A (t u : @cursor M E p A) sender :
  silent m A t u -> receiver_cursor t sender -> False.
Proof.
  destruct 1; cbn [receiver_cursor receiver_ready]; intuition congruence.
Qed.

Lemma sender_first p A (t u : @cursor M E p A) st q a st' q' receiver :
  role_step m R A t st q a u st' q' ->
  sender_cursor t receiver ->
  exists tail, emits R (p,receiver,Choreography.Network.Root) a = [] :: tail.
Proof.
  intro Step. induction Step; cbn [sender_cursor sender_ready]; try
    contradiction.
  - intros [-> [_ [<- Ne]]]. cbn [emits].
    destruct (key_eq_dec _ _) as [Eq|N]; [eauto|contradiction].
  - intros [-> [Eq [_ Ne]]]. congruence.
  - intros [-> [_ [Ne Member]]]. apply announcement_root_nonempty; assumption.
  - intros [-> [Eq [Ne _]]]. congruence.
  - intro Ready. exfalso. eapply sender_no_silent; eassumption.
Qed.

Lemma receiver_first p A (t u : @cursor M E p A) st q a st' q' sender :
  role_step m R A t st q a u st' q' ->
  receiver_cursor t sender ->
  exists tail, receives (sender,p,Choreography.Network.Root) a = [] :: tail.
Proof.
  intro Step. induction Step; cbn [receiver_cursor receiver_ready]; try
    contradiction.
  - intros [-> [_ [Eq Ne]]]. congruence.
  - intros [-> [<- [_ Ne]]]. cbn [receives].
    destruct (key_eq_dec _ _) as [Eq|N]; [eauto|contradiction].
  - intros [-> [_ Ne]]. contradiction.
  - intros [-> [<- Ne]]. cbn [receives].
    destruct (key_eq_dec _ _) as [Eq|N]; [eauto|contradiction].
  - intro Ready. exfalso. eapply receiver_no_silent; eassumption.
Qed.
End RootSteps.

Lemma structural_root_ready {M R S A c Q} :
  structural R M S A c Q ->
  forall p (d : S p) (all : forall l, In l R -> S l), In p R ->
  reader_contract (c p d) (fun X kind sender rd =>
    (exists s : S sender, sender_ready R (c sender s) p) /\
    receiver_ready (c p d) sender).
Proof.
  destruct 1; intros peer mem all Configured.
  all: match goal with H : forall p s, _ p s = _ |- _ =>
    rewrite (H peer mem) end.
  all: cbn [reader_contract]; try exact I.
  - intros <- Ne. split.
    + exists (all l H). rewrite H2. cbn [sender_ready]. auto.
    + cbn [receiver_ready]. auto.
  - intro Ne. split.
    + exists (all l H).
      match goal with F : forall p s, c p s = _ |- _ => rewrite (F l (all l H))
        end.
      cbn [sender_ready]. repeat split; auto; congruence.
    + cbn [receiver_ready]. auto.
Qed.

Section FirstAction.
Context {M E : Type -> Type} {S : Type}.
Variable m : DeadlockLocal.local_model M E role S.
Variable R : list role.
Variable A : role -> Type.
Variable p : role.
Variable F : @source_action E S -> list occurrence.
Hypothesis Other : forall a, action_actor a <> p -> F a = [].
Variable start : @DeadlockSource.configuration M E S A.
Hypothesis First : forall st q a u st' q',
  role_step m R (A p) (positions start p) st q a u st' q' ->
  exists tail, F a = [] :: tail.

(* Before the first real action of p, its cursor is exactly its initial
   cursor. Afterwards the first ledger occurrence persists under snoc. *)
Lemma initial_ledger tc finish :
  DeadlockSource.crun m R start tc finish ->
  (flat_map F tc = [] /\ positions finish p = positions start p) \/
  exists tail, flat_map F tc = [] :: tail.
Proof.
  induction 1 as [s0|s0 tc middle a finish Run IH Step].
  - left; auto.
  - rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r.
    destruct (IH First) as [[Empty Frame]|[tail Head]].
    + rewrite Empty. cbn [app].
      destruct Step as [who act u Member Act Unchanged].
      destruct (role_eq_dec who p) as [->|Ne].
      * right. eapply First. rewrite <- Frame. exact Act.
      * rewrite Other.
        -- left. split; [reflexivity|]. rewrite <- Unchanged by congruence.
           exact Frame.
        -- rewrite (DeadlockCoherence.role_step_actor m R _ _ _ _ _ _ _ _ _
          Act).
           exact Ne.
    + right. rewrite Head. eexists; reflexivity.
Qed.
End FirstAction.

Lemma receives_other_actor {E S} s p sid (a : @source_action E S) :
  action_actor a <> p -> receives (s,p,sid) a = [].
Proof.
  destruct a; cbn [action_actor receives]; intro Ne; try reflexivity.
  all: destruct (key_eq_dec _ _) as [Eq|N];
    [inversion Eq; contradiction|reflexivity].
Qed.

Lemma emits_other_actor {E S} R s p sid (a : @source_action E S) :
  action_actor a <> s -> emits R (s,p,sid) a = [].
Proof.
  destruct a; cbn [action_actor emits]; intro Ne; try reflexivity.
  - destruct (key_eq_dec _ _) as [Eq|N]; [inversion Eq;
    contradiction|reflexivity].
  - apply key_paths_absent. unfold announcement_messages.
    apply Forall_forall. intros g Member. apply in_map_iff in Member.
    destruct Member as [peer [<- _]]. cbn [message_key].
    intro Eq; inversion Eq; contradiction.
Qed.

Section RootHead.
Context {M E : Type -> Type} {Store Input : Type}.
Variable m : DeadlockLocal.local_model M E role (Store * Input).
Variable stores : role -> Store.
Variable input : Input.
Variable R : list role.
Variable A : role -> Type.
Variable c : forall p, Choreo M p (A p).
Local Notation sm := (shared_model m).

Lemma root_head_first_steps tc s tn n gs p X kind sender rd :
  matched_prefix m stores input R A c tc s tn n gs ->
  receive_site sm p (A p) (positions s p) X kind [] sender rd ->
  (forall st q a u st' q',
    role_step sm R (A sender) (Code [] (c sender)) st q a u st' q' ->
    exists tail, emits R (sender,p,Choreography.Network.Root) a = [] :: tail) ->
  (forall st q a u st' q',
    role_step sm R (A p) (Code [] (c p)) st q a u st' q' ->
    exists tail, receives (sender,p,Choreography.Network.Root) a = [] :: tail)
      ->
  forall g, first_for (sender,p,Choreography.Network.Root) gs g ->
    message_path g = [].
Proof.
  intros Prefix Site Sender Receiver g Head.
  pose proof (prefix_source_run m stores input R A c _ _ _ _ _ Prefix) as Run.
  pose proof (initial_ledger sm R A p
    (receives (sender,p,Choreography.Network.Root))
    (receives_other_actor sender p Choreography.Network.Root)
    (DeadlockMatch.source_initial stores input A c) Receiver _ _ Run) as Recv.
  assert (Received : received (sender,p,Choreography.Network.Root) tc = []).
  { destruct Recv as [[Empty _]|[tail Eq]]; [exact Empty|].
    exfalso. eapply (matched_future_unreceived m stores input R A c
      _ _ _ _ _ sender p Choreography.Network.Root [] Prefix).
     - eapply receive_site_future; exact Site.
    - assert (Old : In [] ([] :: tail)) by now left.
      rewrite <- Eq in Old. exact Old. }
  pose proof (initial_ledger sm R A sender
    (emits R (sender,p,Choreography.Network.Root))
    (emits_other_actor R sender p Choreography.Network.Root)
    (DeadlockMatch.source_initial stores input A c) Sender _ _ Run) as Send.
  pose proof (prefix_ledger m stores input R A c _ _ _ _ _
    (sender,p,Choreography.Network.Root) Prefix) as Ledger.
  rewrite Received in Ledger. cbn [app] in Ledger.
  destruct (head_key_path _ _ _ Head) as [rest Pending].
  destruct Send as [[Empty _]|[tail Eq]].
  - change (sent R (sender,p,Choreography.Network.Root) tc = []) in Empty.
    rewrite Ledger, Pending in Empty; discriminate.
  - change (sent R (sender,p,Choreography.Network.Root) tc = [] :: tail) in Eq.
    rewrite Ledger, Pending in Eq. now injection Eq as -> _.
Qed.

Theorem source_head_paths_root tc s tn n gs p :
  well_formed R M A c ->
  matched_prefix m stores input R A c tc s tn n gs ->
  In p R ->
  forall X kind sender rd,
    receive_site sm p (A p) (positions s p) X kind [] sender rd ->
    forall g, first_for (sender,p,Choreography.Network.Root) gs g ->
      message_path g = [].
Proof.
  intros [_ [Q WF]] Prefix Member X kind sender rd Site.
  pose proof (structural_root_ready WF p Member (fun l H => H) Member) as Ready.
  destruct (root_site_contract sm R p A c (stores,input) tc s
    X kind sender rd _ (prefix_source_run m stores input R A c _ _ _ _ _ Prefix)
    Site Ready) as [[present Sender] Receiver].
  eapply root_head_first_steps; [exact Prefix|exact Site| |].
  - intros. eapply sender_first; [eassumption|].
  split; [reflexivity|exact Sender].
  - intros. eapply receiver_first; [eassumption|].
  split; [reflexivity|exact Receiver].
Qed.
End RootHead.

Print Assumptions source_head_paths_root.
