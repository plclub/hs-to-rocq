From Stdlib Require Import Lists.List Arith.PeanoNat.
From ParkourTheories Require Import Semantics.LocalEffects Semantics.SharedState
  Semantics.Runs Choreography.Occurrences Choreography.PendingDeliveries
  Choreography.RoleSteps Choreography.Execution Network.Mailboxes
  Network.Endpoints Network.Execution Projection.FIFO.MessageRepresentation
  Projection.SessionPaths Projection.Matching.CursorAlignment
  Projection.EndpointRunner.
Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree.
Require Choreography.Choreo2.
Import ListNotations.
Import Choreography.Choreo2 (At, unAt, Comm, Cond, Choreo).
Arguments Choreography.Execution.positions {M E Store A} _ _.
Arguments Choreography.Execution.deliveries {M E Store A} _.
Arguments Choreography.Execution.shared_store {M E Store A} _.

(* A receive removes one recipient's exact typed message, at the head of
   its ACTUAL wire key. In particular an opposite-kind entry cannot be skipped.
   Its Show came from a prior decorated source send, not an existential codec.
   *)
#[universes(template)]
Inductive delivery X kind o sender receiver (x : X) (rd : Read X) :
    list message -> wire -> list message -> Prop :=
| Deliver sh pre post :
    Forall (fun g => message_key g <>
      (sender,receiver,session_at o Choreography.Network.Root)) pre ->
    @read X rd (@show X sh x) = Some x ->
    delivery X kind o sender receiver x rd
      (pre ++ Message X kind o sender receiver x sh :: post)
      (@show X sh x) (pre ++ post).

Section Decorated.
Context {M E : Type -> Type} {S : Type}.
Variable model : local_model M E Symbol S.
Variable R : list Symbol.

(* These are source rules with transport decorations. The send/announce
   constructors mention the actual dictionaries in the exposed source syntax.
   Context rules retain the actual residuals and continuation functions. *)
Inductive decorated {p} :
    forall X, @cursor M E p X -> S -> list pending ->
      @source_action E S -> @cursor M E p X -> S -> list pending ->
      @action E S -> list message -> list message -> Prop :=
| DLocal X o t s a t' s' ps gs :
    local_step (reply_local _ _ _ _ model) p t s a t' s' ->
    decorated (At X p p) (RoleSteps.Local o t) s ps (LocalAction o
      a)
      (RoleSteps.Local o t') s' ps (Endpoints.Local a) gs
        gs
| DSend X d o sh rd kl kd sl v sd (h : d <> p) s gs :
    decorated (At X d p)
      (Code o (Perf (@Comm M p X p d sh rd kl kd sl v sd)))
      s (map pending_of gs) (SendAction X o p d (unAt v eq_refl))
      (Returned (off_at h)) s
      (map pending_of (gs ++ [Message X DataDelivery o p d (unAt v eq_refl)
        sh]))
      (Sent p d (session_at o Choreography.Network.Root) (@show X sh (unAt v
        eq_refl)))
      gs (gs ++ [Message X DataDelivery o p d (unAt v eq_refl) sh])
| DReceive X l o sh rd kl kd sl v sd (h : l <> p) s gs gs' x w :
    delivery X DataDelivery o l p x rd gs w gs' ->
    decorated (At X p p)
      (Code o (Perf (@Comm M p X l p sh rd kl kd sl v sd)))
      s (map pending_of gs) (ReceiveAction X o l p x)
      (Returned (here_at x)) s (map pending_of gs')
      (Received l p (session_at o Choreography.Network.Root) w) gs gs'
| DAnnounce X Y o sh rd kl sl v (k : X -> Choreo M p Y) s gs :
    decorated Y (Code o (Perf (@Cond M p X p Y sh rd kl sl v k)))
      s (map pending_of gs) (AnnounceAction X o p (unAt v eq_refl))
      (Code (child o ChoiceBody) (k (unAt v eq_refl))) s
      (map pending_of (gs ++ announcement_messages X o p (unAt v eq_refl) sh R))
      (Announced p (session_at o Choreography.Network.Root) (@show X sh (unAt v
        eq_refl)))
      gs (gs ++ announcement_messages X o p (unAt v eq_refl) sh R)
| DHear X Y l o sh rd kl sl v (k : X -> Choreo M p Y)
    (h : l <> p) s gs gs' x w :
    delivery X ChoiceDelivery o l p x rd gs w gs' ->
    decorated Y (Code o (Perf (@Cond M p X l Y sh rd kl sl v k)))
      s (map pending_of gs) (HearAction X o l p x)
      (Code (child o ChoiceBody) (k x)) s (map pending_of gs')
      (Received l p (session_at o Choreography.Network.Root) w) gs gs'
| DSeq X Y o t t' (k : X -> Choreo M p Y) s ps a s' ps' na gs gs' :
    decorated X t s ps a t' s' ps' na gs gs' ->
    decorated Y (Seq o t k) s ps a (Seq o t' k) s' ps' na gs gs'
| DLeft X Y (f f' : @cursor M E p (X -> Y)) t s ps a s' ps' na gs gs' :
    decorated (X -> Y) f s ps a f' s' ps' na gs gs' ->
    decorated Y (Fork f t) s ps a (Fork f' t) s' ps' na gs gs'
| DRight X Y (f : @cursor M E p (X -> Y)) t t' s ps a s' ps' na gs gs' :
    decorated X t s ps a t' s' ps' na gs gs' ->
    decorated Y (Fork f t) s ps a (Fork f t') s' ps' na gs gs'
| DSilent X t u t' s ps a s' ps' na gs gs' :
    silent model X t u ->
    decorated X u s ps a t' s' ps' na gs gs' ->
    decorated X t s ps a t' s' ps' na gs gs'.

Lemma delivery_source X kind o sender receiver (x : X) rd gs w gs' :
  delivery X kind o sender receiver x rd gs w gs' ->
  take_first_on_source_channel kind o sender receiver x (map pending_of gs) (map
    pending_of
    gs').
Proof.
  intros H. destruct H. apply source_take_different_keys. exact H.
Qed.

Theorem decorated_source p X t s ps a t' s' ps' na gs gs' :
  @decorated p X t s ps a t' s' ps' na gs gs' ->
  role_step model R X t s ps a t' s' ps'.
Proof.
  intro H. induction H.
  - apply RLocal. exact H.
  - rewrite map_app. cbn. apply RSend.
  - apply RReceive; [exact h|]. apply take_pending_at.
    eapply delivery_source. exact H.
  - rewrite map_app, announcement_pending. apply RAnnounce.
  - eapply RHear; [exact h|]. apply take_pending_at.
    eapply delivery_source. exact H.
  - apply RSeq. exact IHdecorated.
  - apply RLeft. exact IHdecorated.
  - apply RRight. exact IHdecorated.
  - eapply RSilent; eassumption.
Qed.

Theorem decorated_action p X t s ps a t' s' ps' na gs gs' :
  @decorated p X t s ps a t' s' ps' na gs gs' ->
  action_matches Choreography.Network.Root a na.
Proof.
  intro H. induction H; try assumption.
  - constructor.
  - apply MatchSend.
  - destruct H. eapply MatchReceive. exact H0.
  - apply MatchAnnounce.
  - destruct H. eapply MatchHear. exact H0.
Qed.
End Decorated.

Lemma delivery_singleton X kind o sender receiver (x : X) sh rd :
  @read X rd (@show X sh x) = Some x ->
  delivery X kind o sender receiver x rd
    [Message X kind o sender receiver x sh] (@show X sh x) [].
Proof. intro H. apply (Deliver _ _ _ _ _ _ _ sh [] []); [constructor|exact H].
Qed.

Lemma delivery_empty_impossible X kind o sender receiver (x : X) rd w gs' :
  ~ delivery X kind o sender receiver x rd [] w gs'.
Proof.
  intro H. inversion H as [sh pre post F D Eq]; subst.
  destruct pre; discriminate.
Qed.

(* Both data and choice use this same raw-key head equation. *)
Lemma delivery_fifo X kind o sender receiver (x : X) rd gs w gs' :
  delivery X kind o sender receiver x rd gs w gs' ->
  at_key (sender,receiver,session_at o Choreography.Network.Root) gs =
    w :: at_key (sender,receiver,session_at o Choreography.Network.Root) gs'.
Proof.
  intro H. destruct H. rewrite !at_key_app.
  rewrite (at_key_absent _ _ H).
  change (at_key (message_key (Message X kind o sender receiver x sh))
    (Message X kind o sender receiver x sh :: post) =
    @show X sh x :: at_key (sender,receiver,session_at o
      Choreography.Network.Root) post).
  rewrite at_key_same. reflexivity.
Qed.

Section Matching.
Context {M E : Type -> Type} {Store Input : Type}.
Variable model : local_model M E Symbol (Store * Input).
Variable stores : Symbol -> Store.
Variable input : Input.
Variable R : list Symbol.
Variable A : Symbol -> Type.
Variable c : forall p, Choreo M p (A p).
Definition source_initial :
    @Choreography.Execution.configuration M E ((Symbol -> Store) * Input) A :=
  Choreography.Execution.initial c
  (stores,input).
Definition network_initial :
    @Network.Execution.configuration M E ((Symbol -> Store) * Input) :=
  initialize R (fun p => runner (c p) Choreography.Network.Root) (stores,input).

(* Alignment is about residual syntax, not aggregate traces. No frontier,
   readiness or future-progress premise is built into this state relation. *)
Definition residuals
    (s :
      @Choreography.Execution.configuration M E ((Symbol -> Store) * Input) A)
    (n : @Network.Execution.configuration M E ((Symbol -> Store) * Input)) :
    Prop :=
  exists ns : forall p, @control M E (A p),
    endpoints n = map (fun p => Endpoint (A p) p (ns p)) R /\
    (forall p, In p R ->
      inhabited (aligned (shared_model model) Choreography.Network.Root
        p (A p) (positions s p)
        (ns p))).

Definition state_match
    (s :
      @Choreography.Execution.configuration M E ((Symbol -> Store) * Input) A)
    (n : @Network.Execution.configuration M E ((Symbol -> Store) * Input))
    gs : Prop :=
  Choreography.Execution.shared_store s = Network.Execution.shared_store n /\
  represents (deliveries s) (mailboxes n) gs /\ residuals s n.

(* One certificate chooses the SAME scheduled role on both machines.
   The network_step is not just a label-level fact: its active endpoint is ns p,
   and the exact residual endpoint is ns'. *)
Inductive paired_step
    (s :
      @Choreography.Execution.configuration M E ((Symbol -> Store) * Input) A)
    (n : @Network.Execution.configuration M E ((Symbol -> Store) * Input)) gs :
    @source_action E ((Symbol -> Store) * Input) ->
    @Choreography.Execution.configuration M E ((Symbol -> Store) * Input) A ->
    @action E ((Symbol -> Store) * Input) ->
    @Network.Execution.configuration M E ((Symbol -> Store) * Input) ->
    list message -> Prop :=
| PairStep p (pre post : list (@endpoint M E)) t t' s' n' a na gs' :
    In p R ->
    endpoints n = pre ++ Endpoint (A p) p t :: post ->
    endpoints n' = pre ++ Endpoint (A p) p t' :: post ->
    decorated (shared_model model) R (A p) (positions s p)
      (Choreography.Execution.shared_store s)
      (deliveries s) a (positions s' p) (Choreography.Execution.shared_store s')
      (deliveries s') na gs gs' ->
    (forall r, r <> p -> positions s r = positions s' r) ->
    Endpoints.step (shared_model model) R p (A p) t (mailboxes n)
      (Network.Execution.shared_store
      n)
      na t' (mailboxes n') (Network.Execution.shared_store n') ->
    paired_step s n gs a s' na n' gs'.

Lemma paired_source s n gs a s' na n' gs' :
  paired_step s n gs a s' na n' gs' ->
  Choreography.Execution.step (shared_model model) R s a s'.
Proof.
  intro H. destruct H. eapply CStep; [eassumption| |eassumption].
  eapply decorated_source. eassumption.
Qed.

Lemma paired_network s n gs a s' na n' gs' :
  paired_step s n gs a s' na n' gs' ->
  Network.Execution.step (shared_model model) R n na n'.
Proof.
  intro H. destruct H.
  destruct n as [es q st], n' as [es' q' st']; cbn in *.
  subst es es'. apply Schedule. assumption.
Qed.

Lemma paired_action s n gs a s' na n' gs' :
  paired_step s n gs a s' na n' gs' ->
  action_matches Choreography.Network.Root a na.
Proof. intro H. destruct H. eapply decorated_action. eassumption. Qed.

(* Prefixes extend in execution order. Next-state certificates restrict
   membership; they do NOT assert that every network step can be extended.
   A separately proved structural invariant can later establish that fact. *)
Inductive matched_prefix :
    list (@source_action E ((Symbol -> Store) * Input)) ->
    @Choreography.Execution.configuration M E ((Symbol -> Store) * Input) A ->
    list (@action E ((Symbol -> Store) * Input)) ->
    @Network.Execution.configuration M E ((Symbol -> Store) * Input) ->
    list message -> Prop
      :=
| PrefixInitial :
    matched_prefix [] source_initial [] network_initial []
| PrefixSnoc tc s tn n gs a s' na n' gs' :
    matched_prefix tc s tn n gs ->
    paired_step s n gs a s' na n' gs' ->
    state_match s' n' gs' ->
    matched_prefix (tc ++ [a]) s' (tn ++ [na]) n' gs'.

Definition matches tc s tn n : Prop :=
  exists gs, matched_prefix tc s tn n gs.

Lemma initial_state_match : state_match source_initial network_initial [].
Proof.
  split; [reflexivity|]. split; [apply represents_empty|].
  exists (fun p => load (runner (c p) Choreography.Network.Root)).
  split; [reflexivity|]. intros p _.
  constructor. apply initial_alignment.
Qed.

Theorem initial_matches : matches [] source_initial [] network_initial.
Proof. exists []. constructor. Qed.

Theorem prefix_state tc s tn n gs :
  matched_prefix tc s tn n gs -> state_match s n gs.
Proof. intro H. destruct H; [apply initial_state_match|assumption]. Qed.

Theorem prefix_order tc s tn n gs :
  matched_prefix tc s tn n gs -> length tc = length tn.
Proof.
  intro H. induction H; [reflexivity|].
  rewrite !length_app. cbn. now rewrite IHmatched_prefix.
Qed.

Theorem prefix_action_order tc s tn n gs :
  matched_prefix tc s tn n gs ->
  Forall2 (action_matches Choreography.Network.Root) tc tn.
Proof.
  intro H. induction H; [constructor|].
  apply Forall2_app; [exact IHmatched_prefix|].
  constructor; [eapply paired_action; eassumption|constructor].
Qed.

Theorem prefix_source_run tc s tn n gs :
  matched_prefix tc s tn n gs ->
  Choreography.Execution.run (shared_model model) R source_initial tc s.
Proof.
  intro H. induction H; [constructor|].
  eapply RunSnoc; [exact IHmatched_prefix|].
  eapply paired_source. eassumption.
Qed.

Lemma network_run_snoc n tn u na v :
  Network.Execution.run (shared_model model) R n tn u ->
  Network.Execution.step (shared_model model) R u na v ->
  Network.Execution.run (shared_model model) R n (tn ++ [na]) v.
Proof.
  intros H Next. induction H; cbn.
  - eapply RunCons; [exact Next|constructor].
  - eapply RunCons; [eassumption|apply IHrun; exact Next].
Qed.

Theorem prefix_network_run tc s tn n gs :
  matched_prefix tc s tn n gs ->
  Network.Execution.run (shared_model model) R network_initial tn n.
Proof.
  intro H. induction H; [constructor|].
  eapply network_run_snoc; [exact IHmatched_prefix|].
  eapply paired_network. eassumption.
Qed.

(* No distinct action can be inserted, dropped, or reordered on one side
   alone; the snoc history contains the exact decorated operational pair. *)
Theorem prefix_last tc s tn n gs a s' na n' gs' :
  matched_prefix tc s tn n gs ->
  paired_step s n gs a s' na n' gs' ->
  state_match s' n' gs' ->
  matches (tc ++ [a]) s' (tn ++ [na]) n'.
Proof. intros H P S. exists gs'. eapply PrefixSnoc; eassumption. Qed.

Theorem unequal_lengths_do_not_match tc s tn n :
  length tc <> length tn -> ~ matches tc s tn n.
Proof. intros N [gs H]. apply N. eapply prefix_order. exact H. Qed.

Theorem terminal_queues tc s tn n :
  matches tc s tn n ->
  (deliveries s = [] <-> forall k, mailboxes n k = []).
Proof.
  intros [gs H]. destruct (prefix_state _ _ _ _ _ H) as [_ [[P Q] _]].
  split.
  - intro Empty. assert (G : gs = []).
    { destruct gs; [reflexivity|]. cbn in P. rewrite Empty in P. discriminate. }
    subst gs. intro k. apply Q.
  - intro Empty. destruct gs as [|m gs]; [symmetry; exact P|].
    specialize (Empty (message_key m)).
    rewrite Q, at_key_same in Empty. discriminate.
Qed.
End Matching.
