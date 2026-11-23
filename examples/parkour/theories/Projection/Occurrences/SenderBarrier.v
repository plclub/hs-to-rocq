From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Projection.Payloads.StaticPackets
  Projection.FIFO.Heads.RootOccurrence Choreography.Histories.RoleChronology
  Choreography.Occurrences Choreography.PendingDeliveries Choreography.RoleSteps
  Choreography.Execution Network.Mailboxes Projection.FIFO.ChannelLedger
  Choreography.Histories.CursorHistories Projection.FIFO.MessageRepresentation
  Choreography.Precedence Projection.SessionPaths Semantics.LocalEffects
  Semantics.Runs.
Require Import Control.Monad.Tree Choreography.Choreo2 Parkour.Symbol.
Import ListNotations.

Definition packed_ready {M p} R receiver (code : option (packed_choreo M p)) :=
  match code with
  | Some (existT _ _ t) => sender_node R t receiver
  | None => False
  end.

Section Barrier.
Context {M E : Type -> Type} {S : Type}.
Variable m : local_model M E role S.
Variable R : list role.
Variable p receiver : role.
Variable site : occurrence.

(* A designated static action remains in the live prefix/branch until the
   sender executes it. A returned prefix cannot contain this guard. *)
Fixpoint guarding {B} (t : @cursor M E p B) : Prop :=
  match t with
  | Code o c => exists path, site = o ++ path /\
      packed_ready R receiver (choreo_at_static_path path c)
  | Seq _ u _ => guarding u
  | Fork f x => guarding f \/ guarding x
  | _ => False
  end.

Lemma descend_perf_ready B o (sig : ChoreoSig M p B) :
  guarding (Code o (Perf sig)) ->
  site = o /\ sender_node R (Perf sig) receiver.
Proof.
  intros ([|edge path] & Eq & Ready).
  - rewrite app_nil_r in Eq. auto.
  - destruct edge; contradiction.
Qed.

Lemma guarding_future B (t : @cursor M E p B) :
  guarding t -> future t site.
Proof.
  induction t; cbn [guarding future]; try tauto.
  intros (path & -> & _). now exists path.
Qed.

Lemma silent_guarding B t u :
  @silent M E S m p B t u -> guarding t -> guarding u.
Proof.
  induction 1; cbn [guarding] in *; try tauto.
  - intros ([|e path] & Eq & Ready); [contradiction|].
    destruct e; contradiction.
  - intros ([|e path] & Eq & Ready); [contradiction|].
    destruct e; try contradiction.
    exists path. split; [|exact Ready].
    unfold child. now rewrite <- app_assoc.
  - intros ([|e path] & Eq & Ready); [contradiction|].
    destruct e; try contradiction;
      [left|right]; exists path; split; try exact Ready;
      unfold child; now rewrite <- app_assoc.
  - intros ([|e path] & Eq & Ready); [contradiction|].
    destruct e; contradiction.
  - intros ([|e path] & Eq & Ready); [contradiction|].
    destruct e; contradiction.
  - intros ([|e path] & Eq & Ready).
    + cbn [choreo_at_static_path packed_ready sender_node] in Ready. intuition
      congruence.
    + destruct e; contradiction.
  - intros ([|e path] & Eq & Ready).
    + cbn [choreo_at_static_path packed_ready sender_node] in Ready. intuition
      congruence.
    + destruct e; contradiction.
Qed.

Lemma step_guarding B t st q a u st' q' :
  @role_step M E S m R p B t st q a u st' q' ->
  guarding t ->
  In site (emits R (p,receiver,session_at site Choreography.Network.Root) a) \/
  guarding u.
Proof.
  intro Step. induction Step; intro Guard; cbn [guarding] in *;
    try contradiction.
  - destruct (descend_perf_ready _ _ _ Guard) as [-> Ready].
    cbn [sender_node] in Ready. destruct Ready as [_ [<- Ne]].
    left. cbn [emits]. destruct (key_eq_dec _ _) as [Eq|N];
      [now left|contradiction].
  - destruct (descend_perf_ready _ _ _ Guard) as [_ Ready].
    cbn [sender_node] in Ready. intuition congruence.
  - destruct (descend_perf_ready _ _ _ Guard) as [-> Ready].
    cbn [sender_node] in Ready. destruct Ready as [_ [Ne Member]].
    left. unfold emits.
    unfold announcement_messages.
    unfold key_paths. apply in_map_iff.
    exists (Message unit ChoiceDelivery o p receiver tt
      Parkour.Codec.show_unit).
    split; [reflexivity|]. apply filter_In. split.
    + apply in_map_iff. exists receiver. split; [reflexivity|].
      apply filter_In. split; [exact Member|].
      destruct (role_eq_dec receiver p); [congruence|reflexivity].
    + cbn [message_key]. destruct (key_eq_dec _ _); [reflexivity|contradiction].
  - destruct (descend_perf_ready _ _ _ Guard) as [_ Ready].
    cbn [sender_node] in Ready. intuition congruence.
  - destruct (IHStep Guard); auto.
  - destruct Guard as [Guard|Guard]; [destruct (IHStep Guard)|]; auto.
  - destruct Guard as [Guard|Guard]; [|destruct (IHStep Guard)]; auto.
  - apply IHStep. eapply silent_guarding; eassumption.
Qed.

Lemma run_guarding A start tr finish :
  @Choreography.Execution.run M E S m R A start tr finish ->
  guarding (positions start p) ->
  In site (sent R (p,receiver,session_at site Choreography.Network.Root) tr) \/
  guarding (positions finish p).
Proof.
  induction 1 as [s|s tr middle a finish Run IH Step]; intro Guard.
  - right; exact Guard.
  - unfold sent in *. rewrite flat_map_app. apply or_ind with
      (A := In site (flat_map (emits R (p,receiver,session_at site
        Choreography.Network.Root)) tr))
      (B := guarding (positions middle p)).
    + intro Old. left. apply in_or_app; auto.
    + intro Now. destruct Step as [who act u Member Act Frame].
      destruct (role_eq_dec who p) as [->|Ne].
      * destruct (step_guarding _ _ _ _ _ _ _ _ Act Now) as [Issued|Rest].
        -- left. apply in_or_app; right. cbn. now rewrite app_nil_r.
        -- right; exact Rest.
      * right. rewrite <- Frame by congruence. exact Now.
    + apply IH; exact Guard.
Qed.
End Barrier.

Lemma emitted_path {E S} R k site (a : @source_action E S) :
  In site (emits R k a) -> site = action_path a.
Proof.
  destruct a; cbn [emits]; try contradiction.
  - destruct (key_eq_dec _ _); cbn; intuition congruence.
  - unfold key_paths, announcement_messages.
    intro Member. apply in_map_iff in Member.
    destruct Member as (g & <- & Member). apply filter_In in Member.
    destruct Member as [Member _]. apply in_map_iff in Member.
    destruct Member as (peer & <- & _). reflexivity.
Qed.

Lemma run_role_scoped {M E S} (m : local_model M E role S) R A start tr finish p
  root :
  @Choreography.Execution.run M E S m R A start tr finish ->
  scoped root (positions start p) -> scoped root (positions finish p).
Proof.
  induction 1; intro Scope; [exact Scope|].
  destruct H0 as [who a u Member Act Frame].
  destruct (role_eq_dec who p) as [->|Ne].
  - eapply role_scoped; [exact Act|auto].
  - rewrite <- Frame by congruence; auto.
Qed.

(* The ledger is the given source run, not a newly constructed traversal of
   the source subtree. In particular, a later dynamic send forces the static
   sender action into this very prefix. *)
Theorem static_sender_predecessor_history {M E S}
    (m : local_model M E role S) R A (c : forall p, Choreo M p (A p))
    initial_store tr finish p receiver site st q a u st' q' :
  @Choreography.Execution.run M E S m R A (initial c initial_store)
    tr finish ->
  packed_ready R receiver (choreo_at_static_path site (c p)) ->
  role_step m R (A p) (positions finish p) st q a u st' q' ->
  consuming a ->
  source_before site (action_path a) ->
  In site (sent R (p,receiver,session_at site Choreography.Network.Root) tr).
Proof.
  intros Run Ready Step Consuming Before.
  destruct (run_guarding m R p receiver site A _ _ _ Run)
    as [Issued|Guard].
  - exists site. auto.
  - exact Issued.
  - destruct (step_guarding m R p receiver site _ _ _ _ _ _ _ _ Step Guard)
      as [Issued|Rest].
    + apply emitted_path in Issued. subst site.
      exfalso; exact (source_before_irreflexive _ Before).
    + exfalso.
      pose proof (run_role_scoped m R A _ _ _ p [] Run (path_prefix_refl [])) as
        Scope.
      exact (proj2 (role_consumes m R p _ _ _ _ _ _ _ _ Step [] Scope
        Consuming site (guarding_future R p receiver site _ u Rest)) Before).
Qed.

Lemma emission_consuming {E S} R k b (a : @source_action E S) :
  In b (emits R k a) -> consuming a.
Proof. destruct a; cbn [emits consuming]; try contradiction; auto. Qed.

Theorem static_sender_barrier {M E S}
    (m : local_model M E role S) R A (c : forall p, Choreo M p (A p))
    initial_store priorTC before a after sender receiver site b :
  @Choreography.Execution.run M E S m R A (initial c initial_store)
    priorTC before ->
  guarding R sender receiver site (@Code M E sender (A sender) [] (c sender)) ->
  Choreography.Execution.step m R before a after ->
  In b (emits R (sender,receiver,session_at site Choreography.Network.Root) a)
    ->
  source_before site b ->
  In site (sent R (sender,receiver,session_at site Choreography.Network.Root)
    priorTC).
Proof.
  intros Run (path & Eq & Ready) Next Emitted Before.
  cbn in Eq. subst path.
  assert (Actor : action_actor a = sender).
  { destruct (role_eq_dec (action_actor a) sender) as [Eq|Ne]; [exact Eq|].
    pose proof (emits_other_actor R sender receiver
      (session_at site Choreography.Network.Root) a Ne) as Empty.
    exfalso. apply (eq_ind _ (fun xs => In b xs) Emitted _ Empty). }
  destruct Next as [who act u Member Step Frame].
  pose proof (role_step_actor m R _ _ _ _ _ _ _ _ _ Step) as Who.
  rewrite Actor in Who. subst who.
  eapply static_sender_predecessor_history; [exact Run|exact Ready|exact Step|
    |].
  - eapply emission_consuming; exact Emitted.
  - rewrite <- (emitted_path _ _ _ _ Emitted). exact Before.
Qed.
