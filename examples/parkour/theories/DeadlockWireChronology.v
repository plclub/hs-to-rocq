From Stdlib Require Import Lists.List Sorting.Sorted.
Require Import DeadlockSource DeadlockNetwork DeadlockOrder DeadlockMessages
  DeadlockFrontiers DeadlockCoherence DeadlockChronology DeadlockFrontierCoverage
  DeadlockMatch DeadlockState DeadlockFirstSend DeadlockHead.
Import ListNotations.
Local Arguments positions {M E Store A} _ _.

Lemma strongly_sorted_snoc {T} (Rel : T -> T -> Prop) xs y :
  StronglySorted Rel xs -> Forall (fun x => Rel x y) xs ->
  StronglySorted Rel (xs ++ [y]).
Proof.
  intro S; induction S; intro F; cbn; constructor.
  - constructor.
  - constructor.
  - apply IHS. inversion F; assumption.
  - rewrite Forall_app. split; [assumption|].
    inversion F; subst; now constructor.
Qed.

Section Histories.
Context {M E : Type -> Type} {S : Type}.
Variable m : DeadlockLocal.local_model M E role S.
Variable R : list role.

Lemma cursor_history_chronology p A (t u : @cursor M E p A) tr root :
  cursor_history m R t tr u -> scoped root t ->
  StronglySorted
    (fun a b => consuming a -> fresh_after (action_path a) (action_path b)) tr.
Proof.
  intro H; induction H; intro Scope; [constructor|now apply IHcursor_history|].
  apply strongly_sorted_snoc; [now apply IHcursor_history|].
  rewrite Forall_forall. intros old Member Consume.
  eapply cursor_history_consumed_safe; [exact H|exact Scope|exact Member|exact Consume|].
  assert (Step : role_step m R A (plug C before) s q a
    (plug C after) s' q').
  { apply role_step_plug. apply primitive_is_role_step. exact H0. }
  exact (proj2 (role_future _ _ _ _ _ _ _ _ _ _ _ Step)).
Qed.
End Histories.

(* A configured role can occur at most once in an announcement batch. This
   is essential: chronology separates distinct actions, not recipients of
   the same action. *)
Lemma announcement_key_single X o owner (x : X) sh R sender receiver sid :
  NoDup R ->
  key_paths (sender,receiver,sid) (announcement_messages X o owner x sh R) = [] \/
  key_paths (sender,receiver,sid) (announcement_messages X o owner x sh R) = [o].
Proof.
  intro ND; induction ND as [|r rs Absent ND IH]; [now left|].
  unfold announcement_messages in *; cbn [filter].
  destruct (role_eq_dec r owner) as [Eq|Ne]; [exact IH|].
  cbn [map].
  destruct (key_eq_dec
    (message_key (Message X ChoiceDelivery o owner r x sh))
    (sender,receiver,sid)) as [Eq|NeK].
  - rewrite <- Eq, key_paths_same.
    assert (Empty : key_paths (message_key (Message X ChoiceDelivery o owner r x sh))
      (map (fun peer => Message X ChoiceDelivery o owner peer x sh)
        (filter (fun peer => if role_eq_dec peer owner then false else true) rs)) = []).
    { apply key_paths_absent. rewrite Forall_forall. intros g InG.
      apply in_map_iff in InG. destruct InG as [peer [<- InPeer]].
      apply filter_In in InPeer as [InPeer _].
      cbn [message_key]. intro E; inversion E; subst; contradiction. }
    rewrite Empty. now right.
  - rewrite key_paths_other by exact NeK. exact IH.
Qed.

Lemma emits_single {E S} R k (a : @source_action E S) :
  NoDup R -> emits R k a = [] \/ emits R k a = [action_path a].
Proof.
  intro ND; destruct a; cbn [emits action_path]; try (now left).
  - destruct (key_eq_dec _ _); [now right|now left].
  - destruct k as [[sender receiver] sid]. apply announcement_key_single; exact ND.
Qed.

Lemma emits_member {E S} R sender receiver sid (a : @source_action E S) o :
  In o (emits R (sender,receiver,sid) a) ->
  action_actor a = sender /\ action_path a = o /\ consuming a /\
  session_at o Choreography.Network.Root = sid.
Proof.
  destruct a; cbn [emits]; intro H; try contradiction.
  - destruct (key_eq_dec _ _) as [Eq|Ne]; [|contradiction].
    destruct H as [<-|No]; [|contradiction]. inversion Eq; subst; repeat split; exact I.
  - apply path_member in H. destruct H as [g [InG [Key Path]]].
    unfold announcement_messages in InG. apply in_map_iff in InG.
    destruct InG as [peer [<- _]]. cbn [message_key message_path] in *.
    inversion Key; subst. repeat split; exact I.
Qed.

Lemma sent_actor_actions {E S} R sender receiver sid (tr : list (@source_action E S)) :
  sent R (sender,receiver,sid) (actor_actions sender tr) =
  sent R (sender,receiver,sid) tr.
Proof.
  unfold sent, actor_actions. induction tr as [|a tr IH]; [reflexivity|].
  cbn [filter]. destruct (list_eq_dec BinNat.N.eq_dec (action_actor a) sender)
    as [Eq|Ne]; cbn [flat_map]; rewrite IH; [reflexivity|].
  assert (Empty : emits R (sender,receiver,sid) a = []).
  { destruct (emits R (sender,receiver,sid) a) as [|o rest] eqn:Em; [reflexivity|].
    exfalso. apply Ne.
    exact (proj1 (emits_member R sender receiver sid a o
      ltac:(rewrite Em; now left))). }
  rewrite Empty. reflexivity.
Qed.

Lemma flat_emits_chronology {E S} R k (tr : list (@source_action E S)) :
  NoDup R ->
  StronglySorted
    (fun a b => consuming a -> fresh_after (action_path a) (action_path b)) tr ->
  StronglySorted fresh_after (sent R k tr).
Proof.
  intros ND H; induction H as [|a tr Sorted IH Later]; [constructor|].
  change (StronglySorted fresh_after (emits R k a ++ sent R k tr)).
  destruct (emits_single R k a ND) as [Empty|One]; rewrite ?Empty, ?One;
    cbn [app]; [exact IH|].
  constructor; [exact IH|]. rewrite Forall_forall.
  intros o InO. unfold sent in InO. apply in_flat_map in InO.
  destruct InO as [b [InB EmB]].
  destruct k as [[sender receiver] sid].
  destruct (emits_member R sender receiver sid b o EmB) as [_ [Path _]].
  assert (EmA : In (action_path a) (emits R (sender,receiver,sid) a)).
  { rewrite One; now left. }
  destruct (emits_member R sender receiver sid a _ EmA) as [_ [_ [Consume _]]].
  rewrite <- Path. rewrite Forall_forall in Later. now apply Later.
Qed.

Lemma fresh_sorted_nodup xs :
  StronglySorted fresh_after xs -> NoDup xs.
Proof.
  induction 1 as [|x xs Sort IH Later]; constructor; [|exact IH].
  intro InX. rewrite Forall_forall in Later.
  exact (proj1 (Later x InX) eq_refl).
Qed.

Section Prefixes.
Context {M E : Type -> Type} {Store Input : Type}.
Variable model : DeadlockLocal.local_model M E role (Store * Input).
Variable stores : role -> Store.
Variable input : Input.
Variable R : list role.
Variable A : role -> Type.
Variable c : forall p, Choreography.Choreo2.Choreo M p (A p).
Local Notation sm := (shared_model model).
Local Notation prefix := (matched_prefix model stores input R A c).

Theorem matched_sent_chronology tc s tn n gs sender receiver sid :
  NoDup R -> prefix tc s tn n gs ->
  StronglySorted fresh_after (sent R (sender,receiver,sid) tc).
Proof.
  intros ND P. rewrite <- sent_actor_actions.
  apply flat_emits_chronology; [exact ND|].
  eapply cursor_history_chronology.
  - exact (initial_actor_history sm R A c (stores,input) _ _
      (prefix_source_run model stores input R A c _ _ _ _ _ P) sender).
  - apply extends_refl.
Qed.

Theorem matched_sent_nodup tc s tn n gs sender receiver sid :
  NoDup R -> prefix tc s tn n gs ->
  NoDup (sent R (sender,receiver,sid) tc).
Proof.
  intros ND P. apply fresh_sorted_nodup.
  eapply matched_sent_chronology; eassumption.
Qed.

(* Compatibility is the sole layout obligation. Freshness and the direction
   of the source order come from the sender's actual chronological history. *)
Theorem matched_sent_sorted tc s tn n gs sender receiver sid :
  NoDup R -> prefix tc s tn n gs ->
  (forall x y, In x (sent R (sender,receiver,sid) tc) ->
    In y (sent R (sender,receiver,sid) tc) -> compatible x y) ->
  StronglySorted source_before (sent R (sender,receiver,sid) tc).
Proof.
  intros ND P Compat.
  pose proof (matched_sent_chronology tc s tn n gs sender receiver sid ND P) as Hist.
  assert (Sessions : forall o, In o (sent R (sender,receiver,sid) tc) ->
    session_at o Choreography.Network.Root = sid).
  { intros o Member. unfold sent in Member. apply in_flat_map in Member.
    destruct Member as [a [_ Em]].
    exact (proj2 (proj2 (proj2 (emits_member R sender receiver sid a o Em)))). }
  revert Compat Sessions. induction Hist as [|x xs Sorted IH Later];
    intros Compat Sessions; constructor.
  - apply IH.
    + intros a b Ha Hb. apply Compat; now right.
    + intros a Ha. apply Sessions; now right.
  - rewrite Forall_forall in Later |- *. intros y Hy.
    destruct (Later y Hy) as [Ne NotBefore].
    destruct (same_session_order x y Choreography.Network.Root
      (Compat x y (or_introl eq_refl) (or_intror Hy))
      ltac:(congruence)
      ltac:(rewrite (Sessions x (or_introl eq_refl)),
        (Sessions y (or_intror Hy)); reflexivity)) as [Before|Before].
    + exact Before.
    + contradiction.
Qed.

Theorem matched_head_from_layout tc s tn n gs sender receiver site head :
  NoDup R -> prefix tc s tn n gs ->
  future (positions s receiver) site ->
  (forall x y, In x (sent R (sender,receiver,
      session_at site Choreography.Network.Root) tc) ->
    In y (sent R (sender,receiver,
      session_at site Choreography.Network.Root) tc) -> compatible x y) ->
  (site = message_path head \/
    source_before (message_path head) site \/
    source_before site (message_path head)) ->
  (source_before (message_path head) site ->
    In (message_path head) (received (sender,receiver,
      session_at site Choreography.Network.Root) tc)) ->
  (source_before site (message_path head) ->
    In site (sent R (sender,receiver,
      session_at site Choreography.Network.Root) tc)) ->
  first_for (sender,receiver,session_at site Choreography.Network.Root) gs head ->
  message_path head = site.
Proof.
  intros ND P Future Compat Compare ReceiverPast SenderPast Head.
  pose proof (matched_sent_sorted tc s tn n gs sender receiver
    (session_at site Choreography.Network.Root) ND P Compat) as Sorted.
  pose proof (prefix_ledger model stores input R A c _ _ _ _ _
    (sender,receiver,session_at site Choreography.Network.Root) P) as Ledger.
  destruct (head_key_path _ _ _ Head) as [tail Pending].
  rewrite Pending in Ledger.
  eapply ordered_head_coverage.
  - rewrite <- Ledger. exact Sorted.
  - eapply matched_future_unreceived; eassumption.
  - exact Compare.
  - exact ReceiverPast.
  - intros Before. rewrite <- Ledger. now apply SenderPast.
Qed.

(* The layout supplies compatibility and mandatory-predecessor evidence.
   The ledger itself places the pending head in the actual sent history;
   neither head identity nor current-site membership is assumed. *)
Theorem matched_head_identity tc s tn n gs sender receiver site head :
  NoDup R -> prefix tc s tn n gs ->
  future (positions s receiver) site ->
  (forall x y, In x (sent R (sender,receiver,
      session_at site Choreography.Network.Root) tc) ->
    In y (sent R (sender,receiver,
      session_at site Choreography.Network.Root) tc) -> compatible x y) ->
  (forall x, In x (sent R (sender,receiver,
      session_at site Choreography.Network.Root) tc) -> compatible x site) ->
  (forall x, In x (sent R (sender,receiver,
      session_at site Choreography.Network.Root) tc) ->
    source_before x site ->
    In x (received (sender,receiver,
      session_at site Choreography.Network.Root) tc)) ->
  (forall x, In x (sent R (sender,receiver,
      session_at site Choreography.Network.Root) tc) ->
    source_before site x ->
    In site (sent R (sender,receiver,
      session_at site Choreography.Network.Root) tc)) ->
  first_for (sender,receiver,session_at site Choreography.Network.Root) gs head ->
  message_path head = site.
Proof.
  intros ND P Future Compat Current ReceiverPast SenderPast Head.
  assert (Member : In (message_path head)
    (sent R (sender,receiver,session_at site Choreography.Network.Root) tc)).
  { rewrite (prefix_ledger model stores input R A c _ _ _ _ _ _ P).
    apply in_or_app; right.
    destruct (head_key_path _ _ _ Head) as [tail Pending].
    rewrite Pending; now left. }
  assert (Session : session_at (message_path head) Choreography.Network.Root =
    session_at site Choreography.Network.Root).
  { unfold sent in Member. apply in_flat_map in Member.
    destruct Member as [a [_ Em]].
    exact (proj2 (proj2 (proj2 (emits_member R sender receiver
      (session_at site Choreography.Network.Root) a _ Em)))). }
  eapply matched_head_from_layout; [exact ND|exact P|exact Future|exact Compat| | | |exact Head].
  - destruct (equal_lane_order _ _ (Current _ Member)
      (proj1 (same_session_iff _ _ Choreography.Network.Root) Session))
      as [Eq|[Before|Before]].
    + left; symmetry; exact Eq.
    + right; now left.
    + right; now right.
  - now apply ReceiverPast.
  - now apply SenderPast.
Qed.
End Prefixes.

Print Assumptions matched_sent_chronology.
Print Assumptions matched_sent_nodup.
Print Assumptions matched_sent_sorted.
Print Assumptions matched_head_from_layout.
Print Assumptions matched_head_identity.
