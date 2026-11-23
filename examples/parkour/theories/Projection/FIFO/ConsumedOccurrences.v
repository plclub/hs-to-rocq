From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Choreography.RoleSteps
  Choreography.Execution Choreography.Histories.CursorHistories
  Choreography.Histories.RoleChronology Projection.FIFO.ChannelLedger
  Projection.Matching.PrefixRelation Semantics.SharedState.
Require Import Parkour.Symbol.
Import ListNotations.
Local Arguments positions {M E Store A} _ _.

Section Histories.
Context {M E : Type -> Type} {S : Type}.
Variable model : LocalEffects.local_model M E Symbol S.
Variable R : list Symbol.

Lemma cursor_history_scoped p A (start finish : @cursor M E p A) tr root :
  cursor_history model R start tr finish ->
  scoped root start -> scoped root finish.
Proof.
  intro H; induction H; intro Scope; [exact Scope| |].
  - eapply silent_scoped; [apply silent_plug; apply primitive_is_silent; exact
    H0|].
    now apply IHcursor_history.
  - eapply role_scoped.
    + apply role_step_plug. apply primitive_is_role_step. exact H0.
    + now apply IHcursor_history.
Qed.

(* Unlike a subtree witness, this lemma preserves membership in the exact
   enclosing role trace. Silent bookkeeping does not add any actions. *)
Lemma cursor_history_consumed_safe p A
    (start finish : @cursor M E p A) tr root a :
  cursor_history model R start tr finish ->
  scoped root start -> In a tr -> consuming a ->
  safe (action_path a) finish.
Proof.
  intro H; induction H; intros Scope Member Consume; [contradiction| |].
  - intros z Future. apply (IHcursor_history Scope Member Consume).
    eapply silent_future;
      [apply silent_plug; apply primitive_is_silent; exact H0|exact Future].
  - apply in_app_or in Member. destruct Member as [Old|[Eq|No]].
    + intros z Future. apply (IHcursor_history Scope Old Consume).
      assert (Step : role_step model R A (plug C before) s q a0
        (plug C after) s' q').
      { apply role_step_plug. apply primitive_is_role_step. exact H0. }
      exact (proj1 (role_future _ _ _ _ _ _ _ _ _ _ _ Step) z Future).
    + subst a. eapply role_consumes.
      * apply role_step_plug. apply primitive_is_role_step. exact H0.
      * eapply cursor_history_scoped; eassumption.
      * exact Consume.
    + contradiction.
Qed.

End Histories.

Lemma received_member_action {E S} sender receiver sid o
    (tr : list (@source_action E S)) :
  In o (received (sender,receiver,sid) tr) ->
  exists a, In a tr /\ action_actor a = receiver /\
    action_path a = o /\ consuming a.
Proof.
  unfold received. intro Member. apply in_flat_map in Member.
  destruct Member as [a [InA At]]. exists a. split; [exact InA|].
  destruct a; cbn [receives] in At; try contradiction;
    destruct (Mailboxes.key_eq_dec _ _) as [Eq|Ne]; try contradiction;
    destruct At as [<-|No]; try contradiction;
    inversion Eq; subst; repeat split; exact I.
Qed.

Section Prefixes.
Context {M E : Type -> Type} {Store Input : Type}.
Variable model : LocalEffects.local_model M E Symbol (Store * Input).
Variable stores : Symbol -> Store.
Variable input : Input.
Variable R : list Symbol.
Variable A : Symbol -> Type.
Variable c : forall p, Choreography.Choreo2.Choreo M p (A p).
Local Notation sm := (shared_model model).

(* Freshness is a consequence of the actual matched history; it is not a
   premise supplied alongside an alleged source frontier. *)
Theorem matched_received_safe tc s tn n gs sender receiver sid o :
  matched_prefix model stores input R A c tc s tn n gs ->
  In o (received (sender,receiver,sid) tc) ->
  safe o (positions s receiver).
Proof.
  intros Prefix Member.
  destruct (received_member_action _ _ _ _ _ Member)
    as (a & InA & Actor & Path & Consume).
  pose proof (prefix_source_run model stores input R A c
    _ _ _ _ _ Prefix) as Run.
  pose proof (initial_actor_history sm R A c (stores,input)
    _ _ Run receiver) as Hist.
  rewrite <- Path. eapply cursor_history_consumed_safe.
  - exact Hist.
  - apply path_prefix_refl.
  - unfold actor_actions. apply filter_In. split; [exact InA|].
    rewrite Actor.
    destruct (list_eq_dec BinNat.N.eq_dec receiver receiver); congruence.
  - exact Consume.
Qed.

Corollary matched_future_unreceived tc s tn n gs sender receiver sid o :
  matched_prefix model stores input R A c tc s tn n gs ->
  future (positions s receiver) o ->
  ~ In o (received (sender,receiver,sid) tc).
Proof.
  intros Prefix Future Old.
  destruct (matched_received_safe _ _ _ _ _ _ _ _ _ Prefix Old o Future)
    as [Different _].
  apply Different; reflexivity.
Qed.

End Prefixes.

Print Assumptions cursor_history_scoped.
Print Assumptions cursor_history_consumed_safe.
Print Assumptions received_member_action.
Print Assumptions matched_received_safe.
Print Assumptions matched_future_unreceived.
