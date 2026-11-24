From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Projection.Matching.PayloadHistory
  Choreography.Histories.TransitionArchive
  Choreography.Histories.CursorHistories
  Choreography.Results.OperandObservations Choreography.RoleSteps
  Choreography.Execution Network.Mailboxes Choreography.ReceiveSites
  Projection.Matching.PrefixRelation Projection.FIFO.MessageRepresentation
  Semantics.LocalEffects Semantics.SharedState.
Require Import Parkour.Symbol.
Require Choreography.Choreo2.
Import ListNotations.
Local Arguments positions {M E Store A} _ _.
Import Choreography.Choreo2 (Choreo).

Section SameHistory.
Context {M E : Type -> Type} {Store Input : Type}.
Variable model : local_model M E role (Store * Input).
Variable stores : role -> Store.
Variable input : Input.
Variable R : list role.
Variable A : role -> Type.
Variable c : forall p, Choreo M p (A p).

Definition recorded p o operand (tree : replay_tree (shared_model model) R p) :=
  exists Y (code : Choreo M p Y) after st sq a st' sq'
    (prim : primitive_action (shared_model model) R Y (Code o code)
      st sq a after st' sq'),
    sender_operand code = Some operand /\
    In (ActionEvent (shared_model model) R p Y (Code o code)
      after st sq a st' sq' prim)
      (lookup (shared_model model) R p o tree).

Definition at_sender_cut p o operand tc
    (s :
      @Choreography.Execution.configuration M E ((role -> Store) * Input) A) :=
  exists cut, cut_history (shared_model model) R p (Code [] (c p))
    (actor_actions p tc) cut /\
    erased_cursor (shared_model model) R p cut = positions s p /\
    recorded p o operand (archive (shared_model model) R p cut).

Lemma keep_sender_cut p o operand tc s a s' :
  Choreography.Execution.step (shared_model model) R s a s' ->
  at_sender_cut p o operand tc s ->
  at_sender_cut p o operand (tc ++ [a]) s'.
Proof.
  intros [r act finish Member Step Frame] (cut & Hist & Eq & Rec).
  unfold at_sender_cut. rewrite actor_actions_snoc.
  rewrite (CursorHistories.role_step_actor (shared_model model)
    R _ _ _ _ _ _ _ _ _ Step).
  destruct (List.list_eq_dec BinNat.N.eq_dec r p) as [->|Ne].
  - rewrite <- Eq in Step.
    destruct (cut_after_role_step (shared_model model)
      R p _ _ _ _ _ _ _ _ _ _ Hist Step)
      as (next & H & End & Ext).
    exists next. split; [exact H|]. split; [exact End|].
    destruct Rec as (Y & code & after & st & sq & b & st' & sq' & prim & Orig &
      Seen).
    exists Y, code, after, st, sq, b, st', sq', prim. auto.
  - rewrite app_nil_r. exists cut. split; [exact Hist|]. split; [|exact Rec].
    rewrite Eq. apply Frame. congruence.
Qed.

Theorem production_at_current_sender tc s tn n gs past :
  payload_history model stores input R A c tc s tn n gs past ->
  forall kind o p r operand, In (Produced kind o p r operand) past ->
  at_sender_cut p o operand tc s.
Proof.
  induction 1 as [|tc s tn n gs past a s' b n' gs' ev H IH Pair State];
    intros kind o p r op Member; [contradiction|].
  apply in_app_or in Member. destruct Member as [Old|New].
  - eapply keep_sender_cut.
    + eapply paired_source. eapply observation_is_paired. exact Pair.
    + exact (IH _ _ _ _ _ Old).
  - destruct Pair as [who pre post t u s' n' a b gs' ev InR Before After Obs
    Frame Step].
    pose proof (observed_production_focus (shared_model model)
      R _ _ _ _ _ _ _ _ _ _ _ _ _ Obs
      _ _ _ _ _ New) as Focus.
    destruct (production_focus_sender (shared_model model)
      R _ _ _ _ _ _ _ _ _ _ _ _ _ _ Focus) as
      [Eq _].
    subst who.
    pose proof (prefix_source_run model stores input R A c _ _ _ _ _
      (history_is_matched model stores input R A c _ _ _ _ _ _ H)) as Run.
    destruct (initial_run_has_annotated_cut (shared_model model)
      R p A c (stores,input) tc s Run)
      as [cut [HC Erase]].
    destruct (production_recorded_in_replay (shared_model model)
      R _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ Focus HC Erase)
      as (next & Hist & End & Y & C & code & after & Prim & Orig & Seen).
    exists next. split; [|split; [exact End|]].
    + rewrite actor_actions_snoc.
      pose proof (decorated_source (shared_model model)
        R _ _ _ _ _ _ _ _ _ _ _ _
        (observed_decorated (shared_model model)
          R _ _ _ _ _ _ _ _ _ _ _ _ _ Obs)) as S.
      rewrite (CursorHistories.role_step_actor (shared_model model)
        R _ _ _ _ _ _ _ _ _ S).
      destruct (List.list_eq_dec BinNat.N.eq_dec p p); [exact
        Hist|contradiction].
    + unfold recorded. do 8 eexists. exists Prim. split; eassumption.
Qed.

(* The raw queue does not contain a typed packet. Start instead from the
   ghost retained by THIS prefix. Return both role cuts at its destination:
   the sender archive still contains the operand, and the receiver can expose
   its present receive by silent bookkeeping only. Do not identify their
   paths, kinds, or hidden types until the structural proof justifies it. *)
Theorem queued_operand_at_receiver tc s tn n gs past
    X gkind path sender receiver (v : X) sh
    Y rkind site rd :
  payload_history model stores input R A c tc s tn n gs past ->
  In (Message X gkind path sender receiver v sh) gs ->
  receive_site (shared_model model) receiver (A receiver) (positions s receiver)
    Y rkind site
    sender rd ->
  at_sender_cut sender path (Operand X sh v) tc s /\
  exists next B (C : @cursor_context M E receiver B (A receiver)) focus,
    cut_history (shared_model model) R receiver (Code [] (c receiver))
      (actor_actions receiver tc)
      next /\
    erased_cursor (shared_model model) R receiver next = plug C focus /\
    receive_focus receiver B focus Y rkind site sender rd.
Proof.
  intros H Member Site. split.
  - apply (production_at_current_sender _ _ _ _ _ _ H gkind path sender
    receiver).
    exact (proj1 (history_past_ok model stores input R A c _ _ _ _ _ _ H) _
      Member).
  - pose proof (prefix_source_run model stores input R A c _ _ _ _ _
      (history_is_matched model stores input R A c _ _ _ _ _ _ H)) as Run.
    destruct (initial_run_has_annotated_cut (shared_model model)
      R receiver A c (stores,input) tc
      s Run)
      as (cut & Hist & End). rewrite <- End in Site.
    destruct (replay_receive_site (shared_model model)
      R receiver _ _ _ cut _ _ _ _ _ Hist Site)
      as (next & B & C & focus & Hist' & End' & More & Focus).
    exists next, B, C, focus. auto.
Qed.
End SameHistory.
