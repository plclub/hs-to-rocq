From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Choreography.Histories.LabelledSteps
  Projection.RoleLogs.ArchiveOrder Choreography.Histories.LogDecomposition
  Projection.Matching.ObservationArchive Semantics.LocalEffects
  Choreography.Occurrences Choreography.PendingDeliveries Choreography.RoleSteps
  Choreography.Histories.CursorHistories Semantics.SharedState Network.Mailboxes
  Projection.Matching.PayloadHistory Projection.Matching.PrefixRelation
  Projection.FIFO.MessageRepresentation Choreography.Results.OperandObservations
  Choreography.Results.CutFamilySoundness.
Require Import Parkour.Symbol Parkour.Codec Choreography.Choreo2
  Control.Monad.Tree.
Import ListNotations.

Section ChoiceLog.
Context {M E : Type -> Type} {S : Type}
  (model : local_model M E role S) (p : role) (L : Type).
Variable leaf : forall B, @cursor M E p B -> L -> @cursor M E p B -> Prop.
Local Notation log := (local_log model p L leaf).

Definition choice_header_step_view {B} (t : @cursor M E p B) tok (u : @cursor M
  E p B)
  :=
  match t with
  | Code _ (Perf (Cond _ _ _)) => exists e, tok = Some e /\ leaf B t e u
  | _ => True
  end.

Lemma choice_header_step_view_correct B t tok u :
  labelled_step model p L leaf B t tok u -> choice_header_step_view t tok u.
Proof.
  destruct 1; cbn [choice_header_step_view]; try exact I.
  - destruct H; exact I.
  - destruct t; cbn [choice_header_step_view]; try exact I.
    destruct c; cbn [choice_header_step_view]; try exact I.
    destruct c; cbn [choice_header_step_view]; eauto.
Qed.

Lemma labelled_choice_leaf X Y l o sh rd kl sl v (k : X -> Choreo M p Y) tok u :
  labelled_step model p L leaf Y
    (Code o (Perf (@Cond M p X l Y sh rd kl sl v k))) tok u ->
  exists e, tok = Some e /\
    leaf Y (Code o (Perf (@Cond M p X l Y sh rd kl sl v k))) e u.
Proof.
  exact (choice_header_step_view_correct _ _ _ _).
Qed.

(* The head is the identical L token, not its erased source action. *)
Theorem local_log_cond X Y l o sh rd kl sl v (k : X -> Choreo M p Y) tr t :
  log (Code o (Perf (@Cond M p X l Y sh rd kl sl v k))) tr t ->
  (tr = [] /\ t = Code o (Perf (@Cond M p X l Y sh rd kl sl v k))) \/
  exists e suffix after,
    tr = e :: suffix /\
    leaf Y (Code o (Perf (@Cond M p X l Y sh rd kl sl v k))) e after /\
    log after suffix t.
Proof.
  intro Run. induction Run.
  - left; auto.
  - destruct IHRun as [[-> ->]|(e & suffix & after & -> & First & Rest)].
    + destruct (labelled_choice_leaf _ _ _ _ _ _ _ _ _ _ _ _ H) as (e & -> &
      First).
      right. exists e,[],u. repeat split; auto. constructor.
    + right. exists e,(snoc_token L suffix token),after. split.
      * destruct token; reflexivity.
      * split; [exact First|]. eapply LogStep; eassumption.
Qed.
End ChoiceLog.

Section ObservedChoice.
Context {M E : Type -> Type} {S : Type}
  (model : local_model M E role S) (R : list role) (p : role).

Definition choice_observed_shape {B} (t : @cursor M E p B)
    (u : @cursor M E p B) gs gs' batch : Prop :=
  match t in cursor _ B return @cursor M E p B -> Prop with
  | Code o code =>
    match code in Tree _ B return @cursor M E p B -> Prop with
    | Perf sig =>
      match sig in ChoreoSig _ _ B return @cursor M E p B -> Prop with
      | @Cond _ _ X l Y sh rd kl sl v k => fun u =>
        exists chosen, u = Code (child o ChoiceBody) (k chosen) /\
          ((exists same : l = p, chosen = unAt v same) \/
           (l <> p /\ exists wire,
             delivery X ChoiceDelivery o l p chosen rd gs wire gs' /\
             batch = [Consumed ChoiceDelivery o l p wire]))
      | _ => fun _ => True
      end
    | _ => fun _ => True
    end
  | _ => fun _ => True
  end u.

Definition not_cond_cursor {B} (t : @cursor M E p B) : Prop :=
  match t with Code _ (Perf (Cond _ _ _)) => False | _ => True end.

Lemma silent_not_cond B t u :
  @silent M E S model p B t u -> not_cond_cursor t.
Proof. destruct 1; exact I. Qed.

Lemma observed_choice_shape_correct B t s q a u s' q' na gs gs' batch :
  @observed M E S model R p B t s q a u s' q' na gs gs' batch ->
  choice_observed_shape t u gs gs' batch.
Proof.
  destruct 1; cbn [choice_observed_shape]; try exact I.
  - eexists. split; [reflexivity|]. left; eexists; reflexivity.
  - eexists. split; [reflexivity|]. right; split; [exact h|].
    eexists; split; [exact H|reflexivity].
  - pose proof (silent_not_cond _ _ _ H) as Not.
    destruct t; cbn [choice_observed_shape not_cond_cursor] in *; try exact I.
    destruct c; cbn [choice_observed_shape not_cond_cursor] in *; try exact I.
    destruct c; cbn [choice_observed_shape not_cond_cursor] in *; try exact I.
    contradiction.
Qed.
End ObservedChoice.

Section StampedChoice.
Context {M E Store Input} (model : local_model M E role (Store * Input))
  (stores : role -> Store) (input : Input) (R : list role) (A : role -> Type)
  (c : forall p, Choreo M p (A p)).
Local Notation sm := (shared_model model).
Local Notation entry := (observed_entry model stores input R A c).
Local Notation stamp := (stamped model stores input R A c).
Local Notation log := (actor_log model stores input R A c).
Local Notation ghosts := (entry_ghosts model stores input R A c).
Local Notation ghosts_after := (entry_ghosts_after model stores input R A c).
Local Notation batch := (entry_batch model stores input R A c).

Theorem stamped_choice_step p X Y l o sh rd kl sl v (k : X -> Choreo M p Y)
    (e : entry p) u :
  stamp p Y (Code o (Perf (@Cond M p X l Y sh rd kl sl v k))) e u ->
  exists chosen, u = Code (child o ChoiceBody) (k chosen) /\
    ((exists same : l = p, chosen = unAt v same) \/
     (l <> p /\ exists wire,
       delivery X ChoiceDelivery o l p chosen rd (ghosts p e) wire (ghosts_after
         p e) /\
       batch p e = [Consumed ChoiceDelivery o l p wire])).
Proof.
  intros [_ Obs].
  exact (observed_choice_shape_correct sm R p _ _ _ _ _ _ _ _ _ _ _ _ Obs).
Qed.

Theorem actor_log_cond p X Y l o sh rd kl sl v (k : X -> Choreo M p Y) tr t :
  log p Y (Code o (Perf (@Cond M p X l Y sh rd kl sl v k))) tr t ->
  (tr = [] /\ t = Code o (Perf (@Cond M p X l Y sh rd kl sl v k))) \/
  exists (e : entry p) suffix chosen,
    tr = e :: suffix /\
    stamp p Y (Code o (Perf (@Cond M p X l Y sh rd kl sl v k))) e
      (Code (child o ChoiceBody) (k chosen)) /\
    ((exists same : l = p, chosen = unAt v same) \/
     (l <> p /\ exists wire,
       delivery X ChoiceDelivery o l p chosen rd (ghosts p e) wire (ghosts_after
         p e) /\
       batch p e = [Consumed ChoiceDelivery o l p wire])) /\
    log p Y (Code (child o ChoiceBody) (k chosen)) suffix t.
Proof.
  intro Run.
  destruct (local_log_cond sm p (entry p) (stamp p)
    X Y l o sh rd kl sl v k tr t Run)
    as [Empty|(e & suffix & after & Trace & First & Rest)].
  - left; exact Empty.
  - destruct (stamped_choice_step p X Y l o sh rd kl sl v k e after First)
      as (chosen & -> & Choice).
    right; exists e,suffix,chosen; auto.
Qed.

(* The batch is included in the SAME global past. This premise is supplied
   by branch_valid for a role-local sublog; it is not a fabricated receive. *)
Theorem actor_log_cond_replay tc s tn n gs past
    p X Y l o sh rd kl sl v (k : X -> Choreo M p Y) tr t :
  payload_history model stores input R A c tc s tn n gs past ->
  (forall e, In e tr -> entry_in_past model stores input R A c p past e) ->
  log p Y (Code o (Perf (@Cond M p X l Y sh rd kl sl v k))) tr t ->
  (tr = [] /\ t = Code o (Perf (@Cond M p X l Y sh rd kl sl v k))) \/
  exists (e : entry p) suffix chosen,
    tr = e :: suffix /\
    stamp p Y (Code o (Perf (@Cond M p X l Y sh rd kl sl v k))) e
      (Code (child o ChoiceBody) (k chosen)) /\
    choice_observation past X l p rd v o chosen /\
    log p Y (Code (child o ChoiceBody) (k chosen)) suffix t.
Proof.
  intros Hist SamePast Run.
  destruct (actor_log_cond p X Y l o sh rd kl sl v k tr t Run)
    as [Empty|(e & suffix & chosen & Trace & First & Choice & Rest)].
  - left; exact Empty.
  - right; exists e,suffix,chosen. split; [exact Trace|].
    split; [exact First|]. split; [|exact Rest].
    destruct Choice as [Owner|(Different & wire & Delivery & Batch)].
    + left; exact Owner.
    + right; split; [exact Different|]. exists wire; split.
      * apply (proj2 (history_past_ok model stores input R A c
          tc s tn n gs past Hist)).
        destruct (SamePast e ltac:(rewrite Trace; now left)) as [tail Eq].
        rewrite Eq. apply in_or_app; right. apply in_or_app; left.
        rewrite Batch; now left.
      * destruct Delivery; assumption.
Qed.
End StampedChoice.

Print Assumptions actor_log_cond.
Print Assumptions actor_log_cond_replay.
