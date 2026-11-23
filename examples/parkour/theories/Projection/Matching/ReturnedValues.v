From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Projection.RoleLogs.Families.RegionOwnership
  Projection.Payloads.OwnedPackets Projection.RoleLogs.PrimitiveObservations
  Projection.Matching.ObservationArchive
  Choreography.Results.OperandObservations
  Choreography.Results.CutFamilySoundness
  Choreography.Histories.SyntaxDecomposition Projection.RoleLogs.ArchiveOrder
  Projection.Matching.PrefixRelation Projection.Matching.PayloadHistory
  Semantics.LocalEffects Semantics.SharedState Choreography.RoleSteps
  Choreography.Execution Choreography.WellFormedness
  Projection.RoleLogs.Families.BranchPartition
  Projection.RoleLogs.Families.ChoicePartition
  Choreography.Results.FiniteSelection.
Require Import Parkour.Symbol Choreography.Choreo2 Control.Monad.Tree.
Import ListNotations.

Lemma finished_cursor {M E p B} (t : @cursor M E p B) v :
  cut_returned p t v -> t = Returned v.
Proof. destruct t; cbn [cut_returned]; try contradiction; intros ->;
  reflexivity. Qed.

Section Instance.
Context {M E Store Input} (model : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input : Input) (R : list Symbol) (A : Symbol ->
    Type)
  (c : forall p, Choreo M p (A p)).
Local Notation Cut := (logged_cut model stores input R A c).
Local Notation atc := (at_node model stores input R A c).
Local Notation done := (finished model stores input R A c).
Local Notation wire := (token_wires model stores input R A c).

Lemma actual_pure_law past p B o (x v : B) (cut : Cut p B) :
  atc past p B o (Pure x) cut -> done p B cut v -> v = x.
Proof.
  destruct cut as [t trace]. intros [Log _] Return.
  destruct t; try contradiction.
  cbn [finished cut_returned cursor_at] in Return.
  subst. eapply (pure_log_returned model stores input R A c past); exact Log.
Qed.

Lemma actual_comm_law tc s tn n gs past ar p X l r sh rd kl kr sl arg sr o cut v
  :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  atc past p _ o (Perf (@Comm M p X l r sh rd kl kr sl arg sr)) cut ->
  done p _ cut v -> comm_observed past o rd p arg v.
Proof.
  intros Archives [Log Stamps] Return.
  pose proof (observed_archives_history model stores input R A c _ _ _ _ _ _ _
    Archives) as Hist.
  destruct cut as [t tr]. cbn [cursor_at tokens] in Log,Stamps.
  assert (Eq : t = Returned v).
  { apply finished_cursor. exact Return. }
  subst t. eapply (comm_log_observed model stores input R A c past); [exact
    Log|].
  intros e InE jk path sender recipient bytes Consumed.
  destruct (Stamps e InE) as [suffix Eq].
  apply (proj2 (history_past_ok model stores input R A c _ _ _ _ _ _ Hist)).
  rewrite Eq. apply in_or_app; right; apply in_or_app; now left.
Qed.
End Instance.

Section RealHistories.
Context {M E Store Input} (model : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input : Input) (R : list Symbol) (A : Symbol ->
    Type)
  (c : forall p, Choreo M p (A p)).
Local Notation Cut := (logged_cut model stores input R A c).
Local Notation atc := (at_node model stores input R A c).
Local Notation done := (finished model stores input R A c).
Local Notation good := (owns_region model stores input R A c).

Theorem actual_replay_laws tc s tn n gs past ar :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  cut_family_laws Cut (atc past) done past (good ar).
Proof.
  intro Hist. constructor.
  - exact (actual_pure_law model stores input R A c past).
  - intros. eapply actual_comm_law; eassumption.
  - intros. eapply owns_sender_present; eassumption.
  - intros. eapply owned_original_operand; eassumption.
  - exact (concrete_replay_app model stores input R A c past ar).
  - exact (concrete_replay_bind model stores input R A c past ar).
  - intros. eapply replay_cond_logged; eassumption.
Qed.

(* The partial result relation of the original WF certificate now applies
   to the actual returned values, even if other roles remain blocked. *)
Theorem matched_partial_results tc s tn n gs Q completed vals :
  NoDup R ->
  structural R M (fun p => In p R) A (fun p _ => c p) Q ->
  matched_prefix model stores input R A c tc s tn n gs ->
  NoDup completed ->
  includes (fun p => In p completed) (fun p => In p R) ->
  (forall p d, cut_returned p (Choreography.Execution.positions s p) (vals p d))
    ->
  Q (fun p => In p completed) vals.
Proof.
  intros ND WF P NC Inc Results.
  destruct (matched_has_observed_archives model stores input R A c _ _ _ _ _ P)
    as (past & ar & Hist & Archives & Valid).
  destruct (root_log_family model stores input R A c _ _ _ _ _ _ _ Archives ND)
    as [Own Nodes].
  eapply (structural_cut_family_results Cut (atc past) done past (good ar)
    (actual_replay_laws _ _ _ _ _ _ _ Archives) _ _ _ _ _ WF R completed
    (fun p d => d) [] (root_cuts model stores input R A c ar s) vals Inc);
    try eassumption.
  - exact (roster_member_unique R ND).
Qed.
End RealHistories.
