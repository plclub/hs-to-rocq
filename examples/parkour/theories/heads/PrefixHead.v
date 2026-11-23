From Stdlib Require Import Lists.List.
Require Import DeadlockLayoutHead DeadlockLayoutOrder DeadlockRealized
  DeadlockFamilyLog DeadlockObservedCut DeadlockPlayedActual
    DeadlockPlayedFamily
  DeadlockSource DeadlockCutSafety DeadlockLocal DeadlockState DeadlockPast
  DeadlockMessages DeadlockOrder DeadlockCoherence DeadlockChronology
  DeadlockMatch DeadlockWellFormed DeadlockPlayedValues DeadlockFrontiers
    DeadlockHead
  Parkour.Symbol Choreography.Choreo2.
Import ListNotations.

Section PrefixHead.
Context {M E Store Input} (model : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input : Input) (R : list Symbol)
  (A : Symbol -> Type) (c : forall p, Choreo M p (A p)).
Local Notation cut := (logged_cut model stores input R A c).
Local Notation tok := (tokens model stores input R A c).
Local Notation act := (entry_action model stores input R A c).
Local Notation path_of := (entry_site model stores input R A c).
Local Notation sm := (shared_model model).
Local Arguments tokens {M E Store Input} model stores input R A c {p B} _.

Lemma owned_token_action tc s tn n gs past ar F active root
    (cuts : family cut F active) p d e :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  owns_region model stores input R A c ar F active root cuts ->
  In e (tok (cuts p d)) -> In (act p e) tc.
Proof.
  intros Archives [_ [_ Own]] Token.
  destruct (observed_archives_trace model stores input R A c
    _ _ _ _ _ _ _ Archives p _ e (proj1 (proj1 (Own p d e) Token)))
    as [suffix Trace].
  rewrite Trace. apply in_or_app; right; now left.
Qed.

(* A production is located in the sender's exact cut, not a fresh cut
   supplied by the existence of some source action with the same path. *)
Lemma produced_cut_reached tc s tn n gs past ar F active
    (cuts : family cut F active) kind o sender receiver operand :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  owns_region model stores input R A c ar F active [] cuts ->
  In (Produced kind o sender receiver operand) past ->
  exists d, cut_reached model stores input R A c sender (F sender) (cuts sender
    d) o.
Proof.
  intros Archives [_ [Present Own]] Produced.
  destruct (observed_past_event_archived model stores input R A c
    _ _ _ _ _ _ _ Archives _ Produced) as (p & route & e & Archived & Batch).
  destruct (entry_produced_site model stores input R A c p e
    kind o sender receiver operand Batch) as [Actor Path].
  subst p.
  destruct (observed_archives_valid model stores input R A c
    _ _ _ _ _ _ _ Archives sender route e Archived) as [Location _].
  assert (Region : in_region model stores input R A c ar sender [] e).
  { split; [now rewrite <- Location|]. exists (path_of sender e); reflexivity. }
  pose proof (Present sender e Region) as d.
  exists d. left. exists e. split; [now apply Own|exact Path].
Qed.

Theorem tracked_layout_head tc s tn n gs past ar tree
    (cuts : family cut A R) sender receiver X kind current rd g :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  NoDup R ->
  owns_region model stores input R A c ar A R [] cuts ->
  tracked_realization model stores input R A c A R [] cuts tree ->
  forall member : In receiver R,
  receive_site sm receiver (A receiver) (positions s receiver) X kind current
    sender rd ->
  cut_receive model stores input R A c receiver (A receiver)
    (cuts receiver member) X kind current sender rd ->
  first_for (sender,receiver,session_at current Choreography.Network.Root) gs g
    ->
  message_path g = current.
Proof.
  intros Archives ND Own Tracked member Site Focus First.
  pose proof (tracked_realized model stores input R A c _ _ _ _ _ Tracked) as
    Layout.
  destruct (realized_receive_site model stores input R A c _ _ _ _ _ Layout
    receiver member X kind current sender rd Focus) as (path & Path & Here).
  cbn in Path; subst path.
  eapply layout_head; [exact Archives|exact ND|exact Own|exact Layout|
    exact member|exact Site|exact Here| | |exact First].
  - intros earlier ek At Before.
    destruct (tracked_predecessor_token model stores input R A c
      _ _ _ _ _ Tracked receiver member current
      (or_intror (ex_intro _ X (ex_intro _ kind (ex_intro _ sender (ex_intro _
        rd Focus)))))
      earlier ek sender receiver At (or_intror eq_refl) Before)
      as (e & Token & Action).
    exists (act receiver e). split; [|exact Action].
    eapply owned_token_action; eassumption.
  - intros later lk operand Produced Before.
    destruct (produced_cut_reached _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Archives Own Produced) as [sender_member Reached].
    destruct (tracked_predecessor_token model stores input R A c
      _ _ _ _ _ Tracked sender sender_member later Reached
      current kind sender receiver Here (or_introl eq_refl) Before)
      as (e & Token & Action).
    exists (act sender e). split; [|exact Action].
    eapply owned_token_action; eassumption.
Qed.

(* The upstream assembly obligation quantifies over the exposed logged family.
   Realization and predecessor closure must concern one and the same tree. *)
Theorem source_head_paths_from_tracked tc s tn n gs past ar :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  NoDup R ->
  (forall cuts : family cut A R,
    owns_region model stores input R A c ar A R [] cuts ->
    (forall p d, at_node model stores input R A c past p (A p) [] (c p) (cuts p
      d)) ->
    exists tree, tracked_realization model stores input R A c A R [] cuts tree)
      ->
  forall p, In p R -> source_head_paths sm p (A p) (positions s p) gs.
Proof.
  intros Archives ND Assemble p Member X kind o sender rd Site g First.
  destruct (expose_logged_receivers model stores input R A c past ar
    _ _ _ _ _ p X kind o sender rd Archives ND Site)
    as (cuts & B & C & focus & Own & Nodes & Cursor & Focus).
  destruct (Assemble cuts Own Nodes) as [tree Tracked].
  eapply (tracked_layout_head tc s tn n gs past ar tree cuts sender p X kind o
    rd g
    Archives ND Own Tracked Member Site); [|exact First].
  exists B, C, focus. split; [exact (Cursor Member)|exact Focus].
Qed.

Theorem source_head_paths_matched_from_tracked tc s tn n gs :
  NoDup R ->
  matched_prefix model stores input R A c tc s tn n gs ->
  (forall past ar,
    observed_archives model stores input R A c tc s tn n gs past ar ->
    forall cuts : family cut A R,
      owns_region model stores input R A c ar A R [] cuts ->
      (forall p d, at_node model stores input R A c past p (A p) [] (c p) (cuts
        p d)) ->
      exists tree, tracked_realization model stores input R A c A R [] cuts
        tree) ->
  forall p, In p R -> source_head_paths sm p (A p) (positions s p) gs.
Proof.
  intros ND Prefix Assemble.
  destruct (matched_has_observed_archives model stores input R A c
    _ _ _ _ _ Prefix) as (past & ar & Hist & Archives & Valid).
  eapply source_head_paths_from_tracked; [exact Archives|exact ND|].
  exact (Assemble past ar Archives).
Qed.
End PrefixHead.

Print Assumptions produced_cut_reached.
Print Assumptions tracked_layout_head.
Print Assumptions source_head_paths_from_tracked.
Print Assumptions source_head_paths_matched_from_tracked.
