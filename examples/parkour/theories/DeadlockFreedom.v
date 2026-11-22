From Stdlib Require Import Lists.List.
Require Import DeadlockLocal DeadlockState DeadlockMatch DeadlockRoster.
Require DeadlockAlignmentProgress.
Require DeadlockMatchStep DeadlockRuns.
Require DeadlockSource DeadlockNetwork DeadlockAlignment Choreography.Network
  Choreography.Choreo2 Parkour.Symbol.
Import ListNotations.

Section Preservation.
Context {M E : Type -> Type} {Store Input : Type}.
Variable model : local_model M E Parkour.Symbol.Symbol (Store * Input).
Variable stores : Parkour.Symbol.Symbol -> Store.
Variable input : Input.
Variable R : list Parkour.Symbol.Symbol.
Variable A : Parkour.Symbol.Symbol -> Type.
Variable c : forall p, Choreography.Choreo2.Choreo M p (A p).
Local Notation sm := (shared_model model).
Local Notation C0 := (@source_initial M E Store Input stores input A c).
Local Notation N0 := (@network_initial M E Store Input stores input R A c).
Local Notation paired := (matches model stores input R A c).

Lemma empty_network_run_has_source n :
  DeadlockNetwork.run sm R N0 [] n ->
  exists tc s, DeadlockSource.crun sm R C0 tc s /\ paired tc s [] n.
Proof.
  intro H. inversion H; subst. exists [], C0.
  split; [constructor | apply initial_matches].
Qed.

(* Returned endpoint values are the actual source values. A bare equality of
   mailboxes would not suffice to reflect finality. *)
Lemma matched_network_final tc s tn n :
  paired tc s tn n ->
  DeadlockNetwork.nfinal sm n -> DeadlockSource.cfinal sm R s.
Proof.
  intros Match Final. split.
  - apply (proj2 (terminal_queues model stores input R A c tc s tn n Match)).
    exact (proj2 Final).
  - destruct Match as [gs H].
    destruct (prefix_state model stores input R A c tc s tn n gs H)
      as [_ [_ [f [Hroster Align]]]].
    destruct n as [es q st]. cbn in Hroster; subst es.
    apply (proj1 (all_returns sm R A f q st)) in Final.
    intros p member. destruct (proj1 Final p member) as [x Hx].
    exists x. destruct (Align p member) as [Ha].
    eapply DeadlockAlignment.aligned_returns; eassumption.
Qed.

Lemma matched_source_final tc s tn n :
  paired tc s tn n ->
  DeadlockSource.cfinal sm R s -> DeadlockNetwork.nfinal sm n.
Proof.
  intros Match [Empty Done].
  pose proof (proj1 (terminal_queues model stores input R A c tc s tn n Match) Empty) as Q.
  destruct Match as [gs H].
  destruct (prefix_state model stores input R A c tc s tn n gs H)
    as [_ [_ [f [Hroster Align]]]].
  destruct n as [es q st]. cbn in Hroster; subst es.
  apply (proj2 (all_returns sm R A f q st)). split; [|exact Q].
  intros p member. destruct (Done p member) as [x Hx].
  exists x. destruct (Align p member) as [Ha].
  eapply DeadlockAlignmentProgress.source_return_is_network_return; eassumption.
Qed.

(* Safety at a receive site concerns the head and the actual decoder. It
   does not say there is a receive, or that any other action is enabled. *)
Definition inputs_available (s : @DeadlockSource.configuration M E
    ((Parkour.Symbol.Symbol -> Store) * Input) A)
    (n : @DeadlockNetwork.configuration M E ((Parkour.Symbol.Symbol -> Store) * Input)) :=
  forall p, In p R ->
    exists (t : @DeadlockNetwork.control M E (A p))
      (h : DeadlockAlignment.aligned sm Choreography.Network.Root p (A p)
        (DeadlockSource.positions s p) t),
      In (DeadlockNetwork.Endpoint (A p) p t) (DeadlockNetwork.endpoints n) /\
      DeadlockAlignmentProgress.delivery_available sm Choreography.Network.Root
        p (A p) (DeadlockSource.positions s p) t h
        (DeadlockNetwork.mailboxes n) (DeadlockSource.deliveries s).

Lemma initial_inputs_available : inputs_available C0 N0.
Proof.
  intros p Hr.
  eexists; exists (DeadlockAlignment.generated_initial_alignment sm
    Choreography.Network.Root p (A p) (c p)).
  split.
  - cbn. induction R as [|r rs IH]; cbn in *; [contradiction|].
    destruct Hr as [->|Hr]; [now left|right; auto].
  - apply DeadlockAlignmentProgress.empty_delivery_available.
Qed.

Lemma matched_ready_from_inputs tc s tn n :
  paired tc s tn n -> inputs_available s n ->
  (DeadlockSource.cfinal sm R s \/ exists a s', DeadlockSource.cstep sm R s a s') ->
  DeadlockNetwork.nfinal sm n \/ exists b n', DeadlockNetwork.nstep sm R n b n'.
Proof.
  intros Match Safe [Done | [a [s' Act]]].
  - left; eapply matched_source_final; eassumption.
  - right. destruct Act as [p a s' Hr Hstep Frame].
    destruct (Safe p Hr) as (t & h & Hin & Hinput).
    destruct Match as [gs H].
    destruct (prefix_state model stores input R A c tc s tn n gs H)
      as [Hstore _].
    rewrite Hstore in Hstep.
    destruct (DeadlockAlignmentProgress.source_action_exposes_network_action
      sm Choreography.Network.Root R p (A p) _ t h _ _ _ _ _ _ _ Hinput Hstep)
      as (b & t' & q' & st' & live).
    destruct n as [es q st]; cbn in Hin,live. apply in_split_large in Hin.
    destruct Hin as (pre & post & ->). exists b. eexists.
    apply DeadlockNetwork.Schedule. exact live.
Qed.
End Preservation.

(* Induction on a particular schedule uses only the receive facts of its
   matched prefixes. The structural proof must establish those facts for
   every reachable prefix. *)
Section Schedules.
Context {M E : Type -> Type} {Store Input : Type}.
Variable model : local_model M E Parkour.Symbol.Symbol (Store * Input).
Variable stores : Parkour.Symbol.Symbol -> Store.
Variable input : Input.
Variable R : list Parkour.Symbol.Symbol.
Variable A : Parkour.Symbol.Symbol -> Type.
Variable c : forall p, Choreography.Choreo2.Choreo M p (A p).
Local Notation sm := (shared_model model).
Local Notation C0 := (@source_initial M E Store Input stores input A c).
Local Notation N0 := (@network_initial M E Store Input stores input R A c).
Local Notation prefix := (matched_prefix model stores input R A c).
Local Notation paired := (matches model stores input R A c).
Local Notation NC := (@DeadlockNetwork.configuration M E ((Parkour.Symbol.Symbol -> Store) * Input)).
Local Notation SC := (@DeadlockSource.configuration M E ((Parkour.Symbol.Symbol -> Store) * Input) A).
Local Notation cstep := (@DeadlockSource.cstep M E _ sm R A).
Local Notation nstep := (DeadlockNetwork.nstep sm R).

Lemma network_run_snoc_view i tr j :
  DeadlockNetwork.run sm R i tr j -> DeadlockRuns.finite_run nstep i tr j.
Proof.
  intro H; induction H; [constructor|].
  apply DeadlockRuns.run_cons_iff. eauto.
Qed.

Lemma schedule_from_safe_receives :
  NoDup R ->
  (forall tc s tn n gs, prefix tc s tn n gs ->
     DeadlockMatchStep.safe_residuals model R A s n gs) ->
  forall tn n, DeadlockNetwork.run sm R N0 tn n ->
    exists tc s, DeadlockSource.crun sm R C0 tc s /\ paired tc s tn n.
Proof.
  intros ND Safe tn n Run. apply network_run_snoc_view in Run.
  remember N0 as start eqn:From in Run.
  induction Run as [start |start tr x a y Run IH Step].
  - subst start. exists [], C0. split; [constructor|apply initial_matches].
  - destruct (IH From) as (tc & s & Source & gs & Match).
    destruct (DeadlockMatchStep.matched_prefix_step model R A stores input c
      tc s tr x gs a y ND Match (Safe _ _ _ _ _ Match) Step)
      as (sa & s' & gs' & Next & Act).
    exists (tc ++ [sa]), s'. split; [eapply DeadlockRuns.RunSnoc; eassumption|].
    now exists gs'.
Qed.

Lemma preservation_from_frontiers :
  NoDup R ->
  (forall tc s tn n gs, prefix tc s tn n gs ->
     DeadlockMatchStep.safe_residuals model R A s n gs) ->
  (forall tc s tn n, paired tc s tn n -> inputs_available model R A s n) ->
  DeadlockRuns.DF cstep (DeadlockSource.cfinal sm R) C0 ->
  forall tn n, DeadlockNetwork.run sm R N0 tn n ->
    DeadlockRuns.ready nstep (DeadlockNetwork.nfinal sm) n.
Proof.
  intros ND Safe Available Source tn n Net.
  destruct (schedule_from_safe_receives ND Safe tn n Net) as (tc & s & Run & H).
  eapply matched_ready_from_inputs; [exact H | exact (Available _ _ _ _ H) |].
  exact (Source tc s Run).
Qed.

Lemma reflection_from_frontiers :
  NoDup R ->
  (forall tc s tn n gs, prefix tc s tn n gs ->
     DeadlockMatchStep.safe_residuals model R A s n gs) ->
  (forall tc s tn n, paired tc s tn n -> inputs_available model R A s n) ->
  forall tn n, DeadlockNetwork.run sm R N0 tn n ->
    DeadlockRuns.stuck nstep (DeadlockNetwork.nfinal sm) n ->
    exists tc s, DeadlockSource.crun sm R C0 tc s /\ paired tc s tn n /\
      DeadlockRuns.stuck cstep (DeadlockSource.cfinal sm R) s.
Proof.
  intros ND Safe Available tn n Net Stuck.
  destruct (schedule_from_safe_receives ND Safe tn n Net) as (tc & s & Run & H).
  exists tc, s. split; [exact Run|]. split; [exact H|].
  eapply DeadlockRuns.ready_stuck_reflection; [|exact Stuck].
  exact (matched_ready_from_inputs model stores input R A c tc s tn n H
    (Available _ _ _ _ H)).
Qed.
End Schedules.
