From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Semantics.LocalEffects
  Choreography.PendingDeliveries Choreography.RoleSteps
  Choreography.Observations Network.Mailboxes Network.Endpoints
  Network.Enabledness Projection.Matching.CursorAlignment
  Projection.SessionPaths Semantics.Roles.
Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree.
Require Choreography.Choreo2.
Import Choreography.Network.
Local Notation Choreo := Choreography.Choreo2.Choreo.
Local Notation At := Choreography.Choreo2.At.
Local Notation unAt := Choreography.Choreo2.unAt.

Section Progress.
Context {M E : Type -> Type} {Store : Type}.
Variable model : local_model M E Symbol Store.
Variable root_session : SessionId.

(* Source observations are insensitive to finite bookkeeping order. In
   particular AlignSilent is handled by silent_result, not by assuming that
   the source and endpoint chose the same administrative evaluation path. *)
Theorem aligned_result p X c n (Ha : aligned model root_session p X c n) y :
  cursor_result model p X c y -> Endpoints.returns model X n y.
Proof.
  induction Ha as
    [X x n H
    | X t u n H Ha IHHa
    | X Y o t n k j Ha IHHa Hcont IHcont
    | X Y f t nf nt HaF IHF HaT IHT
    | X Y c n k x H Ha IHHa
    | X o e
    | X o t
    | X d o sh rd kl kd v neq
    | X l o sh rd kl kd v neq
    | X Y o sh rd kl v k j Hcont IHcont
    | X Y l o sh rd kl v k neq j Hcont IHcont];
    intro Hr; cbn [cursor_result code_result] in Hr.
  - subst y. apply administrative_returns. exact H.
  - apply IHHa. apply (proj1 (silent_result model _ _ _ _ H y)). exact Hr.
  - destruct Hr as [x [Ht Hk]].
    eapply ReturnBind; [apply IHHa; exact Ht | apply IHcont; exact Hk].
  - destruct Hr as [g [x [Hf [Ht ->]]]].
    eapply ReturnApp; [apply IHF; exact Hf | apply IHT; exact Ht].
  - eapply ReturnBind; [apply administrative_returns; exact H |].
    apply IHHa. exact Hr.
  - destruct Hr as [x [Ht ->]].
    eapply ReturnBind; [apply ReturnExec; exact Ht | apply ReturnPure].
  - destruct Hr as [x [Ht ->]].
    eapply ReturnBind; [apply ReturnLocal; exact Ht | apply ReturnPure].
  - unfold primitive_result in Hr.
    destruct (symbol_eq_dec p d); [congruence|].
    destruct (symbol_eq_dec p p); [contradiction|contradiction].
  - unfold primitive_result in Hr.
    destruct (symbol_eq_dec l p); [contradiction|].
    destruct (symbol_eq_dec l p); [contradiction|].
    destruct (symbol_eq_dec p p); [contradiction|contradiction].
  - exact (False_rect _ Hr).
  - exact (False_rect _ Hr).
Qed.

Corollary source_return_is_network_return p X c n
    (Ha : aligned model root_session p X c n) y :
  RoleSteps.returns model c y -> Endpoints.returns model X
    n y.
Proof.
  intro H. apply (aligned_result _ _ _ _ Ha).
  apply source_returns_result. exact H.
Qed.

(* This is the forward half of current delivery coherence. It mentions only
   typed pending entries, the actual FIFO head, and its actual Read dictionary.
   Unlike delivery_consistent it does not reflect a wire receive; it exposes
   a wire receive from an occurrence-only source delivery. In particular it
   cannot discard a source receive using the stronger
     take_first_on_source_channel lane guard.

   Readiness needs some decoded value y, not equality with the payload x of
   every raw take_at_occurrence witness. Requiring that equality here would
     unnecessarily
   ask coherence to extract payload equality from heterogeneous Pending packs;
   that extraction is not justified by UIP for Symbol. Exact action matching
   and codec laws remain separate from this internal readiness condition. *)
Definition delivery_available_at X kind o sender p (rd : Read X) sid
    (q : queues) (sq : list pending) : Prop :=
  forall (x : X) sq', take_at_occurrence kind o sender p x sq sq' ->
    exists w ws y, q (sender,p,sid) = w :: ws /\ @read X rd w = Some y.

Fixpoint delivery_available p X c n
    (Ha : aligned model root_session p X c n) (q : queues) (sq : list pending) :
      Prop.
Proof.
  destruct Ha as
    [X x n H
    | X t u n H Ha
    | X Y o t n k j Ha Hcont
    | X Y f t nf nt HaF HaT
    | X Y c n k x H Ha
    | X o e
    | X o t
    | X d o sh rd kl kd v neq
    | X l o sh rd kl kd v neq
    | X Y o sh rd kl v k j Hcont
    | X Y l o sh rd kl v k neq j Hcont].
  - exact True.
  - exact (delivery_available _ _ _ _ Ha q sq).
  - exact (delivery_available _ _ _ _ Ha q sq /\
      forall x, RoleSteps.returns model t x ->
        delivery_available _ _ _ _ (Hcont x) q sq).
  - exact (delivery_available _ _ _ _ HaF q sq /\
           delivery_available _ _ _ _ HaT q sq).
  - exact (delivery_available _ _ _ _ Ha q sq).
  - exact True.
  - exact True.
  - exact True.
  - exact (delivery_available_at X DataDelivery o l p rd
             (session_at o root_session) q sq).
  - exact True.
  - exact (delivery_available_at X ChoiceDelivery o l p rd
             (session_at o root_session) q sq).
Defined.

Lemma empty_delivery_available p X c n
    (Ha : aligned model root_session p X c n) q :
  delivery_available p X c n Ha q nil.
Proof.
  induction Ha; cbn [delivery_available]; try exact I; try tauto.
  - split; [exact IHHa |]. intros x _. apply H.
  - unfold delivery_available_at. intros x sq' Htake. inversion Htake.
  - unfold delivery_available_at. intros x sq' Htake. inversion Htake.
Qed.

(* The conclusion uses the actual operational enabledness predicate. The only
   additional hypothesis is the concrete source-delivery/FIFO/codec condition
   above; there is no positive target-readiness or EPP-equivalence premise. *)
Theorem aligned_live p X c n (Ha : aligned model root_session p X c n)
    q s sq :
  delivery_available p X c n Ha q sq ->
  cursor_live model p X c s sq ->
  possible model p n q s.
Proof.
  revert q s sq.
  induction Ha as
    [X x n H
    | X t u n H Ha IHHa
    | X Y o t n k j Ha IHHa Hcont IHcont
    | X Y f t nf nt HaF IHF HaT IHT
    | X Y c n k x H Ha IHHa
    | X o e
    | X o t
    | X d o sh rd kl kd v neq
    | X l o sh rd kl kd v neq
    | X Y o sh rd kl v k j Hcont IHcont
    | X Y l o sh rd kl v k neq j Hcont IHcont];
    intros q s sq Havailable Hlive;
    cbn [cursor_live code_live] in Hlive;
    cbn [delivery_available] in Havailable;
    cbn [possible].
  - contradiction.
  - apply IHHa with (sq := sq); [exact Havailable |].
    apply (proj1 (silent_live model _ _ _ _ H s sq)). exact Hlive.
  - destruct Havailable as [Hprefix Hbody].
    destruct Hlive as [Hprefix_live | [x [Hresult Hbody_live]]].
    + left. apply IHHa with (sq := sq); assumption.
    + right. exists x. split.
      * apply (aligned_result _ _ _ _ Ha). exact Hresult.
      * apply IHcont with (sq := sq).
        -- apply Hbody. apply result_source_returns. exact Hresult.
        -- exact Hbody_live.
  - destruct Havailable as [HavailableF HavailableT].
    destruct Hlive as [HliveF | HliveT].
    + left. apply IHF with (sq := sq); assumption.
    + right. apply IHT with (sq := sq); assumption.
  - right. exists x. split.
    + apply administrative_returns. exact H.
    + apply IHHa with (sq := sq); assumption.
  - left. exact Hlive.
  - left. exact Hlive.
  - right. exists (session_at o root_session). split; [apply ReturnPure |].
    left. left. exact I.
  - unfold primitive_live in Hlive.
    destruct (symbol_eq_dec l p); [contradiction|].
    destruct (symbol_eq_dec l p); [contradiction|].
    destruct (symbol_eq_dec p p); [|contradiction].
    destruct Hlive as [x [sq' Htake]].
    destruct (Havailable x sq' Htake) as [w [ws [y [Hhead Hread]]]].
    right. exists (session_at o root_session). split; [apply ReturnPure |].
    left. exists w, ws, y. split; assumption.
  - left. right. exists (session_at o root_session).
    split; [apply ReturnPure | exact I].
  - unfold primitive_live in Hlive.
    destruct (symbol_eq_dec l p); [contradiction|].
    destruct Hlive as [x [sq' Htake]].
    destruct (Havailable x sq' Htake) as [w [ws [y [Hhead Hread]]]].
    left. right. exists (session_at o root_session).
    split; [apply ReturnPure |].
    exists w, ws, y. split; assumption.
Qed.

Variable participants : list role.

Corollary source_action_is_network_enabled p X c n
    (Ha : aligned model root_session p X c n)
    q s sq a c' s' sq' :
  delivery_available p X c n Ha q sq ->
  role_step model participants X c s sq a c' s' sq' ->
  possible model p n q s.
Proof.
  intros Havailable Hstep.
  eapply aligned_live; [exact Havailable |].
  eapply source_step_live. exact Hstep.
Qed.

Corollary source_action_exposes_network_action p X c n
    (Ha : aligned model root_session p X c n)
    q s sq a c' s' sq' :
  delivery_available p X c n Ha q sq ->
  role_step model participants X c s sq a c' s' sq' ->
  exists na n' q' ns', Endpoints.step model participants p X n q s na n' q' ns'.
Proof.
  intros Havailable Hstep. apply possible_step.
  eapply source_action_is_network_enabled; eassumption.
Qed.

(* This is only the per-role part of matched_ready. Global finality still
   needs the separate mailbox/delivery emptiness correspondence. *)
Corollary aligned_role_ready p X c n
    (Ha : aligned model root_session p X c n) q s sq :
  delivery_available p X c n Ha q sq ->
  ((exists x, RoleSteps.returns model c x) \/
   (exists a c' s' sq', role_step model participants X c s sq a c' s' sq')) ->
  ((exists x, Endpoints.returns model X n x) \/
   (exists na n' q' ns', Endpoints.step model participants p X n q s na n' q'
     ns')).
Proof.
  intros Havailable [[x Hr] | (a & c' & s' & sq' & Hstep)].
  - left. exists x. eapply source_return_is_network_return; eassumption.
  - right. eapply source_action_exposes_network_action; eassumption.
Qed.

Corollary generated_source_action_exposes_network_action p X (c : Choreo M p X)
    q s a c' s' sq' :
  role_step model participants X (Code nil c) s nil a c' s' sq' ->
  exists na n' q' ns',
    Endpoints.step model participants p X (load (EndpointRunner.runner c
      root_session))
      q s na n' q' ns'.
Proof.
  intro Hstep. eapply source_action_exposes_network_action with
      (Ha := generated_initial_alignment model root_session p X c).
  - apply empty_delivery_available.
  - exact Hstep.
Qed.
End Progress.
