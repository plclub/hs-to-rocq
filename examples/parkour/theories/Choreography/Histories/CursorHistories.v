From Stdlib Require Import Lists.List.
Require Import Choreography.Choreo2 Control.Monad.Tree Parkour.Symbol.
From ParkourTheories.Choreography Require Import Occurrences PendingDeliveries
  RoleSteps Execution WellFormedness.
From ParkourTheories.Choreography.Results Require Import FiniteSelection.
Import ListNotations.

(* Typed zippers retain actual continuations and both live App branches.
   They are not paths alone: plugging an action focus reconstructs the exact
   pre/post cursor, with no erasure or guessed Bind argument. *)
Section PrefixHistories.
Context {M E : Type -> Type} {Store : Type}.
Variable model : LocalEffects.local_model M E Symbol Store.
Variable configured : list Symbol.

Inductive cursor_context (p : Symbol) : Type -> Type -> Type :=
| ContextHole X : cursor_context p X X
| ContextSeq X Y Z (o : occurrence) (k : Y -> Choreo M p Z) :
    cursor_context p X Y -> cursor_context p X Z
| ContextLeft X Y Z (x : @cursor M E p Y) :
    cursor_context p X (Y -> Z) -> cursor_context p X Z
| ContextRight X Y Z (f : @cursor M E p (Y -> Z)) :
    cursor_context p X Y -> cursor_context p X Z.
Arguments ContextHole {p X}.
Arguments ContextSeq {p X Y Z} _ _ _.
Arguments ContextLeft {p X Y Z} _ _.
Arguments ContextRight {p X Y Z} _ _.

Fixpoint plug {p X A} (C : cursor_context p X A)
    (t : @cursor M E p X) : cursor p A :=
  match C in cursor_context _ U B return cursor p U -> cursor p B with
  | ContextHole => fun t => t
  | ContextSeq o k C => fun t => Seq o (plug C t) k
  | ContextLeft x C => fun t => Fork (plug C t) x
  | ContextRight f C => fun t => Fork f (plug C t)
  end t.

#[universes(template)]
Inductive silent_prefix {p A} : @cursor M E p A -> cursor p A -> Prop :=
| PrefixRefl t : silent_prefix t t
| PrefixCons t u v :
    silent model A t u -> silent_prefix u v -> silent_prefix t v.

Lemma silent_plug p X A (C : cursor_context p X A) t u :
  silent model X t u -> silent model A (plug C t) (plug C u).
Proof.
  intro S. induction C; cbn.
  - exact S.
  - apply SSeqUnder. apply IHC. exact S.
  - apply SForkLeft. apply IHC. exact S.
  - apply SForkRight. apply IHC. exact S.
Qed.

Lemma silent_prefix_plug p X A (C : cursor_context p X A) t u :
  silent_prefix t u -> silent_prefix (plug C t) (plug C u).
Proof.
  induction 1.
  - constructor.
  - eapply PrefixCons; [apply silent_plug; exact H | exact IHsilent_prefix].
Qed.

(* The real actions at a focus. These are exactly the five primitive Source
   rules, including their real local-event and typed take_at_occurrence
     evidence. *)
Inductive primitive_action {p} :
    forall X, cursor p X -> Store -> list pending -> @source_action E Store ->
      cursor p X -> Store -> list pending -> Prop :=
| PrimitiveLocal X o t s a t' s' q :
    LocalEffects.local_step (LocalEffects.reply_local _ _ _ _ model)
      p t s a t' s' ->
    primitive_action (At X p p) (Local o t) s q (LocalAction o a)
      (Local o t') s' q
| PrimitiveSend X d o sh rd kl kd sl v sd (h : d <> p) s q :
    primitive_action (At X d p)
      (Code o (Perf (@Comm M p X p d sh rd kl kd sl v sd))) s q
      (SendAction X o p d (unAt v eq_refl)) (Returned (off_at h)) s
      (q ++ [Pending X DataDelivery o p d (unAt v eq_refl)])
| PrimitiveReceive X l o sh rd kl kd sl v sd (h : l <> p) s q q' x :
    take_at_occurrence DataDelivery o l p x q q' ->
    primitive_action (At X p p)
      (Code o (Perf (@Comm M p X l p sh rd kl kd sl v sd))) s q
      (ReceiveAction X o l p x) (Returned (here_at x)) s q'
| PrimitiveAnnounce X Y o sh rd kl sl v (k : X -> Choreo M p Y) s q :
    primitive_action Y
      (Code o (Perf (@Cond M p X p Y sh rd kl sl v k))) s q
      (AnnounceAction X o p (unAt v eq_refl))
      (Code (child o ChoiceBody) (k (unAt v eq_refl))) s
      (q ++ announcement configured X o p (unAt v eq_refl))
| PrimitiveHear X Y l o sh rd kl sl v (k : X -> Choreo M p Y)
    (h : l <> p) s q q' x :
    take_at_occurrence ChoiceDelivery o l p x q q' ->
    primitive_action Y
      (Code o (Perf (@Cond M p X l Y sh rd kl sl v k))) s q
      (HearAction X o l p x) (Code (child o ChoiceBody) (k x)) s q'.

Lemma primitive_is_role_step p A t s q a u s' q' :
  @primitive_action p A t s q a u s' q' ->
  role_step model configured A t s q a u s' q'.
Proof.
  destruct 1.
  - apply RLocal. exact H.
  - apply RSend.
  - eapply RReceive; eassumption.
  - apply RAnnounce.
  - eapply RHear; eassumption.
Qed.

Lemma role_step_plug p X A (C : cursor_context p X A) t s q a u s' q' :
  role_step model configured X t s q a u s' q' ->
  role_step model configured A (plug C t) s q a (plug C u) s' q'.
Proof.
  intro S. induction C; cbn.
  - exact S.
  - apply RSeq. apply IHC. exact S.
  - apply RLeft. apply IHC. exact S.
  - apply RRight. apply IHC. exact S.
Qed.

(* Every actual step exposes an exact primitive focus after finitely many
   real silent changes. No constraint on the initial code or WF is added. *)
Theorem role_step_focus p A t s q a u s' q' :
  @role_step M E Store model configured p A t s q a u s' q' ->
  exists X (C : cursor_context p X A) before after,
    silent_prefix t (plug C before) /\
    primitive_action X before s q a after s' q' /\
    u = plug C after.
Proof.
  intro Step. induction Step.
  - eexists _, ContextHole, _, _. split; [constructor |].
    split; [apply PrimitiveLocal; exact H | reflexivity].
  - eexists _, ContextHole, _, _. split; [constructor |].
    split; [apply PrimitiveSend | reflexivity].
  - eexists _, ContextHole, _, _. split; [constructor |].
    split; [eapply PrimitiveReceive; eassumption | reflexivity].
  - eexists _, ContextHole, _, _. split; [constructor |].
    split; [apply PrimitiveAnnounce | reflexivity].
  - eexists _, ContextHole, _, _. split; [constructor |].
    split; [eapply PrimitiveHear; eassumption | reflexivity].
  - destruct IHStep as (B & C & b & z & Sil & Act & Eq).
    exists B, (ContextSeq o k C), b, z. cbn. split.
    + exact (silent_prefix_plug p X Y (ContextSeq o k ContextHole) _ _ Sil).
    + split; [exact Act | now rewrite Eq].
  - destruct IHStep as (B & C & b & z & Sil & Act & Eq).
    exists B, (ContextLeft x C), b, z. cbn. split.
    + exact (silent_prefix_plug p (X -> Y) Y
        (ContextLeft x ContextHole) _ _ Sil).
    + split; [exact Act | now rewrite Eq].
  - destruct IHStep as (B & C & b & z & Sil & Act & Eq).
    exists B, (ContextRight f C), b, z. cbn. split.
    + exact (silent_prefix_plug p X Y (ContextRight f ContextHole) _ _ Sil).
    + split; [exact Act | now rewrite Eq].
  - destruct IHStep as (B & C & b & z & Sil & Act & Eq).
    exists B, C, b, z. split.
    + eapply PrefixCons; eassumption.
    + split; assumption.
Qed.
Inductive primitive_silent {p} : forall X, @cursor M E p X -> cursor p X -> Prop
  :=
| PrimitivePure X o (x : X) :
    primitive_silent X (Code o (Pure x)) (Returned x)
| PrimitiveBind X Y o (t : Choreo M p X) (k : X -> Choreo M p Y) :
    primitive_silent Y (Code o (Bind t k))
      (Seq o (Code (child o BindPrefix) t) k)
| PrimitiveApp X Y o (f : Choreo M p (X -> Y)) x :
    primitive_silent Y (Code o (App f x))
      (Fork (Code (child o AppFunction) f) (Code (child o AppArgument) x))
| PrimitiveBody X Y o (x : X) (k : X -> Choreo M p Y) :
    primitive_silent Y (Seq o (Returned x) k)
      (Code (child o BindBody) (k x))
| PrimitiveJoin X Y (f : X -> Y) x :
    primitive_silent Y (Fork (Returned f) (Returned x)) (Returned (f x))
| PrimitiveLocalStart X o ks ss (f : Unwrap p p -> M X) :
    primitive_silent (At X p p)
      (Code o (Perf (@Locally M p X p ks ss f)))
      (Local o (LocalEffects.interpret_local _ _ _ _ model X
        (f (RoleSteps.owner_unwrap p))))
| PrimitiveLocalOther X l o ks ss f (h : l <> p) :
    primitive_silent (At X l p)
      (Code o (Perf (@Locally M p X l ks ss f))) (Returned (off_at h))
| PrimitiveLocalDone X o t x :
    LocalEffects.local_return t x ->
    primitive_silent (At X p p) (Local o t) (Returned (here_at x))
| PrimitiveCommOther X l d o sh rd kl kd sl v sd
    (hl : l <> p) (hd : d <> p) (hne : l <> d) :
    primitive_silent (At X d p)
      (Code o (Perf (@Comm M p X l d sh rd kl kd sl v sd)))
      (Returned (off_at hd))
| PrimitiveCommSelf X l o sh rd kl kd sl v sd :
    primitive_silent (At X l p)
      (Code o (Perf (@Comm M p X l l sh rd kl kd sl v sd))) (Returned v).

Lemma primitive_is_silent p A t u :
  @primitive_silent p A t u -> silent model A t u.
Proof. destruct 1; econstructor; eassumption. Qed.

Lemma silent_focus p A t u :
  @silent M E Store model p A t u ->
  exists X (C : cursor_context p X A) before after,
    t = plug C before /\ primitive_silent X before after /\ u = plug C after.
Proof.
  intro S. induction S.
  - eexists _, ContextHole, _, _. split; [reflexivity |].
    split; [apply PrimitivePure | reflexivity].
  - eexists _, ContextHole, _, _. split; [reflexivity |].
    split; [apply PrimitiveBind | reflexivity].
  - eexists _, ContextHole, _, _. split; [reflexivity |].
    split; [apply PrimitiveApp | reflexivity].
  - eexists _, ContextHole, _, _. split; [reflexivity |].
    split; [apply PrimitiveBody | reflexivity].
  - destruct IHS as (B & C & b & z & Eq & Prim & Eq').
    exists B, (ContextSeq o k C), b, z. cbn.
    split; [now rewrite Eq |]. split; [exact Prim | now rewrite Eq'].
  - destruct IHS as (B & C & b & z & Eq & Prim & Eq').
    exists B, (ContextLeft x C), b, z. cbn.
    split; [now rewrite Eq |]. split; [exact Prim | now rewrite Eq'].
  - destruct IHS as (B & C & b & z & Eq & Prim & Eq').
    exists B, (ContextRight f C), b, z. cbn.
    split; [now rewrite Eq |]. split; [exact Prim | now rewrite Eq'].
  - eexists _, ContextHole, _, _. split; [reflexivity |].
    split; [apply PrimitiveJoin | reflexivity].
  - eexists _, ContextHole, _, _. split; [reflexivity |].
    split; [apply PrimitiveLocalStart | reflexivity].
  - eexists _, ContextHole, _, _. split; [reflexivity |].
    split; [apply PrimitiveLocalOther | reflexivity].
  - eexists _, ContextHole, _, _. split; [reflexivity |].
    split; [apply PrimitiveLocalDone; exact H | reflexivity].
  - eexists _, ContextHole, _, _. split; [reflexivity |].
    split; [eapply PrimitiveCommOther; eassumption | reflexivity].
  - eexists _, ContextHole, _, _. split; [reflexivity |].
    split; [apply PrimitiveCommSelf | reflexivity].
Qed.

Fixpoint compose_context {p X A} (C : cursor_context p X A)
    {U} (D : cursor_context p U X) : cursor_context p U A :=
  match C in cursor_context _ V B
    return cursor_context p U V -> cursor_context p U B with
  | ContextHole => fun D => D
  | ContextSeq o k C => fun D => ContextSeq o k (compose_context C D)
  | ContextLeft x C => fun D => ContextLeft x (compose_context C D)
  | ContextRight f C => fun D => ContextRight f (compose_context C D)
  end D.

Lemma plug_compose p X A (C : cursor_context p X A) U
    (D : cursor_context p U X) t :
  plug (compose_context C D) t = plug C (plug D t).
Proof.
  induction C; cbn; [reflexivity |..]; now rewrite IHC.
Qed.

(* A history is rooted at an actual cursor. Each edge retains its typed
   primitive focus; action edges also retain real queue/store witnesses.
   In particular a body-entry edge stores the actual Returned prefix value,
   and never selects an arbitrary argument for its continuation.
   Intervening changes by other actors are forgotten: cursor_history alone
   does NOT assert global reachability or cross-role message consistency.
   run_actor_history below extracts these histories from a real global run. *)
#[universes(template)]
Inductive cursor_history {p A} (start : @cursor M E p A) :
    list (@source_action E Store) -> cursor p A -> Prop :=
| HistoryStart : cursor_history start [] start
| HistorySilent tr X (C : cursor_context p X A) before after :
    cursor_history start tr (plug C before) ->
    primitive_silent X before after ->
    cursor_history start tr (plug C after)
| HistoryAction tr X (C : cursor_context p X A) before after s q a s' q' :
    cursor_history start tr (plug C before) ->
    primitive_action X before s q a after s' q' ->
    cursor_history start (tr ++ [a]) (plug C after).

Lemma history_after_silent p A start tr t u :
  @cursor_history p A start tr t ->
  silent model A t u -> cursor_history start tr u.
Proof.
  intros Hist S. destruct (silent_focus p A t u S)
    as (X & C & b & z & -> & Prim & ->).
  eapply HistorySilent; eassumption.
Qed.

Lemma history_after_silent_prefix p A start tr t u :
  @cursor_history p A start tr t ->
  silent_prefix t u -> cursor_history start tr u.
Proof.
  intros Hist S. induction S; [exact Hist |].
  apply IHS. eapply history_after_silent; eassumption.
Qed.

Theorem history_after_role_step p A start tr t s q a u s' q' :
  @cursor_history p A start tr t ->
  role_step model configured A t s q a u s' q' ->
  cursor_history start (tr ++ [a]) u.
Proof.
  intros Hist Step.
  destruct (role_step_focus p A t s q a u s' q' Step)
    as (X & C & b & z & Sil & Prim & ->).
  eapply HistoryAction; [|exact Prim].
  eapply history_after_silent_prefix; eassumption.
Qed.

Lemma history_after_returns p A start tr t x :
  @cursor_history p A start tr t ->
  returns model t x ->
  cursor_history start tr (Returned x).
Proof.
  intros Hist Ret. induction Ret; [exact Hist |].
  apply IHRet. eapply history_after_silent; eassumption.
Qed.

Lemma history_plug p X A (C : cursor_context p X A) start tr t :
  cursor_history start tr t ->
  cursor_history (plug C start) tr (plug C t).
Proof.
  intro Hist. induction Hist.
  - constructor.
  - rewrite <- !plug_compose.
    eapply HistorySilent; [rewrite plug_compose; exact IHHist | exact H].
  - rewrite <- !plug_compose.
    eapply HistoryAction; [rewrite plug_compose; exact IHHist | exact H].
Qed.

Lemma history_append p A start tr t more u :
  @cursor_history p A start tr t ->
  cursor_history t more u ->
  cursor_history start (tr ++ more) u.
Proof.
  intros Hist Rest. induction Rest.
  - now rewrite app_nil_r.
  - eapply HistorySilent; eassumption.
  - rewrite app_assoc. eapply HistoryAction; eassumption.
Qed.

(* Prefix completion remains usable after a role enters its body. This
   lemma permits real local actions, sends, receives, and Cond announcements
   in BOTH histories. It does not require other roles to have completed. *)
Theorem history_bind_body p X Y o (t : Choreo M p X)
    (k : X -> Choreo M p Y) prefix body x u :
  cursor_history (Code (child o BindPrefix) t) prefix (Returned x) ->
  cursor_history (Code (child o BindBody) (k x)) body u ->
  cursor_history (Code o (Bind t k)) (prefix ++ body) u.
Proof.
  intros Prefix Body.
  assert (Begin : cursor_history (Code o (Bind t k)) []
    (Seq o (Code (child o BindPrefix) t) k)).
  { eapply HistorySilent with (C := ContextHole).
    - constructor.
    - apply PrimitiveBind. }
  pose proof (history_plug p X Y (ContextSeq o k ContextHole) _ _ _ Prefix)
    as Under.
  pose proof (history_append p Y _ _ _ _ _ Begin Under) as Complete.
  cbn in Complete.
  assert (Entered : cursor_history (Code o (Bind t k)) prefix
    (Code (child o BindBody) (k x))).
  { eapply HistorySilent with (C := ContextHole).
    - exact Complete.
    - apply PrimitiveBody. }
  eapply history_append; eassumption.
Qed.

(* A real prefix action can determine an arbitrary typed Bind argument.
   Its residual may finish through owner-local return, self communication,
   or a chosen Cond branch; no evaluator or total-family premise is used. *)
Theorem history_bind_prefix_action p X Y o (t : Choreo M p X)
    (k : X -> Choreo M p Y) s q a residual s' q' x :
  role_step model configured X (Code (child o BindPrefix) t)
    s q a residual s' q' ->
  returns model residual x ->
  cursor_history (Code o (Bind t k)) [a]
    (Code (child o BindBody) (k x)).
Proof.
  intros Step Ret.
  assert (Prefix : cursor_history (Code (child o BindPrefix) t)
    [a] (Returned x)).
  { eapply history_after_returns; [|exact Ret].
    eapply history_after_role_step with (tr := []); [constructor |exact Step]. }
  exact (history_bind_body p X Y o t k [a] [] x
    (Code (child o BindBody) (k x)) Prefix
    (HistoryStart (Code (child o BindBody) (k x)))).
Qed.

Theorem history_bind_receive p X Y l o sh rd kl kd sl v sd
    (k : At X p p -> Choreo M p Y) (h : l <> p) (s : Store) q q' x :
  take_at_occurrence DataDelivery (child o BindPrefix) l p x q q' ->
  cursor_history
    (Code o (Bind (Perf (@Comm M p X l p sh rd kl kd sl v sd)) k))
    [ReceiveAction X (child o BindPrefix) l p x]
    (Code (child o BindBody) (k (here_at x))).
Proof.
  intro Take.
  eapply history_bind_prefix_action with (s := s) (q := q) (s' := s)
    (q' := q') (residual := Returned (here_at x)).
  - eapply RReceive; eassumption.
  - constructor.
Qed.

Definition action_actor (a : @source_action E Store) : Symbol :=
  match a with
  | LocalAction _ (LocalEffects.LocalEvent p _ _ _ _) => p
  | SendAction _ _ p _ _ => p
  | ReceiveAction _ _ _ p _ => p
  | AnnounceAction _ _ p _ => p
  | HearAction _ _ _ p _ => p
  end.

Lemma role_step_actor p A t s q a u s' q' :
  @role_step M E Store model configured p A t s q a u s' q' ->
  action_actor a = p.
Proof.
  induction 1; cbn; try reflexivity; try assumption.
  destruct H. reflexivity.
Qed.

Definition actor_actions p (tr : list (@source_action E Store)) :=
  filter (fun a => if List.list_eq_dec BinNat.N.eq_dec (action_actor a) p
                  then true else false) tr.

Lemma actor_actions_snoc p tr a :
  actor_actions p (tr ++ [a]) =
    actor_actions p tr ++
    if List.list_eq_dec BinNat.N.eq_dec (action_actor a) p then [a] else [].
Proof.
  unfold actor_actions. rewrite filter_app. cbn.
  destruct (List.list_eq_dec BinNat.N.eq_dec (action_actor a) p); reflexivity.
Qed.

(* Actual global runs supply the history at EVERY role, with exactly that
   actor's actions in global order. Histories include nonconfigured observers;
   there is no completion or coherence assumption in this extraction theorem. *)
Theorem run_actor_history A (start finish : configuration A) tr :
  Choreography.Execution.run model configured start tr finish ->
  forall p, cursor_history (@positions M E Store A start p) (actor_actions p tr)
    (@positions M E Store A finish p).
Proof.
  intro Run. induction Run as [start | start tr middle a finish Run IH Step].
  - intro p. constructor.
  - intro p. destruct Step as [actor a finish Member Step Frame].
    rewrite actor_actions_snoc.
    pose proof (role_step_actor _ _ _ _ _ _ _ _ _ Step) as Actor.
    rewrite Actor.
    destruct (List.list_eq_dec BinNat.N.eq_dec actor p) as [Eq|Ne].
    + subst p. eapply history_after_role_step; [apply IH | exact Step].
    + rewrite app_nil_r. rewrite <- Frame.
      * apply IH.
      * intro Eq. apply Ne. symmetry. exact Eq.
Qed.

Corollary initial_actor_history A (c : forall p, Choreo M p (A p))
    s tr finish :
  Choreography.Execution.run model configured (initial c s) tr finish ->
  forall p, cursor_history (Code [] (c p)) (actor_actions p tr)
    (@positions M E Store A finish p).
Proof. apply run_actor_history. Qed.

(* Select ONLY completed roles, keeping each selected actual result attached
   to its complete syntax-rooted history. No full result tuple is requested,
   even if other roles have uninhabited result types or entered other nodes. *)
Theorem run_completed_partial_histories A (start finish : configuration A)
    tr completed :
  Choreography.Execution.run model configured start tr finish ->
  (forall p, In p completed ->
    exists x, returns model (@positions M E Store A finish p) x) ->
  exists v : values A (fun p => In p completed),
    forall p d,
      returns model (@positions M E Store A finish p) (v p d) /\
      cursor_history (@positions M E Store A start p) (actor_actions p tr)
        (Returned (v p d)).
Proof.
  intros Run Done.
  destruct (FiniteSelection.select_returned A
    (fun p x => returns model (@positions M E Store A finish p) x)
    completed Done) as [v Actual].
  exists v. intros p d. split; [exact (Actual p d) |].
  eapply history_after_returns.
  - exact (run_actor_history A start finish tr Run p).
  - exact (Actual p d).
Qed.

End PrefixHistories.

(* A diagnostic about the LEGACY FIFO relation take_first_on_source_channel, NOT
  the
   occurrence-only take_at_occurrence used by Source steps. Reaching a
     syntactically
   matching occurrence is insufficient on an arbitrary queue: an earlier
   same-channel entry must be ruled out by a reachable-cursor invariant. *)
Lemma take_pending_same_channel_head X k o s d (x : X) q q' :
  take_first_on_source_channel k o s d x q q' ->
  forall v tail, q = v :: tail -> same_channel k o s d v ->
    v = Pending X k o s d x.
Proof.
  intro Take. induction Take; intros v0 tail Eq Same.
  - inversion Eq. reflexivity.
  - inversion Eq; subst. contradiction.
Qed.

Lemma same_lane_earlier_occurrence_blocks X k earlier o s d (x y : X) q q' :
  source_lane earlier = source_lane o ->
  earlier <> o ->
  ~ take_first_on_source_channel k o s d x
      (Pending X k earlier s d y :: q) q'.
Proof.
  intros Lane Different Take.
  pose proof (take_pending_same_channel_head _ _ _ _ _ _ _ _ Take
    (Pending X k earlier s d y) q eq_refl) as Head.
  assert (Same : same_channel k o s d (Pending X k earlier s d y)).
  { cbn. repeat split. symmetry. exact Lane. }
  specialize (Head Same).
  apply Different.
  exact (f_equal
    (fun v => match v with Pending _ _ occurrence _ _ _ => occurrence end)
    Head).
Qed.

(* Observations of ACTUAL constructor dictionaries and values. Unlike encodes,
   the sender predicate names the value stored in the source Comm itself. *)
Definition encodes_source_value {M p A} (c : Choreo M p A)
    (wire : GHC.Base.String) : Prop :=
  match c with
  | Perf (@Comm _ _ X l _ sh _ _ _ _ v _) =>
      forall own : l = p, @Parkour.Codec.show X sh (unAt v own) = wire
  | _ => False
  end.

Definition decodes_returned_value {M p A} (c : Choreo M p A)
    (wire : GHC.Base.String) (result : A) : Prop :=
  match c in Tree _ B return B -> Prop with
  | Perf e =>
      match e in ChoreoSig _ _ B return B -> Prop with
      | @Comm _ _ X _ r _ rd _ _ _ _ _ => fun result =>
          forall own : r = p,
            @Parkour.Codec.read X rd wire = Some (unAt result own)
      | _ => fun _ => False
      end
  | _ => fun _ => False
  end result.

(* Constructor coherence for a partial completed receiver family. The only
   execution evidence requested is a PAST wire read using the real source
   dictionaries. A matched-history invariant supplies this from decorated
   deliveries and their same-occurrence sends; it is not a readiness premise.
   In particular sender roles need not be in the completed subset D. *)
Theorem structural_comm_partial_read_results R M S A c Q :
  structural R M S A c Q ->
  forall p (available : S p) l r,
    communication_head (c p available) = Some (l,r) ->
    l <> r ->
    forall D (v : values A D) (inc : includes D S),
      (forall (sender : S l) (receiver : D r),
        exists wire,
          encodes_source_value (c l sender) wire /\
          decodes_returned_value (c r (inc r receiver)) wire (v r receiver)) ->
      Q D v.
Proof.
  intro W. induction W; intros p available a b Head Different D v inc Reads;
    match goal with
    | Eq : forall p s, _ = _ |- _ => rewrite Eq in Head
    end; cbn in Head; try discriminate.
  inversion Head; subst a b.
  split; [exact inc |]. intros sender receiver.
  destruct (Reads sender receiver) as (wire & Sent & Received).
  rewrite H2 in Sent, Received. cbn in Sent, Received.
  specialize (Sent eq_refl). specialize (Received eq_refl).
  rewrite <- Sent in Received.
  pose proof (H1 sender (inc r receiver) Different
    (unAt (x l sender) eq_refl)) as Roundtrip.
  rewrite Roundtrip in Received. now inversion Received.
Qed.
