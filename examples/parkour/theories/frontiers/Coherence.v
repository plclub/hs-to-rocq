From Stdlib Require Import Lists.List Logic.Eqdep_dec.
Require Import Choreography.Choreo2 Control.Monad.Tree Parkour.Symbol.
Require Import DeadlockSource DeadlockWellFormed.
Require Import DeadlockPartialValues.
Import ListNotations.

(* A deliberately executable slice of source coherence. This evaluator performs
   bookkeeping only: it neither supplies local results nor fabricates messages.
   In particular it cannot cross Cond, a send, or a receive. Its fuel is not a
   progress hypothesis. Every successful result has an actual Source returns
   derivation, and partial families of these results satisfy structural's
   result relation, including its partial Bind-prefix obligation. *)
Fixpoint silent_value {M p A} (fuel : nat) (c : Choreo M p A) : option A :=
  match fuel with
  | O => None
  | S n =>
    match c with
    | Pure x => Some x
    | App f x =>
      match silent_value n f, silent_value n x with
      | Some g, Some y => Some (g y)
      | _, _ => None
      end
    | Bind t k =>
      match silent_value n t with
      | Some x => silent_value n (k x)
      | None => None
      end
    | Perf e =>
      match e with
      | @Locally _ _ X l _ _ _ =>
        match @Symbol.decide l p MkSSymbol MkSSymbol with
        | Proved _ => None
        | Disproved h => Some (DeadlockSource.off_at (fun e => GHC.Base.absurd
          (h e)))
        end
      | @Comm _ _ X l r _ _ _ _ _ v _ =>
        match @Symbol.decide l r MkSSymbol MkSSymbol with
        | Proved h =>
          match h in _ = r' return option (At X r' p) with
          | eq_refl => Some v
          end
        | Disproved _ =>
          match @Symbol.decide l p MkSSymbol MkSSymbol,
                @Symbol.decide r p MkSSymbol MkSSymbol with
          | Disproved _, Disproved hr =>
            Some (DeadlockSource.off_at (fun e => GHC.Base.absurd (hr e)))
          | _, _ => None
          end
        end
      | @Cond _ _ _ _ _ _ _ _ _ _ _ => None
      end
    end
  end.

Section Execution.
Context {M E : Type -> Type} {Store : Type}.
Variable model : DeadlockLocal.local_model M E Symbol Store.

Lemma returns_seq p X Y o (t : @cursor M E p X)
    (k : X -> Choreo M p Y) x y :
  returns model t x ->
  returns model (Code (child o BindBody) (k x)) y ->
  returns model (Seq o t k) y.
Proof.
  intros H. induction H; intro K.
  - eapply ReturnsSilent; [apply SSeq | exact K].
  - eapply ReturnsSilent; [apply SSeqUnder; exact H | apply IHreturns; exact K].
Qed.

End Execution.

(* Typed zippers retain actual continuations and both live App branches.
   They are not paths alone: plugging an action focus reconstructs the exact
   pre/post cursor, with no erasure or guessed Bind argument. *)
Section PrefixHistories.
Context {M E : Type -> Type} {Store : Type}.
Variable model : DeadlockLocal.local_model M E Symbol Store.
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
   rules, including their real local-event and typed take_at evidence. *)
Inductive primitive_action {p} :
    forall X, cursor p X -> Store -> list pending -> @source_action E Store ->
      cursor p X -> Store -> list pending -> Prop :=
| PrimitiveLocal X o t s a t' s' q :
    DeadlockLocal.local_step (DeadlockLocal.reply_local _ _ _ _ model)
      p t s a t' s' ->
    primitive_action (At X p p) (Local o t) s q (LocalAction o a)
      (Local o t') s' q
| PrimitiveSend X d o sh rd kl kd sl v sd (h : d <> p) s q :
    primitive_action (At X d p)
      (Code o (Perf (@Comm M p X p d sh rd kl kd sl v sd))) s q
      (SendAction X o p d (unAt v eq_refl)) (Returned (off_at h)) s
      (q ++ [Pending X DataDelivery o p d (unAt v eq_refl)])
| PrimitiveReceive X l o sh rd kl kd sl v sd (h : l <> p) s q q' x :
    take_at DataDelivery o l p x q q' ->
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
    take_at ChoiceDelivery o l p x q q' ->
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
      (Local o (DeadlockLocal.interpret_local _ _ _ _ model X
        (f (DeadlockSource.owner_unwrap p))))
| PrimitiveLocalOther X l o ks ss f (h : l <> p) :
    primitive_silent (At X l p)
      (Code o (Perf (@Locally M p X l ks ss f))) (Returned (off_at h))
| PrimitiveLocalDone X o t x :
    DeadlockLocal.local_return t x ->
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
  take_at DataDelivery (child o BindPrefix) l p x q q' ->
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
  | LocalAction _ (DeadlockLocal.LocalEvent p _ _ _ _) => p
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
  crun model configured start tr finish ->
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
  crun model configured (initial c s) tr finish ->
  forall p, cursor_history (Code [] (c p)) (actor_actions p tr)
    (@positions M E Store A finish p).
Proof. apply run_actor_history. Qed.

(* Select ONLY completed roles, keeping each selected actual result attached
   to its complete syntax-rooted history. No full result tuple is requested,
   even if other roles have uninhabited result types or entered other nodes. *)
Theorem run_completed_partial_histories A (start finish : configuration A)
    tr completed :
  crun model configured start tr finish ->
  (forall p, In p completed ->
    exists x, returns model (@positions M E Store A finish p) x) ->
  exists v : values A (fun p => In p completed),
    forall p d,
      returns model (@positions M E Store A finish p) (v p d) /\
      cursor_history (@positions M E Store A start p) (actor_actions p tr)
        (Returned (v p d)).
Proof.
  intros Run Done.
  destruct (DeadlockPartialValues.select_returned A
    (fun p x => returns model (@positions M E Store A finish p) x)
    completed Done) as [v Actual].
  exists v. intros p d. split; [exact (Actual p d) |].
  eapply history_after_returns.
  - exact (run_actor_history A start finish tr Run p).
  - exact (Actual p d).
Qed.

End PrefixHistories.

Section ExecutionRemainder.
Context {M E : Type -> Type} {Store : Type}.
Variable model : DeadlockLocal.local_model M E Symbol Store.

Lemma returns_fork_left p X Y (f : @cursor M E p (X -> Y))
    (x : @cursor M E p X) g y :
  returns model f g -> returns model x y ->
  returns model (Fork f x) (g y).
Proof.
  intros H. induction H; intro K.
  - induction K.
    + eapply ReturnsSilent; [apply SJoin | constructor].
    + eapply ReturnsSilent; [apply SForkRight; exact H | exact IHK].
  - eapply ReturnsSilent; [apply SForkLeft; exact H | apply IHreturns; exact K].
Qed.

Lemma silent_value_returns fuel p A (c : Choreo M p A) x o :
  silent_value fuel c = Some x ->
  returns model (Code o c) x.
Proof.
  revert p A c x o. induction fuel as [|n IH]; intros p A c x o H;
    [discriminate |].
  destruct c as [A e | A y | X A f t | X A t k]; cbn in H.
  - destruct e as [X l kl sl f | X l r sh rd kl kr sl v sr |
                   X l A sh rd kl sl v k].
    + destruct (@Symbol.decide l p MkSSymbol MkSSymbol) as [eq|ne];
        [discriminate |].
      inversion H; subst x.
      eapply ReturnsSilent; [apply SLocalOther | constructor].
    + destruct (@Symbol.decide l r MkSSymbol MkSSymbol) as [eq|ne].
      * destruct eq. inversion H; subst x.
        eapply ReturnsSilent; [apply SCommSelf | constructor].
      * destruct (@Symbol.decide l p MkSSymbol MkSSymbol) as [eq|nl];
          [discriminate |].
        destruct (@Symbol.decide r p MkSSymbol MkSSymbol) as [eq|nr];
          [discriminate |].
        inversion H; subst x.
        eapply ReturnsSilent.
        -- eapply SCommOther; intro eq; apply GHC.Base.absurd;
             first [exact (nl eq) | exact (nr eq) | exact (ne eq)].
        -- constructor.
    + discriminate.
  - inversion H; subst x. eapply ReturnsSilent; [apply SPure | constructor].
  - destruct (silent_value n f) as [g|] eqn:F; [|discriminate].
    destruct (silent_value n t) as [y|] eqn:T; [|discriminate].
    inversion H; subst x.
    eapply ReturnsSilent; [apply SApp |].
    eapply returns_fork_left; apply IH; eassumption.
  - destruct (silent_value n t) as [y|] eqn:T; [|discriminate].
    eapply ReturnsSilent; [apply SBind |].
    eapply returns_seq; apply IH; eassumption.
Qed.
End ExecutionRemainder.

(* Extracting witnesses from a successful computation needs neither choice nor
   an inhabitant of the source result type. *)
Definition option_value {A} (o : option A) (ok : o <> None) : A :=
  match o as z return z <> None -> A with
  | Some x => fun _ => x
  | None => fun h => False_rect A (h eq_refl)
  end ok.

Lemma option_value_spec {A} (o : option A) (ok : o <> None) :
  o = Some (option_value o ok).
Proof. destruct o; [reflexivity | contradiction]. Qed.

(* Proof-index independence is explicit, rather than using the axiom of proof
   irrelevance. This is only a condition on evidence for role-set membership,
   not a causal or next-step condition. *)
Definition role_evidence_irrelevant (S : roles) :=
  forall p (s t : S p), s = t.

Lemma structural_empty_results R M S A c Q :
  structural R M S A c Q ->
  forall D (v : values A D), (forall p, ~ D p) -> Q D v.
Proof.
  intro W. induction W; intros D v Empty.
  - split; intros p d; exact (False_rect _ (Empty p d)).
  - intros p d. exact (False_rect _ (Empty p d)).
  - split; [intros p d; exact (False_rect _ (Empty p d)) |].
    intros s d. exact (False_rect _ (Empty r d)).
  - left. exact Empty.
  - exists (fun p d => False_rect _ (Empty p d)),
      (fun p d => False_rect _ (Empty p d)).
    repeat split; try (apply IHW1 || apply IHW2); try exact Empty.
    intros p d. exact (False_rect _ (Empty p d)).
  - unfold bind_results.
    exists D, (fun p d => False_rect _ (Empty p d)).
    split; [apply IHW; exact Empty |].
    eapply H0.
    + intros p d. exact (False_rect _ (Empty p d)).
    + apply IHW. exact Empty.
    + exact Empty.
Qed.

Lemma structural_silent_values R M S A c Q :
  structural R M S A c Q ->
  role_evidence_irrelevant S ->
  forall fuel D (v : values A D) (inc : includes D S),
    role_evidence_irrelevant D ->
    (forall p d, silent_value fuel (c p (inc p d)) = Some (v p d)) ->
    Q D v.
Proof.
  intros W. pose proof W as Original.
  induction W; intros PI fuel D v inc PId Eval;
    destruct fuel as [|n];
    try solve [eapply (structural_empty_results _ _ _ _ _ _ Original);
      intros p d; specialize (Eval p d); discriminate].
  - split; [exact inc |].
    intros p d s.
    specialize (Eval p d). rewrite H in Eval. cbn in Eval.
    rewrite (PI p (inc p d) s) in Eval. inversion Eval. reflexivity.
  - exact inc.
  - split; [exact inc |].
    intros s d.
    specialize (Eval r d). rewrite H2 in Eval. cbn in Eval.
    destruct (@Symbol.decide l r MkSSymbol MkSSymbol) as [eq|ne].
    + destruct eq. cbn in Eval. inversion Eval; subst.
      rewrite (PI l (inc l d) s). reflexivity.
    + destruct (@Symbol.decide r r MkSSymbol MkSSymbol) as [eq|nr].
      * discriminate.
      * exfalso. exact (GHC.Base.absurd (nr eq_refl)).
  - left. intros p d. specialize (Eval p d). rewrite H3 in Eval. discriminate.
  - assert (NF : forall p d, silent_value n (f p (inc p d)) <> None).
    { intros p d Z. specialize (Eval p d). rewrite H in Eval.
      cbn in Eval. rewrite Z in Eval. discriminate. }
    assert (NX : forall p d, silent_value n (x p (inc p d)) <> None).
    { intros p d Z. specialize (Eval p d). rewrite H in Eval.
      cbn in Eval. rewrite Z in Eval.
      destruct (silent_value n (f p (inc p d))); discriminate. }
    exists (fun p d => option_value _ (NF p d)),
      (fun p d => option_value _ (NX p d)).
    split.
    + eapply IHW1; [exact W1 | exact PI | exact PId |].
      intros p d. apply option_value_spec.
    + split.
      * eapply IHW2; [exact W2 | exact PI | exact PId |].
        intros p d. apply option_value_spec.
      * intros p d. specialize (Eval p d). rewrite H in Eval. cbn in Eval.
        rewrite (option_value_spec _ (NF p d)),
          (option_value_spec _ (NX p d)) in Eval.
        inversion Eval. reflexivity.
  - assert (NT : forall p d, silent_value n (t p (inc p d)) <> None).
    { intros p d Z. specialize (Eval p d). rewrite H1 in Eval.
      cbn in Eval. rewrite Z in Eval. discriminate. }
    set (a := (fun p d => option_value _ (NT p d)) : values A D).
    assert (Prefix : P D a).
    { eapply IHW; [exact W | exact PI | exact PId |].
      intros p d. apply option_value_spec. }
    unfold bind_results. exists D, a. split; [exact Prefix |].
    apply (H0 D a inc Prefix (H D a inc Prefix) PId n D v
      (fun p d => d) PId).
    intros p d. specialize (Eval p d). rewrite H1 in Eval. cbn in Eval.
    rewrite (option_value_spec _ (NT p d)) in Eval.
    exact Eval.
Qed.

Lemma list_role_evidence_irrelevant R :
  NoDup R -> role_evidence_irrelevant (fun p => In p R).
Proof.
  induction R as [|r R IH]; intro ND.
  - intros p s. inversion s.
  - inversion ND as [|? ? NotIn Tail]; subst.
    intros p [e|s] [f|t].
    + f_equal. apply UIP_dec. apply List.list_eq_dec. exact BinNat.N.eq_dec.
    + subst p. contradiction.
    + subst p. contradiction.
    + f_equal. exact (IH Tail p s t).
Qed.

(* This public slice has no proof-irrelevance premise or axiom: NoDup lists
   supply unique membership evidence constructively. The completed roles may
   be a strict subset, and no value is required at any other role. *)
Theorem structural_partial_silent_results R M A c Q completed
    (v : values A (fun p => In p completed))
    (inc : includes (fun p => In p completed) (fun p => In p R)) fuel :
  structural R M (fun p => In p R) A c Q ->
  NoDup R -> NoDup completed ->
  (forall p d, silent_value fuel (c p (inc p d)) = Some (v p d)) ->
  Q (fun p => In p completed) v.
Proof.
  intros W NR NC Eval.
  eapply structural_silent_values.
  - exact W.
  - apply list_role_evidence_irrelevant. exact NR.
  - apply list_role_evidence_irrelevant. exact NC.
  - exact Eval.
Qed.

Theorem well_formed_computed_partial_returns {M E Store}
    (model : DeadlockLocal.local_model M E Symbol Store)
    R A (c : forall p, Choreo M p (A p)) completed
    (v : values A (fun p => In p completed)) fuel :
  well_formed R M A c ->
  NoDup completed ->
  includes (fun p => In p completed) (fun p => In p R) ->
  (forall p d, silent_value fuel (c p) = Some (v p d)) ->
  exists Q,
    structural R M (fun p => In p R) A (fun p _ => c p) Q /\
    Q (fun p => In p completed) v /\
    forall p (d : In p completed) o, returns model (Code o (c p)) (v p d).
Proof.
  intros [NR [Q W]] NC inc Eval. exists Q. split; [exact W |]. split.
  - exact (structural_partial_silent_results R M A (fun p _ => c p) Q
      completed v inc fuel W NR NC Eval).
  - intros p d o.
    exact (silent_value_returns model fuel p (A p) (c p) (v p d) o (Eval p d)).
Qed.

(* A diagnostic about the LEGACY FIFO relation take_pending, NOT the
   occurrence-only take_at used by Source steps. Reaching a syntactically
   matching occurrence is insufficient on an arbitrary queue: an earlier
   same-channel entry must be ruled out by a reachable-cursor invariant. *)
Lemma take_pending_same_channel_head X k o s d (x : X) q q' :
  take_pending k o s d x q q' ->
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
  ~ take_pending k o s d x
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
