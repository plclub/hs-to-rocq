From Stdlib Require Import Lists.List.
From Stdlib Require NArith.BinNat.
From ITree Require Import ITree.
Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree.
From ParkourTheories Require Import Semantics.LocalEffects
  Choreography.PendingDeliveries Choreography.Occurrences.
Require Choreography.Choreo2.
Local Notation At := Choreography.Choreo2.At.
Local Notation Mk_At := Choreography.Choreo2.Mk_At.
Local Notation unAt := Choreography.Choreo2.unAt.
Local Notation Unwrap := Choreography.Choreo2.Unwrap.
Local Notation Choreo := Choreography.Choreo2.Choreo.
Local Notation Locally := Choreography.Choreo2.Locally.
Local Notation Comm := Choreography.Choreo2.Comm.
Local Notation Cond := Choreography.Choreo2.Cond.
Import ListNotations.

Definition off_at {X l p} (h : l <> p) : At X l p :=
  match @Parkour.Symbol.decide l p MkSSymbol MkSSymbol with
  | Proved e => False_rect _ (h e)
  | Disproved dpf => Mk_At (fun pf => GHC.Base.absurd (dpf pf))
  end.

Lemma off_at_decide {X l p} (h : l <> p) dpf :
  @Parkour.Symbol.decide l p MkSSymbol MkSSymbol = Disproved dpf ->
  @off_at X l p h = Mk_At (fun pf => GHC.Base.absurd (dpf pf)).
Proof. intros H. unfold off_at. rewrite H. reflexivity. Qed.
Definition here_at {X p} (x : X) : At X p p := Mk_At (fun _ => x).
Definition owner_unwrap (p : Symbol) : Unwrap p p :=
  fun X v => unAt v eq_refl.

Section Source.
Context {M E : Type -> Type} {Store : Type}.
Variable model : local_model M E Symbol Store.
Variable roles : list Symbol.

(* Each role has its own cursor, including each live App branch. A Bind
   continuation is retained as an actual Gallina function, never guessed. *)
Inductive cursor (p : Symbol) : Type -> Type :=
| Code : forall X, occurrence -> Choreo M p X -> cursor p X
| Returned : forall X, X -> cursor p X
| Local : forall X, occurrence -> itree E X -> cursor p (At X p p)
| Seq : forall X Y, occurrence -> cursor p X ->
    (X -> Choreo M p Y) -> cursor p Y
| Fork : forall X Y, cursor p (X -> Y) -> cursor p X -> cursor p Y.
Arguments Code {p X} _ _.
Arguments Returned {p X} _.
Arguments Local {p X} _ _.
Arguments Seq {p X Y} _ _ _.
Arguments Fork {p X Y} _ _.

(* Finite pure bookkeeping. These rules do not assert progress. *)
Inductive silent {p} : forall X, cursor p X -> cursor p X -> Prop :=
| SPure X o (x : X) : silent X (Code o (Pure x)) (Returned x)
| SBind X Y o (t : Choreo M p X) (k : X -> Choreo M p Y) :
    silent Y (Code o (Bind t k)) (Seq o (Code (child o BindPrefix) t) k)
| SApp X Y o (f : Choreo M p (X -> Y)) x :
    silent Y (Code o (App f x))
      (Fork (Code (child o AppFunction) f) (Code (child o AppArgument) x))
| SSeq X Y o (x : X) (k : X -> Choreo M p Y) :
    silent Y (Seq o (Returned x) k) (Code (child o BindBody) (k x))
| SSeqUnder X Y o t t' (k : X -> Choreo M p Y) :
    silent X t t' -> silent Y (Seq o t k) (Seq o t' k)
| SForkLeft X Y (f f' : cursor p (X -> Y)) x :
    silent (X -> Y) f f' -> silent Y (Fork f x) (Fork f' x)
| SForkRight X Y (f : cursor p (X -> Y)) x x' :
    silent X x x' -> silent Y (Fork f x) (Fork f x')
| SJoin X Y (f : X -> Y) x :
    silent Y (Fork (Returned f) (Returned x)) (Returned (f x))
| SLocalStart X o ks ss (f : Unwrap p p -> M X) :
    silent (At X p p)
      (Code o (Perf (@Locally M p X p ks ss f)))
      (Local o (interpret_local _ _ _ _ model X (f (owner_unwrap p))))
| SLocalOther X l o ks ss f (h : l <> p) :
    silent (At X l p) (Code o (Perf (@Locally M p X l ks ss f)))
      (Returned (off_at h))
| SLocalReturn X o t x :
    local_return t x ->
    silent (At X p p) (Local o t) (Returned (here_at x))
| SCommOther X l d o sh rd kl kd sl v sd
    (hl : l <> p) (hd : d <> p) (hne : l <> d) :
    silent (At X d p)
      (Code o (Perf (@Comm M p X l d sh rd kl kd sl v sd)))
      (Returned (off_at hd))
| SCommSelf X l o sh rd kl kd sl v sd :
    silent (At X l p)
      (Code o (Perf (@Comm M p X l l sh rd kl kd sl v sd)))
      (Returned v).

Inductive source_action : Type :=
| LocalAction : occurrence -> local_event E Symbol Store -> source_action
| SendAction : forall X, occurrence -> Symbol -> Symbol -> X -> source_action
| ReceiveAction : forall X, occurrence -> Symbol -> Symbol -> X -> source_action
| AnnounceAction : forall X, occurrence -> Symbol -> X -> source_action
| HearAction : forall X, occurrence -> Symbol -> Symbol -> X -> source_action.

Definition announcement X o owner (x : X) :=
  map (fun peer => Pending X ChoiceDelivery o owner peer x)
    (filter (fun peer => if List.list_eq_dec BinNat.N.eq_dec peer owner
                        then false else true) roles).

(* One real action, with closure under finite bookkeeping and live branches. *)
Inductive role_step {p} :
    forall X, cursor p X -> Store -> list pending ->
    source_action -> cursor p X -> Store -> list pending -> Prop :=
| RLocal X o t s a t' s' q :
    local_step (reply_local _ _ _ _ model) p t s a t' s' ->
    role_step (At X p p) (Local o t) s q (LocalAction o a)
      (Local o t') s' q
| RSend X d o sh rd kl kd sl v sd (h : d <> p) s q :
    role_step (At X d p)
      (Code o (Perf (@Comm M p X p d sh rd kl kd sl v sd))) s q
      (SendAction X o p d (unAt v eq_refl)) (Returned (off_at h)) s
      (q ++ [Pending X DataDelivery o p d (unAt v eq_refl)])
| RReceive X l o sh rd kl kd sl v sd (h : l <> p) s q q' x :
    take_at_occurrence DataDelivery o l p x q q' ->
    role_step (At X p p)
      (Code o (Perf (@Comm M p X l p sh rd kl kd sl v sd))) s q
      (ReceiveAction X o l p x) (Returned (here_at x)) s q'
| RAnnounce X Y o sh rd kl sl v (k : X -> Choreo M p Y) s q :
    role_step Y
      (Code o (Perf (@Cond M p X p Y sh rd kl sl v k))) s q
      (AnnounceAction X o p (unAt v eq_refl))
      (Code (child o ChoiceBody) (k (unAt v eq_refl))) s
      (q ++ announcement X o p (unAt v eq_refl))
| RHear X Y l o sh rd kl sl v (k : X -> Choreo M p Y)
    (h : l <> p) s q q' x :
    take_at_occurrence ChoiceDelivery o l p x q q' ->
    role_step Y (Code o (Perf (@Cond M p X l Y sh rd kl sl v k))) s q
      (HearAction X o l p x) (Code (child o ChoiceBody) (k x)) s q'
| RSeq X Y o t t' (k : X -> Choreo M p Y) s q a s' q' :
    role_step X t s q a t' s' q' ->
    role_step Y (Seq o t k) s q a (Seq o t' k) s' q'
| RLeft X Y (f f' : cursor p (X -> Y)) x s q a s' q' :
    role_step (X -> Y) f s q a f' s' q' ->
    role_step Y (Fork f x) s q a (Fork f' x) s' q'
| RRight X Y (f : cursor p (X -> Y)) x x' s q a s' q' :
    role_step X x s q a x' s' q' ->
    role_step Y (Fork f x) s q a (Fork f x') s' q'
| RSilent X t u t' s q a s' q' :
    silent X t u -> role_step X u s q a t' s' q' ->
    role_step X t s q a t' s' q'.

#[universes(template)]
Inductive returns {p X} : cursor p X -> X -> Prop :=
| Returns x : returns (Returned x) x
| ReturnsSilent t u x : silent X t u -> returns u x -> returns t x.

End Source.

Arguments Code {M E p X} _ _.
Arguments Returned {M E p X} _.
Arguments Local {M E p X} _ _.
Arguments Seq {M E p X Y} _ _ _.
Arguments Fork {M E p X Y} _ _.

(* A structural receive barrier. It inspects actual prefix syntax and never
   invokes its continuation, so ignoring an argument cannot erase a receive. *)
Fixpoint waiting_code {M p X} (t : Choreography.Choreo2.Choreo M p X) : Prop :=
  match t with
  | Perf e =>
      match e with
      | @Choreography.Choreo2.Comm _ _ _ l d _ _ _ _ _ _ _ =>
          l <> p /\ d = p
      | _ => False
      end
  | Bind t _ => waiting_code t
  | _ => False
  end.

Fixpoint waiting_cursor {M E p X} (t : @cursor M E p X) : Prop :=
  match t with
  | Code _ c => waiting_code c
  | Seq _ t _ => waiting_cursor t
  | _ => False
  end.

Lemma silent_waiting {M E Store} (model : local_model M E Symbol Store)
    p X (t u : @cursor M E p X) :
  silent model X t u -> waiting_cursor t -> waiting_cursor u.
Proof.
  intros H. induction H; cbn in *; intuition congruence.
Qed.

Lemma empty_queue_barrier {M E Store} (model : local_model M E Symbol Store)
    roles p X (t t' : @cursor M E p X) s q a s' q' :
  role_step model roles X t s q a t' s' q' ->
  q = [] -> waiting_cursor t -> False.
Proof.
  intros H. induction H; intros Hq Hw; cbn in Hw; try contradiction.
  - destruct Hw as [H _]. exact (H eq_refl).
  - subst q. inversion H.
  - eapply IHrole_step; eassumption.
  - eapply IHrole_step; [exact Hq |].
    eapply silent_waiting; eassumption.
Qed.

Definition action_occurrence {E Store} (a : @source_action E Store) : occurrence
  :=
  match a with
  | LocalAction o _ | SendAction _ o _ _ _ | ReceiveAction _ o _ _ _
  | AnnounceAction _ o _ _ | HearAction _ o _ _ _ => o
  end.

Definition acting_role {E Store} (a : @source_action E Store) : Symbol :=
  match a with
  | LocalAction _ (LocalEvent p _ _ _ _) => p
  | SendAction _ _ p _ _ | ReceiveAction _ _ _ p _
  | AnnounceAction _ _ p _ | HearAction _ _ _ p _ => p
  end.

Lemma role_step_actor {M E Store} (model : local_model M E Symbol Store)
    roles p X (t t' : @cursor M E p X) s q a s' q' :
  role_step model roles X t s q a t' s' q' -> acting_role a = p.
Proof.
  induction 1; try reflexivity; try assumption.
  destruct H. reflexivity.
Qed.

Fixpoint waiting_at_code {M p X} (path : occurrence)
    (t : Choreography.Choreo2.Choreo M p X) (o : occurrence) : Prop :=
  match t with
  | Perf e =>
      match e with
      | @Choreography.Choreo2.Comm _ _ _ l d _ _ _ _ _ _ _ =>
          l <> p /\ d = p /\ path = o
      | _ => False
      end
  | Bind t _ => waiting_at_code (child path BindPrefix) t o
  | _ => False
  end.

Fixpoint waiting_at_cursor {M E p X} (t : @cursor M E p X)
    (o : occurrence) : Prop :=
  match t with
  | Code path c => waiting_at_code path c o
  | Seq _ t _ => waiting_at_cursor t o
  | _ => False
  end.

Lemma silent_waiting_at {M E Store} (model : local_model M E Symbol Store)
    p X (t u : @cursor M E p X) :
  silent model X t u ->
  forall o, waiting_at_cursor t o -> waiting_at_cursor u o.
Proof.
  intros H. induction H; intros pos Hw; cbn in *;
    first [solve [intuition congruence] | eauto].
Qed.

Lemma waiting_action_at {M E Store} (model : local_model M E Symbol Store)
    roles p X (t t' : @cursor M E p X) s q a s' q' :
  role_step model roles X t s q a t' s' q' ->
  forall o, waiting_at_cursor t o -> action_occurrence a = o.
Proof.
  intros H. induction H; intros pos Hw; cbn in Hw; try contradiction.
  - destruct Hw as [H _]. exfalso. exact (H eq_refl).
  - exact (proj2 (proj2 Hw)).
  - apply IHrole_step. exact Hw.
  - apply IHrole_step. eapply silent_waiting_at; eassumption.
Qed.

Section Composition.
Context {M E : Type -> Type} {Store : Type}.
Variable model : local_model M E Symbol Store.
Variable roles : list Symbol.

Lemma source_seq_returns p X Y o (t : @cursor M E p X)
    (k : X -> Choreo M p Y) x y :
  returns model t x ->
  returns model (Code (child o BindBody) (k x)) y ->
  returns model (Seq o t k) y.
Proof.
  intros H. induction H; intros Hk.
  - eapply ReturnsSilent; [apply SSeq | exact Hk].
  - eapply ReturnsSilent; [apply SSeqUnder; exact H |].
    exact (IHreturns Hk).
Qed.

Lemma source_fork_returns p X Y (f : @cursor M E p (X -> Y)) t g x :
  returns model f g ->
  returns model t x ->
  returns model (Fork f t) (g x).
Proof.
  intros Hf. induction Hf; intros Ht.
  - induction Ht.
    + eapply ReturnsSilent; [apply SJoin | apply Returns].
    + eapply ReturnsSilent; [apply SForkRight; exact H | exact IHHt].
  - eapply ReturnsSilent; [apply SForkLeft; exact H | exact (IHHf Ht)].
Qed.

Lemma source_seq_step p X Y o (t : @cursor M E p X)
    (k : X -> Choreo M p Y) x s sq a t' s' sq' :
  returns model t x ->
  role_step model roles Y (Code (child o BindBody) (k x))
    s sq a t' s' sq' ->
  role_step model roles Y (Seq o t k) s sq a t' s' sq'.
Proof.
  intros H. induction H; intro Hk.
  - eapply RSilent; [apply SSeq | exact Hk].
  - eapply RSilent; [apply SSeqUnder; exact H | exact (IHreturns Hk)].
Qed.

End Composition.
