From ITree Require Import ITree.
From Stdlib Require Import Lists.List.
Require Import Choreography.Network Control.Monad.Tree Parkour.Codec.
From ParkourTheories.Semantics Require Import LocalEffects.
Import ListNotations.

From ParkourTheories.Network Require Import Mailboxes.

(* Syntax is generated Tree/NetworkSig. Only suspended Exec needs a new node.
   The other nodes retain fork/join and value-dependent continuation structure.
   *)
Section Machine.
Context {M E : Type -> Type} {Store : Type}.
Variable model : local_model M E role Store.
Variable participants : list role.

Inductive control : Type -> Type :=
| CPure : forall A, A -> control A
| CPerf : forall A, NetworkSig M A -> control A
| CBind : forall A B, control A -> (A -> control B) -> control B
| CApp : forall A B, control (A -> B) -> control A -> control B
| CLocal : forall A, itree E A -> control A.
Arguments CPure {A} _.
Arguments CPerf {A} _.
Arguments CBind {A B} _ _.
Arguments CApp {A B} _ _.
Arguments CLocal {A} _.

Fixpoint load {A} (t : Network M A) : control A :=
  match t with
  | Pure x => CPure x
  | Perf e => CPerf e
  | Bind t k => CBind (load t) (fun x => load (k x))
  | App f x => CApp (load f) (load x)
  end.

(* Finite silent evaluation, never an action and never a fuel cutoff. *)
Inductive returns : forall A, control A -> A -> Prop :=
| ReturnPure : forall A (x : A), returns A (CPure x) x
| ReturnExec : forall A (e : M A) x,
    local_return (interpret_local _ _ _ _ model A e) x ->
    returns A (CPerf (Exec e)) x
| ReturnLocal : forall A (t : itree E A) x,
    local_return t x -> returns A (CLocal t) x
| ReturnBind : forall A B (t : control A) (k : A -> control B) x y,
    returns A t x -> returns B (k x) y -> returns B (CBind t k) y
| ReturnApp : forall A B (f : control (A -> B)) (t : control A) g x,
    returns (A -> B) f g -> returns A t x -> returns B (CApp f t) (g x).

Inductive action : Type :=
| Sent : role -> role -> SessionId -> wire -> action
| Received : role -> role -> SessionId -> wire -> action
| Announced : role -> SessionId -> wire -> action
| Local : local_event E role Store -> action.

Inductive step (p : role) :
    forall A, control A -> queues -> Store -> action ->
      control A -> queues -> Store -> Prop :=
| StepSend : forall A (sh : Show A) sid (x : A) r q s,
    step p unit (CPerf (@Send M A sh sid x r)) q s
      (Sent p r sid (@show A sh x)) (CPure tt)
      (enqueue q (p,r,sid) (@show A sh x)) s
| StepRecv : forall A (rd : Read A) sid sender q s w ws x,
    q (sender,p,sid) = w :: ws ->
    @read A rd w = Some x ->
    step p A (CPerf (@Recv M A rd sid sender)) q s
      (Received sender p sid w) (CPure x)
      (replace_queue q (sender,p,sid) ws) s
| StepBCast : forall A (sh : Show A) sid (x : A) q s,
    step p unit (CPerf (@BCast M A sh sid x)) q s
      (Announced p sid (@show A sh x)) (CPure tt)
      (announce participants p sid (@show A sh x) q) s
| StepExec : forall A (e : M A) q s a t s',
    local_step (reply_local _ _ _ _ model) p
      (interpret_local _ _ _ _ model A e) s a t s' ->
    step p A (CPerf (Exec e)) q s (Local a) (CLocal t) q s'
| StepLocal : forall A (t : itree E A) q s a t' s',
    local_step (reply_local _ _ _ _ model) p t s a t' s' ->
    step p A (CLocal t) q s (Local a) (CLocal t') q s'
| StepBind : forall A B (t t' : control A) (k : A -> control B) q s a q' s',
    step p A t q s a t' q' s' ->
    step p B (CBind t k) q s a (CBind t' k) q' s'
| StepContinue : forall A B (t : control A) (k : A -> control B) x
    q s a u q' s',
    returns A t x -> step p B (k x) q s a u q' s' ->
    step p B (CBind t k) q s a u q' s'
| StepLeft : forall A B (f f' : control (A -> B)) (x : control A)
    q s a q' s',
    step p (A -> B) f q s a f' q' s' ->
    step p B (CApp f x) q s a (CApp f' x) q' s'
| StepRight : forall A B (f : control (A -> B)) (x x' : control A)
    q s a q' s',
    step p A x q s a x' q' s' ->
    step p B (CApp f x) q s a (CApp f x') q' s'.

(* Necessary conditions used for negative scheduling tests. They do not
   define the operational relation, and grant no step by themselves. *)
Fixpoint return_shape {A} (t : control A) : Prop :=
  match t with
  | CPure _ => True
  | CPerf e =>
      match e with
      | Exec e => exists x, local_return (interpret_local _ _ _ _ model _ e) x
      | _ => False
      end
  | CLocal t => exists x, local_return t x
  | CBind u _ => return_shape u
  | CApp f x => return_shape f /\ return_shape x
  end.

Lemma returns_shape A (t : control A) x :
  returns A t x -> return_shape t.
Proof. intros H. induction H; cbn; eauto. Qed.

Fixpoint possible {A} (p : role) (t : control A) (q : queues) (s : Store) : Prop
  :=
  match t with
  | CPure _ => False
  | CPerf e =>
      match e with
      | @Recv _ X rd sid sender =>
          exists w ws (x : X),
            q (sender,p,sid) = w :: ws /\ @read X rd w = Some x
      | Exec e => exists a t' s',
          local_step (reply_local _ _ _ _ model) p
            (interpret_local _ _ _ _ model _ e) s a t' s'
      | _ => True
      end
  | CLocal t => exists a t' s',
      local_step (reply_local _ _ _ _ model) p t s a t' s'
  | CBind u k =>
      possible p u q s \/ exists x, returns _ u x /\ possible p (k x) q s
  | CApp f x => possible p f q s \/ possible p x q s
  end.

Lemma step_possible p A (t u : control A) q s a q' s' :
  step p A t q s a u q' s' -> possible p t q s.
Proof. intros H. induction H; cbn; eauto 8. Qed.

Inductive endpoint : Type :=
| Endpoint : forall A, role -> control A -> endpoint.

Definition endpoint_final (e : endpoint) : Prop :=
  match e with Endpoint A _ t => exists x, returns A t x end.

Definition endpoint_possible (q : queues) (s : Store) (e : endpoint) : Prop :=
  match e with Endpoint _ p t => possible p t q s end.

Fixpoint endpoints_possible (q : queues) (s : Store) (es : list endpoint) : Prop
  :=
  match es with
  | [] => False
  | e :: rest => endpoint_possible q s e \/ endpoints_possible q s rest
  end.

End Machine.

Arguments CPure {M E A} _.
Arguments CPerf {M E A} _.
Arguments CBind {M E A B} _ _.
Arguments CApp {M E A B} _ _.
Arguments CLocal {M E A} _.
Arguments load {M E A} _.
