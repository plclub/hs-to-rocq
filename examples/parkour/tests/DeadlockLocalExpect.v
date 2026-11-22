From ITree Require Import ITree.
Require Import DeadlockLocal.

(* Frozen inputs and propositions. Proof bodies belong in DeadlockLocalCases.v. *)
Inductive request : Type -> Type := Get : request bool.

Definition reply (X : Type) (p : nat) (e : request X)
    (s : nat) (x : X) (s' : nat) : Prop :=
  match e in request Y return Y -> Prop with
  | Get => fun b => p = 7 /\ s = 3 /\ b = true /\ s' = 4
  end x.

Fixpoint ticks {A : Type} (n : nat) (t : itree request A) :
    itree request A :=
  match n with O => t | S k => Tau (ticks k t) end.

Definition ask : itree request nat :=
  Vis Get (fun b : bool => Ret (if b then 11 else 22)).
Definition twice : itree request nat :=
  Vis Get (fun _ => ask).
CoFixpoint forever : itree request nat := Tau forever.

Definition finite_return_contract : Prop :=
  forall n, local_return (ticks n (Ret 19)) 19.
Definition finite_action_contract : Prop :=
  forall n, local_step reply 7 (ticks n ask) 3
    (LocalEvent 7 Get 3 true 4) (Ret 11) 4.
Definition one_event_contract : Prop :=
  local_step reply 7 twice 3 (LocalEvent 7 Get 3 true 4) ask 4.
Definition blocked_store_contract : Prop :=
  forall n a t s, ~ local_step reply 7 (ticks n ask) 0 a t s.
Definition blocked_role_contract : Prop :=
  forall n a t s, ~ local_step reply 8 (ticks n ask) 3 a t s.
Definition no_invented_reply_contract : Prop :=
  ~ local_step reply 7 ask 3 (LocalEvent 7 Get 3 false 4) (Ret 22) 4.
Definition visible_not_return_contract : Prop :=
  forall n x, ~ local_return (ticks n ask) x.
Definition return_not_action_contract : Prop :=
  forall n a t s, ~ local_step reply 7 (ticks n (Ret 19)) 3 a t s.
Definition infinite_not_return_contract : Prop :=
  forall x, ~ local_return forever x.
Definition infinite_not_action_contract : Prop :=
  forall a t s, ~ local_step reply 7 forever 3 a t s.

(* This existential retains the real dependent event and its typed reply.
   It is not a string tag or an untyped outcome chosen by an observer. *)
Definition typed_trace_contract : Prop :=
  forall (E : Type -> Type) (Role Store A : Type)
    (r : forall X, Role -> E X -> Store -> X -> Store -> Prop)
    p (t : itree E A) s a t' s',
    local_step r p t s a t' s' ->
    exists (X : Type) (e : E X) (x : X) (k : X -> itree E A),
      local_view t (VisF e k) /\
      r X p e s x s' /\
      a = LocalEvent p e s x s' /\ t' = k x.

(* An independent declarative closure: exactly finitely many Tau observations
   followed by the specified observable layer. No coinductive/fuel closure. *)
#[universes(template)]
Inductive expected_view {E A} :
    itree E A -> itreeF E A (itree E A) -> Prop :=
| ExpectedNow : forall t v, observe t = v -> expected_view t v
| ExpectedTau : forall t u v,
    observe t = TauF u -> expected_view u v -> expected_view t v.
Definition view_exact_contract : Prop :=
  forall (E : Type -> Type) (A : Type) (t : itree E A) v,
    local_view t v <-> expected_view t v.
