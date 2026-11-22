From ITree Require Import ITree.

(* Shared by source Locally and target Exec. Consumers retain their own
   control positions and pass the SAME interpretation and reply relation.
   Store may be a whole shared store; the relation decides which updates a
   role may perform. There is no totality or progress field. *)
#[universes(template)]
Record local_model (M E : Type -> Type) (Role Store : Type) := {
  interpret_local : forall X, M X -> itree E X;
  reply_local : forall X, Role -> E X -> Store -> X -> Store -> Prop
}.

(* Finite bookkeeping only. A Tau layer is never an observable action.
   The terminal layer is checked by each consumer (RetF or VisF). *)
#[universes(template)]
Inductive local_view {E A} :
    itree E A -> itreeF E A (itree E A) -> Prop :=
| ViewNow : forall t v, observe t = v -> local_view t v
| ViewTau : forall t u v,
    observe t = TauF u -> local_view u v -> local_view t v.

Definition local_return {E A} (t : itree E A) (x : A) : Prop :=
  local_view t (RetF x).

(* A dependent trace entry packages the actual event AND its actual reply,
   together with the role and pre/post stores. No serialization is involved. *)
#[universes(template)]
Inductive local_event (E : Type -> Type) (Role Store : Type) : Type :=
| LocalEvent : forall X, Role -> E X -> Store -> X -> Store ->
    local_event E Role Store.
Arguments LocalEvent {E Role Store X} _ _ _ _ _.

#[universes(template)]
Inductive local_step {E Role Store A}
    (reply : forall X, Role -> E X -> Store -> X -> Store -> Prop)
    (p : Role) (t : itree E A) (s : Store) :
    local_event E Role Store -> itree E A -> Store -> Prop :=
| LocalStep : forall X (e : E X) k x s',
    local_view t (VisF e k) ->
    reply X p e s x s' ->
    local_step reply p t s (LocalEvent p e s x s') (k x) s'.

Lemma local_step_typed_trace {E Role Store A}
    (r : forall X, Role -> E X -> Store -> X -> Store -> Prop)
    p (t : itree E A) s a t' s' :
    local_step r p t s a t' s' ->
    exists (X : Type) (e : E X) (x : X) (k : X -> itree E A),
      local_view t (VisF e k) /\
      r X p e s x s' /\
      a = LocalEvent p e s x s' /\ t' = k x.
Proof.
  intros H. destruct H.
  do 4 eexists. repeat split; eassumption || reflexivity.
Qed.
