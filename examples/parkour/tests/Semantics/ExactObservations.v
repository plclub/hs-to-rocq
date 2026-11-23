From ITree Require Import ITree.
From ParkourTheories Require Import Semantics.LocalEffects
  Tests.Semantics.LocalEffectContracts.

(* Additive generic contracts: no existing expectation changes. *)
Definition return_exact_contract : Prop :=
  forall (E : Type -> Type) (A : Type) (t : itree E A) x,
    local_return t x <-> expected_view t (RetF x).

Definition step_exact_contract : Prop :=
  forall (E : Type -> Type) (Role Store A : Type)
    (r : forall X, Role -> E X -> Store -> X -> Store -> Prop)
    p (t : itree E A) s a t' s',
    local_step r p t s a t' s' <->
    exists (X : Type) (e : E X) (x : X) (k : X -> itree E A),
      expected_view t (VisF e k) /\
      r X p e s x s' /\
      a = LocalEvent p e s x s' /\ t' = k x.
