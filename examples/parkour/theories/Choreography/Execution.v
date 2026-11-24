From Stdlib Require Import Lists.List.
Require Import Parkour.Symbol.
From ParkourTheories Require Import Semantics.LocalEffects Semantics.Runs
  Choreography.PendingDeliveries Choreography.RoleSteps.
Require Choreography.Choreo2.
Import Choreography.Choreo2 (Choreo).
Import ListNotations.

Section Source.
Context {M E : Type -> Type} {Store : Type}.
Variable model : local_model M E Symbol Store.
Variable roles : list Symbol.

#[universes(template)]
Record configuration (A : Symbol -> Type) := Config {
  positions : forall p, @cursor M E p (A p);
  shared_store : Store;
  deliveries : list pending
}.
Arguments positions {A} _ _.
Arguments shared_store {A} _.
Arguments deliveries {A} _.

Definition initial {A} (c : forall p, Choreo M p (A p))
    (s : Store) : configuration A :=
  {| positions := fun p => Code [] (c p); shared_store := s; deliveries := []
    |}.

#[universes(template)]
Inductive step {A} (c : configuration A) :
    (@source_action E Store) -> configuration A -> Prop :=
| CStep p a c' :
    In p roles ->
    role_step model roles (A p)
      (positions c p) (shared_store c) (deliveries c) a
      (positions c' p) (shared_store c') (deliveries c') ->
    (forall r, r <> p -> positions c r = positions c' r) ->
    step c a c'.

Definition final {A} (c : configuration A) : Prop :=
  deliveries c = [] /\ forall p, In p roles ->
    exists x, returns model (positions c p) x.

Definition run {A} :=
  @finite_run (configuration A) (@source_action E Store) (@step A).
End Source.
