From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Semantics.LocalEffects Semantics.SharedState
  Choreography.Execution Network.Mailboxes Network.Endpoints Network.Execution.
From ParkourTheories.Projection.Matching Require RoleReadiness.
Local Arguments Choreography.Execution.positions {M E Store A} _ _.
Local Arguments Choreography.Execution.deliveries {M E Store A} _.

(* Both the frontier proof and readiness transfer use the same local-input
   condition. It has no dependency on the deadlock-freedom library. *)
Definition inputs_available {M E : Type -> Type} {Store Input : Type}
    (model : local_model M E role (Store * Input)) R A
    (s : @Choreography.Execution.configuration M E ((role -> Store) * Input) A)
    (n : @Network.Execution.configuration M E ((role -> Store) * Input)) :=
  forall p, In p R ->
    exists (t : @control M E (A p))
      (h : CursorAlignment.aligned (shared_model model)
        Choreography.Network.Root
        p (A p) (Choreography.Execution.positions s p) t),
      In (Endpoint (A p) p t) (endpoints n) /\
      RoleReadiness.delivery_available (shared_model model)
        Choreography.Network.Root
        p (A p) (Choreography.Execution.positions s p) t h (mailboxes n)
          (Choreography.Execution.deliveries s).
