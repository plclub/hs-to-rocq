From Stdlib Require Import Lists.List.
Require Import DeadlockLocal DeadlockState DeadlockSource DeadlockNetwork.
Require DeadlockAlignmentProgress.
Local Arguments DeadlockSource.positions {M E Store A} _ _.
Local Arguments DeadlockSource.deliveries {M E Store A} _.

(* Both the frontier proof and readiness transfer use the same local-input
   condition. It has no dependency on the deadlock-freedom library. *)
Definition inputs_available {M E : Type -> Type} {Store Input : Type}
    (model : local_model M E role (Store * Input)) R A
    (s : @DeadlockSource.configuration M E ((role -> Store) * Input) A)
    (n : @DeadlockNetwork.configuration M E ((role -> Store) * Input)) :=
  forall p, In p R ->
    exists (t : @control M E (A p))
      (h : DeadlockAlignment.aligned (shared_model model)
        Choreography.Network.Root
        p (A p) (DeadlockSource.positions s p) t),
      In (Endpoint (A p) p t) (endpoints n) /\
      DeadlockAlignmentProgress.delivery_available (shared_model model)
        Choreography.Network.Root
        p (A p) (DeadlockSource.positions s p) t h (mailboxes n)
          (DeadlockSource.deliveries s).
