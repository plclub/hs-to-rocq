Require DeadlockLibraryExpect DeadlockQuorumFreedomExpect DeadlockMatch.

(* These identities validate the concrete expected types with local binders.
   They prove no preservation or simulation statement and declare no axioms. *)
Module Parametric.
Definition preservation
  (w : forall (M E : Type -> Type) (Store Input : Type)
    (model : DeadlockLocal.local_model M E Parkour.Symbol.Symbol (Store * Input))
    (stores : Parkour.Symbol.Symbol -> Store) (input : Input)
    (R : list Parkour.Symbol.Symbol) (A : Parkour.Symbol.Symbol -> Type)
    (c : forall p, Choreography.Choreo2.Choreo M p (A p)),
    DeadlockLibraryExpect.DeadlockContract.epp_preserves_deadlock_freedom
      M E Store Input model stores input R A c) := w.

Definition correspondence
  (w : forall (M E : Type -> Type) (Store Input : Type)
    (model : DeadlockLocal.local_model M E Parkour.Symbol.Symbol (Store * Input))
    (stores : Parkour.Symbol.Symbol -> Store) (input : Input)
    (R : list Parkour.Symbol.Symbol) (A : Parkour.Symbol.Symbol -> Type)
    (c : forall p, Choreography.Choreo2.Choreo M p (A p)),
    DeadlockLibraryExpect.DeadlockContract.network_run_has_source
      M E Store Input model stores input R A c
      (DeadlockMatch.matches model stores input R A c)) := w.

Definition readiness
  (w : forall (M E : Type -> Type) (Store Input : Type)
    (model : DeadlockLocal.local_model M E Parkour.Symbol.Symbol (Store * Input))
    (stores : Parkour.Symbol.Symbol -> Store) (input : Input)
    (R : list Parkour.Symbol.Symbol) (A : Parkour.Symbol.Symbol -> Type)
    (c : forall p, Choreography.Choreo2.Choreo M p (A p)),
    DeadlockLibraryExpect.DeadlockContract.matched_ready
      M E Store Input model stores input R A c
      (DeadlockMatch.matches model stores input R A c)) := w.

Definition reflection
  (w : forall (M E : Type -> Type) (Store Input : Type)
    (model : DeadlockLocal.local_model M E Parkour.Symbol.Symbol (Store * Input))
    (stores : Parkour.Symbol.Symbol -> Store) (input : Input)
    (R : list Parkour.Symbol.Symbol) (A : Parkour.Symbol.Symbol -> Type)
    (c : forall p, Choreography.Choreo2.Choreo M p (A p)),
    DeadlockLibraryExpect.DeadlockContract.deadlock_reflection
      M E Store Input model stores input R A c
      (DeadlockMatch.matches model stores input R A c)) := w.

Definition client
  (w : DeadlockQuorumFreedomExpect.quorum_deadlock_freedom_expected) := w.
End Parametric.
