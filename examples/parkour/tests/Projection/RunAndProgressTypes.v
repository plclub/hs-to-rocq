From ParkourTheories Require Tests.Projection.RunCorrespondenceTypes
  Tests.Protocols.QuorumProgress Projection.Matching.PrefixRelation.
From ParkourTheories Require Projection.RunCorrespondence Projection.Progress
  Protocols.QuorumVoting.

(* Permanent independent acceptance gate. The expected propositions were
   frozen before the library proofs. These are direct references to all real
   exports, not declarations conditional on their existence. Missing modules
   or exports MUST fail compilation. No implementation statement is inferred. *)
Definition epp_preserves_deadlock_freedom :
  forall (M E : Type -> Type) (Store Input : Type)
    (model : LocalEffects.local_model M E Parkour.Symbol.Symbol (Store *
      Input))
    (stores : Parkour.Symbol.Symbol -> Store) (input : Input)
    (R : list Parkour.Symbol.Symbol) (A : Parkour.Symbol.Symbol -> Type)
    (c : forall p, Choreography.Choreo2.Choreo M p (A p)),
  RunCorrespondenceTypes.RunAndProgressTypes.epp_preserves_deadlock_freedom
    M E Store Input model stores input R A c :=
  @Progress.epp_preserves_deadlock_freedom.

Definition network_run_has_source :
  forall (M E : Type -> Type) (Store Input : Type)
    (model : LocalEffects.local_model M E Parkour.Symbol.Symbol (Store *
      Input))
    (stores : Parkour.Symbol.Symbol -> Store) (input : Input)
    (R : list Parkour.Symbol.Symbol) (A : Parkour.Symbol.Symbol -> Type)
    (c : forall p, Choreography.Choreo2.Choreo M p (A p)),
  RunCorrespondenceTypes.RunAndProgressTypes.network_run_has_source
    M E Store Input model stores input R A c
    (PrefixRelation.matches model stores input R A c) :=
  @RunCorrespondence.network_run_has_source.

Definition matched_ready :
  forall (M E : Type -> Type) (Store Input : Type)
    (model : LocalEffects.local_model M E Parkour.Symbol.Symbol (Store *
      Input))
    (stores : Parkour.Symbol.Symbol -> Store) (input : Input)
    (R : list Parkour.Symbol.Symbol) (A : Parkour.Symbol.Symbol -> Type)
    (c : forall p, Choreography.Choreo2.Choreo M p (A p)),
  RunCorrespondenceTypes.RunAndProgressTypes.matched_ready
    M E Store Input model stores input R A c
    (PrefixRelation.matches model stores input R A c) :=
  @Progress.matched_ready.

Definition deadlock_reflection :
  forall (M E : Type -> Type) (Store Input : Type)
    (model : LocalEffects.local_model M E Parkour.Symbol.Symbol (Store *
      Input))
    (stores : Parkour.Symbol.Symbol -> Store) (input : Input)
    (R : list Parkour.Symbol.Symbol) (A : Parkour.Symbol.Symbol -> Type)
    (c : forall p, Choreography.Choreo2.Choreo M p (A p)),
  RunCorrespondenceTypes.RunAndProgressTypes.deadlock_reflection
    M E Store Input model stores input R A c
    (PrefixRelation.matches model stores input R A c) :=
  @Progress.deadlock_reflection.

Definition quorum_deadlock_freedom :
  QuorumProgress.quorum_deadlock_freedom_expected :=
  @QuorumVoting.quorum_deadlock_freedom.
