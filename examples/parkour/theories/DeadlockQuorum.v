From Stdlib Require Import Lists.List Strings.String.
Require Import Main DeadlockWellFormed.
Require DeadlockFreedom DeadlockState DeadlockSource DeadlockNetwork DeadlockMatch.
Require Import Choreography.Choreo2 Control.Monad.Tree Parkour.Codec Parkour.Symbol.
Import ListNotations.

Definition quorum_roles : list Symbol :=
  [GHC.Base.hs_string__ "candidate";
   GHC.Base.hs_string__ "voter1";
   GHC.Base.hs_string__ "voter2";
   GHC.Base.hs_string__ "voter3"].

Lemma bool_wire : wire_law show_bool read_bool.
Proof.
  intros []; reflexivity.
Qed.

Ltac quorum_structure :=
  first
  [ eapply WFPure; intros; reflexivity
  | eapply WFLocally;
      [ | intros; reflexivity ];
      unfold quorum_roles; cbn [In]; auto
  | eapply WFComm;
      [ | | | intros; reflexivity ];
      try (solve [unfold quorum_roles; cbn [In]; auto]); intros; apply bool_wire
  | eapply WFApp;
      [ | | intros; reflexivity ];
      quorum_structure
  | eapply WFBind;
      [ | | intros; reflexivity ];
      [ quorum_structure | intros; quorum_structure ] ].

Theorem quorum_well_formed :
  well_formed quorum_roles Parkour.Runtime.IO
    (fun _ : Symbol => unit) (@Main.quorumVoting).
Proof.
  split.
  - unfold quorum_roles.
    repeat first [apply NoDup_cons | apply NoDup_nil];
      vm_compute; intuition discriminate.
  - eexists.
    cbn [Main.quorumVoting Choreography.Choreo2.locally
      Choreography.Choreo2.op_z7eUz7eUzg__
      Choreography.Choreo2.op_z7eUzg__
      Control.Monad.Tree.par Data.Functor.void
      GHC.Base.op_zgzgze__ GHC.Base.op_zgzg__
      GHC.Base.op_zlztzg__ GHC.Base.fmap GHC.Base.op_zlzd__].
    quorum_structure.
Qed.

(* Local effects may block. The corollary transfers source deadlock freedom;
   it does not assume that STM, or any other local effect, is total. *)
Theorem quorum_deadlock_freedom :
  forall (E : Type -> Type) (Store Input : Type)
    (model : DeadlockLocal.local_model Parkour.Runtime.IO E Symbol (Store * Input))
    (stores : Symbol -> Store) (input : Input),
  (forall tc s,
    DeadlockSource.crun (DeadlockState.shared_model model) quorum_roles
      (DeadlockSource.initial (@Main.quorumVoting) (stores, input)) tc s ->
    DeadlockSource.cfinal (DeadlockState.shared_model model) quorum_roles s \/
      exists a s',
        DeadlockSource.cstep (DeadlockState.shared_model model) quorum_roles s a s') ->
  forall tn n,
    DeadlockNetwork.run (DeadlockState.shared_model model) quorum_roles
      (@DeadlockMatch.network_initial Parkour.Runtime.IO E Store Input
        stores input quorum_roles (fun _ => unit) (@Main.quorumVoting)) tn n ->
    DeadlockNetwork.nfinal (DeadlockState.shared_model model) n \/
      exists b n',
        DeadlockNetwork.nstep (DeadlockState.shared_model model) quorum_roles n b n'.
Proof.
  intros E Store Input model stores input.
  exact (DeadlockFreedom.epp_preserves_deadlock_freedom
    model stores input quorum_roles (fun _ => unit) (@Main.quorumVoting)
    quorum_well_formed).
Qed.

Print Assumptions quorum_deadlock_freedom.
