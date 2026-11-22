From Stdlib Require Import Lists.List.
Require Import DeadlockMatch DeadlockLibraryExpect DeadlockSource DeadlockNetwork
  DeadlockMessages DeadlockOrder DeadlockLocal DeadlockProjectionExpect Parkour.Codec.
Import ListNotations.

(* Separate closure and interface checks. No network-run correspondence or
   matched-ready theorem is assumed or claimed by these tests. *)
Section Interface.
Context {M E : Type -> Type} {Store Input : Type}.
Variable model : local_model M E role (Store * Input).
Variable stores : role -> Store.
Variable input : Input.
Variable R : list role.
Variable A : role -> Type.
Variable c : forall p, Choreography.Choreo2.Choreo M p (A p).

Definition actual_interface :
    DeadlockContract.matches_interface M E Store Input A :=
  DeadlockMatch.matches model stores input R A c.

Example literal_initial :
  actual_interface []
    (DeadlockContract.source_initial M E Store Input stores input A c) []
    (DeadlockContract.network_initial M E Store Input stores input R A c).
Proof. apply initial_matches. Qed.

Example inserted_target_event_rejected na :
  ~ actual_interface [] (DeadlockMatch.source_initial stores input A c)
      [na] (DeadlockMatch.network_initial stores input R A c).
Proof. apply unequal_lengths_do_not_match. discriminate. Qed.
End Interface.

Definition sender : role := [].
Definition receiver : role := [BinNums.N0].

Example concrete_delivery :
  delivery bool DataDelivery [BindPrefix] sender receiver true read_bool
    [Message bool DataDelivery [BindPrefix] sender receiver true show_bool]
    (@show bool show_bool true) [].
Proof. apply delivery_singleton. reflexivity. Qed.

Example no_fabricated_delivery :
  ~ delivery bool DataDelivery [] sender receiver true read_bool
      [] (@show bool show_bool true) [].
Proof. apply delivery_empty_impossible. Qed.

Example opposite_kind_cannot_jump :
  ~ delivery bool DataDelivery [] sender receiver false read_bool
      [Message bool ChoiceDelivery [] sender receiver true show_bool;
       Message bool DataDelivery [] sender receiver false show_bool]
      (@show bool show_bool false)
      [Message bool ChoiceDelivery [] sender receiver true show_bool].
Proof.
  intro H. apply delivery_fifo in H. vm_compute in H. discriminate.
Qed.

Example app_branch_cannot_alias :
  session_at [AppFunction] Choreography.Network.Root <>
  session_at [AppArgument] Choreography.Network.Root.
Proof. discriminate. Qed.

Print Assumptions initial_matches.
Print Assumptions prefix_source_run.
Print Assumptions prefix_network_run.
Print Assumptions prefix_action_order.
Print Assumptions terminal_queues.
Print Assumptions opposite_kind_cannot_jump.
