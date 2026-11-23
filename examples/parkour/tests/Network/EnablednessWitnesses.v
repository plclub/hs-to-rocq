From ParkourTheories Require Import Network.Endpoints Network.Enabledness
  Tests.Network.EnablednessContracts.

Definition role_enabled_exact : role_enabled_contract.
Proof.
  intros M E S m roles p A t q s. split.
  - apply possible_step.
  - intros (a & u & q' & s' & H). eapply step_possible; exact H.
Qed.

Definition network_exact : network_enabled_contract := @network_enabled_exact.
Definition unique_value : returns_unique_contract := @return_unique.
Definition returned_is_silent : returns_no_action_contract.
Proof.
  intros M E S m A t x roles p q s a u q' s' H.
  eapply return_no_action; exact H.
Qed.
