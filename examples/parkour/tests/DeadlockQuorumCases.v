Require Import DeadlockQuorumExpect DeadlockQuorum.

Definition quorum_has_frozen_type : quorum_client_contract :=
  DeadlockQuorum.quorum_well_formed.

Locate Main.quorumVoting.
Print Assumptions DeadlockQuorum.quorum_well_formed.
