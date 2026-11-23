From ParkourTheories Require Import Tests.Protocols.QuorumWellFormedness
  Protocols.QuorumVoting.

Definition quorum_has_frozen_type : quorum_client_contract :=
  QuorumVoting.quorum_well_formed.

Locate Main.quorumVoting.
Print Assumptions QuorumVoting.quorum_well_formed.
