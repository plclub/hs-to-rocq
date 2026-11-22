From Stdlib Require Import Lists.List Strings.String.
Require Import Main DeadlockWellFormed Parkour.Runtime Parkour.Symbol.
Import ListNotations.

(* Freeze the concrete client before attempting its proof. This is the actual
   generated family and its actual runtime, not an abstract replacement. *)
Definition quorum_client_contract : Prop :=
  DeadlockWellFormed.well_formed
    [GHC.Base.hs_string__ "candidate";
     GHC.Base.hs_string__ "voter1";
     GHC.Base.hs_string__ "voter2";
     GHC.Base.hs_string__ "voter3"]
    Parkour.Runtime.IO (fun _ : Symbol => unit) (@Main.quorumVoting).

Check (@Main.quorumVoting) :
  forall p : Symbol, Choreography.Choreo2.Choreo Parkour.Runtime.IO p unit.
