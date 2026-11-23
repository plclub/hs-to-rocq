From Stdlib Require Import Lists.List Strings.String.
From ParkourTheories Require Import Tests.FIFO.ScheduledTraceContracts
  Choreography.Occurrences Choreography.RoleSteps Network.Endpoints
  Projection.Matching.PrefixRelation.
Import ListNotations.

(* The owner announced "True". The bool the peer claims to hear is observable
   here through the actual received bytes; the packet addressed to C cannot
   supply a "False" packet to B. *)
Definition wire_reject_invented_bytes : Prop :=
  forall s n,
    ~ PrefixRelation.matches wire_model wire_stores tt wire_roles
      (fun _ => bool) wire_choice
      [AnnounceAction bool [] wire_A true;
       SendAction bool [ChoiceBody; BindPrefix] wire_A wire_C false;
       HearAction bool [] wire_A wire_B false] s
      [Announced wire_A Choreography.Network.Root (GHC.Base.hs_string__ "True");
       Sent wire_A wire_C Choreography.Network.Root (GHC.Base.hs_string__
         "False");
       Received wire_A wire_B Choreography.Network.Root (GHC.Base.hs_string__
         "False")] n.
