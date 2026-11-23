From ITree Require Import ITree.
From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Network.Mailboxes Network.Endpoints
  Network.Execution Tests.Network.CommunicationRules
  Tests.Network.SharedStoreScheduling.
Import ListNotations.

Definition silent_join : prog nat :=
  CBind (CApp (pure (fun n : nat => S n)) (pure 4)) (fun n => pure (S n)).
Definition bookkeeping_contract : Prop :=
  done silent_join 6 /\ blocked alice silent_join empty_queues false.
Definition after_bookkeeping_contract : Prop :=
  can alice (CBind silent_join (fun _ => send true)) empty_queues false
    (sent true) (pure tt)
    (enqueue empty_queues (alice,bob,Choreography.Network.Root)
      (@Parkour.Codec.show bool Parkour.Codec.show_bool true)) false.
Definition wait_blocked_contract : Prop :=
  blocked alice wait_code empty_queues false.
Definition empty_receivers : net :=
  {| endpoints :=
       [@Endpoint (itree flag_event) flag_event bool alice recv;
        @Endpoint (itree flag_event) flag_event bool bob recv];
     mailboxes := empty_queues; shared_store := false |}.
Definition empty_endpoints_contract : Prop :=
  ~ Network.Execution.final flag_model empty_receivers /\
  forall a n', ~ Network.Execution.step flag_model roles empty_receivers a n'.
Definition finished : net :=
  {| endpoints :=
       [@Endpoint (itree flag_event) flag_event nat alice silent_join];
     mailboxes := empty_queues; shared_store := false |}.
Definition finished_contract : Prop := Network.Execution.final flag_model
  finished.
