From ITree Require Import ITree.
From Stdlib Require Import Lists.List.
Require Import Control.Monad.Tree Choreography.Network Parkour.Codec
  Data.Either.
From ParkourTheories Require Import Network.Mailboxes Network.Endpoints
  Network.Execution Tests.Network.CommunicationRules.
Import ListNotations.

Definition twosends : prog unit :=
  CApp (CBind (send true) (fun _ => pure (fun _ : unit => tt))) (send false).
Definition both_sends_contract : Prop :=
  (exists u, can alice twosends empty_queues false (sent true) u
    (enqueue empty_queues (alice,bob,Root) (@show bool show_bool true)) false)
      /\
  (exists u, can alice twosends empty_queues false (sent false) u
    (enqueue empty_queues (alice,bob,Root) (@show bool show_bool false)) false).

Definition wrong_session_contract : Prop :=
  blocked bob
    (load (Perf (@Recv (itree flag_event) bool read_bool
      (Nest (Left tt) Root) alice)))
    (enqueue empty_queues (alice,bob,Root) (@show bool show_bool true)) false.
Definition wrong_sender_contract : Prop :=
  blocked bob recv
    (enqueue empty_queues (carol,bob,Root) (@show bool show_bool true)) false.
Definition wrong_receiver_contract : Prop :=
  blocked bob recv
    (enqueue empty_queues (alice,carol,Root) (@show bool show_bool true)) false.
Definition bad_head_contract : Prop :=
  blocked bob recv
    (replace_queue empty_queues (alice,bob,Root)
      [[]; @show bool show_bool true]) false.

Definition announcement_contract : Prop :=
  can alice (load (Perf (@BCast (itree flag_event) bool show_bool Root true)))
    empty_queues false
    (@Announced flag_event bool alice Root (@show bool show_bool true))
    (pure tt)
    (announce [alice; bob; carol] alice Root (@show bool show_bool true)
      empty_queues)
    false /\
  let q := announce [alice; bob; carol] alice Root
    (@show bool show_bool true) empty_queues in
  q (alice,bob,Root) = [@show bool show_bool true] /\
  q (alice,carol,Root) = [@show bool show_bool true] /\
  q (alice,alice,Root) = [].
Definition singleton_announcement_contract : Prop :=
  forall k, announce [alice] alice Root (@show bool show_bool true) empty_queues
    k = [].

Definition net := @configuration (itree flag_event) flag_event bool.
Definition orphan : net :=
  {| endpoints := [@Endpoint (itree flag_event) flag_event unit alice (pure
    tt)];
     mailboxes := enqueue empty_queues (alice,bob,Root) (@show bool show_bool
       true);
     shared_store := false |}.
Definition orphan_contract : Prop :=
  ~ Network.Execution.final flag_model orphan /\
  forall a n', ~ Network.Execution.step flag_model roles orphan a n'.

Definition two_roles : net :=
  {| endpoints :=
       [@Endpoint (itree flag_event) flag_event unit alice (send true);
        @Endpoint (itree flag_event) flag_event unit carol (send false)];
     mailboxes := empty_queues; shared_store := false |}.
Definition two_roles_contract : Prop :=
  (exists n', Network.Execution.step flag_model roles two_roles (sent true) n')
    /\
  (exists n', Network.Execution.step flag_model roles two_roles
    (@Sent flag_event bool carol bob Root (@show bool show_bool false)) n').

CoFixpoint spin : itree flag_event unit := Tau spin.
Definition spin_contract : Prop :=
  blocked alice (CLocal spin) empty_queues false /\
  forall x, ~ done (CLocal spin) x.
Definition local_return_contract : Prop :=
  done (CLocal (Tau (Ret tt))) tt /\
  blocked alice (CLocal (Tau (Ret tt))) empty_queues false.
Definition two_events : itree flag_event unit :=
  Vis SetFlag (fun _ => wait).
Definition one_event_only_contract : Prop :=
  can alice (load (Perf (Exec two_events))) empty_queues false (local_set false)
    (CLocal wait) empty_queues true /\
  (forall x, ~ done (CLocal wait) x) /\
  can alice (CLocal wait) empty_queues true local_wait
    (CLocal (Ret tt)) empty_queues true.
