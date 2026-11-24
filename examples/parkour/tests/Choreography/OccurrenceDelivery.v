From Stdlib Require Import Lists.List.
From Stdlib Require NArith.BinNat.
From ITree Require Import ITree.
Require Import Parkour.Symbol Control.Monad.Tree.
From ParkourTheories Require Import Semantics.Runs
  Choreography.PendingDeliveries Choreography.RoleSteps Choreography.Execution
  Tests.Choreography.CommunicationOrder.
Require Choreography.Choreo2.
From ParkourTheories.Choreography Require WellFormedness.
Import ListNotations.
Import Choreography.Choreo2 (At).

(* New acceptance inputs; existing source/FIFO expectations remain untouched. *)
Definition result_family p := At bool B p.
Definition good_family p : Choreography.Choreo2.Choreo (itree request) p
  (result_family p) :=
  Bind (comm p A B (located true)) (fun _ => comm p A B (located false)).
Definition bad_family p : Choreography.Choreo2.Choreo (itree request) p
  (result_family p) :=
  if List.list_eq_dec BinNat.N.eq_dec p A then good_family p else
    Bind (comm p A A (located true)) (fun _ => comm p A B (located false)).

Lemma B_not_A : B <> A.
Proof. discriminate. Qed.

Definition replace_A {T : Symbol -> Type} (v : T A) (old : forall p, T p) p : T
  p :=
  match List.list_eq_dec BinNat.N.eq_dec A p with
  | left e => eq_rect A T v p e
  | right _ => old p
  end.
Definition state_type := @configuration (itree request) request nat
  result_family.
Definition start (c : forall p, Choreography.Choreo2.Choreo
    (itree request) p (result_family p)) : state_type := initial c 0.
Definition sent_once (c : forall p, Choreography.Choreo2.Choreo
    (itree request) p (result_family p)) : state_type :=
  {| positions := replace_A
       (Seq [] (Returned (off_at (X := bool) B_not_A))
         (fun _ => comm A A B (located false))) (positions _ (start c));
     shared_store := 0;
     deliveries := [Pending bool DataDelivery first_path A B true] |}.
Definition sent_twice (c : forall p, Choreography.Choreo2.Choreo
    (itree request) p (result_family p)) : state_type :=
  {| positions := replace_A (Returned (off_at (X := bool) B_not_A))
       (positions _ (start c));
     shared_store := 0;
     deliveries := two_pending |}.

Definition send_true : @source_action request nat := SendAction bool first_path
  A B true.
Definition send_false : @source_action request nat := SendAction bool
  second_path A B false.
Definition receive_true : @source_action request nat := ReceiveAction bool
  first_path A B true.
Definition receive_false : @source_action request nat := ReceiveAction bool
  second_path A B false.

Definition occurrence_exact_contract : Prop :=
  forall X k o s d (x : X) q q',
    take_at_occurrence k o s d x q q' <->
    exists front back,
      q = front ++ Pending X k o s d x :: back /\ q' = front ++ back.
Definition old_take_inclusion_contract : Prop :=
  forall X k o s d (x : X) q q',
    take_first_on_source_channel k o s d x q q' -> take_at_occurrence k o s d x
      q q'.
Definition delayed_wf_contract : Prop :=
  WellFormedness.well_formed roles (itree request) result_family good_family.
Definition delayed_run_contract : Prop :=
  Choreography.Execution.run model roles (start good_family) [send_true;
    send_false]
    (sent_twice good_family).
Definition delayed_second_negative_contract : Prop :=
  forall c', ~ Choreography.Execution.step model roles (sent_twice good_family)
    receive_false c'.
Definition delayed_first_positive_contract : Prop :=
  exists c', Choreography.Execution.step model roles (sent_twice good_family)
    receive_true
    c' /\
    deliveries _ c' = [Pending bool DataDelivery second_path A B false].

(* The discrepancy control is reachable but structurally incoherent. Its
   second receive must not be suppressed by an unrelated earlier occurrence. *)
Definition discrepancy_not_wf_contract : Prop :=
  ~ WellFormedness.well_formed roles (itree request) result_family bad_family.
Definition discrepancy_run_contract : Prop :=
  Choreography.Execution.run model roles (start bad_family) [send_true;
    send_false]
    (sent_twice bad_family).
Definition discrepancy_receive_contract : Prop :=
  exists c', Choreography.Execution.step model roles (sent_twice bad_family)
    receive_false
    c' /\
    deliveries _ c' = [Pending bool DataDelivery first_path A B true].
Definition discrepancy_old_rejects_contract : Prop :=
  forall q', ~ take_first_on_source_channel DataDelivery second_path A B false
    two_pending q'.
