From Stdlib Require Import Lists.List.
From Stdlib Require Strings.String NArith.BinNat.
Import String.
From ParkourTheories Require Import Projection.FIFO.MessageRepresentation
  Choreography.Occurrences Choreography.PendingDeliveries Network.Mailboxes.
Require Import Choreography.Network Parkour.Codec.
Import ListNotations.
Local Open Scope string_scope.

(* Literal expectations do not call at_key to compute their expected queues. *)
Definition a : role := [].
Definition b : role := [BinNums.N0].
Definition c : role := [BinNums.Npos BinNums.xH].
Definition root_key : key := (a,b,Root).
Definition first : message :=
  Message bool DataDelivery [BindPrefix] a b true show_bool.
Definition second : message :=
  Message bool DataDelivery [BindBody] a b false show_bool.
Definition choice : message :=
  Message bool ChoiceDelivery [] a b true show_bool.
Definition two_wires : queues :=
  enqueue (enqueue empty_queues root_key (GHC.Base.hs_string__ "True"))
    root_key (GHC.Base.hs_string__ "False").

Example literal_empty : represents [] empty_queues [].
Proof. apply represents_empty. Qed.

Example literal_app_session :
  message_key (Message unit DataDelivery
    [BindPrefix; AppFunction; ChoiceBody; AppArgument; BindBody] a b tt
      show_unit) =
  (a,b,Nest (Data.Either.Right tt) (Nest (Data.Either.Left tt) Root)).
Proof. reflexivity. Qed.

Example repeated_root_keys :
  message_key first = root_key /\ message_key second = root_key.
Proof. split; reflexivity. Qed.

Example repeated_root_queue :
  two_wires root_key =
    [GHC.Base.hs_string__ "True"; GHC.Base.hs_string__ "False"].
Proof. vm_compute. reflexivity. Qed.

Example repeated_root_invariant :
  represents
    [Pending bool DataDelivery [BindPrefix] a b true;
     Pending bool DataDelivery [BindBody] a b false]
    two_wires [first;second].
Proof.
  exact (represents_snoc _ _ _ second
    (represents_snoc _ _ _ first represents_empty)).
Qed.

Example swapped_wire_entries_rejected :
  ~ represents
    [Pending bool DataDelivery [BindBody] a b false;
     Pending bool DataDelivery [BindPrefix] a b true]
    two_wires [second;first].
Proof. intros [_ H]. specialize (H root_key). vm_compute in H. discriminate.
  Qed.

Example swapped_occurrences_rejected_even_equal_wire :
  ~ represents
    [Pending bool DataDelivery [BindPrefix] a b true;
     Pending bool DataDelivery [BindBody] a b true]
    (enqueue (enqueue empty_queues root_key (GHC.Base.hs_string__ "True"))
      root_key (GHC.Base.hs_string__ "True"))
    [Message bool DataDelivery [BindBody] a b true show_bool;
     Message bool DataDelivery [BindPrefix] a b true show_bool].
Proof. intros [H _]. cbn in H. discriminate. Qed.

Example data_choice_share_queue :
  at_key root_key [choice; second] =
    [GHC.Base.hs_string__ "True"; GHC.Base.hs_string__ "False"].
Proof. vm_compute. reflexivity. Qed.

Example data_choice_invariant :
  represents
    [Pending bool ChoiceDelivery [] a b true;
     Pending bool DataDelivery [BindBody] a b false]
    two_wires [choice;second].
Proof.
  exact (represents_snoc _ _ _ second
    (represents_snoc _ _ _ choice represents_empty)).
Qed.

Example same_kind_source_fifo_cannot_skip :
  ~ take_first_on_source_channel DataDelivery [BindBody] a b false
    [Pending bool DataDelivery [BindPrefix] a b true;
     Pending bool DataDelivery [BindBody] a b false]
    [Pending bool DataDelivery [BindPrefix] a b true].
Proof.
  intro H. inversion H; subst.
  match goal with
  | N : ~ same_channel _ _ _ _ _ |- _ =>
      apply N; repeat split; reflexivity
  end.
Qed.

Example source_can_skip_same_key_opposite_kind :
  take_first_on_source_channel DataDelivery [BindBody] a b false
    [Pending bool ChoiceDelivery [] a b true;
     Pending bool DataDelivery [BindBody] a b false]
    [Pending bool ChoiceDelivery [] a b true].
Proof.
  apply TakeOther.
  - cbn. intros [H _]. discriminate.
  - constructor.
Qed.

Example same_key_skip_has_no_wire_frontier :
  ~ wire_frontier (Pending bool DataDelivery [BindBody] a b false)
      [choice;second].
Proof.
  intro H.
  specialize (H [choice] second [] eq_refl eq_refl).
  inversion H as [|? ? N _]; subst. apply N. reflexivity.
Qed.

Example different_app_key_skip :
  take_first_on_source_channel DataDelivery [BindBody] a b false
    [Pending unit ChoiceDelivery [AppFunction] a b tt;
     Pending bool DataDelivery [BindBody] a b false]
    [Pending unit ChoiceDelivery [AppFunction] a b tt].
Proof.
  apply (source_take_different_keys bool DataDelivery [BindBody] a b false
    show_bool
    [Message unit ChoiceDelivery [AppFunction] a b tt show_unit] []).
  constructor; [discriminate|constructor].
Qed.

Example literal_announcement_owner_excluded :
  announcement_messages bool [] a true show_bool [a;b;c] =
    [Message bool ChoiceDelivery [] a b true show_bool;
     Message bool ChoiceDelivery [] a c true show_bool].
Proof. vm_compute. reflexivity. Qed.

Example literal_atomic_announcement :
  represents
    [Pending bool ChoiceDelivery [] a b true;
     Pending bool ChoiceDelivery [] a c true]
    (announce [a;b;c] a Root (GHC.Base.hs_string__ "True") empty_queues)
    [Message bool ChoiceDelivery [] a b true show_bool;
     Message bool ChoiceDelivery [] a c true show_bool].
Proof.
  exact (represents_announcement bool [] a true show_bool [a;b;c]
    [] empty_queues [] represents_empty).
Qed.

Example literal_exact_first_consume :
  represents [Pending bool DataDelivery [BindBody] a b false]
    (replace_queue two_wires root_key [GHC.Base.hs_string__ "False"]) [second].
Proof.
  exact (proj2 (represents_consume [] first [second] _ _
    repeated_root_invariant (Forall_nil _))).
Qed.

Example literal_matching_decode :
  @read bool read_bool (GHC.Base.hs_string__ "True") = Some true.
Proof. vm_compute. reflexivity. Qed.

Example other_key_framed :
  replace_queue two_wires root_key [GHC.Base.hs_string__ "False"]
    (a,c,Root) = [].
Proof. vm_compute. reflexivity. Qed.

Definition custom_sender : Show bool := fun _ => GHC.Base.hs_string__ "sender".
Example actual_sender_codec :
  message_wire (Message bool DataDelivery [] a b true custom_sender) =
    GHC.Base.hs_string__ "sender".
Proof. reflexivity. Qed.
