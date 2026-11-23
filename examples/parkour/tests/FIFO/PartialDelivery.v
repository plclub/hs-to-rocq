From Stdlib Require Import Lists.List Strings.String.
From ParkourTheories Require Import Tests.FIFO.ScheduledTraceContracts
  Network.Mailboxes Network.Endpoints Network.Execution Choreography.Occurrences
  Choreography.PendingDeliveries Choreography.RoleSteps Choreography.Execution
  Projection.Matching.PrefixRelation Projection.Matching.ActionReflection
  Projection.Matching.CursorAlignment Projection.FIFO.MessageRepresentation
  Network.Scheduling Semantics.SharedState Semantics.Runs
  Projection.EndpointRunner.
Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree
  Choreography.Choreo2.
Import ListNotations.

Module Partial.
Definition A := wire_A.
Definition B := wire_B.
Definition C := wire_C.
Definition roles := wire_roles.
Definition model := wire_model.
Definition stores := wire_stores.
Definition value (_ : Symbol) := bool.
Definition sm := shared_model model.
Definition tag := Choreography.Network.Root.
Definition truth := GHC.Base.hs_string__ "True".
Definition falsehood := GHC.Base.hs_string__ "False".
Lemma CA : C <> A.
Proof. discriminate. Qed.
Definition branch p b : Choreo wire_effect p bool :=
  Bind (Perf (@Comm wire_effect p bool A C show_bool read_bool
    (known A) (known C) MkSSymbol (Mk_At (fun _ => false)) MkSSymbol))
    (fun _ => Pure b).
Definition c0 p : @cursor wire_effect wire_event p bool := Code [] (wire_choice
  p).
Definition a1 : @cursor wire_effect wire_event A bool :=
  Code [ChoiceBody] (branch A true).
Definition a2 : @cursor wire_effect wire_event A bool :=
  Seq [ChoiceBody] (Returned (@off_at bool C A CA))
    (fun _ => Pure true).
Definition b1 : @cursor wire_effect wire_event B bool :=
  Code [ChoiceBody] (branch B true).
Definition cs1 := set_cursor value c0 A a1.
Definition cs2 := set_cursor value cs1 A a2.
Definition cs3 := set_cursor value cs2 B b1.
Definition n0 p : @control wire_effect wire_event bool :=
  load (runner (wire_choice p) tag).
Definition na1 : @control wire_effect wire_event bool :=
  CBind (CPure tt) (fun _ => load (runner (branch A true) tag)).
Definition na2 : @control wire_effect wire_event bool :=
  CBind
    (CApp (CBind (CPure tt) (fun _ => CPure (fun z : At bool C A => z)))
      (CPure (@off_at bool C A CA)))
    (fun _ => CPure true).
Definition nb1 : @control wire_effect wire_event bool :=
  CBind (CPure true) (fun b => load (runner (branch B b) tag)).
Definition ns1 := set_control value n0 A na1.
Definition ns2 := set_control value ns1 A na2.
Definition ns3 := set_control value ns2 B nb1.
Definition gb := Message bool ChoiceDelivery [] A B true show_bool.
Definition gc := Message bool ChoiceDelivery [] A C true show_bool.
Definition gd := Message bool DataDelivery [ChoiceBody;BindPrefix] A C false
  show_bool.
Definition gs1 := [gb;gc].
Definition gs2 := [gb;gc;gd].
Definition gs3 := [gc;gd].
Definition q1 := announce roles A tag truth empty_queues.
Definition q2 := enqueue q1 (A,C,tag) falsehood.
Definition q3 := replace_queue q2 (A,B,tag) [].
Definition source cs gs : @Choreography.Execution.configuration wire_effect
  wire_event
    ((Symbol -> unit) * unit) value :=
  {| positions := cs; Choreography.Execution.shared_store := (stores,tt);
     deliveries := map pending_of gs |}.
Definition net ns q : @Network.Execution.configuration wire_effect wire_event
    ((Symbol -> unit) * unit) := assembled roles value ns q (stores,tt).
Definition s0 := source c0 [].
Definition s1 := source cs1 gs1.
Definition s2 := source cs2 gs2.
Definition s3 := source cs3 gs3.
Definition t0 := net n0 empty_queues.
Definition t1 := net ns1 q1.
Definition t2 := net ns2 q2.
Definition t3 := net ns3 q3.
Definition sa1 : @source_action wire_event ((Symbol -> unit) * unit) :=
  AnnounceAction bool [] A true.
Definition sa2 : @source_action wire_event ((Symbol -> unit) * unit) :=
  SendAction bool [ChoiceBody;BindPrefix] A C false.
Definition sa3 : @source_action wire_event ((Symbol -> unit) * unit) :=
  HearAction bool [] A B true.
Definition la1 : @action wire_event ((Symbol -> unit) * unit) := Announced A tag
  truth.
Definition la2 : @action wire_event ((Symbol -> unit) * unit) := Sent A C tag
  falsehood.
Definition la3 : @action wire_event ((Symbol -> unit) * unit) := Received A B
  tag truth.

Ltac updates :=
  unfold cs1, cs2, cs3, ns1, ns2, ns3;
  repeat first [rewrite cursor_here | rewrite set_here |
    rewrite cursor_other by congruence | rewrite set_other by congruence].

Lemma align_a1 : aligned sm tag A bool a1 na1.
Proof.
  eapply AlignAdministrative; [apply AdminPure|].
  exact (initial_alignment sm tag A bool [ChoiceBody] (branch A true)).
Qed.
Lemma align_a2 : aligned sm tag A bool a2 na2.
Proof.
  apply AlignSeq.
  - apply AlignReturned. apply AdminApp with
      (g := fun z : At bool C A => z)
      (x := @off_at bool C A CA).
    + eapply AdminBind; apply AdminPure.
    + apply AdminPure.
  - intros x. exact (initial_alignment sm tag A bool
      [ChoiceBody;BindBody] (Pure true)).
Qed.
Lemma align_b1 : aligned sm tag B bool b1 nb1.
Proof.
  eapply AlignAdministrative; [apply AdminPure|].
  exact (initial_alignment sm tag B bool [ChoiceBody] (branch B true)).
Qed.
Lemma state1 : state_match model roles value s1 t1 gs1.
Proof.
  split; [reflexivity|]. split.
  - exact (represents_announcement bool [] A true show_bool roles
      [] empty_queues [] represents_empty).
  - exists ns1. split; [reflexivity|].
    intros p [<-|[<-|[<-|F]]]; [| | |contradiction];
      constructor; cbn [s1 source positions]; updates.
    + exact align_a1.
    + apply initial_alignment.
    + apply initial_alignment.
Qed.
Lemma state2 : state_match model roles value s2 t2 gs2.
Proof.
  split; [reflexivity|]. split.
  - exact (represents_send bool [ChoiceBody;BindPrefix] A C false show_bool
      _ _ _ (proj1 (proj2 state1))).
  - exists ns2. split; [reflexivity|].
    intros p [<-|[<-|[<-|F]]]; [| | |contradiction];
      constructor; cbn [s2 source positions]; updates.
    + exact align_a2.
    + apply initial_alignment.
    + apply initial_alignment.
Qed.
Lemma state3 : state_match model roles value s3 t3 gs3.
Proof.
  split; [reflexivity|]. split.
  - eapply (delivery_represents bool ChoiceDelivery [] A B true read_bool
      gs2 truth gs3 q2 []); [exact (proj1 (proj2 state2))| |reflexivity].
    change (delivery bool ChoiceDelivery [] A B true read_bool
      [gb;gc;gd] (@show bool show_bool true) [gc;gd]).
    apply (Deliver _ _ _ _ _ _ _ show_bool [] [gc;gd]);
      [constructor|reflexivity].
  - exists ns3. split; [reflexivity|].
    intros p [<-|[<-|[<-|F]]]; [| | |contradiction];
      constructor; cbn [s3 source positions]; updates.
    + exact align_a2.
    + exact align_b1.
    + apply initial_alignment.
Qed.
Lemma pair1 : paired_step model roles value s0 t0 [] sa1 s1 la1 t1 gs1.
Proof.
  eapply PairStep with (p := A) (pre := [])
    (post := [Endpoint _ B (n0 B);Endpoint _ C (n0 C)])
    (t := n0 A) (t' := na1).
  - now left.
  - reflexivity.
  - cbn [t1 net assembled endpoints roles wire_roles List.map entry]. updates.
    reflexivity.
  - cbn [s0 s1 source positions deliveries Choreography.Execution.shared_store].
    updates. apply DAnnounce.
  - intros r Ne. cbn [s0 s1 source positions].
    unfold cs1. rewrite cursor_other by congruence. reflexivity.
  - cbn. apply StepBind. eapply StepContinue; [apply ReturnPure|apply
    StepBCast].
Qed.
Lemma pair2 : paired_step model roles value s1 t1 gs1 sa2 s2 la2 t2 gs2.
Proof.
  eapply PairStep with (p := A) (pre := [])
    (post := [Endpoint _ B (n0 B);Endpoint _ C (n0 C)])
    (t := na1) (t' := na2).
  - now left.
  - cbn [t1 net assembled endpoints roles wire_roles List.map entry]. updates.
    reflexivity.
  - cbn [t2 net assembled endpoints roles wire_roles List.map entry]. updates.
    reflexivity.
  - cbn [s1 s2 source positions deliveries Choreography.Execution.shared_store].
    updates. eapply DSilent; [apply SBind|]. apply DSeq. apply DSend.
  - intros r Ne. cbn [s1 s2 source positions].
    unfold cs2. rewrite cursor_other by congruence. reflexivity.
  - cbn. eapply StepContinue; [apply ReturnPure|].
    apply StepBind. eapply StepContinue; [apply ReturnPure|].
    apply StepLeft. apply StepBind. apply StepSend.
Qed.
Lemma pair3 : paired_step model roles value s2 t2 gs2 sa3 s3 la3 t3 gs3.
Proof.
  eapply PairStep with (p := B) (pre := [Endpoint _ A na2])
    (post := [Endpoint _ C (n0 C)]) (t := n0 B) (t' := nb1).
  - right. now left.
  - cbn [t2 net assembled endpoints roles wire_roles List.map entry]. updates.
    reflexivity.
  - cbn [t3 net assembled endpoints roles wire_roles List.map entry]. updates.
    reflexivity.
  - cbn [s2 s3 source positions deliveries Choreography.Execution.shared_store].
    updates. apply DHear; [discriminate|].
    change (delivery bool ChoiceDelivery [] A B true read_bool
      [gb;gc;gd] (@show bool show_bool true) [gc;gd]).
    apply (Deliver _ _ _ _ _ _ _ show_bool [] [gc;gd]);
      [constructor|reflexivity].
  - intros r Ne. cbn [s2 s3 source positions].
    unfold cs3. rewrite cursor_other by congruence. reflexivity.
  - cbn. apply StepBind. eapply StepContinue; [apply ReturnPure|].
    eapply StepRecv with (x := true); reflexivity.
Qed.
Lemma prefix1 : matched_prefix model stores tt roles value wire_choice [sa1] s1
  [la1] t1 gs1.
Proof.
  change (matched_prefix model stores tt roles value wire_choice
    ([] ++ [sa1]) s1 ([] ++ [la1]) t1 gs1).
  eapply PrefixSnoc; [apply PrefixInitial|exact pair1|exact state1].
Qed.
Lemma prefix2 : matched_prefix model stores tt roles value wire_choice
  [sa1;sa2] s2 [la1;la2] t2 gs2.
Proof.
  eapply (PrefixSnoc _ _ _ _ _ _ [sa1] s1 [la1] t1 gs1);
    [exact prefix1|exact pair2|exact state2].
Qed.
Lemma prefix3 : matched_prefix model stores tt roles value wire_choice
  [sa1;sa2;sa3] s3 [la1;la2;la3] t3 gs3.
Proof.
  eapply (PrefixSnoc _ _ _ _ _ _ [sa1;sa2] s2 [la1;la2] t2 gs2);
    [exact prefix2|exact pair3|exact state3].
Qed.
End Partial.

Theorem partial_delivery : wire_partial_delivery.
Proof.
  exists Partial.s3, Partial.t3.
  split.
  - exact (prefix_source_run Partial.model Partial.stores tt Partial.roles
      Partial.value wire_choice _ _ _ _ _ Partial.prefix3).
  - split.
    + change (finite_run (Network.Execution.step Partial.sm Partial.roles)
      Partial.t0
        [Partial.la1;Partial.la2;Partial.la3] Partial.t3).
      change (finite_run (Network.Execution.step Partial.sm Partial.roles)
        Partial.t0
        ([Partial.la1;Partial.la2] ++ [Partial.la3]) Partial.t3).
      eapply RunSnoc with (x := Partial.t2).
      * change (finite_run (Network.Execution.step Partial.sm Partial.roles)
        Partial.t0
          ([Partial.la1] ++ [Partial.la2]) Partial.t2).
        eapply RunSnoc with (x := Partial.t1).
        -- change (finite_run (Network.Execution.step Partial.sm Partial.roles)
          Partial.t0
             ([] ++ [Partial.la1]) Partial.t1).
           eapply RunSnoc with (x := Partial.t0).
           ++ constructor.
           ++ eapply paired_network. exact Partial.pair1.
        -- eapply paired_network. exact Partial.pair2.
      * eapply paired_network. exact Partial.pair3.
    + split.
      * exists Partial.gs3. exact Partial.prefix3.
      * split; [reflexivity|]. split.
        -- cbn [Partial.s3 Partial.source positions].
           Partial.updates. reflexivity.
        -- intro k.
           pose proof (proj2 (proj1 (proj2 Partial.state3)) k) as Queue.
           rewrite Queue.
           change (at_key k [Partial.gc;Partial.gd] =
             if key_eq_dec k (wire_A,wire_C,Choreography.Network.Root)
             then [GHC.Base.hs_string__ "True";GHC.Base.hs_string__ "False"]
               else []).
           change ((if key_eq_dec (wire_A,wire_C,Choreography.Network.Root) k
             then GHC.Base.hs_string__ "True" ::
               (if key_eq_dec (wire_A,wire_C,Choreography.Network.Root) k
                then [GHC.Base.hs_string__ "False"] else [])
             else (if key_eq_dec (wire_A,wire_C,Choreography.Network.Root) k
                then [GHC.Base.hs_string__ "False"] else [])) =
             if key_eq_dec k (wire_A,wire_C,Choreography.Network.Root)
             then [GHC.Base.hs_string__ "True";GHC.Base.hs_string__ "False"]
               else []).
           destruct (key_eq_dec (wire_A,wire_C,Choreography.Network.Root) k);
             destruct (key_eq_dec k (wire_A,wire_C,Choreography.Network.Root));
             try congruence; reflexivity.
Qed.

Print Assumptions partial_delivery.
