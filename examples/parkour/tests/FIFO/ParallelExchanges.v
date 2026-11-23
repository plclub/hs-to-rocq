From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Tests.FIFO.ScheduledTraceContracts
  Choreography.Occurrences Choreography.PendingDeliveries Choreography.RoleSteps
  Choreography.Execution Network.Mailboxes Network.Endpoints Network.Execution
  Projection.Matching.PrefixRelation Projection.Matching.ActionReflection
  Projection.Matching.CursorAlignment Projection.FIFO.MessageRepresentation
  Network.Scheduling Semantics.SharedState Projection.EndpointRunner
  Projection.ConstructorEquations.
Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree.
Require Choreography.Choreo2.
Import ListNotations.

Module WireParallel.
Definition A := wire_A.
Definition B := wire_B.
Definition roles := [A; B].
Definition result p := Choreography.Choreo2.At bool B p.
Definition sm := shared_model wire_model.
Definition tag := Choreography.Network.Nest (Data.Either.Right tt)
  Choreography.Network.Root.
Definition left_tag := Choreography.Network.Nest (Data.Either.Left tt)
  Choreography.Network.Root.
Definition fn p : Choreography.Choreo2.Choreo wire_effect p (result p -> result
  p) :=
  Bind (Perf (@Choreography.Choreo2.Comm wire_effect p bool A A
    show_bool read_bool (known A) (known A) MkSSymbol
    (Choreography.Choreo2.Mk_At (fun _ => true)) MkSSymbol))
    (fun _ => Pure (fun x => x)).
Definition arg p : Choreography.Choreo2.Choreo wire_effect p (result p) :=
  Perf (@Choreography.Choreo2.Comm wire_effect p bool A B
    show_bool read_bool (known A) (known B) MkSSymbol
    (Choreography.Choreo2.Mk_At (fun _ => false)) MkSSymbol).
Lemma AB : A <> B. Proof. discriminate. Qed.
Lemma BA : B <> A. Proof. discriminate. Qed.
Definition c0 p : @cursor wire_effect wire_event p (result p) :=
  Code [] (wire_app_self p).
Definition ca : @cursor wire_effect wire_event A (result A) :=
  Fork (Code [AppFunction] (fn A)) (Returned (@off_at bool B A BA)).
Definition cb : @cursor wire_effect wire_event B (result B) :=
  Fork (Code [AppFunction] (fn B)) (Returned (here_at false)).
Definition cs1 := set_cursor result c0 A ca.
Definition cs2 := set_cursor result cs1 B cb.
Definition n0 p : @control wire_effect wire_event (result p) :=
  load (runner (wire_app_self p) Choreography.Network.Root).
Definition nf p : @control wire_effect wire_event (result p -> result p) :=
  load (runner (fn p) left_tag).
Definition na : @control wire_effect wire_event (result A) :=
  CApp (nf A)
    (CApp (CBind (CPure tt) (fun _ => CPure (fun z : result A => z)))
      (CPure (@off_at bool B A BA))).
Definition nb : @control wire_effect wire_event (result B) :=
  CApp (nf B) (CBind (CPure false) (fun x => CPure (@here_at bool B x))).
Definition ns1 := set_control result n0 A na.
Definition ns2 := set_control result ns1 B nb.
Definition g := Message bool DataDelivery [AppArgument] A B false show_bool.
Definition q1 := enqueue empty_queues (A,B,tag) (@show bool show_bool false).
Definition q2 := replace_queue q1 (A,B,tag) [].
Definition source cs gs : @Choreography.Execution.configuration wire_effect
  wire_event
    ((Symbol -> unit) * unit) result :=
  {| positions := cs; Choreography.Execution.shared_store := (wire_stores,tt);
     deliveries := map pending_of gs |}.
Definition net ns q : @Network.Execution.configuration wire_effect wire_event
    ((Symbol -> unit) * unit) :=
  assembled roles result ns q (wire_stores,tt).
Definition s0 := source c0 [].
Definition s1 := source cs1 [g].
Definition s2 := source cs2 [].
Definition t0 := net n0 empty_queues.
Definition t1 := net ns1 q1.
Definition t2 := net ns2 q2.
Definition sa : @source_action wire_event ((Symbol -> unit) * unit) :=
  SendAction bool [AppArgument] A B false.
Definition sb : @source_action wire_event ((Symbol -> unit) * unit) :=
  ReceiveAction bool [AppArgument] A B false.
Definition la : @action wire_event ((Symbol -> unit) * unit) :=
  Sent A B tag (@show bool show_bool false).
Definition lb : @action wire_event ((Symbol -> unit) * unit) :=
  Received A B tag (@show bool show_bool false).

Lemma step1 : Endpoints.step sm roles A (result A) (n0 A) empty_queues
  (wire_stores,tt)
  la na q1 (wire_stores,tt).
Proof.
  cbn. apply StepRight.
  eapply StepContinue; [apply ReturnPure|].
  apply StepLeft. apply StepBind. apply StepSend.
Qed.
Lemma step2 : Endpoints.step sm roles B (result B) (n0 B) q1 (wire_stores,tt)
  lb nb q2 (wire_stores,tt).
Proof.
  cbn. apply StepRight.
  eapply StepContinue; [apply ReturnPure|].
  apply StepBind. eapply StepRecv with (x := false); reflexivity.
Qed.
Lemma align_a : aligned sm Choreography.Network.Root A (result A) ca na.
Proof.
  apply AlignFork.
  - exact (initial_alignment sm Choreography.Network.Root A _
      [AppFunction] (fn A)).
  - apply AlignReturned.
    eapply AdminApp with (g := fun z : result A => z) (x := @off_at bool B A
      BA).
    + eapply AdminBind; apply AdminPure.
    + apply AdminPure.
Qed.
Lemma align_b : aligned sm Choreography.Network.Root B (result B) cb nb.
Proof.
  apply AlignFork.
  - exact (initial_alignment sm Choreography.Network.Root B _
      [AppFunction] (fn B)).
  - apply AlignReturned. eapply AdminBind; apply AdminPure.
Qed.
Ltac updates :=
  unfold cs1, cs2, ns1, ns2;
  repeat first [rewrite cursor_here | rewrite set_here |
    rewrite cursor_other by (first [congruence | discriminate]) |
    rewrite set_other by (first [congruence | discriminate])].
Lemma residual1 : residuals wire_model roles result s1 t1.
Proof.
  exists ns1. split; [reflexivity|].
  intros p [<-|[<-|H]]; [| |contradiction];
    constructor; cbn [s1 source positions]; updates.
  - exact align_a.
  - apply initial_alignment.
Qed.
Lemma residual2 : residuals wire_model roles result s2 t2.
Proof.
  exists ns2. split; [reflexivity|].
  intros p [<-|[<-|H]]; [| |contradiction];
    constructor; cbn [s2 source positions]; updates.
  - exact align_a.
  - exact align_b.
Qed.
Lemma state1 : state_match wire_model roles result s1 t1 [g].
Proof.
  split; [reflexivity|]. split; [|exact residual1].
  exact (represents_send bool [AppArgument] A B false show_bool [] empty_queues
    []
    represents_empty).
Qed.
Lemma state2 : state_match wire_model roles result s2 t2 [].
Proof.
  split; [reflexivity|]. split; [|exact residual2].
  change (represents [] q2 []).
  eapply (delivery_represents bool DataDelivery [AppArgument] A B false
    read_bool
    [g] (@show bool show_bool false) [] q1 []);
    [exact (proj1 (proj2 state1))| |reflexivity].
  apply delivery_singleton. reflexivity.
Qed.
Lemma pair1 : paired_step wire_model roles result s0 t0 [] sa s1 la t1 [g].
Proof.
  eapply PairStep with (p := A) (pre := []) (post := [Endpoint _ B (n0 B)])
    (t := n0 A) (t' := na).
  - now left.
  - reflexivity.
  - cbn [t1 net assembled endpoints roles List.map entry]. updates. reflexivity.
  - cbn [s0 s1 source positions deliveries Choreography.Execution.shared_store].
    updates. eapply DSilent; [apply SApp|]. apply DRight. apply DSend.
  - intros r H. cbn [s0 s1 source positions].
    unfold cs1. rewrite cursor_other by congruence. reflexivity.
  - exact step1.
Qed.
Lemma pair2 : paired_step wire_model roles result s1 t1 [g] sb s2 lb t2 [].
Proof.
  eapply PairStep with (p := B) (pre := [Endpoint _ A na]) (post := [])
    (t := n0 B) (t' := nb).
  - right. now left.
  - cbn [t1 net assembled endpoints roles List.map entry]. updates. reflexivity.
  - cbn [t2 net assembled endpoints roles List.map entry]. updates. reflexivity.
  - cbn [s1 s2 source positions deliveries Choreography.Execution.shared_store].
    updates. eapply DSilent; [apply SApp|]. apply DRight.
    apply DReceive; [exact AB|]. apply delivery_singleton. reflexivity.
  - intros r H. cbn [s1 s2 source positions].
    unfold cs2. rewrite cursor_other by congruence. reflexivity.
  - exact step2.
Qed.
Lemma matched : PrefixRelation.matches wire_model wire_stores tt roles result
  wire_app_self
    [sa;sb] s2 [la;lb] t2.
Proof.
  exists [].
  change (matched_prefix wire_model wire_stores tt roles result wire_app_self
    ([sa] ++ [sb]) s2 ([la] ++ [lb]) t2 []).
  eapply PrefixSnoc; [|exact pair2|exact state2].
  change (matched_prefix wire_model wire_stores tt roles result wire_app_self
    ([] ++ [sa]) s1 ([] ++ [la]) t1 [g]).
  eapply PrefixSnoc; [constructor|exact pair1|exact state1].
Qed.
Lemma queues_empty k : q2 k = [].
Proof.
  unfold q2, q1, enqueue, replace_queue, empty_queues.
  destruct (key_eq_dec k (A,B,tag)); reflexivity.
Qed.
Lemma function_returns p : Endpoints.returns sm _ (nf p)
    (fun z : result p => z).
Proof.
  unfold nf, fn. rewrite runner_bind. cbn [load].
  rewrite runner_comm_self. cbn [load].
  eapply ReturnBind; apply ReturnPure.
Qed.
Lemma final_network : Network.Execution.final sm t2.
Proof.
  split; [|exact queues_empty].
  cbn [t2 net assembled endpoints roles List.map entry]. updates.
  constructor.
  - exists (@off_at bool B A BA). updates. unfold na.
    eapply ReturnApp with (g := fun z : result A => z); [apply
      function_returns|].
    eapply ReturnApp with (g := fun z : result A => z).
    + eapply ReturnBind; apply ReturnPure.
    + apply ReturnPure.
  - constructor; [|constructor].
    exists (@here_at bool B false). updates. unfold nb.
    eapply ReturnApp with (g := fun z : result B => z); [apply
      function_returns|].
    eapply ReturnBind; apply ReturnPure.
Qed.
Lemma final_source : Choreography.Execution.final sm roles s2.
Proof.
  split; [reflexivity|].
  intros p [<-|[<-|H]]; [| |contradiction];
    cbn [s2 source positions]; updates.
  - exists (@off_at bool B A BA).
    eapply aligned_returns; [exact align_a|].
    unfold na. eapply ReturnApp with (g := fun z : result A => z);
      [apply function_returns|].
    eapply ReturnApp with (g := fun z : result A => z).
    + eapply ReturnBind; apply ReturnPure.
    + apply ReturnPure.
  - exists (@here_at bool B false).
    eapply aligned_returns; [exact align_b|].
    unfold nb. eapply ReturnApp with (g := fun z : result B => z);
      [apply function_returns|].
    eapply ReturnBind; apply ReturnPure.
Qed.
End WireParallel.

Theorem app_self_completed : ScheduledTraceContracts.wire_app_self_completed.
Proof.
  exists WireParallel.s2, WireParallel.t2.
  split; [exact WireParallel.matched|].
  split; [exact WireParallel.final_source|].
  split; [exact WireParallel.final_network|].
  split; [reflexivity|exact WireParallel.queues_empty].
Qed.

Theorem app_reject_root_tag : ScheduledTraceContracts.wire_app_reject_root_tag.
Proof.
  intros s n [gs H].
  apply prefix_action_order in H.
  inversion H as [|a b tc tn Match Rest]; subst.
  inversion Match.
Qed.
