From Stdlib Require Import Lists.List Strings.String.
From ITree Require ITree.
Require Import DeadlockLocal DeadlockNetwork DeadlockSource DeadlockMatch
  DeadlockMatchStep DeadlockAlignment DeadlockMessages DeadlockOrder
  DeadlockRoster DeadlockState DeadlockProjectionExpect DeadlockStepView.
Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree Choreography.Choreo2.
Import ListNotations.

(* The same two-role, two-type, reused-Root family as DeadlockRepairCases.
   These are generated endpoints, not a relation substituted for matches. *)
Module RepairMatch.
Definition A : Symbol := GHC.Base.hs_string__ "A".
Definition B : Symbol := GHC.Base.hs_string__ "B".
Definition Id (X : Type) := X.
Definition NoEvent (_ : Type) := Empty_set.
Definition model : local_model Id NoEvent role (unit * unit) :=
  {| interpret_local := fun _ x => ITreeDefinition.Ret x;
     reply_local := fun _ _ _ _ _ _ => False |}.
Definition stores (_ : role) := tt.
Definition roles := [A;B].
Definition result p := At unit B p.
Definition choice p : At bool A p := Mk_At (fun _ => true).
Definition payload p : At unit A p := Mk_At (fun _ => tt).
Definition branch p (_ : bool) : Choreo Id p (result p) :=
  op_z7eUzg__ (payload p) (@MkSSymbol B).
Definition program p : Choreo Id p (result p) := cond (choice p) (branch p).
Definition sm := shared_model model.
Definition truth := @show bool show_bool true.
Definition unit_wire := @show unit show_unit tt.
Definition tag := Choreography.Network.Root.
Lemma AB : A <> B. Proof. discriminate. Qed.
Lemma BA : B <> A. Proof. discriminate. Qed.

Definition c0 p : @cursor Id NoEvent p (result p) := Code [] (program p).
Definition a1 : @cursor Id NoEvent A (result A) := Code [ChoiceBody] (branch A true).
Definition a2 : @cursor Id NoEvent A (result A) := Returned (@off_at unit B A BA).
Definition b1 : @cursor Id NoEvent B (result B) := Code [ChoiceBody] (branch B true).
Definition b2 : @cursor Id NoEvent B (result B) := Returned (here_at tt).
Definition cs1 := set_cursor result c0 A a1.
Definition cs2 := set_cursor result cs1 A a2.
Definition cs3 := set_cursor result cs2 B b1.
Definition cs4 := set_cursor result cs3 B b2.

Definition n0 p : @control Id NoEvent (result p) := load (runner (program p) tag).
Definition na1 : @control Id NoEvent (result A) :=
  CBind (CPure tt) (fun _ => load (runner (branch A true) tag)).
Definition na2 : @control Id NoEvent (result A) :=
  CApp (CBind (CPure tt) (fun _ => CPure (fun z : result A => z)))
    (CPure (@off_at unit B A BA)).
Definition nb1 : @control Id NoEvent (result B) :=
  CBind (CPure true) (fun x => load (runner (branch B x) tag)).
Definition nb2 : @control Id NoEvent (result B) :=
  CBind (CPure tt) (fun x => CPure (@here_at unit B x)).
Definition ns1 := set_control result n0 A na1.
Definition ns2 := set_control result ns1 A na2.
Definition ns3 := set_control result ns2 B nb1.
Definition ns4 := set_control result ns3 B nb2.

Definition gchoice := Message bool ChoiceDelivery [] A B true show_bool.
Definition gdata := Message unit DataDelivery [ChoiceBody] A B tt show_unit.
Definition gs1 := [gchoice].
Definition gs2 := [gchoice;gdata].
Definition gs3 := [gdata].
Definition q1 := announce roles A tag truth empty_queues.
Definition q2 := enqueue q1 (A,B,tag) unit_wire.
Definition q3 := replace_queue q2 (A,B,tag) [unit_wire].
Definition q4 := replace_queue q3 (A,B,tag) [].
Definition source cs gs : @DeadlockSource.configuration Id NoEvent
    ((role -> unit) * unit) result :=
  {| positions := cs; DeadlockSource.shared_store := (stores,tt);
     deliveries := map pending_of gs |}.
Definition net ns q : @DeadlockNetwork.configuration Id NoEvent
    ((role -> unit) * unit) := assembled roles result ns q (stores,tt).
Definition s0 := source c0 [].
Definition s1 := source cs1 gs1.
Definition s2 := source cs2 gs2.
Definition s3 := source cs3 gs3.
Definition s4 := source cs4 [].
Definition t0 := net n0 empty_queues.
Definition t1 := net ns1 q1.
Definition t2 := net ns2 q2.
Definition t3 := net ns3 q3.
Definition t4 := net ns4 q4.
Definition sa1 : @source_action NoEvent ((role -> unit) * unit) :=
  AnnounceAction bool [] A true.
Definition sa2 : @source_action NoEvent ((role -> unit) * unit) :=
  SendAction unit [ChoiceBody] A B tt.
Definition sa3 : @source_action NoEvent ((role -> unit) * unit) :=
  HearAction bool [] A B true.
Definition sa4 : @source_action NoEvent ((role -> unit) * unit) :=
  ReceiveAction unit [ChoiceBody] A B tt.
Definition la1 : @action NoEvent ((role -> unit) * unit) := Announced A tag truth.
Definition la2 : @action NoEvent ((role -> unit) * unit) := Sent A B tag unit_wire.
Definition la3 : @action NoEvent ((role -> unit) * unit) := Received A B tag truth.
Definition la4 : @action NoEvent ((role -> unit) * unit) := Received A B tag unit_wire.

Lemma step1 : step sm roles A (result A) (n0 A) empty_queues (stores,tt)
  la1 na1 q1 (stores,tt).
Proof.
  cbn. apply StepBind. eapply StepContinue; [apply ReturnPure|apply StepBCast].
Qed.
Lemma step2 : step sm roles A (result A) na1 q1 (stores,tt)
  la2 na2 q2 (stores,tt).
Proof.
  cbn. eapply StepContinue; [apply ReturnPure|].
  eapply StepContinue; [apply ReturnPure|].
  apply StepLeft. apply StepBind. apply StepSend.
Qed.
Lemma fifo2 : q2 (A,B,tag) = [truth;unit_wire].
Proof. reflexivity. Qed.
Lemma step3 : step sm roles B (result B) (n0 B) q2 (stores,tt)
  la3 nb1 q3 (stores,tt).
Proof.
  cbn. apply StepBind. eapply StepContinue; [apply ReturnPure|].
  eapply StepRecv with (x := true); reflexivity.
Qed.
Lemma step4 : step sm roles B (result B) nb1 q3 (stores,tt)
  la4 nb2 q4 (stores,tt).
Proof.
  cbn. eapply StepContinue; [apply ReturnPure|].
  eapply StepContinue; [apply ReturnPure|].
  apply StepBind. eapply StepRecv with (x := tt); reflexivity.
Qed.

Lemma align_a1 : aligned sm tag A (result A) a1 na1.
Proof.
  apply AlignAdministrative with (x := tt); [apply AdminPure|].
  exact (initial_alignment sm tag A (result A) [ChoiceBody] (branch A true)).
Qed.
Lemma align_a2 : aligned sm tag A (result A) a2 na2.
Proof.
  apply AlignReturned. unfold na2.
  apply AdminApp with (g := fun z : result A => z) (x := @off_at unit B A BA).
  - eapply AdminBind; apply AdminPure.
  - apply AdminPure.
Qed.
Lemma align_b1 : aligned sm tag B (result B) b1 nb1.
Proof.
  apply AlignAdministrative with (x := true); [apply AdminPure|].
  exact (initial_alignment sm tag B (result B) [ChoiceBody] (branch B true)).
Qed.
Lemma align_b2 : aligned sm tag B (result B) b2 nb2.
Proof. apply AlignReturned. eapply AdminBind; apply AdminPure. Qed.

Ltac updates :=
  unfold cs1, cs2, cs3, cs4, ns1, ns2, ns3, ns4;
  repeat first [rewrite cursor_here | rewrite set_here |
    rewrite cursor_other by congruence | rewrite set_other by congruence].

Lemma residual1 : residuals model roles result s1 t1.
Proof.
  exists ns1. split; [reflexivity|]. intros p [<-|[<-|H]]; [| |contradiction];
  constructor; cbn [s1 t1 source]; updates.
  - exact align_a1.
  - apply initial_alignment.
Qed.
Lemma residual2 : residuals model roles result s2 t2.
Proof.
  exists ns2. split; [reflexivity|]. intros p [<-|[<-|H]]; [| |contradiction];
  constructor; cbn [s2 t2 source]; updates.
  - exact align_a2.
  - apply initial_alignment.
Qed.
Lemma residual3 : residuals model roles result s3 t3.
Proof.
  exists ns3. split; [reflexivity|]. intros p [<-|[<-|H]]; [| |contradiction];
  constructor; cbn [s3 t3 source]; updates.
  - exact align_a2.
  - exact align_b1.
Qed.
Lemma residual4 : residuals model roles result s4 t4.
Proof.
  exists ns4. split; [reflexivity|]. intros p [<-|[<-|H]]; [| |contradiction];
  constructor; cbn [s4 t4 source]; updates.
  - exact align_a2.
  - exact align_b2.
Qed.

Lemma state1 : state_match model roles result s1 t1 gs1.
Proof.
  split; [reflexivity|]. split; [|exact residual1].
  exact (represents_announcement bool [] A true show_bool roles [] empty_queues []
    represents_empty).
Qed.
Lemma state2 : state_match model roles result s2 t2 gs2.
Proof.
  split; [reflexivity|]. split; [|exact residual2].
  exact (represents_send unit [ChoiceBody] A B tt show_unit _ _ _
    (proj1 (proj2 state1))).
Qed.
Lemma state3 : state_match model roles result s3 t3 gs3.
Proof.
  split; [reflexivity|]. split; [|exact residual3].
  change (represents (map pending_of gs3) q3 gs3).
  eapply (delivery_represents bool ChoiceDelivery [] A B true read_bool
    gs2 truth gs3 q2 [unit_wire]);
    [exact (proj1 (proj2 state2))| |exact fifo2].
  change (delivery bool ChoiceDelivery [] A B true read_bool
    [gchoice;gdata] truth [gdata]).
  apply (Deliver _ _ _ _ _ _ _ show_bool [] [gdata]); [constructor|reflexivity].
Qed.
Lemma state4 : state_match model roles result s4 t4 [].
Proof.
  split; [reflexivity|]. split; [|exact residual4].
  change (represents [] q4 []).
  eapply (delivery_represents unit DataDelivery [ChoiceBody] A B tt read_unit
    gs3 unit_wire [] q3 []);
    [exact (proj1 (proj2 state3))| |reflexivity].
  apply delivery_singleton. reflexivity.
Qed.

Lemma pair1 : paired_step model roles result s0 t0 [] sa1 s1 la1 t1 gs1.
Proof.
  eapply PairStep with (p := A) (pre := []) (post := [Endpoint _ B (n0 B)])
    (t := n0 A) (t' := na1).
  - now left.
  - reflexivity.
  - cbn [t1 net assembled endpoints roles List.map entry]. updates. reflexivity.
  - cbn [s0 s1 source positions deliveries DeadlockSource.shared_store].
    updates. apply DAnnounce.
  - intros r H. cbn [s0 s1 source positions].
    unfold cs1. rewrite cursor_other by congruence. reflexivity.
  - exact step1.
Qed.
Lemma pair2 : paired_step model roles result s1 t1 gs1 sa2 s2 la2 t2 gs2.
Proof.
  eapply PairStep with (p := A) (pre := []) (post := [Endpoint _ B (n0 B)])
    (t := na1) (t' := na2).
  - now left.
  - cbn [t1 net assembled endpoints roles List.map entry]. updates. reflexivity.
  - cbn [t2 net assembled endpoints roles List.map entry]. updates. reflexivity.
  - cbn [s1 s2 source positions deliveries DeadlockSource.shared_store].
    updates. apply DSend.
  - intros r H. cbn [s1 s2 source positions].
    unfold cs2. rewrite cursor_other by congruence. reflexivity.
  - exact step2.
Qed.
Lemma pair3 : paired_step model roles result s2 t2 gs2 sa3 s3 la3 t3 gs3.
Proof.
  eapply PairStep with (p := B) (pre := [Endpoint _ A na2]) (post := [])
    (t := n0 B) (t' := nb1).
  - right. now left.
  - cbn [t2 net assembled endpoints roles List.map entry]. updates. reflexivity.
  - cbn [t3 net assembled endpoints roles List.map entry]. updates. reflexivity.
  - cbn [s2 s3 source positions deliveries DeadlockSource.shared_store].
    updates. apply DHear; [exact AB|].
    apply (Deliver _ _ _ _ _ _ _ show_bool [] [gdata]); [constructor|reflexivity].
  - intros r H. cbn [s2 s3 source positions].
    unfold cs3. rewrite cursor_other by congruence. reflexivity.
  - exact step3.
Qed.
Lemma pair4 : paired_step model roles result s3 t3 gs3 sa4 s4 la4 t4 [].
Proof.
  eapply PairStep with (p := B) (pre := [Endpoint _ A na2]) (post := [])
    (t := nb1) (t' := nb2).
  - right. now left.
  - cbn [t3 net assembled endpoints roles List.map entry]. updates. reflexivity.
  - cbn [t4 net assembled endpoints roles List.map entry]. updates. reflexivity.
  - cbn [s3 s4 source positions deliveries DeadlockSource.shared_store].
    updates. apply DReceive; [exact AB|].
    apply delivery_singleton. reflexivity.
  - intros r H. cbn [s3 s4 source positions].
    unfold cs4. rewrite cursor_other by congruence. reflexivity.
  - exact step4.
Qed.

Lemma prefix1 : matched_prefix model stores tt roles result program
  [sa1] s1 [la1] t1 gs1.
Proof.
  change (matched_prefix model stores tt roles result program
    ([] ++ [sa1]) s1 ([] ++ [la1]) t1 gs1).
  eapply PrefixSnoc; [apply PrefixInitial|exact pair1|exact state1].
Qed.
Lemma prefix2 : matched_prefix model stores tt roles result program
  [sa1;sa2] s2 [la1;la2] t2 gs2.
Proof.
  eapply (PrefixSnoc _ _ _ _ _ _ [sa1] s1 [la1] t1 gs1);
    [exact prefix1|exact pair2|exact state2].
Qed.
Lemma prefix3 : matched_prefix model stores tt roles result program
  [sa1;sa2;sa3] s3 [la1;la2;la3] t3 gs3.
Proof.
  eapply (PrefixSnoc _ _ _ _ _ _ [sa1;sa2] s2 [la1;la2] t2 gs2);
    [exact prefix2|exact pair3|exact state3].
Qed.
Lemma prefix4 : matched_prefix model stores tt roles result program
  [sa1;sa2;sa3;sa4] s4 [la1;la2;la3;la4] t4 [].
Proof.
  eapply (PrefixSnoc _ _ _ _ _ _ [sa1;sa2;sa3] s3 [la1;la2;la3] t3 gs3);
    [exact prefix3|exact pair4|exact state4].
Qed.

Example positive_between_sends_and_receives :
  DeadlockMatch.matches model stores tt roles result program [sa1;sa2] s2 [la1;la2] t2 /\
  mailboxes t2 (A,B,tag) = [truth;unit_wire].
Proof. split; [exists gs2; exact prefix2|exact fifo2]. Qed.

Example complete_repaired_match :
  DeadlockMatch.matches model stores tt roles result program
    [sa1;sa2;sa3;sa4] s4 [la1;la2;la3;la4] t4.
Proof. exists []. exact prefix4. Qed.

Example repaired_final : nfinal sm t4.
Proof.
  split.
  - cbn [t4 net assembled roles List.map entry endpoints].
    updates. constructor.
    + eexists. apply administrative_returns.
      unfold na2. apply AdminApp with
        (g := fun z : result A => z) (x := @off_at unit B A BA).
      * eapply AdminBind; apply AdminPure.
      * apply AdminPure.
    + constructor.
      * eexists. eapply ReturnBind; apply ReturnPure.
      * constructor.
  - exact (proj2 (proj1 (proj2 state4))).
Qed.

Example source_final : cfinal sm roles s4.
Proof.
  split; [reflexivity|].
  intros p [<-|[<-|F]]; [| |contradiction];
    cbn [s4 source positions]; updates; eexists; apply Returns.
Qed.

Example actual_machine_four_actions :
  run sm roles t0 [la1;la2;la3;la4] t4 /\ nfinal sm t4.
Proof.
  split; [|exact repaired_final].
  exact (prefix_network_run model stores tt roles result program _ _ _ _ _ prefix4).
Qed.

Example positive_after_choice_receive :
  DeadlockMatch.matches model stores tt roles result program
    [sa1;sa2;sa3] s3 [la1;la2;la3] t3 /\
  mailboxes t3 (A,B,tag) = [unit_wire].
Proof. split; [exists gs3; exact prefix3|reflexivity]. Qed.

(* Negative tests inspect the actual generated receiver, independently of
   matches. An undecodable FIFO head cannot be skipped or consumed. *)
Lemma generated_choice_receive q st obs u q' st' :
  step sm roles B (result B) (n0 B) q st obs u q' st' ->
  exists w ws x, q (A,B,tag) = w :: ws /\
    @read bool read_bool w = Some x /\ obs = Received A B tag w.
Proof.
  intro H. apply view_of_step in H.
  cbn [step_view] in H.
  destruct H as [(v & [(z & F & Inner)|(sid & Ret & P)] & Outer)| (x & Ret & P)].
  - contradiction.
  - apply returns_view in Ret. change (sid = tag) in Ret. subst sid.
    change (primitive_view sm roles B
      (@Choreography.Network.Recv Id bool read_bool tag A) q st obs v q' st') in P.
    destruct P as (w & ws & x & Head & Decode & Obs & Rest).
    exists w,ws,x. auto.
  - apply returns_view in Ret. cbn [return_view] in Ret.
    destruct Ret as (sid & R & Recv).
    apply returns_view in R. change (sid = tag) in R. subst sid.
    apply returns_view in Recv. change False in Recv. contradiction.
Qed.

Definition swapped := replace_queue q2 (A,B,tag) [unit_wire;truth].
Example swapped_head_cannot_explain_choice u q st :
  ~ step sm roles B (result B) (n0 B) swapped (stores,tt) la3 u q st.
Proof.
  intro H. destruct (generated_choice_receive _ _ _ _ _ _ H)
    as (w & ws & x & Head & Decode & Obs).
  change ([unit_wire;truth] = w :: ws) in Head.
  injection Head as <- Tail. discriminate Decode.
Qed.

Definition wrong_tag := Choreography.Network.Nest (Data.Either.Left tt) tag.
Definition mistagged := enqueue empty_queues (A,B,wrong_tag) truth.
Example wrong_tag_does_not_enable_generated_receive u q st :
  ~ step sm roles B (result B) (n0 B) mistagged (stores,tt) la3 u q st.
Proof.
  intro H. destruct (generated_choice_receive _ _ _ _ _ _ H)
    as (w & ws & x & Head & Decode & Obs).
  discriminate Head.
Qed.

Example invented_branch_is_not_a_receive u q st :
  ~ step sm roles B (result B) (n0 B) q2 (stores,tt)
    (Received A B tag (@show bool show_bool false)) u q st.
Proof.
  intro H. destruct (generated_choice_receive _ _ _ _ _ _ H)
    as (w & ws & x & Head & Decode & Obs).
  rewrite fifo2 in Head. injection Head as <- Tail. discriminate Obs.
Qed.

Lemma generated_owner_announcement q st obs u q' st' :
  step sm roles A (result A) (n0 A) q st obs u q' st' -> obs = la1.
Proof.
  intro H. apply view_of_step in H. cbn [step_view] in H.
  destruct H as [(v & [(z & F & Inner)|(sid & Ret & P)] & Outer)| (x & Ret & P)].
  - contradiction.
  - apply returns_view in Ret. change (sid = tag) in Ret. subst sid.
    change (primitive_view sm roles A
      (@Choreography.Network.BCast Id bool show_bool tag true) q st obs v q' st') in P.
    exact (proj1 P).
  - apply returns_view in Ret. cbn [return_view] in Ret.
    destruct Ret as (sid & R & Cast).
    apply returns_view in R. change (sid = tag) in R. subst sid.
    apply returns_view in Cast. change False in Cast. contradiction.
Qed.

Lemma roles_nodup : NoDup roles.
Proof.
  constructor.
  - intros [Eq|F]; [exact (BA Eq)|contradiction].
  - constructor; [intro F; contradiction|constructor].
Qed.

Lemma only_initial_action obs n : nstep sm roles t0 obs n -> obs = la1.
Proof.
  intro H.
  destruct (roster_step sm roles result n0 empty_queues (stores,tt) obs n
    roles_nodup H) as (p & u & q & st & Member & Step & Target).
  destruct Member as [<-|[<-|F]].
  - eapply generated_owner_announcement. exact Step.
  - destruct (generated_choice_receive _ _ _ _ _ _ Step)
      as (w & ws & x & Head & Decode & Obs). discriminate Head.
  - contradiction.
Qed.

Lemma one_action_match_is_announcement tc s obs n :
  DeadlockMatch.matches model stores tt roles result program tc s [obs] n ->
  obs = la1.
Proof.
  intros [gs H].
  pose proof (prefix_network_run model stores tt roles result program _ _ _ _ _ H) as Run.
  inversion Run; subst. eapply only_initial_action. eassumption.
Qed.

Example wrong_tag_prefix_rejected :
  ~ DeadlockMatch.matches model stores tt roles result program
    [sa1] s1 [Announced A wrong_tag truth] t1.
Proof.
  intro H. apply one_action_match_is_announcement in H. discriminate H.
Qed.

Example invented_choice_prefix_rejected :
  ~ DeadlockMatch.matches model stores tt roles result program
    [sa1] s1 [Announced A tag (@show bool show_bool false)] t1.
Proof.
  intro H. apply one_action_match_is_announcement in H. discriminate H.
Qed.

(* The queue effect is obtained from real constructors; this detects a
   swapped final FIFO even when both action histories are left untouched. *)
Definition wire_effect (obs : @action NoEvent ((role -> unit) * unit)) q q' :=
  match obs with
  | DeadlockNetwork.Local _ => q' = q
  | Sent p r sid w => q' = enqueue q (p,r,sid) w
  | Announced p sid w => q' = announce roles p sid w q
  | Received p r sid w => exists ws, q (p,r,sid) = w :: ws /\
      q' = replace_queue q (p,r,sid) ws
  end.
Lemma step_wire_effect p X t q st obs u q' st' :
  step sm roles p X t q st obs u q' st' -> wire_effect obs q q'.
Proof.
  induction 1; cbn [wire_effect]; eauto.
Qed.
Lemma network_wire_effect n obs n' :
  nstep sm roles n obs n' -> wire_effect obs (mailboxes n) (mailboxes n').
Proof. destruct 1. cbn. eapply step_wire_effect. eassumption. Qed.

Lemma two_send_queue n :
  run sm roles t0 [la1;la2] n -> mailboxes n = q2.
Proof.
  intro H. inversion H; subst.
  match goal with
  | H : run _ _ _ [la2] _ |- _ => inversion H; subst; clear H
  end.
  match goal with
  | H : run _ _ _ [] _ |- _ => inversion H; subst; clear H
  end.
  apply network_wire_effect in H3.
  change (mailboxes u = q1) in H3.
  match goal with
  | H : nstep _ _ _ la2 _ |- _ =>
      apply network_wire_effect in H; cbn [wire_effect la2] in H;
      rewrite H
  end.
  unfold q2. f_equal. assumption.
Qed.

Example swapped_fifo_prefix_rejected :
  ~ DeadlockMatch.matches model stores tt roles result program
    [sa1;sa2] s2 [la1;la2] (net ns2 swapped).
Proof.
  intros [gs H].
  pose proof (prefix_network_run model stores tt roles result program _ _ _ _ _ H) as Run.
  pose proof (two_send_queue _ Run) as Queues.
  pose proof (f_equal (fun q => q (A,B,tag)) Queues) as Head.
  change ([unit_wire;truth] = [truth;unit_wire]) in Head.
  discriminate Head.
Qed.

Print Assumptions complete_repaired_match.
Print Assumptions actual_machine_four_actions.
Print Assumptions source_final.
Print Assumptions positive_between_sends_and_receives.
Print Assumptions swapped_head_cannot_explain_choice.
Print Assumptions wrong_tag_does_not_enable_generated_receive.
Print Assumptions invented_branch_is_not_a_receive.
Print Assumptions wrong_tag_prefix_rejected.
Print Assumptions invented_choice_prefix_rejected.
Print Assumptions swapped_fifo_prefix_rejected.
End RepairMatch.
