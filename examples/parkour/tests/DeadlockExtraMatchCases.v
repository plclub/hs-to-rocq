From Stdlib Require Import Lists.List.
From ITree Require ITree.
Require Import DeadlockLocal DeadlockNetwork DeadlockSource DeadlockMatch
  DeadlockMatchStep DeadlockAlignment DeadlockMessages DeadlockOrder
  DeadlockRoster DeadlockState DeadlockProjectionExpect DeadlockProjection
  DeadlockStepView Parkour.Symbol Parkour.Codec Control.Monad.Tree.
Require Choreography.Choreo2.
Import ListNotations.

Module ExtraMatch.
Definition A : Symbol := [].
Definition B : Symbol := [BinNums.N0].
Definition C : Symbol := [BinNums.Npos BinNums.xH].
Definition Id (X : Type) := X.
Definition NoEvent (_ : Type) := Empty_set.
Definition model : local_model Id NoEvent role (unit * unit) :=
  {| interpret_local := fun _ x => ITreeDefinition.Ret x;
     reply_local := fun _ _ _ _ _ _ => False |}.
Definition stores (_ : role) := tt.
Definition sm := shared_model model.
Definition roles := [A;B;C].
Definition tag := Choreography.Network.Root.
Definition truth := @show bool show_bool true.
Definition falsehood := @show bool show_bool false.
Definition payload p b : Choreography.Choreo2.At bool A p :=
  Choreography.Choreo2.Mk_At (fun _ => b).

Lemma roles_nodup : NoDup roles.
Proof.
  repeat constructor; cbn; intuition discriminate.
Qed.

(* The App is in the choreography, not a manually assembled network CApp.
   Either generated branch can send first, using its projected session. *)
Module Parallel.
Definition value p := Choreography.Choreo2.At bool B p.
Definition comm p b : Choreography.Choreo2.Choreo Id p (value p) :=
  Perf (@Choreography.Choreo2.Comm Id p bool A B show_bool read_bool
    (known A) (known B) MkSSymbol (payload p b) MkSSymbol).
Definition left p : Choreography.Choreo2.Choreo Id p (value p -> value p) :=
  Bind (comm p true) (fun _ => Pure (fun x => x)).
Definition program p := App (left p) (comm p false).
Definition controls p : @control Id NoEvent (value p) :=
  load (runner (program p) tag).
Definition initial : @DeadlockNetwork.configuration Id NoEvent
    ((role -> unit) * unit) :=
  DeadlockMatch.network_initial stores tt roles value program.
Definition left_tag := session_at [AppFunction] tag.
Definition right_tag := session_at [AppArgument] tag.
Definition left_action : @action NoEvent ((role -> unit) * unit) :=
  Sent A B left_tag truth.
Definition right_action : @action NoEvent ((role -> unit) * unit) :=
  Sent A B right_tag falsehood.

Lemma generated_left :
  exists u, step sm roles A (value A) (controls A) empty_queues (stores,tt)
    left_action u (enqueue empty_queues (A,B,left_tag) truth) (stores,tt).
Proof.
  unfold controls, program, left, comm. cbn.
  eexists. apply StepLeft. apply StepBind.
  eapply StepContinue; [apply ReturnPure|].
  apply StepLeft. apply StepBind. apply StepSend.
Qed.

Lemma generated_right :
  exists u, step sm roles A (value A) (controls A) empty_queues (stores,tt)
    right_action u (enqueue empty_queues (A,B,right_tag) falsehood) (stores,tt).
Proof.
  unfold controls, program, left, comm. cbn.
  eexists. apply StepRight.
  eapply StepContinue; [apply ReturnPure|].
  apply StepLeft. apply StepBind. apply StepSend.
Qed.

Lemma reflect_initial obs u q :
  step sm roles A (value A) (controls A) empty_queues (stores,tt) obs u q (stores,tt) ->
  exists sa s,
    DeadlockMatch.matches model stores tt roles value program
      [sa] s [obs] (assembled roles value
        (set_control value controls A u) q (stores,tt)).
Proof.
  intro Step.
  assert (Net : nstep sm roles initial obs
    (assembled roles value (set_control value controls A u) q (stores,tt))).
  { apply schedule_role; [exact roles_nodup|now left|exact Step]. }
  destruct (initial_prefix_step model roles value stores tt program obs _
    roles_nodup Net) as (sa & s & gs & Prefix & Source).
  exists sa,s,gs. exact Prefix.
Qed.

Example left_branch_actual_match :
  exists u sa s,
    DeadlockMatch.matches model stores tt roles value program [sa] s
      [left_action] (assembled roles value (set_control value controls A u)
        (enqueue empty_queues (A,B,left_tag) truth) (stores,tt)) /\
    enqueue empty_queues (A,B,left_tag) truth (A,B,right_tag) = [].
Proof.
  destruct generated_left as [u Step].
  destruct (reflect_initial _ _ _ Step) as (sa & s & Match).
  exists u,sa,s. split; [exact Match|reflexivity].
Qed.

Example right_branch_actual_match :
  exists u sa s,
    DeadlockMatch.matches model stores tt roles value program [sa] s
      [right_action] (assembled roles value (set_control value controls A u)
        (enqueue empty_queues (A,B,right_tag) falsehood) (stores,tt)) /\
    enqueue empty_queues (A,B,right_tag) falsehood (A,B,left_tag) = [].
Proof.
  destruct generated_right as [u Step].
  destruct (reflect_initial _ _ _ Step) as (sa & s & Match).
  exists u,sa,s. split; [exact Match|reflexivity].
Qed.

(* A specific negative MATCH, not just inequality of the two session IDs:
   a source send in AppFunction cannot be explained by AppArgument's send. *)
Example cross_branch_match_rejected s n :
  ~ DeadlockMatch.matches model stores tt roles value program
      [SendAction bool [AppFunction;BindPrefix] A B true] s [right_action] n.
Proof.
  intros [gs Prefix].
  pose proof (prefix_action_order model stores tt roles value program
    _ _ _ _ _ Prefix) as Order.
  inversion Order; subst.
  match goal with H : action_matches _ _ _ |- _ => inversion H end.
Qed.

(* Test the actual generated receiver in the right branch. A left-branch
   packet does not enable it, even though sender, receiver and type agree. *)
Example wrong_branch_packet u q st :
  ~ step sm roles B (value B)
    (load (runner (comm B false) right_tag))
    (enqueue empty_queues (A,B,left_tag) truth) (stores,tt)
    (Received A B right_tag truth) u q st.
Proof.
  intro H. apply view_of_step in H. cbn [step_view] in H.
  destruct H as [(v & F & Rest)|(sid & Ret & Inner)].
  - contradiction.
  - apply returns_view in Ret. change (sid = right_tag) in Ret. subst sid.
    destruct Inner as [(v & P & Rest)|(x & Ret & P)].
    + destruct P as (w & ws & x & Head & Tail). discriminate Head.
    + apply returns_view in Ret. contradiction.
Qed.
End Parallel.

(* Self-Comm must retain the exact located value at BOTH the owner and an
   uninvolved role. It has an empty actual match and no network action. *)
Module SelfComm.
Definition value p := Choreography.Choreo2.At bool A p.
Definition program p : Choreography.Choreo2.Choreo Id p (value p) :=
  Perf (@Choreography.Choreo2.Comm Id p bool A A show_bool read_bool
    (known A) (known A) MkSSymbol (payload p true) MkSSymbol).
Definition initial : @DeadlockNetwork.configuration Id NoEvent
    ((role -> unit) * unit) :=
  DeadlockMatch.network_initial stores tt roles value program.

Example actual_empty_match :
  DeadlockMatch.matches model stores tt roles value program []
    (DeadlockMatch.source_initial stores tt value program) [] initial.
Proof. apply initial_matches. Qed.

Example generated_exact_return p :
  runner (program p) tag = Pure (payload p true).
Proof. apply runner_comm_self. Qed.

Example generated_final : nfinal sm initial.
Proof.
  split.
  - change (Forall (fun e => endpoint_final sm e)
      [Endpoint (value A) A (load (runner (program A) tag));
       Endpoint (value B) B (load (runner (program B) tag));
       Endpoint (value C) C (load (runner (program C) tag))]).
    constructor.
    + cbn [endpoint_final]. rewrite generated_exact_return. eexists. apply ReturnPure.
    + constructor.
      * cbn [endpoint_final]. rewrite generated_exact_return. eexists. apply ReturnPure.
      * constructor.
        -- cbn [endpoint_final]. rewrite generated_exact_return. eexists. apply ReturnPure.
        -- constructor.
  - reflexivity.
Qed.

Example fabricated_self_send_rejected s n :
  ~ DeadlockMatch.matches model stores tt roles value program [] s
      [Sent A A tag truth] n.
Proof. apply unequal_lengths_do_not_match. discriminate. Qed.
End SelfComm.

Module Choice.
Definition value (_ : role) := bool.
Definition program p : Choreography.Choreo2.Choreo Id p bool :=
  Perf (@Choreography.Choreo2.Cond Id p bool A bool show_bool read_bool
    (known A) MkSSymbol (payload p true) (fun b => Pure b)).
Definition c0 p : @cursor Id NoEvent p bool := Code [] (program p).
Definition n0 p : @control Id NoEvent bool := load (runner (program p) tag).
Definition ca : @cursor Id NoEvent A bool := Code [ChoiceBody] (Pure true).
Definition cb : @cursor Id NoEvent B bool := Code [ChoiceBody] (Pure true).
Definition na : @control Id NoEvent bool := CBind (CPure tt) (fun _ => CPure true).
Definition nb : @control Id NoEvent bool := CBind (CPure true) (fun x => CPure x).
Definition cs1 := set_cursor value c0 A ca.
Definition cs2 := set_cursor value cs1 B cb.
Definition ns1 := set_control value n0 A na.
Definition ns2 := set_control value ns1 B nb.
Definition gb := Message bool ChoiceDelivery [] A B true show_bool.
Definition gc := Message bool ChoiceDelivery [] A C true show_bool.
Definition gs1 := [gb;gc].
Definition gs2 := [gc].
Definition q1 := announce roles A tag truth empty_queues.
Definition q2 := replace_queue q1 (A,B,tag) [].
Definition source cs gs : @DeadlockSource.configuration Id NoEvent
    ((role -> unit) * unit) value :=
  {| positions := cs; DeadlockSource.shared_store := (stores,tt);
     deliveries := map pending_of gs |}.
Definition net ns q : @DeadlockNetwork.configuration Id NoEvent
    ((role -> unit) * unit) := assembled roles value ns q (stores,tt).
Definition s0 := source c0 [].
Definition s1 := source cs1 gs1.
Definition s2 := source cs2 gs2.
Definition t0 := net n0 empty_queues.
Definition t1 := net ns1 q1.
Definition t2 := net ns2 q2.
Definition sa : @source_action NoEvent ((role -> unit) * unit) :=
  AnnounceAction bool [] A true.
Definition sb : @source_action NoEvent ((role -> unit) * unit) :=
  HearAction bool [] A B true.
Definition la : @action NoEvent ((role -> unit) * unit) := Announced A tag truth.
Definition lb : @action NoEvent ((role -> unit) * unit) := Received A B tag truth.

Ltac updates :=
  unfold cs1, cs2, ns1, ns2;
  repeat first [rewrite cursor_here | rewrite set_here |
    rewrite cursor_other by congruence | rewrite set_other by congruence].

Lemma align_a : aligned sm tag A bool ca na.
Proof.
  eapply AlignAdministrative; [apply AdminPure|].
  eapply AlignSilent; [apply SPure|]. apply AlignReturned. apply AdminPure.
Qed.
Lemma align_b : aligned sm tag B bool cb nb.
Proof.
  eapply AlignAdministrative; [apply AdminPure|].
  eapply AlignSilent; [apply SPure|]. apply AlignReturned. apply AdminPure.
Qed.

Lemma state1 : state_match model roles value s1 t1 gs1.
Proof.
  split; [reflexivity|]. split.
  - exact (represents_announcement bool [] A true show_bool roles
      [] empty_queues [] represents_empty).
  - exists ns1. split; [reflexivity|].
    intros p [<-|[<-|[<-|F]]]; [| | |contradiction];
      constructor; cbn [s1 source positions]; updates.
    + exact align_a.
    + apply initial_alignment.
    + apply initial_alignment.
Qed.

Lemma state2 : state_match model roles value s2 t2 gs2.
Proof.
  split; [reflexivity|]. split.
  - eapply (delivery_represents bool ChoiceDelivery [] A B true read_bool
      gs1 truth gs2 q1 []); [exact (proj1 (proj2 state1))| |reflexivity].
    apply (Deliver _ _ _ _ _ _ _ show_bool [] [gc]); [constructor|reflexivity].
  - exists ns2. split; [reflexivity|].
    intros p [<-|[<-|[<-|F]]]; [| | |contradiction];
      constructor; cbn [s2 source positions]; updates.
    + exact align_a.
    + exact align_b.
    + apply initial_alignment.
Qed.

Lemma pair1 : paired_step model roles value s0 t0 [] sa s1 la t1 gs1.
Proof.
  eapply PairStep with (p := A) (pre := [])
    (post := [Endpoint _ B (n0 B);Endpoint _ C (n0 C)])
    (t := n0 A) (t' := na).
  - now left.
  - reflexivity.
  - cbn [t1 net assembled endpoints roles List.map entry]. updates. reflexivity.
  - cbn [s0 s1 source positions deliveries DeadlockSource.shared_store].
    updates. apply DAnnounce.
  - intros r Ne. cbn [s0 s1 source positions].
    unfold cs1. rewrite cursor_other by congruence. reflexivity.
  - cbn. apply StepBind. eapply StepContinue; [apply ReturnPure|apply StepBCast].
Qed.

Lemma pair2 : paired_step model roles value s1 t1 gs1 sb s2 lb t2 gs2.
Proof.
  eapply PairStep with (p := B) (pre := [Endpoint _ A na])
    (post := [Endpoint _ C (n0 C)]) (t := n0 B) (t' := nb).
  - right. now left.
  - cbn [t1 net assembled endpoints roles List.map entry]. updates. reflexivity.
  - cbn [t2 net assembled endpoints roles List.map entry]. updates. reflexivity.
  - cbn [s1 s2 source positions deliveries DeadlockSource.shared_store].
    updates. apply DHear; [discriminate|].
    apply (Deliver _ _ _ _ _ _ _ show_bool [] [gc]); [constructor|reflexivity].
  - intros r Ne. cbn [s1 s2 source positions].
    unfold cs2. rewrite cursor_other by congruence. reflexivity.
  - cbn. apply StepBind. eapply StepContinue; [apply ReturnPure|].
    eapply StepRecv with (x := true); reflexivity.
Qed.

Lemma prefix1 : matched_prefix model stores tt roles value program [sa] s1 [la] t1 gs1.
Proof.
  change (matched_prefix model stores tt roles value program
    ([] ++ [sa]) s1 ([] ++ [la]) t1 gs1).
  eapply PrefixSnoc; [apply PrefixInitial|exact pair1|exact state1].
Qed.
Lemma prefix2 : matched_prefix model stores tt roles value program
  [sa;sb] s2 [la;lb] t2 gs2.
Proof.
  eapply (PrefixSnoc _ _ _ _ _ _ [sa] s1 [la] t1 gs1);
    [exact prefix1|exact pair2|exact state2].
Qed.

Example multi_peer_pending_match :
  DeadlockMatch.matches model stores tt roles value program [sa;sb] s2 [la;lb] t2 /\
  deliveries s2 = [Pending bool ChoiceDelivery [] A C true] /\
  mailboxes t2 (A,B,tag) = [] /\
  mailboxes t2 (A,C,tag) = [truth] /\
  mailboxes t2 (A,A,tag) = [].
Proof. split; [exists gs2; exact prefix2|]. repeat split; reflexivity. Qed.

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
Proof. induction 1; cbn [wire_effect]; eauto. Qed.
Lemma network_wire_effect n obs n' :
  nstep sm roles n obs n' -> wire_effect obs (mailboxes n) (mailboxes n').
Proof. destruct 1. cbn. eapply step_wire_effect. eassumption. Qed.

Example invented_peer_value_rejected n :
  ~ DeadlockMatch.matches model stores tt roles value program [sa;sb] s2
      [la;Received A B tag falsehood] n.
Proof.
  intros [gs Prefix].
  pose proof (prefix_network_run model stores tt roles value program
    _ _ _ _ _ Prefix) as Run.
  inversion Run; subst.
  match goal with
  | H : nstep _ _ _ la _ |- _ =>
      apply network_wire_effect in H; change (mailboxes u = q1) in H
  end.
  match goal with
  | H : run _ _ _ [Received A B tag falsehood] _ |- _ => inversion H; subst
  end.
  match goal with
  | H : nstep _ _ _ (Received A B tag falsehood) _ |- _ =>
      apply network_wire_effect in H;
      destruct H as (ws & Head & Tail)
  end.
  pose proof (f_equal (fun q => q (A,B,tag)) H2) as Queue.
  change (mailboxes u (A,B,tag) = [truth]) in Queue.
  cbv [role Choreography.Location.LocTm Symbol] in Head, Queue.
  assert (Eq : [truth] = falsehood :: ws) by congruence.
  discriminate Eq.
Qed.

(* One-role Cond is also a genuine action/match, but produces no self-copy. *)
Example singleton_actual_match :
  exists sa' s n,
    DeadlockMatch.matches model stores tt [A] value program [sa'] s [la] n /\
    (forall k, mailboxes n k = []) /\ nfinal sm n.
Proof.
  set (n := assembled [A] value (set_control value n0 A na)
    (announce [A] A tag truth empty_queues) (stores,tt)).
  assert (ND : NoDup [A]) by (constructor; [intro F; contradiction|constructor]).
  assert (Net : nstep sm [A]
    (DeadlockMatch.network_initial stores tt [A] value program) la n).
  { apply schedule_role; [exact ND|now left|].
    cbn. apply StepBind. eapply StepContinue; [apply ReturnPure|apply StepBCast]. }
  destruct (initial_prefix_step model [A] value stores tt program la n ND Net)
    as (sa' & s & gs & Prefix & Source).
  exists sa',s,n. split; [exists gs; exact Prefix|].
  assert (Queues : forall k, mailboxes n k = []) by reflexivity.
  split; [exact Queues|]. split; [|exact Queues].
  change (Forall (endpoint_final sm)
    [Endpoint bool A (set_control value n0 A na A)]).
  rewrite set_here. constructor; [|constructor].
  eexists. eapply ReturnBind; apply ReturnPure.
Qed.
End Choice.
End ExtraMatch.

Print Assumptions ExtraMatch.Parallel.left_branch_actual_match.
Print Assumptions ExtraMatch.Parallel.right_branch_actual_match.
Print Assumptions ExtraMatch.Parallel.cross_branch_match_rejected.
Print Assumptions ExtraMatch.Parallel.wrong_branch_packet.
Print Assumptions ExtraMatch.SelfComm.actual_empty_match.
Print Assumptions ExtraMatch.SelfComm.generated_exact_return.
Print Assumptions ExtraMatch.SelfComm.generated_final.
Print Assumptions ExtraMatch.SelfComm.fabricated_self_send_rejected.
Print Assumptions ExtraMatch.Choice.multi_peer_pending_match.
Print Assumptions ExtraMatch.Choice.invented_peer_value_rejected.
Print Assumptions ExtraMatch.Choice.singleton_actual_match.
