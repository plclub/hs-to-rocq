From Stdlib Require Import Lists.List Strings.String.
From Stdlib Require NArith.BinNat.
From ITree Require ITree.
Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree
  Choreography.Choreo2 Choreography.Network
  DeadlockLocal DeadlockRuns DeadlockSource DeadlockNetwork
  DeadlockWellFormed DeadlockProjectionExpect DeadlockProjection
  DeadlockMutationExpect.
Import ListNotations.

(* These mutations are fixtures, not alternate source or endpoint semantics. *)
Module Mutation.
Import MutationExpect.

Lemma source_well_formed : well_formed [A; B] Id _ family.
Proof.
  split.
  - constructor; [cbn; intuition discriminate |].
    constructor; [cbn; tauto | constructor].
  - eexists. eapply WFComm with
      (x := fun p _ => payload p)
      (sh := fun _ _ => show_unit) (rd := fun _ _ => read_unit).
    + cbn; auto.
    + cbn; auto.
    + intros. intros []; reflexivity.
    + reflexivity.
Qed.

(* Concrete EPP equations are proved from the generated local equations. *)
Definition sender := load (E := no_event) (runner (family A) Root).
Definition receiver sid := load (E := no_event) (runner (family B) sid).
Definition net (o : @control Id no_event (At unit B A))
    (b : @control Id no_event (At unit B B)) q
    : @DeadlockNetwork.configuration Id no_event unit :=
  {| endpoints := [Endpoint _ A o; Endpoint _ B b];
     mailboxes := q; DeadlockNetwork.shared_store := tt |}.
Definition initial := net sender (receiver Root) empty_queues.
Definition bytes := GHC.Base.hs_string__ "()".
Definition sent_queue := enqueue empty_queues (A,B,Root) bytes.
Lemma AB : A <> B.
Proof. discriminate. Qed.
Lemma BA : B <> A.
Proof. discriminate. Qed.
Definition sender_done : @control Id no_event (At unit B A) :=
  CApp (CBind (CPure tt) (fun _ => CPure (fun v : At unit B A => v)))
    (CPure (absent (X := unit) BA)).
Definition receiver_done : @control Id no_event (At unit B B) := CBind (CPure tt)
  (fun v => CPure (@Mk_At unit B B (fun _ => v))).

Lemma sender_equation :
  sender = CBind (CPure Root) (fun sid =>
    CApp (CBind (CPerf (@Send Id unit show_unit sid tt B))
      (fun _ => CPure (fun v : At unit B A => v)))
      (CPure (absent (X := unit) BA))).
Proof.
  unfold sender, family.
  rewrite (runner_comm_sender Id A B unit show_unit read_unit
    (known A) (known B) (payload A) BA Root).
  reflexivity.
Qed.
Lemma receiver_equation sid :
  receiver sid = CBind (CPure sid) (fun tag =>
    CBind (CPerf (@Recv Id unit read_unit tag A))
      (fun v => CPure (@Mk_At unit B B (fun _ => v)))).
Proof.
  unfold receiver, family.
  rewrite (runner_comm_receiver Id A B unit show_unit read_unit
    (known A) (known B) (payload B) AB sid).
  reflexivity.
Qed.

Lemma send_correct :
  nstep model [A;B] initial (Sent A B Root bytes)
    (net sender_done (receiver Root) sent_queue).
Proof.
  unfold initial, net. rewrite sender_equation.
  eapply Schedule with (pre := []) (post := [_]).
  eapply StepContinue; [apply ReturnPure |].
  apply StepLeft. apply StepBind. apply StepSend.
Qed.
Lemma receive_correct :
  nstep model [A;B] (net sender_done (receiver Root) sent_queue)
    (Received A B Root bytes)
    (net sender_done receiver_done
      (replace_queue sent_queue (A,B,Root) [])).
Proof.
  unfold net. rewrite receiver_equation.
  eapply Schedule with (pre := [_]) (post := []).
  eapply StepContinue; [apply ReturnPure |].
  apply StepBind. eapply StepRecv with (x := tt).
  - reflexivity.
  - reflexivity.
Qed.
Lemma correct_final :
  nfinal model (net sender_done receiver_done
    (replace_queue sent_queue (A,B,Root) [])).
Proof.
  split.
  - constructor.
    + eexists. eapply ReturnApp.
      * eapply ReturnBind; apply ReturnPure.
      * apply ReturnPure.
    + constructor; [| constructor].
      eexists. eapply ReturnBind; apply ReturnPure.
  - intro k. cbn. unfold sent_queue, enqueue, replace_queue, empty_queues.
    destruct (key_eq_dec k (A,B,Root)); reflexivity.
Qed.
Theorem generated_communicates :
  exists n, run model [A;B] initial
    [Sent A B Root bytes; Received A B Root bytes] n /\ nfinal model n.
Proof.
  eexists. split; [| apply correct_final].
  eapply RunCons; [apply send_correct |].
  eapply RunCons; [apply receive_correct | apply RunNil].
Qed.

Definition wrong_sid := Nest (Data.Either.Left tt) Root.
Definition wrong_initial := net sender (receiver wrong_sid) empty_queues.
Definition wrong_residual := net sender_done (receiver wrong_sid) sent_queue.
Definition omitted_sender : @DeadlockNetwork.configuration Id no_event unit :=
  {| endpoints := [Endpoint _ B (receiver Root)];
     mailboxes := empty_queues; DeadlockNetwork.shared_store := tt |}.

Lemma wrong_run :
  run model [A;B] wrong_initial [Sent A B Root bytes] wrong_residual.
Proof.
  eapply RunCons; [|apply RunNil].
  unfold wrong_initial, wrong_residual, net. rewrite sender_equation.
  eapply Schedule with (pre := []) (post := [_]).
  eapply StepContinue; [apply ReturnPure |].
  apply StepLeft. apply StepBind. apply StepSend.
Qed.

Lemma sender_done_impossible q s : ~ possible model A sender_done q s.
Proof.
  cbn. intros [[H | [x [H Hfalse]]] | H]; contradiction.
Qed.

Lemma receiver_impossible sid q s :
  q (A,B,sid) = [] -> ~ possible model B (receiver sid) q s.
Proof.
  intros Hq. rewrite receiver_equation. cbn.
  intros [H | [x [Hr [H | [y [Hy _]]]]]]; try contradiction.
  - assert (Hx : x = sid).
    { generalize Hr.
      assert (K : forall X (t : @control Id no_event X) y,
        returns model X t y ->
        (match t in control T return T -> Prop with
         | CPure v => fun z => v = z
         | _ => fun _ => True end) y).
      { intros X t y HK. induction HK; cbn; auto. }
      intro HK. symmetry. exact (K _ _ _ HK). }
    destruct H as [w [ws [v [H _]]]].
    rewrite Hx in H. change (q (A,B,sid) = w :: ws) in H.
    rewrite Hq in H. discriminate.
  - apply returns_shape in Hy. exact Hy.
Qed.

Theorem wrong_stuck :
  stuck (nstep model [A;B]) (nfinal model) wrong_residual.
Proof.
  split.
  - eapply orphan_not_final with (k := (A,B,Root)) (w := bytes) (ws := []).
    reflexivity.
  - intros a n H. apply nstep_possible in H.
    change (possible model A sender_done sent_queue tt \/
      possible model B (receiver wrong_sid) sent_queue tt \/ False) in H.
    destruct H as [H | [H | H]]; [eapply sender_done_impossible; exact H | | contradiction].
    eapply receiver_impossible; [| exact H]. reflexivity.
Qed.

Theorem omitted_stuck :
  stuck (nstep model [B]) (nfinal model) omitted_sender.
Proof.
  split.
  - intros [H _]. inversion H as [|e es He Hrest]; subst.
    destruct He as [x Hx]. rewrite receiver_equation in Hx.
    assert (K : forall X (t : @control Id no_event X) y,
      returns model X t y ->
      (match t in control T return T -> Prop with
       | CBind u k => fun z => exists v,
           returns model _ u v /\ returns model _ (k v) z
       | _ => fun _ => True end) y).
    { intros X t y HK. induction HK; cbn; eauto. }
    destruct (K _ _ _ Hx) as [tag [_ Hr]].
    destruct (K _ _ _ Hr) as [v [Hrecv _]].
    apply returns_shape in Hrecv. exact Hrecv.
  - intros a n H. apply nstep_possible in H.
    change (possible model B (receiver Root) empty_queues tt \/ False) in H.
    destruct H as [H | H]; [| contradiction].
    exact (receiver_impossible Root empty_queues tt eq_refl H).
Qed.

(* A proof over actual source cursors, including every cstep interleaving. *)
Definition terminal {p X} (t : @cursor Id no_event p X) : Prop :=
  match t with Returned _ => True | _ => False end.
Definition active {p X} (t : @cursor Id no_event p X) : Prop :=
  match t with
  | Code _ (Perf (@Comm _ _ _ l r _ _ _ _ _ _ _)) =>
      l <> r /\ (l = p \/ r = p)
  | _ => False
  end.
Definition comm_effect {p X} (t : @cursor Id no_event p X) q q' : Prop :=
  match t with
  | Code o (Perf (@Comm _ _ T l r _ _ _ _ _ v _)) =>
      (exists pf : l = p, r <> p /\
        q' = q ++ [Pending T DataDelivery o l r (unAt v pf)]) \/
      (l <> p /\ r = p /\
        exists x : T, take_at DataDelivery o l r x q q')
  | _ => False
  end.

Lemma silent_not_active p X (t u : @cursor Id no_event p X) :
  silent model X t u -> ~ active t.
Proof.
  intros H. destruct H; cbn; intuition congruence.
Qed.
Lemma silent_not_terminal p X (t u : @cursor Id no_event p X) :
  silent model X t u -> ~ terminal t.
Proof. intros H. destruct H; cbn; tauto. Qed.
Lemma step_not_terminal p X (t u : @cursor Id no_event p X) s q a s' q' :
  role_step model [A;B] X t s q a u s' q' -> ~ terminal t.
Proof.
  intros H. induction H; cbn; try tauto.
  eapply silent_not_terminal; eassumption.
Qed.
Lemma step_comm_effect p X (t u : @cursor Id no_event p X) s q a s' q' :
  role_step model [A;B] X t s q a u s' q' ->
  active t -> terminal u /\ comm_effect t q q'.
Proof.
  intros H. induction H; cbn; try tauto.
  - intros _. split; [exact I |]. left. exists eq_refl. auto.
  - intros _. split; [exact I |]. right. eauto.
  - intro Ha. exfalso. eapply silent_not_active; eassumption.
Qed.

Definition packet := Pending unit DataDelivery [] A B tt.
Lemma sender_source_step u s q a s' q' :
  role_step model [A;B] (At unit B A)
    (Code [] (family A)) s q a u s' q' ->
  terminal u /\ q' = q ++ [packet].
Proof.
  intros H. apply step_comm_effect in H.
  - destruct H as [Ht [[pf [_ Hq]] | [Hbad _]]].
    + split; [exact Ht | exact Hq].
    + contradiction.
  - split; [exact AB | auto].
Qed.
Lemma receiver_source_step u s q a s' q' :
  role_step model [A;B] (At unit B B)
    (Code [] (family B)) s q a u s' q' ->
  terminal u /\ exists x : unit,
    take_at DataDelivery [] A B x q q'.
Proof.
  intros H. apply step_comm_effect in H.
  - destruct H as [Ht [[pf _] | [_ [_ Hq]]]].
    + exact (False_rect _ (AB pf)).
    + auto.
  - split; [exact AB | auto].
Qed.
Lemma take_empty X k o s d (x : X) q' :
  ~ take_at k o s d x [] q'.
Proof. intro H; inversion H. Qed.
Lemma take_singleton (x : unit) q' :
  take_at DataDelivery [] A B x [packet] q' -> q' = [].
Proof.
  intros H. inversion H; subst; [reflexivity |].
  exfalso. eapply take_empty; eassumption.
Qed.

Local Notation pos := (DeadlockSource.positions (fun p => At unit B p)).
Local Notation queue := (DeadlockSource.deliveries (fun p => At unit B p)).
Definition state (c : @DeadlockSource.configuration Id no_event unit
    (fun p => At unit B p)) : Prop :=
  (pos c A = Code [] (family A) /\
   pos c B = Code [] (family B) /\ queue c = []) \/
  (terminal (pos c A) /\
   pos c B = Code [] (family B) /\ queue c = [packet]) \/
  (terminal (pos c A) /\
   terminal (pos c B) /\ queue c = []).

Lemma state_preserved c a c' :
  state c -> cstep model [A;B] c a c' -> state c'.
Proof.
  intros Hstate Hstep. destruct Hstep as [p a c' Hp Hact Hframe].
  change (A = p \/ B = p \/ False) in Hp.
  destruct Hp as [Hp | [Hp | Hp]]; [subst p | subst p | contradiction].
  - assert (HB : pos c B = pos c' B) by (apply Hframe; exact BA).
    destruct Hstate as [[HA [HB0 Hq]] | [[HA [HB0 Hq]] | [HA [HB0 Hq]]]].
    + rewrite HA, Hq in Hact.
      destruct (sender_source_step _ _ _ _ _ _ Hact) as [Ht Hq'].
      cbn in Hq'.
      right; left. split; [exact Ht |]. split; congruence.
    + exfalso. exact (step_not_terminal _ _ _ _ _ _ _ _ _ Hact HA).
    + exfalso. exact (step_not_terminal _ _ _ _ _ _ _ _ _ Hact HA).
  - assert (HA : pos c A = pos c' A) by (apply Hframe; exact AB).
    destruct Hstate as [[HA0 [HB Hq]] | [[HA0 [HB Hq]] | [HA0 [HB Hq]]]].
    + rewrite HB, Hq in Hact.
      destruct (receiver_source_step _ _ _ _ _ _ Hact) as [_ [x Htake]].
      exfalso. eapply take_empty; exact Htake.
    + rewrite HB, Hq in Hact.
      destruct (receiver_source_step _ _ _ _ _ _ Hact) as [Ht [x Htake]].
      right; right. split; [rewrite <- HA; exact HA0 |].
      split; [exact Ht | exact (take_singleton x _ Htake)].
    + exfalso. exact (step_not_terminal _ _ _ _ _ _ _ _ _ Hact HB).
Qed.

Definition update (c : @DeadlockSource.configuration Id no_event unit
    (fun p => At unit B p)) p (t : @cursor Id no_event p (At unit B p)) r :=
  match symbol_eq_dec p r with
  | left e => eq_rect p (fun r => @cursor Id no_event r (At unit B r)) t r e
  | right _ => pos c r
  end.
Lemma update_same c p t : update c p t p = t.
Proof.
  unfold update. destruct (symbol_eq_dec p p) as [e | H].
  - rewrite (symbol_uip p p e eq_refl). reflexivity.
  - contradiction.
Qed.
Lemma update_other c p t r : r <> p -> update c p t r = pos c r.
Proof.
  intros H. unfold update. destruct (symbol_eq_dec p r); [congruence | reflexivity].
Qed.
Lemma commit c p t' s' q' a :
  In p [A;B] ->
  role_step model [A;B] (At unit B p) (pos c p)
    (DeadlockSource.shared_store _ c) (queue c) a t' s' q' ->
  exists c', cstep model [A;B] c a c'.
Proof.
  intros Hp H.
  exists (@DeadlockSource.Config Id no_event unit _
    (update c p t') s' q').
  eapply CStep with (p := p); [exact Hp | |].
  - cbn. rewrite update_same. exact H.
  - intros r Hr. cbn. symmetry. apply update_other. exact Hr.
Qed.

Lemma terminal_returns p X (t : @cursor Id no_event p X) :
  terminal t -> exists x, DeadlockSource.returns model t x.
Proof.
  destruct t; cbn; intros H; try contradiction.
  eexists. apply Returns.
Qed.
Lemma state_ready c :
  state c ->
  ready (cstep model [A;B]) (cfinal model [A;B]) c.
Proof.
  intros [[HA [HB Hq]] | [[HA [HB Hq]] | [HA [HB Hq]]]].
  - right. exists (SendAction unit [] A B tt).
    eapply commit with (p := A); [cbn; auto |].
    rewrite HA. apply RSend with (h := BA).
  - right. exists (ReceiveAction unit [] A B tt).
    eapply commit with (p := B); [cbn; auto |].
    rewrite HB, Hq. eapply RReceive; [exact AB | apply TakeAtHead].
  - left. split; [exact Hq |].
    intros p Hp. change (A = p \/ B = p \/ False) in Hp.
    destruct Hp as [Hp | [Hp | Hp]];
      [subst p; apply terminal_returns; exact HA |
       subst p; apply terminal_returns; exact HB | contradiction].
Qed.

Theorem source_DF :
  DF (cstep model [A;B]) (cfinal model [A;B]) source_initial.
Proof.
  intros tr c Hrun. apply state_ready.
  assert (K : forall c0 tr c,
    crun model [A;B] c0 tr c -> state c0 -> state c).
  { intros c0 tr0 c1 H. induction H; intro Hi; [exact Hi |].
    eapply state_preserved; [apply IHfinite_run; exact Hi | exact H0]. }
  eapply K; [exact Hrun |].
  left. repeat split; reflexivity.
Qed.

(* The original, fully configured source has no stuck reachable explanation
   for either fixture's target deadlock. *)
Theorem no_source_explanation tr c :
  crun model [A;B] source_initial tr c ->
  ~ stuck (cstep model [A;B]) (cfinal model [A;B]) c.
Proof.
  intros H. eapply DF_no_stuck; [exact source_DF | exact H].
Qed.

Theorem frozen_wf : MutationExpect.wf_contract.
Proof. exact source_well_formed. Qed.
Theorem frozen_source_df : MutationExpect.source_df_contract.
Proof. exact source_DF. Qed.
Theorem frozen_correct : MutationExpect.correct_contract.
Proof. exact generated_communicates. Qed.
Theorem frozen_wrong : MutationExpect.wrong_contract.
Proof.
  exists wrong_residual. split; [exact wrong_run |].
  split; [reflexivity |]. split; [reflexivity | exact wrong_stuck].
Qed.
Theorem frozen_omitted : MutationExpect.omitted_contract.
Proof. split; [apply RunNil | exact omitted_stuck]. Qed.
Theorem frozen_no_explanation : MutationExpect.no_explanation_contract.
Proof. exact no_source_explanation. Qed.
Theorem frozen_wrong_progress : MutationExpect.wrong_progress_contract.
Proof.
  intros n Hrun Hstuck trace c Hsource Htransfer.
  apply (proj1 (stuck_iff_not_ready _ _ n) Hstuck).
  apply Htransfer. exact (source_DF trace c Hsource).
Qed.
Theorem frozen_omitted_progress : MutationExpect.omitted_progress_contract.
Proof.
  intros trace c Hsource Htransfer.
  apply (proj1 (stuck_iff_not_ready _ _ omitted_sender) omitted_stuck).
  apply Htransfer. exact (source_DF trace c Hsource).
Qed.

End Mutation.
