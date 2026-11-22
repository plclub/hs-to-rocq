From Stdlib Require Import Lists.List.
From ITree Require Import ITree.
Require Import DeadlockLocal DeadlockSource DeadlockNetwork DeadlockEnabled DeadlockStepView DeadlockOrder DeadlockProjection
  DeadlockProjectionExpect Parkour.Symbol Parkour.Codec Control.Monad.Tree.
Require Choreography.Choreo2.
Import Choreography.Network.
Local Notation Choreo := Choreography.Choreo2.Choreo.
Local Notation At := Choreography.Choreo2.At.
Local Notation unAt := Choreography.Choreo2.unAt.
Local Notation Comm := Choreography.Choreo2.Comm.
Local Notation Cond := Choreography.Choreo2.Cond.
Import ListNotations.

(* A concrete, finite administrative fragment. In particular Exec, Send and
   Recv cannot be hidden here, even if a surrounding continuation ignores them. *)
Section Alignment.
Context {M E : Type -> Type} {Store : Type}.
Variable model : local_model M E Symbol Store.

Inductive administrative : forall X, @control M E X -> X -> Prop :=
| AdminPure X (x : X) : administrative X (CPure x) x
| AdminBind X Y t (k : X -> @control M E Y) x y :
    administrative X t x -> administrative Y (k x) y ->
    administrative Y (CBind t k) y
| AdminApp X Y f t (g : X -> Y) x :
    administrative (X -> Y) f g -> administrative X t x ->
    administrative Y (CApp f t) (g x).

(* The session is an index of code, not an approximation of its occurrence.
   App changes both indices; Bind and choice change only the source occurrence.
   Every continuation below is the actual source/target continuation. *)
Variable root_session : SessionId.

Inductive aligned (p : Symbol) :
    forall X, @cursor M E p X -> @control M E X -> Type :=
| AlignReturned X (x : X) n :
    administrative X n x -> aligned p X (Returned x) n
| AlignSilent X t u n :
    silent model X t u -> aligned p X u n -> aligned p X t n
| AlignSeq X Y o t n (k : X -> Choreo M p Y) j :
    aligned p X t n ->
    (forall x, aligned p Y (Code (child o BindBody) (k x)) (j x)) ->
    aligned p Y (Seq o t k) (CBind n j)
| AlignFork X Y f t nf nt :
    aligned p (X -> Y) f nf -> aligned p X t nt ->
    aligned p Y (Fork f t) (CApp nf nt)
| AlignAdministrative X Y (c : @cursor M E p Y) n
    (k : X -> @control M E Y) x :
    administrative X n x -> aligned p Y c (k x) ->
    aligned p Y c (CBind n k)
| AlignExec X o (e : M X) :
    aligned p (At X p p)
      (DeadlockSource.Local o (interpret_local _ _ _ _ model X e))
      (CBind (CPerf (Exec e)) (fun x => CPure (here_at x)))
| AlignLocal X o (t : itree E X) :
    aligned p (At X p p) (DeadlockSource.Local o t)
      (CBind (CLocal t) (fun x => CPure (here_at x)))
| AlignSend X d o sh rd kl kd v (neq : d <> p) :
    aligned p (At X d p)
      (Code o (Perf (@Comm M p X p d sh rd kl kd MkSSymbol v MkSSymbol)))
      (CBind (CPure (session_at o root_session)) (fun tag =>
        CApp (CBind (CPerf (@Send M X sh tag (unAt v eq_refl) d))
                   (fun _ => CPure (fun z : At X d p => z)))
             (CPure (off_at neq))))
| AlignReceive X l o sh rd kl kd v (neq : l <> p) :
    aligned p (At X p p)
      (Code o (Perf (@Comm M p X l p sh rd kl kd MkSSymbol v MkSSymbol)))
      (CBind (CPure (session_at o root_session)) (fun tag =>
        CBind (CPerf (@Recv M X rd tag l))
              (fun x => CPure (here_at x))))
| AlignAnnounce X Y o sh rd kl v (k : X -> Choreo M p Y) j :
    (forall x, aligned p Y (Code (child o ChoiceBody) (k x)) (j x)) ->
    aligned p Y
      (Code o (Perf (@Cond M p X p Y sh rd kl MkSSymbol v k)))
      (CBind (CBind (CPure (session_at o root_session))
                   (fun tag => CPerf (@BCast M X sh tag (unAt v eq_refl))))
             (fun _ => j (unAt v eq_refl)))
| AlignHear X Y l o sh rd kl v (k : X -> Choreo M p Y)
    (neq : l <> p) j :
    (forall x, aligned p Y (Code (child o ChoiceBody) (k x)) (j x)) ->
    aligned p Y
      (Code o (Perf (@Cond M p X l Y sh rd kl MkSSymbol v k)))
      (CBind (CBind (CPure (session_at o root_session))
                   (fun tag => CPerf (@Recv M X rd tag l))) j).

Lemma absent_off X l p (h : l <> p) :
  @absent X l p h = off_at h.
Proof.
  unfold absent, off_role, off_at.
  destruct (decide (@MkSSymbol l) (@MkSSymbol p)) as [e | d].
  - contradiction.
  - reflexivity.
Qed.

Definition tree_alignment p
    (primitive : forall X (e : Choreography.Choreo2.ChoreoSig M p X) o,
      aligned p X (Code o (Perf e))
        (load (runner (Perf e) (session_at o root_session))))
    X (c : Choreo M p X) o :
    aligned p X (Code o c) (load (runner c (session_at o root_session))).
Proof.
  revert o.
  induction c as [X e | X x | X Y f IHf t IHt | X Y t IHt k IHk];
    intros o.
  - apply primitive.
  - rewrite runner_pure. cbn [load].
    eapply AlignSilent; [apply SPure |]. apply AlignReturned. apply AdminPure.
  - rewrite runner_app. cbn [load].
    eapply AlignSilent; [apply SApp |].
    apply AlignFork.
    + rewrite <- (session_at_child o AppFunction root_session). apply IHf.
    + rewrite <- (session_at_child o AppArgument root_session). apply IHt.
  - rewrite runner_bind. cbn [load].
    eapply AlignSilent; [apply SBind |].
    apply AlignSeq.
    + rewrite <- (session_at_child o BindPrefix root_session). apply IHt.
    + intros x. rewrite <- (session_at_child o BindBody root_session). apply IHk.
Defined.

Definition primitive_alignment p X (e : Choreography.Choreo2.ChoreoSig M p X) o :
  aligned p X (Code o (Perf e))
    (load (runner (Perf e) (session_at o root_session))).
Proof.
  revert X e o.
  fix IH 2. intros X e o.
  set (sid := session_at o root_session).
  destruct e as [X l kl sl body | X l d sh rd kl kd sl v sd |
                   X l Y sh rd kl sl v k].
    + destruct sl. destruct (symbol_eq_dec l p) as [eq | neq].
      * subst l. fold (@Choreography.Choreo2.locally p p M X kl MkSSymbol body).
        rewrite runner_locally_owner. cbn [load].
        eapply AlignSilent; [apply SLocalStart |]. apply AlignExec.
      * fold (@Choreography.Choreo2.locally l p M X kl MkSSymbol body).
        rewrite (runner_locally_other M l p X kl body neq sid).
        rewrite absent_off. cbn [load].
        eapply AlignSilent; [apply SLocalOther |].
        apply AlignReturned. apply AdminPure.
    + destruct sl, sd.
      destruct (symbol_eq_dec l d) as [eq | distinct].
      * subst d. rewrite runner_comm_self. cbn [load].
        eapply AlignSilent; [apply SCommSelf |].
        apply AlignReturned. apply AdminPure.
      * destruct (symbol_eq_dec l p) as [eq | ns].
        -- subst l.
           assert (nr : d <> p) by congruence.
           rewrite (runner_comm_sender M p d X sh rd kl kd v nr sid).
           rewrite absent_off. cbn [load]. apply AlignSend.
        -- destruct (symbol_eq_dec d p) as [eq | nr].
           ++ subst d.
              rewrite (runner_comm_receiver M l p X sh rd kl kd v ns sid).
              cbn [load]. apply AlignReceive. exact ns.
           ++ rewrite (runner_comm_other M l d p X sh rd kl kd v distinct ns nr sid).
              rewrite absent_off. cbn [load].
              eapply AlignSilent; [eapply SCommOther; eassumption |].
              apply AlignReturned. apply AdminPure.
    + destruct sl. destruct (symbol_eq_dec l p) as [eq | neq].
      * subst l. rewrite runner_cond_owner. cbn [load].
        apply (AlignAnnounce p X Y o sh rd kl v k
                 (fun x => load (runner (k x) sid))).
        intros x. unfold sid.
        rewrite <- (session_at_child o ChoiceBody root_session).
        apply (tree_alignment p IH).
      * rewrite (runner_cond_peer M l p X Y sh rd kl v k neq sid).
        cbn [load]. apply AlignHear; [exact neq |].
        intros x. unfold sid.
        rewrite <- (session_at_child o ChoiceBody root_session).
        apply (tree_alignment p IH).
Defined.

Theorem initial_alignment p X o (c : Choreo M p X) :
  aligned p X (Code o c) (load (runner c (session_at o root_session))).
Proof. exact (tree_alignment p (primitive_alignment p) X c o). Qed.

Lemma administrative_returns X n (x : X) :
  administrative X n x -> DeadlockNetwork.returns model X n x.
Proof.
  intros H. induction H.
  - apply ReturnPure.
  - eapply ReturnBind; eassumption.
  - eapply ReturnApp; eassumption.
Qed.

(* These views eliminate indexed derivations without dependent destruction,
   equality reflection, or UIP for arbitrary result types. *)
Definition return_view X (n : @control M E X) : X -> Prop :=
  match n in control Y return Y -> Prop with
  | CPure x => fun y => y = x
  | CPerf e =>
      match e in NetworkSig _ Y return Y -> Prop with
      | Exec e => fun y => local_return (interpret_local _ _ _ _ model _ e) y
      | _ => fun _ => False
      end
  | CLocal t => fun y => local_return t y
  | CBind t k => fun y =>
      exists x, DeadlockNetwork.returns model _ t x /\
                DeadlockNetwork.returns model _ (k x) y
  | CApp f t => fun y =>
      exists g x, DeadlockNetwork.returns model _ f g /\
                  DeadlockNetwork.returns model _ t x /\ y = g x
  end.

Lemma returns_view X n (x : X) :
  DeadlockNetwork.returns model X n x -> return_view X n x.
Proof. intros H. destruct H; cbn [return_view]; eauto. Qed.

Lemma administrative_unique X n (x y : X) :
  administrative X n x -> DeadlockNetwork.returns model X n y -> y = x.
Proof.
  intros H Hr. eapply return_unique; [exact Hr |].
  apply administrative_returns. exact H.
Qed.

Lemma source_seq_returns p X Y o (t : @cursor M E p X)
    (k : X -> Choreo M p Y) x y :
  DeadlockSource.returns model t x ->
  DeadlockSource.returns model (Code (child o BindBody) (k x)) y ->
  DeadlockSource.returns model (Seq o t k) y.
Proof.
  intros H. induction H; intros Hk.
  - eapply ReturnsSilent; [apply SSeq | exact Hk].
  - eapply ReturnsSilent; [apply SSeqUnder; exact H |].
    exact (IHreturns Hk).
Qed.

Lemma source_fork_returns p X Y (f : @cursor M E p (X -> Y)) t g x :
  DeadlockSource.returns model f g ->
  DeadlockSource.returns model t x ->
  DeadlockSource.returns model (Fork f t) (g x).
Proof.
  intros Hf. induction Hf; intros Ht.
  - induction Ht.
    + eapply ReturnsSilent; [apply SJoin | apply Returns].
    + eapply ReturnsSilent; [apply SForkRight; exact H | exact IHHt].
  - eapply ReturnsSilent; [apply SForkLeft; exact H | exact (IHHf Ht)].
Qed.

Theorem aligned_returns p X c n (y : X) :
  aligned p X c n ->
  DeadlockNetwork.returns model X n y ->
  DeadlockSource.returns model c y.
Proof.
  intros Ha. revert y.
  induction Ha as
    [X x n H
    | X t u n H Ha IHHa
    | X Y o t n k j Ha IHHa Hcont IHcont
    | X Y f t nf nt HaF IHHa1 HaT IHHa2
    | X Y c n k x H Ha IHHa
    | X o e
    | X o t
    | X d o sh rd kl kd v neq
    | X l o sh rd kl kd v neq
    | X Y o sh rd kl v k j Hcont IHcont
    | X Y l o sh rd kl v k neq j Hcont IHcont];
    intros y Hr.
  - pose proof (administrative_unique _ _ _ _ H Hr). subst y. apply Returns.
  - eapply ReturnsSilent; [exact H | apply IHHa; exact Hr].
  - apply returns_view in Hr. cbn [return_view] in Hr.
    destruct Hr as [x [Ht Hk]].
    eapply source_seq_returns; [apply IHHa; exact Ht | apply IHcont; exact Hk].
  - apply returns_view in Hr. cbn [return_view] in Hr.
    destruct Hr as [g [x [Hf [Ht ->]]]].
    apply source_fork_returns; [apply IHHa1 | apply IHHa2]; assumption.
  - apply returns_view in Hr. cbn [return_view] in Hr.
    destruct Hr as [z [Hn Hk]].
    pose proof (administrative_unique _ _ _ _ H Hn). subst z.
    apply IHHa. exact Hk.
  - apply returns_view in Hr. cbn [return_view] in Hr.
    destruct Hr as [x [He Hr]].
    apply returns_view in He, Hr. cbn [return_view] in He, Hr. subst y.
    eapply ReturnsSilent; [apply SLocalReturn; exact He | apply Returns].
  - apply returns_view in Hr. cbn [return_view] in Hr.
    destruct Hr as [x [He Hr]].
    apply returns_view in He, Hr. cbn [return_view] in He, Hr. subst y.
    eapply ReturnsSilent; [apply SLocalReturn; exact He | apply Returns].
  - apply returns_view in Hr. cbn [return_view] in Hr.
    destruct Hr as [tag [_ Hr]]. apply returns_view in Hr.
    cbn [return_view] in Hr.
    destruct Hr as [g [x [Hsend _]]].
    apply returns_view in Hsend. cbn [return_view] in Hsend.
    destruct Hsend as [z [Hsend _]].
    apply returns_view in Hsend. contradiction Hsend.
  - apply returns_view in Hr. cbn [return_view] in Hr.
    destruct Hr as [tag [_ Hr]]. apply returns_view in Hr.
    cbn [return_view] in Hr. destruct Hr as [x [Hrecv _]].
    apply returns_view in Hrecv. contradiction Hrecv.
  - apply returns_view in Hr. cbn [return_view] in Hr.
    destruct Hr as [z [Hcast _]]. apply returns_view in Hcast.
    cbn [return_view] in Hcast. destruct Hcast as [tag [_ Hcast]].
    apply returns_view in Hcast. contradiction Hcast.
  - apply returns_view in Hr. cbn [return_view] in Hr.
    destruct Hr as [z [Hrecv _]]. apply returns_view in Hrecv.
    cbn [return_view] in Hrecv. destruct Hrecv as [tag [_ Hrecv]].
    apply returns_view in Hrecv. contradiction Hrecv.
Qed.

(* Only actual, currently reachable receive sites impose an obligation.
   This says which typed occurrence a successfully decoded wire delivers.
   It says nothing about readiness, scheduling, or deadlock freedom. *)
Definition delivery_at X kind o sender p (rd : Read X) sid
    (q : queues) (sq : list pending) : Prop :=
  forall w ws x, q (sender,p,sid) = w :: ws ->
    @read X rd w = Some x ->
    exists sq', take_pending kind o sender p x sq sq'.

Fixpoint delivery_consistent p X c n (a : aligned p X c n)
    (q : queues) (sq : list pending) : Prop.
Proof.
  destruct a as
    [X x n H
    | X t u n H Ha
    | X Y o t n k j Ha Hcont
    | X Y f t nf nt HaF HaT
    | X Y c n k x H Ha
    | X o e
    | X o t
    | X d o sh rd kl kd v neq
    | X l o sh rd kl kd v neq
    | X Y o sh rd kl v k j Hcont
    | X Y l o sh rd kl v k neq j Hcont].
  - exact True.
  - exact (delivery_consistent _ _ _ _ Ha q sq).
  - exact (delivery_consistent _ _ _ _ Ha q sq /\
      forall x, DeadlockSource.returns model t x ->
        delivery_consistent _ _ _ _ (Hcont x) q sq).
  - exact (delivery_consistent _ _ _ _ HaF q sq /\
           delivery_consistent _ _ _ _ HaT q sq).
  - exact (delivery_consistent _ _ _ _ Ha q sq).
  - exact True.
  - exact True.
  - exact True.
  - exact (delivery_at X DataDelivery o l p rd (session_at o root_session) q sq).
  - exact True.
  - exact (delivery_at X ChoiceDelivery o l p rd (session_at o root_session) q sq).
Defined.

Lemma empty_delivery_consistent p X c n (Ha : aligned p X c n) sq :
  delivery_consistent p X c n Ha empty_queues sq.
Proof.
  induction Ha; cbn [delivery_consistent]; try exact I; try tauto.
  - split; [exact IHHa |]. intros x _. apply H.
  - unfold delivery_at, empty_queues. intros w ws x Hhead. discriminate.
  - unfold delivery_at, empty_queues. intros w ws x Hhead. discriminate.
Qed.

Corollary generated_initial_alignment p X (c : Choreo M p X) :
  aligned p X (Code [] c) (load (runner c root_session)).
Proof. exact (initial_alignment p X [] c). Qed.

Variable participants : list role.

Lemma administrative_no_action p X n (x : X) q s a n' q' s' :
  administrative X n x -> ~ step model participants p X n q s a n' q' s'.
Proof.
  intro H. apply (return_no_action model participants X n x).
  apply administrative_returns. exact H.
Qed.

Lemma source_seq_step p X Y o (t : @cursor M E p X)
    (k : X -> Choreo M p Y) x s sq a t' s' sq' :
  DeadlockSource.returns model t x ->
  role_step model participants Y (Code (child o BindBody) (k x))
    s sq a t' s' sq' ->
  role_step model participants Y (Seq o t k) s sq a t' s' sq'.
Proof.
  intros H. induction H; intro Hk.
  - eapply RSilent; [apply SSeq | exact Hk].
  - eapply RSilent; [apply SSeqUnder; exact H | exact (IHreturns Hk)].
Qed.

(* Serialization witnesses here are the dictionaries of the exposed syntax.
   Delivery consistency, separately, relates its occurrence to the wire FIFO. *)
Inductive action_matches : @source_action E Store -> @action E Store -> Prop :=
| MatchLocal o la :
    action_matches (LocalAction o la) (DeadlockNetwork.Local la)
| MatchSend X o p r (x : X) (sh : Show X) :
    action_matches (SendAction X o p r x)
      (Sent p r (session_at o root_session) (@show X sh x))
| MatchReceive X o p r (x : X) (rd : Read X) w :
    @read X rd w = Some x ->
    action_matches (ReceiveAction X o p r x)
      (Received p r (session_at o root_session) w)
| MatchAnnounce X o p (x : X) (sh : Show X) :
    action_matches (AnnounceAction X o p x)
      (Announced p (session_at o root_session) (@show X sh x))
| MatchHear X o p r (x : X) (rd : Read X) w :
    @read X rd w = Some x ->
    action_matches (HearAction X o p r x)
      (Received p r (session_at o root_session) w).

Lemma administrative_no_view p X n (x : X) q s a n' q' s' :
  administrative X n x ->
  ~ DeadlockStepView.step_view model participants p n q s a n' q' s'.
Proof.
  intros H Hv. eapply administrative_no_action; [exact H |].
  apply step_of_view. exact Hv.
Qed.

(* A single real endpoint action reflects to a source action, after only
   finite source bookkeeping. The result retains actual local resumptions
   and actual continuation arguments. No scheduling/progress premise occurs. *)
Theorem aligned_step p X c n (Ha : aligned p X c n)
    q s sq na n' q' s' :
  delivery_consistent p X c n Ha q sq ->
  DeadlockStepView.step_view model participants p n q s na n' q' s' ->
  exists sa c' sq',
    role_step model participants X c s sq sa c' s' sq' /\
    action_matches sa na /\ inhabited (aligned p X c' n').
Proof.
  revert q s sq na n' q' s'.
  induction Ha as
    [X x n H
    | X t u n H Ha IHHa
    | X Y o t n k j Ha IHHa Hcont IHcont
    | X Y f t nf nt HaF IHF HaT IHT
    | X Y c n k x H Ha IHHa
    | X o e
    | X o t
    | X d o sh rd kl kd v neq
    | X l o sh rd kl kd v neq
    | X Y o sh rd kl v k j Hcont IHcont
    | X Y l o sh rd kl v k neq j Hcont IHcont];
    intros q s sq na n' q' s' Hco Hv.
  - exfalso. eapply administrative_no_view; eassumption.
  - destruct (IHHa _ _ _ _ _ _ _ Hco Hv)
      as (sa & c' & sq' & Hs & Hm & Hal).
    exists sa, c', sq'. split; [eapply RSilent; eassumption |].
    split; assumption.
  - cbn [delivery_consistent] in Hco. destruct Hco as [Hco Hbody].
    cbn [DeadlockStepView.step_view] in Hv.
    destruct Hv as [(u & Hu & ->) | (x & Hr & Hk)].
    + destruct (IHHa _ _ _ _ _ _ _ Hco Hu)
        as (sa & c' & sq' & Hs & Hm & [Hal]).
      exists sa, (Seq o c' k), sq'. refine (conj _ (conj _ _)).
      * apply RSeq. exact Hs.
      * exact Hm.
      * constructor. apply AlignSeq; assumption.
    + pose proof (aligned_returns _ _ _ _ _ Ha Hr) as Hsource.
      destruct (IHcont x _ _ _ _ _ _ _ (Hbody x Hsource) Hk)
        as (sa & c' & sq' & Hs & Hm & Hal).
      exists sa, c', sq'. split; [eapply source_seq_step; eassumption |].
      split; assumption.
  - cbn [delivery_consistent] in Hco. destruct Hco as [HcoF HcoT].
    cbn [DeadlockStepView.step_view] in Hv.
    destruct Hv as [(u & Hu & ->) | (u & Hu & ->)].
    + destruct (IHF _ _ _ _ _ _ _ HcoF Hu)
        as (sa & c' & sq' & Hs & Hm & [Hal]).
      exists sa, (Fork c' t), sq'. refine (conj _ (conj _ _)).
      * apply RLeft. exact Hs.
      * exact Hm.
      * constructor. apply AlignFork; assumption.
    + destruct (IHT _ _ _ _ _ _ _ HcoT Hu)
        as (sa & c' & sq' & Hs & Hm & [Hal]).
      exists sa, (Fork f c'), sq'. refine (conj _ (conj _ _)).
      * apply RRight. exact Hs.
      * exact Hm.
      * constructor. apply AlignFork; assumption.
  - cbn [delivery_consistent] in Hco.
    cbn [DeadlockStepView.step_view] in Hv.
    destruct Hv as [(u & Hu & _) | (z & Hr & Hk)].
    + exfalso. eapply administrative_no_view; eassumption.
    + pose proof (administrative_unique _ _ _ _ H Hr). subst z.
      exact (IHHa _ _ _ _ _ _ _ Hco Hk).
  - cbn [DeadlockStepView.step_view DeadlockStepView.primitive_view] in Hv.
    destruct Hv as [(u & (la & t' & Hlocal & -> & -> & ->) & ->) |
                    (x & _ & Hfalse)]; [|contradiction].
    exists (LocalAction o la), (DeadlockSource.Local o t'), sq.
    refine (conj _ (conj _ _)).
    + apply RLocal. exact Hlocal.
    + apply MatchLocal.
    + constructor. apply AlignLocal.
  - cbn [DeadlockStepView.step_view] in Hv.
    destruct Hv as [(u & (la & t' & Hlocal & -> & -> & ->) & ->) |
                    (x & _ & Hfalse)]; [|contradiction].
    exists (LocalAction o la), (DeadlockSource.Local o t'), sq.
    refine (conj _ (conj _ _)).
    + apply RLocal. exact Hlocal.
    + apply MatchLocal.
    + constructor. apply AlignLocal.
  - cbn [DeadlockStepView.step_view DeadlockStepView.primitive_view] in Hv.
    destruct Hv as [(u & Hfalse & _) | (tag & Htag & Hv)]; [contradiction|].
    apply returns_view in Htag. cbn [return_view] in Htag. subst tag.
    destruct Hv as [(u & Hv & ->) | (u & Hfalse & _)]; [|contradiction].
    destruct Hv as [(u0 & (-> & -> & -> & ->) & ->) |
                    (x & _ & Hfalse)]; [|contradiction].
    exists (SendAction X o p d (unAt v eq_refl)), (Returned (off_at neq)),
      (sq ++ [Pending X DataDelivery o p d (unAt v eq_refl)]).
    refine (conj _ (conj _ _)).
    + apply RSend.
    + apply MatchSend.
    + constructor. apply AlignReturned.
      eapply AdminApp with (g := fun z : At X d p => z) (x := off_at neq).
      * eapply AdminBind; apply AdminPure.
      * apply AdminPure.
  - cbn [delivery_consistent] in Hco.
    cbn [DeadlockStepView.step_view DeadlockStepView.primitive_view] in Hv.
    destruct Hv as [(u & Hfalse & _) | (tag & Htag & Hv)]; [contradiction|].
    apply returns_view in Htag. cbn [return_view] in Htag. subst tag.
    destruct Hv as [(u & (w & ws & x & Hhead & Hread & -> & -> & -> & ->) & ->) |
                    (x & _ & Hfalse)]; [|contradiction].
    destruct (Hco w ws x Hhead Hread) as [sq' Htake].
    exists (ReceiveAction X o l p x), (Returned (here_at x)), sq'.
    refine (conj _ (conj _ _)).
    + eapply RReceive; [exact neq | apply take_pending_at; exact Htake].
    + eapply MatchReceive. exact Hread.
    + constructor. apply AlignReturned.
      eapply AdminBind; apply AdminPure.
  - cbn [DeadlockStepView.step_view DeadlockStepView.primitive_view] in Hv.
    destruct Hv as [(u & Hv & ->) | (x & Hr & _)].
    + destruct Hv as [(u0 & Hfalse & _) | (tag & Htag & Hv)]; [contradiction|].
      apply returns_view in Htag. cbn [return_view] in Htag. subst tag.
      destruct Hv as (-> & -> & -> & ->).
      exists (AnnounceAction X o p (unAt v eq_refl)),
        (Code (child o ChoiceBody) (k (unAt v eq_refl))),
        (sq ++ announcement participants X o p (unAt v eq_refl)).
      refine (conj _ (conj _ _)).
      * apply RAnnounce.
      * apply MatchAnnounce.
      * constructor. eapply AlignAdministrative; [apply AdminPure | apply Hcont].
    + apply returns_result in Hr. cbn [result_of] in Hr.
      destruct Hr as [tag [_ Hfalse]]. contradiction.
  - cbn [delivery_consistent] in Hco.
    cbn [DeadlockStepView.step_view DeadlockStepView.primitive_view] in Hv.
    destruct Hv as [(u & Hv & ->) | (x & Hr & _)].
    + destruct Hv as [(u0 & Hfalse & _) | (tag & Htag & Hv)]; [contradiction|].
      apply returns_view in Htag. cbn [return_view] in Htag. subst tag.
      destruct Hv as (w & ws & x & Hhead & Hread & -> & -> & -> & ->).
      destruct (Hco w ws x Hhead Hread) as [sq' Htake].
      exists (HearAction X o l p x), (Code (child o ChoiceBody) (k x)), sq'.
      refine (conj _ (conj _ _)).
      * eapply RHear; [exact neq | apply take_pending_at; exact Htake].
      * eapply MatchHear. exact Hread.
      * constructor. eapply AlignAdministrative; [apply AdminPure | apply Hcont].
    + apply returns_result in Hr. cbn [result_of] in Hr.
      destruct Hr as [tag [_ Hfalse]]. contradiction.
Qed.

Corollary network_action_reflects p X c n (Ha : aligned p X c n)
    q s sq na n' q' s' :
  delivery_consistent p X c n Ha q sq ->
  step model participants p X n q s na n' q' s' ->
  exists sa c' sq',
    role_step model participants X c s sq sa c' s' sq' /\
    action_matches sa na /\ inhabited (aligned p X c' n').
Proof.
  intros Hco Hs. eapply aligned_step; [exact Hco |].
  apply view_of_step. exact Hs.
Qed.

Corollary generated_initial_action_reflects p X (c : Choreo M p X)
    s na n' q' s' :
  step model participants p X (load (runner c root_session))
    empty_queues s na n' q' s' ->
  exists sa c' sq',
    role_step model participants X (Code [] c) s [] sa c' s' sq' /\
    action_matches sa na /\ inhabited (aligned p X c' n').
Proof.
  intro Hs. eapply network_action_reflects with
      (Ha := generated_initial_alignment p X c).
  - apply empty_delivery_consistent.
  - exact Hs.
Qed.
End Alignment.
