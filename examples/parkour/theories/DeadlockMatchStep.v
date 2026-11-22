From Stdlib Require Import Lists.List Logic.Eqdep_dec.
Require Import DeadlockMatch DeadlockAlignment DeadlockMessages DeadlockOrder
  DeadlockSource DeadlockNetwork DeadlockRoster DeadlockState DeadlockLocal
  DeadlockStepView DeadlockEnabled Parkour.Symbol Parkour.Codec Control.Monad.Tree.
Require Import DeadlockProjectionExpect.
Require Choreography.Choreo2.
Import ListNotations.
Local Notation At := Choreography.Choreo2.At.
Local Notation unAt := Choreography.Choreo2.unAt.
Local Notation Choreo := Choreography.Choreo2.Choreo.

(* A safety statement about successful receives, not an assertion that any
   receive can execute. The dictionary is the exposed receiver's dictionary;
   delivery selects the sender dictionary already stored in the ghost list. *)
Definition receive_at X kind o sender receiver (rd : Read X)
    (q : queues) (gs : list message) : Prop :=
  forall w ws x,
    q (sender,receiver,session_at o Choreography.Network.Root) = w :: ws ->
    @read X rd w = Some x ->
    exists (sh : Show X) pre post,
      gs = pre ++ Message X kind o sender receiver x sh :: post /\
      Forall (fun g => message_key g <>
        (sender,receiver,session_at o Choreography.Network.Root)) pre /\
      @show X sh x = w.

(* Turn only the raw head/occurrence/codec facts into the operational ghost
   removal. The existential dictionary above must occur in the actual gs. *)
Lemma receive_delivery X kind o sender receiver (x : X) rd q gs w ws :
  receive_at X kind o sender receiver rd q gs ->
  q (sender,receiver,session_at o Choreography.Network.Root) = w :: ws ->
  @read X rd w = Some x ->
  exists gs', delivery X kind o sender receiver x rd gs w gs'.
Proof.
  intros Safe Head Decode.
  destruct (Safe w ws x Head Decode) as (sh & pre & post & G & Front & Wire).
  exists (pre ++ post). subst gs w. apply Deliver; assumption.
Qed.

Lemma delivery_represents X kind o sender receiver (x : X) rd gs w gs' q ws :
  represents (map pending_of gs) q gs ->
  delivery X kind o sender receiver x rd gs w gs' ->
  q (sender,receiver,session_at o Choreography.Network.Root) = w :: ws ->
  represents (map pending_of gs')
    (replace_queue q (sender,receiver,session_at o Choreography.Network.Root) ws) gs'.
Proof.
  intros Rep Del Head. destruct Del as [sh pre post Front Decode].
  destruct (represents_consume pre
    (Message X kind o sender receiver x sh) post _ q Rep Front) as [H R].
  cbn [message_key message_wire] in H, R.
  rewrite Head in H. injection H as Tail.
  rewrite Tail. exact R.
Qed.

Section Endpoint.
Context {M E : Type -> Type} {S : Type}.
Variable model : local_model M E role S.
Variable R : list role.

Fixpoint receive_safety p X c n
    (a : aligned model Choreography.Network.Root p X c n)
    (q : queues) (gs : list message) : Prop.
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
  - exact (receive_safety _ _ _ _ Ha q gs).
  - exact (receive_safety _ _ _ _ Ha q gs /\
      forall x, DeadlockSource.returns model t x ->
        receive_safety _ _ _ _ (Hcont x) q gs).
  - exact (receive_safety _ _ _ _ HaF q gs /\
           receive_safety _ _ _ _ HaT q gs).
  - exact (receive_safety _ _ _ _ Ha q gs).
  - exact True.
  - exact True.
  - exact True.
  - exact (receive_at X DataDelivery o l p rd q gs).
  - exact True.
  - exact (receive_at X ChoiceDelivery o l p rd q gs).
Defined.

Lemma empty_receive_safety p X c n
    (Ha : aligned model Choreography.Network.Root p X c n) gs :
  receive_safety p X c n Ha empty_queues gs.
Proof.
  induction Ha; cbn [receive_safety]; try exact I; try tauto.
  - split; [exact IHHa|]. intros x _. apply H.
  - unfold receive_at, empty_queues. intros w ws x Head. discriminate.
  - unfold receive_at, empty_queues. intros w ws x Head. discriminate.
Qed.

Lemma decorated_seq_returns p X Y o (t : @cursor M E p X)
    (k : X -> Choreo M p Y) x s gs sa t' s' gs' na :
  DeadlockSource.returns model t x ->
  decorated model R Y (Code (child o BindBody) (k x)) s (map pending_of gs)
    sa t' s' (map pending_of gs') na gs gs' ->
  decorated model R Y (Seq o t k) s (map pending_of gs)
    sa t' s' (map pending_of gs') na gs gs'.
Proof.
  intro H. induction H; intro D.
  - eapply DSilent; [apply SSeq|exact D].
  - eapply DSilent; [apply SSeqUnder; exact H|apply IHreturns; exact D].
Qed.

(* Reflect a GIVEN arbitrary endpoint action. All transport and residual
   certificates in the conclusion are constructed, not supplied as premises. *)
Theorem aligned_decorated_step p X c n
    (Ha : aligned model Choreography.Network.Root p X c n)
    q s gs na n' q' s' :
  receive_safety p X c n Ha q gs ->
  represents (map pending_of gs) q gs ->
  step_view model R p n q s na n' q' s' ->
  exists sa c' gs',
    decorated model R X c s (map pending_of gs)
      sa c' s' (map pending_of gs') na gs gs' /\
    inhabited (aligned model Choreography.Network.Root p X c' n') /\
    represents (map pending_of gs') q' gs'.
Proof.
  revert q s gs na n' q' s'.
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
    intros q s gs na n' q' s' Safe Rep Hv.
  - exfalso. eapply administrative_no_view; eassumption.
  - destruct (IHHa _ _ _ _ _ _ _ Safe Rep Hv)
      as (sa & c' & gs' & D & Al & Re).
    exists sa, c', gs'. split; [eapply DSilent; eassumption|]. auto.
  - cbn [receive_safety] in Safe. destruct Safe as [Safe Body].
    cbn [step_view] in Hv.
    destruct Hv as [(u & Hu & ->) | (x & Hr & Hk)].
    + destruct (IHHa _ _ _ _ _ _ _ Safe Rep Hu)
        as (sa & c' & gs' & D & [Al] & Re).
      exists sa, (Seq o c' k), gs'. split; [apply DSeq; exact D|].
      split; [constructor; apply AlignSeq; assumption|exact Re].
    + pose proof (aligned_returns _ _ _ _ _ _ _ Ha Hr) as SourceReturn.
      destruct (IHcont x _ _ _ _ _ _ _ (Body x SourceReturn) Rep Hk)
        as (sa & c' & gs' & D & Al & Re).
      exists sa, c', gs'. split.
      * eapply decorated_seq_returns; eassumption.
      * auto.
  - cbn [receive_safety] in Safe. destruct Safe as [SafeF SafeT].
    cbn [step_view] in Hv.
    destruct Hv as [(u & Hu & ->) | (u & Hu & ->)].
    + destruct (IHF _ _ _ _ _ _ _ SafeF Rep Hu)
        as (sa & c' & gs' & D & [Al] & Re).
      exists sa, (Fork c' t), gs'. split; [apply DLeft; exact D|].
      split; [constructor; apply AlignFork; assumption|exact Re].
    + destruct (IHT _ _ _ _ _ _ _ SafeT Rep Hu)
        as (sa & c' & gs' & D & [Al] & Re).
      exists sa, (Fork f c'), gs'. split; [apply DRight; exact D|].
      split; [constructor; apply AlignFork; assumption|exact Re].
  - cbn [receive_safety] in Safe.
    cbn [step_view] in Hv.
    destruct Hv as [(u & Hu & _) | (z & Hr & Hk)].
    + exfalso. eapply administrative_no_view; eassumption.
    + pose proof (administrative_unique _ _ _ _ _ H Hr). subst z.
      exact (IHHa _ _ _ _ _ _ _ Safe Rep Hk).
  - cbn [step_view primitive_view] in Hv.
    destruct Hv as [(u & (la & t' & Hl & -> & -> & ->) & ->) |
                   (x & _ & Hfalse)]; [|contradiction].
    exists (LocalAction o la), (DeadlockSource.Local o t'), gs.
    split; [apply DLocal; exact Hl|].
    split; [constructor; apply AlignLocal|exact Rep].
  - cbn [step_view] in Hv.
    destruct Hv as [(u & (la & t' & Hl & -> & -> & ->) & ->) |
                   (x & _ & Hfalse)]; [|contradiction].
    exists (LocalAction o la), (DeadlockSource.Local o t'), gs.
    split; [apply DLocal; exact Hl|].
    split; [constructor; apply AlignLocal|exact Rep].
  - cbn [step_view primitive_view] in Hv.
    destruct Hv as [(u & Hfalse & _) | (tag & Htag & Hv)]; [contradiction|].
    apply returns_view in Htag. cbn [return_view] in Htag. subst tag.
    destruct Hv as [(u & Hv & ->) | (u & Hfalse & _)]; [|contradiction].
    destruct Hv as [(u0 & (-> & -> & -> & ->) & ->) |
                   (x & _ & Hfalse)]; [|contradiction].
    exists (SendAction X o p d (unAt v eq_refl)), (Returned (off_at neq)),
      (gs ++ [Message X DataDelivery o p d (unAt v eq_refl) sh]).
    split; [apply DSend|]. split.
    + constructor. apply AlignReturned.
      eapply AdminApp with (g := fun z : At X d p => z) (x := off_at neq).
      * eapply AdminBind; apply AdminPure.
      * apply AdminPure.
    + rewrite map_app. cbn. apply represents_send. exact Rep.
  - cbn [receive_safety] in Safe.
    cbn [step_view primitive_view] in Hv.
    destruct Hv as [(u & Hfalse & _) | (tag & Htag & Hv)]; [contradiction|].
    apply returns_view in Htag. cbn [return_view] in Htag. subst tag.
    destruct Hv as [(u & (w & ws & x & Head & Read & -> & -> & -> & ->) & ->) |
                   (x & _ & Hfalse)]; [|contradiction].
    destruct (receive_delivery _ _ _ _ _ _ _ _ _ _ _ Safe Head Read) as [gs' Del].
    exists (ReceiveAction X o l p x), (Returned (here_at x)), gs'.
    split; [apply DReceive; [exact neq|exact Del]|]. split.
    + constructor. apply AlignReturned. eapply AdminBind; apply AdminPure.
    + eapply delivery_represents; eassumption.
  - cbn [step_view primitive_view] in Hv.
    destruct Hv as [(u & Hv & ->) | (x & Hr & _)].
    + destruct Hv as [(u0 & Hfalse & _) | (tag & Htag & Hv)]; [contradiction|].
      apply returns_view in Htag. cbn [return_view] in Htag. subst tag.
      destruct Hv as (-> & -> & -> & ->).
      exists (AnnounceAction X o p (unAt v eq_refl)),
        (Code (child o ChoiceBody) (k (unAt v eq_refl))),
        (gs ++ announcement_messages X o p (unAt v eq_refl) sh R).
      split; [apply DAnnounce|]. split.
      * constructor. eapply AlignAdministrative; [apply AdminPure|apply Hcont].
      * rewrite map_app, announcement_pending. apply represents_announcement. exact Rep.
    + apply returns_result in Hr. cbn [result_of] in Hr.
      destruct Hr as [tag [_ Hfalse]]. contradiction.
  - cbn [receive_safety] in Safe.
    cbn [step_view primitive_view] in Hv.
    destruct Hv as [(u & Hv & ->) | (x & Hr & _)].
    + destruct Hv as [(u0 & Hfalse & _) | (tag & Htag & Hv)]; [contradiction|].
      apply returns_view in Htag. cbn [return_view] in Htag. subst tag.
      destruct Hv as (w & ws & x & Head & Read & -> & -> & -> & ->).
      destruct (receive_delivery _ _ _ _ _ _ _ _ _ _ _ Safe Head Read) as [gs' Del].
      exists (HearAction X o l p x), (Code (child o ChoiceBody) (k x)), gs'.
      split; [eapply DHear; [exact neq|exact Del]|]. split.
      * constructor. eapply AlignAdministrative; [apply AdminPure|apply Hcont].
      * eapply delivery_represents; eassumption.
    + apply returns_result in Hr. cbn [result_of] in Hr.
      destruct Hr as [tag [_ Hfalse]]. contradiction.
Qed.

Corollary endpoint_decorated_step p X c n
    (Ha : aligned model Choreography.Network.Root p X c n)
    q s gs na n' q' s' :
  receive_safety p X c n Ha q gs ->
  represents (map pending_of gs) q gs ->
  step model R p X n q s na n' q' s' ->
  exists sa c' gs',
    decorated model R X c s (map pending_of gs)
      sa c' s' (map pending_of gs') na gs gs' /\
    inhabited (aligned model Choreography.Network.Root p X c' n') /\
    represents (map pending_of gs') q' gs'.
Proof.
  intros Safe Rep H. eapply aligned_decorated_step; [exact Safe|exact Rep|].
  apply view_of_step. exact H.
Qed.
End Endpoint.

Section CursorUpdate.
Context {M E : Type -> Type} (A : role -> Type).

Definition set_cursor (f : forall p, @cursor M E p (A p))
    p (u : @cursor M E p (A p)) : forall r, @cursor M E r (A r) :=
  fun r => match role_eq_dec p r with
           | left h => eq_rect p (fun i => @cursor M E i (A i)) u r h
           | right _ => f r
           end.

Lemma cursor_here f p u : set_cursor f p u p = u.
Proof.
  unfold set_cursor; destruct (role_eq_dec p p) as [h|N]; [|contradiction].
  rewrite (UIP_dec role_eq_dec h eq_refl). reflexivity.
Qed.

Lemma cursor_other f p u r : p <> r -> set_cursor f p u r = f r.
Proof. intro N. unfold set_cursor. destruct (role_eq_dec p r); congruence. Qed.
End CursorUpdate.

Section Global.
Context {M E : Type -> Type} {Store Input : Type}.
Variable model : local_model M E role (Store * Input).
Variable R : list role.
Variable A : role -> Type.
Local Notation sm := (shared_model model).
Local Notation SC := (@DeadlockSource.configuration M E ((role -> Store) * Input) A).
Local Notation NC := (@DeadlockNetwork.configuration M E ((role -> Store) * Input)).

(* This adds only exposed-receive safety to a residual alignment witness.
   There is no invariant-preservation, scheduling, or progress clause here. *)
Definition safe_residuals (s : SC) (n : NC) gs : Prop :=
  exists f : forall p, @control M E (A p),
    endpoints n = map (entry A f) R /\
    forall p, In p R ->
      exists Ha : aligned sm Choreography.Network.Root p (A p) (positions s p) (f p),
        receive_safety sm p (A p) (positions s p) (f p) Ha (mailboxes n) gs.

Theorem state_step s n gs na n' :
  NoDup R ->
  state_match model R A s n gs ->
  safe_residuals s n gs ->
  nstep sm R n na n' ->
  exists sa s' gs',
    paired_step model R A s n gs sa s' na n' gs' /\
    state_match model R A s' n' gs'.
Proof.
  intros ND [StoreEq [Rep Residual]] [f [Entries Safe]] Net.
  assert (Assembled : n = assembled R A f (mailboxes n) (DeadlockNetwork.shared_store n)).
  { destruct n as [es q st]. cbn in *. unfold assembled. now rewrite Entries. }
  rewrite Assembled in Net.
  destruct (roster_step sm R A f _ _ na n' ND Net)
    as (p & u & q' & st' & Member & Step & Result).
  destruct (Safe p Member) as [Ha HS].
  assert (RepMap : represents (map pending_of gs) (mailboxes n) gs).
  { split; [reflexivity|exact (proj2 Rep)]. }
  destruct (endpoint_decorated_step sm R p (A p) (positions s p) (f p) Ha
    (mailboxes n) (DeadlockNetwork.shared_store n) gs na u q' st' HS RepMap Step)
    as (sa & cp & gs' & Decor & [Align] & Rep').
  rewrite <- StoreEq in Decor.
  assert (Decor' : decorated sm R (A p) (positions s p)
      (DeadlockSource.shared_store s) (deliveries s) sa cp st'
      (map pending_of gs') na gs gs').
  { rewrite <- (proj1 Rep). exact Decor. }
  set (s' := ({| positions := set_cursor A (positions s) p cp;
                     DeadlockSource.shared_store := st';
                     deliveries := map pending_of gs' |} : SC)).
  exists sa, s', gs'. split.
  - apply in_split in Member. destruct Member as [before [after Roles]].
    eapply PairStep with (p := p)
      (pre := map (entry A f) before) (post := map (entry A f) after)
      (t := f p) (t' := u).
    + rewrite Roles. apply in_or_app. right. now left.
    + transitivity (map (entry A f) R); [exact Entries|].
      rewrite Roles. clear Roles ND Net Entries Safe.
      induction before as [|r before IH]; cbn [List.map List.app entry].
      * reflexivity.
      * f_equal. exact IH.
    + rewrite Result. cbn [assembled].
      rewrite Roles in ND |- *. apply set_entries. exact ND.
    + unfold s'. cbn [positions DeadlockSource.shared_store deliveries].
      rewrite cursor_here. exact Decor'.
    + intros r Ne. unfold s'. cbn [positions].
      rewrite cursor_other by congruence. reflexivity.
    + rewrite Result. cbn [assembled]. exact Step.
  - split.
    + unfold s'. rewrite Result. reflexivity.
    + split.
      * unfold s'. rewrite Result. exact Rep'.
      * exists (set_control A f p u). split.
        -- rewrite Result. reflexivity.
        -- intros r InR. destruct (role_eq_dec p r) as [Eq|Ne].
           ++ subst r. unfold s'. cbn [positions].
              rewrite cursor_here, set_here. constructor. exact Align.
           ++ unfold s'. cbn [positions].
              rewrite cursor_other by exact Ne.
              rewrite set_other by exact Ne.
              destruct (Safe r InR) as [H _]. constructor. exact H.
Qed.

Variable stores : role -> Store.
Variable input : Input.
Variable c : forall p, Choreo M p (A p).

(* An arbitrary actual network step now extends the exact ordered matched
   history. The conclusion includes the constructed source step, residuals,
   and ghost updates; none of them is an input certificate. *)
Theorem matched_prefix_step tc s tn n gs na n' :
  NoDup R ->
  matched_prefix model stores input R A c tc s tn n gs ->
  safe_residuals s n gs ->
  nstep sm R n na n' ->
  exists sa s' gs',
    matched_prefix model stores input R A c
      (tc ++ [sa]) s' (tn ++ [na]) n' gs' /\
    cstep sm R s sa s'.
Proof.
  intros ND Prefix Safe Net.
  destruct (state_step s n gs na n' ND
    (prefix_state model stores input R A c tc s tn n gs Prefix) Safe Net)
    as (sa & s' & gs' & Pair & State).
  exists sa, s', gs'. split.
  - eapply PrefixSnoc; eassumption.
  - eapply paired_source. exact Pair.
Qed.

Lemma initial_safe_residuals :
  safe_residuals (DeadlockMatch.source_initial stores input A c)
    (DeadlockMatch.network_initial stores input R A c) [].
Proof.
  exists (fun p => load (runner (c p) Choreography.Network.Root)).
  split; [reflexivity|]. intros p _.
  exists (generated_initial_alignment sm Choreography.Network.Root p (A p) (c p)).
  apply empty_receive_safety.
Qed.

(* Unconditional reflection of every actual INITIAL action: the safety
   certificate is proved here from empty queues, not required from a caller. *)
Theorem initial_prefix_step na n' :
  NoDup R ->
  nstep sm R (DeadlockMatch.network_initial stores input R A c) na n' ->
  exists sa s' gs',
    matched_prefix model stores input R A c
      [sa] s' [na] n' gs' /\
    cstep sm R (DeadlockMatch.source_initial stores input A c) sa s'.
Proof.
  intros ND Net.
  exact (matched_prefix_step [] _ [] _ [] na n' ND
    (PrefixInitial model stores input R A c) initial_safe_residuals Net).
Qed.
End Global.
