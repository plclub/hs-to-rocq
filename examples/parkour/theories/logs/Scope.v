From Stdlib Require Import Lists.List.
Require Import DeadlockLocalLog DeadlockChronology DeadlockEnteredOrigin
  DeadlockRootOrigin DeadlockPast DeadlockReplay DeadlockCoherence
  DeadlockObservedCut DeadlockSource DeadlockLocal DeadlockPlayedValues
  DeadlockMessages DeadlockNetwork DeadlockState Parkour.Symbol
    Choreography.Choreo2.
Import ListNotations.

Section Scope.
Context {M E Store Input} (model : local_model M E role (Store * Input))
  (stores : role -> Store) (input : Input) (R : list role)
  (A : role -> Type) (c : forall p, Choreo M p (A p)).
Local Notation sm := (shared_model model).
Local Notation entry := (observed_entry model stores input R A c).
Local Notation log := (actor_log model stores input R A c).
Local Notation stamp := (stamped model stores input R A c).
Local Notation site := (entry_site model stores input R A c).

Lemma entry_forall_snoc p (P : entry p -> Prop) tr e :
  Forall P tr -> P e -> Forall P (tr ++ [e]).
Proof. intros H He; induction H; cbn; constructor; auto. Qed.

Lemma micro_focus p B t tok u :
  micro sm p (entry p) (stamp p) B t tok u ->
  (tok = None /\ silent sm B t u) \/
  exists X (C : @cursor_context M E p X B) f e g,
    tok = Some e /\ t = plug C f /\ u = plug C g /\ stamp p X f e g.
Proof.
  induction 1.
  - left; split; [reflexivity|now apply primitive_is_silent].
  - right; exists B, ContextHole, t, token, u; auto.
  - destruct IHmicro as [[-> Hs]|(Z & C & focus & e & g & -> & -> & -> & Hs)].
    + left; split; [reflexivity|now apply SSeqUnder].
    + right; exists Z, (ContextSeq o k C), focus, e, g; auto.
  - destruct IHmicro as [[-> Hs]|(Z & C & focus & e & after & -> & -> & -> &
    Hs)].
    + left; split; [reflexivity|now apply SForkLeft].
    + right; exists Z, (ContextLeft t C), focus, e, after; auto.
  - destruct IHmicro as [[-> Hs]|(Z & C & focus & e & after & -> & -> & -> &
    Hs)].
    + left; split; [reflexivity|now apply SForkRight].
    + right; exists Z, (ContextRight f C), focus, e, after; auto.
Qed.

Lemma actor_log_history p B start tr (t : @cursor M E p B) :
  log p B start tr t ->
  exists actions, cursor_history sm R start actions t.
Proof.
  induction 1 as [|tr t tok u Prior IH Step].
  - exists []; constructor.
  - destruct IH as [actions Hist].
    destruct (micro_focus _ _ _ _ _ Step)
      as [[_ Sil]|(X & C & f & e & g & _ & -> & -> & [Prim Obs])].
    + eexists; eapply history_after_silent; eassumption.
    + eexists; eapply HistoryAction; eassumption.
Qed.

Lemma actor_log_scoped p B start tr (t : @cursor M E p B) root :
  log p B start tr t -> scoped root start -> scoped root t.
Proof.
  induction 1 as [|tr t tok u Prior IH Step]; intro Scope; [exact Scope|].
  specialize (IH Scope).
  destruct (micro_focus _ _ _ _ _ Step)
    as [[_ Sil]|(X & C & f & e & g & _ & -> & -> & [Prim Obs])].
  - eapply silent_scoped; eassumption.
  - eapply role_scoped; [apply role_step_plug; apply primitive_is_role_step;
    exact Prim|exact IH].
Qed.

Lemma primitive_entry_site p B (f : @cursor M E p B) e g :
  stamp p B f e g ->
  action_path (entry_action model stores input R A c p e) = site p e.
Proof.
  intros [Prim _].
  pose proof (entry_primitive model stores input R A c p e) as Actual.
  unfold entry_site, event_route.
  destruct Actual; reflexivity.
Qed.

Lemma actor_log_scope p B root (code : Choreo M p B) tr t :
  log p B (Code root code) tr t ->
  Forall (fun e => DeadlockChronology.extends root (site p e)) tr /\ scoped root
    t.
Proof.
  intro Hist. split.
  - remember (Code root code) as start in Hist.
    assert (Init : scoped root start) by (subst; apply extends_refl).
    clear Heqstart code.
    induction Hist as [|tr t tok u Prior IH Step]; [constructor|].
    destruct (micro_focus _ _ _ _ _ Step)
      as [[-> Sil]|(X & C & f & e & g & -> & -> & -> & Stamp)].
    + exact IH.
    + cbn [snoc_token]. apply entry_forall_snoc; [exact IH|].
      rewrite <- (primitive_entry_site _ _ _ _ _ Stamp).
      pose proof (role_step_plug sm R _ _ _ C _ _ _ _ _ _ _
        (primitive_is_role_step sm R _ _ _ _ _ _ _ _ _ (proj1 Stamp))) as Act.
      eapply scoped_future.
      * eapply actor_log_scoped; eassumption.
      * exact (proj2 (role_future sm R _ _ _ _ _ _ _ _ _ Act)).
  - eapply actor_log_scoped; [exact Hist|apply extends_refl].
Qed.

Lemma actor_log_token p B start tr (t : @cursor M E p B) e :
  log p B start tr t -> In e tr ->
  exists prior X (C : @cursor_context M E p X B) f g,
    log p B start prior (plug C f) /\ stamp p X f e g.
Proof.
  intros Hist; induction Hist as [|tr t tok u Prior IH Step]; intro Member;
    [contradiction|].
  destruct tok as [token|].
  - cbn [snoc_token] in Member.
    assert (Split : In e tr \/ e = token).
    { clear -Member. revert tr Member. fix IHtr 1.
      intros [|x xs] Member; cbn in *.
      - destruct Member as [Eq|[]]; right; symmetry; exact Eq.
      - destruct Member as [EqHead|Member]; [left; left; exact EqHead|].
        destruct (IHtr xs Member) as [Old|Eq]; [left; now right|now right]. }
    destruct Split as [Old | EqToken]; [exact (IH Old)|].
    subst token.
    destruct (micro_focus _ _ _ _ _ Step)
      as [[Bad _]|(X & C & f & found & g & Eq & -> & _ & Stamp)];
      [discriminate|].
    injection Eq as Eq; subst found. exists tr, X, C, f, g; auto.
  - exact (IH Member).
Qed.

(* Observe the packed typed node through its operand and packet. No equality
   between hidden result types is extracted from the origin certificate. *)
Theorem actor_log_produced_here p B root (code : Choreo M p B) tr t e
    kind d operand :
  log p B (Code root code) tr t -> In e tr ->
  In (Produced kind root p d operand)
    (entry_batch model stores input R A c p e) ->
  sender_operand code = Some operand /\
  outgoing code root d = event_packet (Produced kind root p d operand).
Proof.
  intros Hist Member Produced.
  destruct (actor_log_token _ _ _ _ _ _ Hist Member)
    as (prior & X & C & f & g & Prior & [Prim Obs]).
  destruct (actor_log_history _ _ _ _ _ Prior) as [actions History].
  pose proof (entered_history_origin sm R p B root code _ _ History) as Origin.
  pose proof (relative_plug p B root code _ _ C _ Origin) as AtFocus.
  destruct (observed_production_focus sm R _ _ _ _ _ _ _ _ _ _ _ _ _ Obs
    _ _ _ _ _ Produced)
    as (Y & D & before & after & Sil & Act & End & Site).
  assert (Rel : relative_cursor p B root code before).
  { assert (Mid : relative_cursor p B root code (plug D before)).
    { clear -AtFocus Sil. induction Sil; [exact AtFocus|].
      apply IHSil. eapply relative_silent; eassumption. }
    eapply relative_plug; exact Mid. }
  pose proof (focus_packet R _ _ _ _ Site) as Packet.
  destruct (sender_site_operand R _ _ _ _ _ _ _ _ Site)
    as [_ [original [Eq Operand]]].
  subst before. cbn [relative_cursor relative_node] in Rel.
  destruct Rel as (path & Eq & Desc).
  assert (Empty : path = []).
  { apply app_inv_head with (l := root).
    rewrite <- Eq, app_nil_r; reflexivity. }
  subst path. specialize (Desc []).
  cbn in Desc.
  assert (Static : DeadlockStaticOrigin.static_path []).
  { split; intro Bad; contradiction. }
  specialize (Desc Static).
  split.
  - pose proof (f_equal
      (fun node : option { T : Type & Choreo M p T } =>
         match node with Some (existT _ _ term) => sender_operand term
         | None => None end) Desc) as Same.
    cbn in Same. now rewrite <- Same.
  - pose proof (f_equal
      (fun node : option { T : Type & Choreo M p T } =>
         match node with Some (existT _ _ term) => outgoing term root d
         | None => None end) Desc) as Same.
    cbn in Same. cbn in Packet. now rewrite <- Same.
Qed.

Corollary actor_log_message_here p B root (code : Choreo M p B) tr t e
    X kind d (v : X) sh :
  log p B (Code root code) tr t -> In e tr ->
  In (Produced kind root p d (Operand X sh v))
    (entry_batch model stores input R A c p e) ->
  outgoing code root d = Some (Message X kind root p d v sh).
Proof.
  intros Hist Member Produced.
  exact (proj2 (actor_log_produced_here _ _ _ _ _ _ _ _ _ _
    Hist Member Produced)).
Qed.
End Scope.

Print Assumptions actor_log_scope.
Print Assumptions actor_log_produced_here.
Print Assumptions actor_log_message_here.
