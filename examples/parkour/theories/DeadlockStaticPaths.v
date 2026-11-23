From Stdlib Require Import Lists.List.
Require Import DeadlockStaticOrigin DeadlockSource DeadlockNetwork DeadlockOrder
  DeadlockWellFormed DeadlockLocal DeadlockMatch DeadlockPast DeadlockState
  DeadlockCoherence DeadlockCutSafety DeadlockPlayedValues DeadlockMessages
  Choreography.Choreo2 Control.Monad.Tree Parkour.Symbol.
Import ListNotations.

(* Stop at the first edge whose body depends on a run-time result. No branch
   choice is assumed there. Against a static path this suffices: either their
   first different edges are known or the static path ended at a choice. *)
Fixpoint possible_path {M p A} (path : occurrence) (c : Choreo M p A) : Prop :=
  match path with
  | [] => match c with Perf _ => True | _ => False end
  | edge :: rest =>
    match edge, c with
    | AppFunction, App f _ => possible_path rest f
    | AppArgument, App _ t | BindPrefix, Bind t _ => possible_path rest t
    | BindBody, Bind _ _ | ChoiceBody, Perf (Cond _ _ _) => True
    | _, _ => False end end.

Lemma static_compatible {M p A} path b (c : Choreo M p A) :
  static_path path -> possible_path path c -> possible_path b c -> compatible path b.
Proof.
  revert b A c. induction path as [|e path IH]; intros [|f b] A c Static;
    destruct c; cbn [possible_path]; try contradiction; try solve [constructor].
  all: try destruct e; try destruct f; cbn [possible_path]; try contradiction;
    try match goal with u : ChoreoSig _ _ _ |- _ => destruct u; cbn [possible_path] end;
    try contradiction; intros; try constructor; try assumption;
    try solve [destruct Static as [C B]; cbn in C,B; tauto].
  all: eapply IH; try eassumption; destruct Static; unfold static_path in *; cbn in *; tauto.
Qed.

Lemma structural_paths R M roles A c Q :
  structural R M roles A c Q ->
  forall path p r (s : roles p) (t : roles r),
    possible_path path (c p s) -> possible_path path (c r t).
Proof.
  induction 1; intros [|e path] who peer whoIn peerIn;
    match goal with F : forall p s, _ p s = _ |- _ =>
      rewrite (F who whoIn), (F peer peerIn) end;
    try destruct e; cbn [possible_path]; eauto.
Qed.

Section Witness.
Context {M E : Type -> Type} {S : Type} (m : local_model M E role S)
    (R : list role) (p : role) (A : Type) (original : Choreo M p A).
Definition follows {B} o (c : Choreo M p B) :=
  forall tail, possible_path tail c -> possible_path (o ++ tail) original.
Fixpoint follows_cursor {B} (t : @cursor M E p B) :=
  match t with
  | Code o c => follows o c
  | Seq o u _ => follows_cursor u /\ forall tail, possible_path (child o BindBody ++ tail) original
  | Fork f x => follows_cursor f /\ follows_cursor x
  | _ => True end.

Lemma silent_follows B t u : @silent M E S m p B t u ->
  follows_cursor t -> follows_cursor u.
Proof.
  induction 1; cbn [follows_cursor]; try tauto.
  - intro Parent. split; intro tail; unfold child; rewrite <- app_assoc.
    + exact (Parent (BindPrefix :: tail)).
    + apply (Parent (BindBody :: tail)). exact I.
  - intro Parent. split; intro tail; unfold child; rewrite <- app_assoc.
    + exact (Parent (AppFunction :: tail)).
    + exact (Parent (AppArgument :: tail)).
  - intros [_ Body] tail _. apply Body.
Qed.

Lemma step_follows B t st q a u st' q' :
  @role_step M E S m R p B t st q a u st' q' -> follows_cursor t -> follows_cursor u.
Proof.
  induction 1; cbn [follows_cursor]; try tauto.
  all: try solve [intros Parent tail _; unfold child; rewrite <- app_assoc;
    apply (Parent (ChoiceBody :: tail)); exact I].
  intro Root. apply IHrole_step. eapply silent_follows; eassumption.
Qed.

Lemma run_follows F s tr u :
  @crun M E S m R F s tr u ->
  follows_cursor (positions s p) -> follows_cursor (positions u p).
Proof.
  induction 1; intro Start; [exact Start|].
  destruct H0 as [r a finish Hr Step Frame]. destruct (role_eq_dec r p) as [->|Ne].
  - eapply step_follows; [exact Step|auto].
  - rewrite <- Frame by congruence; auto.
Qed.

Lemma focus_follows B Y (C : @cursor_context M E p B Y) t :
  follows_cursor (plug C t) -> follows_cursor t.
Proof. induction C; cbn; intros H; first [exact H|apply IHC; tauto]. Qed.

Lemma reached_action_path B Y o (code : Choreo M p B) (C : @cursor_context M E p B Y) t :
  follows_cursor t -> silent_prefix m t (plug C (Code o code)) ->
  possible_path [] code -> possible_path o original.
Proof.
  intros Good Sil Action. rewrite <- (app_nil_r o).
  apply (focus_follows _ _ C (Code o code)).
  - induction Sil; [exact Good|]. apply IHSil; eapply silent_follows; eassumption.
  - exact Action.
Qed.
End Witness.

Lemma sampled_send_site {M E Store Input} (model : local_model M E role (Store * Input))
    stores input R A c tc s tn n gs past X kind path sender recipient (v : X) sh :
  payload_history model stores input R A c tc s tn n gs past ->
  In (Message X kind path sender recipient v sh) gs ->
  In sender R /\ possible_path path (c sender).
Proof.
  intros Hist Member. destruct (actual_production_focus model stores input R A c
    kind path sender recipient (Operand X sh v)
    (history_production model stores input R A c _ _ _ _ _ _ Hist _ _ _ _ _
      (proj1 (history_past_ok model stores input R A c _ _ _ _ _ _ Hist) _ Member)))
    as (tc0 & s0 & tn0 & n0 & gs0 & a & s1 & na & n1 & gs1 & ev & who & Prefix & Pair & Hin & Focus).
  destruct (production_focus_sender _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Focus) as [Eq _].
  subst who. split; [exact Hin|].
  destruct Focus as (Y & C & before & after & Sil & Prim & End & Site).
  assert (Action : match before with Code _ code => possible_path [] code | _ => False end)
    by (destruct Site; exact I).
  destruct (sender_site_operand _ _ _ _ _ _ _ _ _ Site) as [_ [code [-> _]]].
  eapply reached_action_path; [|exact Sil|exact Action].
  eapply run_follows; [exact (prefix_source_run model stores input R A c _ _ _ _ _ Prefix)|].
  intros tail H; exact H.
Qed.

Theorem static_receive_compares_to_queued {M E Store Input}
    (model : local_model M E role (Store * Input)) stores input R A c tc s tn n gs
    p X kind site sender rd g :
  well_formed R M A c ->
  matched_prefix model stores input R A c tc s tn n gs ->
  In p R -> static_path site ->
  receive_site (shared_model model) p (A p) (positions s p) X kind site sender rd ->
  In g gs -> message_key g = (sender,p,session_at site Choreography.Network.Root) ->
  site = message_path g \/ source_before site (message_path g) \/ source_before (message_path g) site.
Proof.
  intros [_ [Q WF]] Prefix Member Static (B & C & focus & Sil & Site) InG Key.
  destruct g as [Y k path from dest v sh]. cbn [message_key message_path] in Key |- *.
  injection Key as -> -> Same.
  destruct (matched_payload_history model stores input R A c _ _ _ _ _ Prefix) as [past Hist].
  destruct (sampled_send_site model stores input R A c _ _ _ _ _ _ Y k path sender p v sh Hist InG)
    as [Sender Other].
  assert (This : possible_path site (c p)).
  { assert (At : exists code, focus = Code site code /\ possible_path [] code).
    { destruct Site; eexists; split; [reflexivity|exact I|reflexivity|exact I]. }
    destruct At as (code & -> & At). eapply reached_action_path; [|exact Sil|exact At].
    eapply run_follows; [exact (prefix_source_run model stores input R A c _ _ _ _ _ Prefix)|].
    intros tail H; exact H. }
  apply equal_lane_order;
    [eapply static_compatible; [exact Static|exact This|]
    |apply (proj1 (same_session_iff _ _ Choreography.Network.Root)); symmetry; exact Same].
  exact (structural_paths _ _ _ _ _ _ WF path sender p Sender Member Other).
Qed.
