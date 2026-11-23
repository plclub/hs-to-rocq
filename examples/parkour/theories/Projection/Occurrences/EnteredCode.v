From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Projection.Payloads.StaticPackets
  Choreography.Histories.CursorHistories Choreography.Occurrences
  Choreography.RoleSteps Semantics.LocalEffects Network.Mailboxes
  Choreography.Histories.RoleChronology
  Choreography.Histories.TransitionArchive.
Require Import Choreography.Choreo2 Control.Monad.Tree.
Import ListNotations.

(* Anchor a cursor to a body the role actually entered, not necessarily to
   the initial program. Absolute queue occurrences stay unchanged. *)
Section Entered.
Context {M E : Type -> Type} {S : Type} (m : local_model M E role S) (R : list
  role)
    (p : role) (A : Type) (base : occurrence) (body : Choreo M p A).
Definition relative_node {Y} o (code : Choreo M p Y) :=
  exists path, o = base ++ path /\
    forall tail, static_path (path ++ tail) ->
      choreo_at_static_path tail code = choreo_at_static_path (path ++ tail)
        body.

Fixpoint relative_cursor {Y} (t : @cursor M E p Y) :=
  match t with
  | Code o code => relative_node o code
  | Seq o u _ => RoleChronology.path_prefix base o /\ relative_cursor u
  | Fork f x => relative_cursor f /\ relative_cursor x
  | _ => True end.

Lemma relative_child B (code : Choreo M p B) o e :
  (e = BindBody \/ e = ChoiceBody) -> RoleChronology.path_prefix base o ->
  relative_node (child o e) code.
Proof.
  intros Eq [path ->]. exists (path ++ [e]). unfold child; rewrite app_assoc.
  split; [reflexivity|]. intros tail [Choice Bind]; destruct Eq as [Eq|Eq];
    subst e; exfalso; [apply Bind|apply Choice];
    rewrite <- app_assoc; apply in_or_app; right; now left.
Qed.

Lemma relative_prefix B (code : Choreo M p B) o :
  relative_node o code -> RoleChronology.path_prefix base o.
Proof. intros (path & Eq & _); now exists path. Qed.

Lemma relative_silent B t u : @silent M E S m p B t u ->
  relative_cursor t -> relative_cursor u.
Proof.
  induction 1; cbn [relative_cursor]; try tauto.
  - intros (path & -> & Origin). split; [now exists path|].
    exists (path ++ [BindPrefix]). unfold child. rewrite app_assoc.
    split; [reflexivity|]. intro tail; rewrite <- app_assoc.
    exact (Origin (BindPrefix :: tail)).
  - intros (path & -> & Origin). split.
    + exists (path ++ [AppFunction]). unfold child. rewrite app_assoc.
      split; [reflexivity|]. intro tail; rewrite <- app_assoc.
      exact (Origin (AppFunction :: tail)).
    + exists (path ++ [AppArgument]). unfold child. rewrite app_assoc.
      split; [reflexivity|]. intro tail; rewrite <- app_assoc.
      exact (Origin (AppArgument :: tail)).
  - intros [Scope _]. apply relative_child; auto.
Qed.

Lemma relative_step B t st q a u st' q' :
  @role_step M E S m R p B t st q a u st' q' ->
  relative_cursor t -> relative_cursor u.
Proof.
  induction 1; cbn [relative_cursor]; try tauto.
  all: try solve [intro Old; apply relative_child; [auto|eapply relative_prefix;
    exact Old]].
  intro Old. apply IHrole_step. eapply relative_silent; eassumption.
Qed.

Lemma relative_plug B Y (C : @cursor_context M E p B Y) t :
  relative_cursor (plug C t) -> relative_cursor t.
Proof. induction C; cbn; intros H; first [exact H|apply IHC; tauto]. Qed.

Theorem entered_history_origin tr t :
  cursor_history m R (Code base body) tr t -> relative_cursor t.
Proof.
  intro H. remember (Code base body) as start in H.
  induction H.
  - subst. exists []; rewrite app_nil_r; auto.
  - eapply relative_silent; [apply silent_plug; eapply primitive_is_silent;
    exact H0|auto].
  - eapply relative_step; [apply role_step_plug; eapply primitive_is_role_step;
    exact H0|auto].
Qed.

Theorem entered_focus_original B (C : @cursor_context M E p B A) code site
    tr t :
  cursor_history m R (Code base body) tr t ->
  silent_prefix m t (plug C (Code (base ++ site) code)) -> static_path site ->
  choreo_at_static_path site body = Some (existT _ B code).
Proof.
  intros Hist Sil Static. pose proof (entered_history_origin _ _ Hist) as Start.
  assert (End : relative_cursor (plug C (Code (base ++ site) code))).
  { clear -Start Sil; induction Sil; [exact Start|].
    apply IHSil; eapply relative_silent; eassumption. }
  destruct (relative_plug _ _ C _ End) as [path [Eq Origin]].
  apply app_inv_head in Eq. subst path. specialize (Origin []).
  rewrite app_nil_r in Origin. exact (eq_sym (Origin Static)).
Qed.
End Entered.

(* A peer still waiting at its original condition cannot expose a nested
   Code by silent steps. In particular it cannot witness a send in a body
   merely because another role has already selected that body. *)
Lemma before_choice_no_child {M E S} (m : local_model M E role S) p X l A
    sh rd kl sl value (k : X -> Choreo M p A) base B (C : @cursor_context M E p
      B A)
    child_site code :
  silent_prefix m (Code base (Perf (@Cond M p X l A sh rd kl sl value k)))
    (plug C (Code child_site code)) ->
  child_site = base.
Proof.
  intro Sil. remember (Code base (Perf (@Cond M p X l A sh rd kl sl value k)))
    as initial in Sil. remember (plug C (Code child_site code)) as last in Sil.
  destruct Sil.
  - subst. destruct C; cbn in *; congruence.
  - subst. pose proof (silent_shape_correct m p _ _ _ H) as Atom.
    change (atomic p A (Perf (@Cond M p X l A sh rd kl sl value k))) in Atom.
    inversion Atom.
Qed.
