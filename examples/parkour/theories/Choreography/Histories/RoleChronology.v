From Stdlib Require Import Lists.List Sorting.Sorted.
From ParkourTheories.Choreography Require Import Occurrences PendingDeliveries
  RoleSteps Precedence.
Import ListNotations.

(* Pinned contract: chronological claims below concern actual role_step
   histories from Code, not a premise that the history is already sorted.
   LocalAction is deliberately excluded from the consumption claim. *)
Definition path_prefix (root path : occurrence) : Prop :=
  exists suffix, path = root ++ suffix.

Lemma path_prefix_refl o : path_prefix o o.
Proof. exists []; now rewrite app_nil_r. Qed.

Lemma path_prefix_parent o e z :
  path_prefix (child o e) z -> path_prefix o z.
Proof.
  intros [tail ->]. exists (e :: tail).
  unfold child; now rewrite <- app_assoc.
Qed.

Lemma path_prefix_trans a b c : path_prefix a b -> path_prefix b c ->
  path_prefix a c.
Proof.
  intros [u ->] [v ->]. exists (u ++ v). now rewrite app_assoc.
Qed.

Lemma path_prefix_extend_path o v e :
  path_prefix o v -> path_prefix o (child v e).
Proof.
  intro H; eapply path_prefix_trans; [exact H|].
  exists [e]; reflexivity.
Qed.

Lemma before_cancel root a b :
  source_before (root ++ a) (root ++ b) -> source_before a b.
Proof.
  induction root as [|e root IH]; cbn; intro H; [exact H|].
  inversion H; subst; now apply IH.
Qed.

Definition fresh_after (a z : occurrence) :=
  z <> a /\ ~ source_before z a.

Lemma siblings_fresh o e f a z :
  e <> f -> (e <> BindBody \/ f <> BindPrefix) ->
  path_prefix (child o e) a -> path_prefix (child o f) z ->
  fresh_after a z.
Proof.
  intros Ne Order [u ->] [v ->].
  unfold child; rewrite <- !app_assoc; cbn.
  split.
  - intro H. apply app_inv_head in H. injection H as H _. congruence.
  - intro H. apply before_cancel in H. inversion H; subst;
      intuition congruence.
Qed.

Lemma choice_fresh o z :
  path_prefix (child o ChoiceBody) z -> fresh_after o z.
Proof.
  intros [v ->]. unfold child; rewrite <- app_assoc.
  split.
  - intro H.
    assert (E : o ++ ChoiceBody :: v = o ++ []) by now rewrite app_nil_r.
    apply app_inv_head in E; discriminate.
  - intro H.
    assert (B : source_before (o ++ ChoiceBody :: v) (o ++ [])).
    { now rewrite app_nil_r. }
    apply before_cancel in B; inversion B.
Qed.

Section Chronology.
Context {M E : Type -> Type} {Store : Type}.
Variable model : LocalEffects.local_model M E Parkour.Symbol.Symbol Store.
Variable roles : list Parkour.Symbol.Symbol.

(* Regions include all possible continuation values. They do not evaluate,
   predict, or compare Gallina continuations. *)
Fixpoint scoped {p X} (o : occurrence) (t : @cursor M E p X) : Prop :=
  match t with
  | Code v _ => path_prefix o v
  | Returned _ => True
  | Local v _ => path_prefix o v
  | Seq v t _ => path_prefix o v /\ scoped (child v BindPrefix) t
  | Fork f x => exists v, path_prefix o v /\
      scoped (child v AppFunction) f /\ scoped (child v AppArgument) x
  end.

Fixpoint future {p X} (t : @cursor M E p X) (z : occurrence) : Prop :=
  match t with
  | Code o _ => path_prefix o z
  | Returned _ => False
  | Local o _ => z = o
  | Seq o t _ => future t z \/ path_prefix (child o BindBody) z
  | Fork f x => future f z \/ future x z
  end.

Definition safe {p X} a (t : @cursor M E p X) :=
  forall z, future t z -> fresh_after a z.

Lemma scoped_future p X o (t : @cursor M E p X) :
  scoped o t -> forall z, future t z -> path_prefix o z.
Proof.
  revert o; induction t; cbn; intros root Scope z Hz.
  - eapply path_prefix_trans; eassumption.
  - contradiction.
  - subst; exact Scope.
  - destruct Scope as [Bound Scope]. destruct Hz as [Hz|Hz].
    + eapply path_prefix_trans; [exact Bound|].
      apply path_prefix_parent with (e := BindPrefix); eapply IHt; eauto.
    + eapply path_prefix_trans; [exact Bound|]. now apply path_prefix_parent in
      Hz.
  - destruct Scope as [v [Bound [Sf Sx]]]. destruct Hz as [Hz|Hz].
    + eapply path_prefix_trans; [exact Bound|].
      apply path_prefix_parent with (e := AppFunction); eapply IHt1; eauto.
    + eapply path_prefix_trans; [exact Bound|].
      apply path_prefix_parent with (e := AppArgument); eapply IHt2; eauto.
Qed.

Lemma silent_future p X (t u : @cursor M E p X) :
  silent model X t u -> forall z, future u z -> future t z.
Proof.
  intro H; induction H; cbn; intros z Hz; try contradiction.
  - destruct Hz; now apply path_prefix_parent in H.
  - destruct Hz; now apply path_prefix_parent in H.
  - right; exact Hz.
  - destruct Hz; auto.
  - destruct Hz; auto.
  - destruct Hz; auto.
  - subst; apply path_prefix_refl.
Qed.

Lemma silent_scoped p X (t u : @cursor M E p X) :
  silent model X t u -> forall o, scoped o t -> scoped o u.
Proof.
  intro H; induction H; cbn; intros root Scope; auto.
  - split; auto using path_prefix_refl.
  - exists o; auto using path_prefix_refl.
  - destruct Scope as [Bound _]; now apply path_prefix_extend_path.
  - destruct Scope; split; auto.
  - destruct Scope as [v [Bound [Sf Sx]]]; exists v; auto.
  - destruct Scope as [v [Bound [Sf Sx]]]; exists v; auto.
Qed.

Definition action_path (a : @source_action E Store) : occurrence :=
  match a with
  | LocalAction o _ => o
  | SendAction _ o _ _ _ | ReceiveAction _ o _ _ _ => o
  | AnnounceAction _ o _ _ | HearAction _ o _ _ _ => o
  end.

Definition consuming (a : @source_action E Store) : Prop :=
  match a with LocalAction _ _ => False | _ => True end.

(* These are the preservation/consumption obligations, stated before their
   proofs so that future changes cannot silently weaken the contract. *)
Lemma role_future p X (t u : @cursor M E p X) s q a s' q' :
  role_step model roles X t s q a u s' q' ->
  (forall z, future u z -> future t z) /\ future t (action_path a).
Proof.
  intro H; induction H; cbn in *.
  all: try (split; [intros z Hz; contradiction|apply path_prefix_refl]).
  all: try (split; [auto|reflexivity]).
  all: try (split; [intros z Hz; now apply path_prefix_parent in Hz|apply
    path_prefix_refl]).
  all: try (firstorder; fail).
  destruct IHrole_step as [Future Action]. split.
  - intros z Hz. eapply silent_future; [exact H|now apply Future].
  - eapply silent_future; eauto.
Qed.

Lemma role_scoped p X (t u : @cursor M E p X) s q a s' q' :
  role_step model roles X t s q a u s' q' ->
  forall o, scoped o t -> scoped o u.
Proof.
  intro H; induction H; cbn; intros root Scope; auto using
    path_prefix_extend_path.
  - destruct Scope; split; auto.
  - destruct Scope as [v [Bound [Sf Sx]]]; exists v; auto.
  - destruct Scope as [v [Bound [Sf Sx]]]; exists v; auto.
  - eapply IHrole_step. eapply silent_scoped; eauto.
Qed.

Lemma role_consumes p X (t u : @cursor M E p X) s q a s' q' :
  role_step model roles X t s q a u s' q' ->
  forall o, scoped o t -> consuming a -> safe (action_path a) u.
Proof.
  intro H; induction H; intros root Scope Consume z Future;
    cbn in *; try contradiction.
  - now apply choice_fresh.
  - now apply choice_fresh.
  - destruct Scope as [Bound Scope]. destruct Future as [Future|Future].
    + eapply IHrole_step; eauto.
    + eapply siblings_fresh with (e := BindPrefix) (f := BindBody);
        try discriminate; try (left; discriminate); eauto.
      eapply scoped_future; [eassumption|].
      exact (proj2 (role_future _ _ _ _ _ _ _ _ _ H)).
  - destruct Scope as [v [Bound [Sf Sx]]]. destruct Future as [Future|Future].
    + eapply IHrole_step; eauto.
    + eapply siblings_fresh with (e := AppFunction) (f := AppArgument);
        try discriminate; try (left; discriminate).
      * eapply scoped_future; [eassumption|].
        exact (proj2 (role_future _ _ _ _ _ _ _ _ _ H)).
      * eapply scoped_future; eassumption.
  - destruct Scope as [v [Bound [Sf Sx]]]. destruct Future as [Future|Future].
    + eapply siblings_fresh with (e := AppArgument) (f := AppFunction);
        try discriminate; try (left; discriminate).
      * eapply scoped_future; [eassumption|].
        exact (proj2 (role_future _ _ _ _ _ _ _ _ _ H)).
      * eapply scoped_future; eassumption.
    + eapply IHrole_step; eauto.
  - eapply IHrole_step; eauto. eapply silent_scoped; eauto.
Qed.

#[universes(template)]
Inductive role_history {p X} :
    @cursor M E p X -> Store -> list pending ->
    list (@source_action E Store) ->
    @cursor M E p X -> Store -> list pending -> Prop :=
| HistoryNil t s q : role_history t s q [] t s q
| HistoryCons t s q a u s' q' events v s'' q'' :
    role_step model roles X t s q a u s' q' ->
    role_history u s' q' events v s'' q'' ->
    role_history t s q (a :: events) v s'' q''.

Lemma history_safe p X (t u : @cursor M E p X) s q events s' q' a :
  role_history t s q events u s' q' -> safe a t ->
  Forall (fun b => fresh_after a (action_path b)) events.
Proof.
  intro H; induction H; intro Safe; constructor.
  - apply Safe. exact (proj2 (role_future _ _ _ _ _ _ _ _ _ H)).
  - apply IHrole_history. intros z Hz; apply Safe.
    exact (proj1 (role_future _ _ _ _ _ _ _ _ _ H) z Hz).
Qed.

(* Every communication/choice action consumes its occurrence once. Every later
   action of this role is unequal and is not a strict syntax predecessor.
   Repeated visible local events remain permitted at the same Local path. *)
Theorem role_history_chronology p X (t u : @cursor M E p X)
    s q events s' q' root :
  role_history t s q events u s' q' -> scoped root t ->
  StronglySorted
    (fun a b => consuming a -> fresh_after (action_path a) (action_path b))
    events.
Proof.
  intro H; revert root; induction H; intros root Scope; constructor.
  - apply IHrole_history with (root := root).
    eapply role_scoped; eauto.
  - rewrite Forall_forall. intros b InB Consume.
    pose proof (history_safe _ _ _ _ _ _ _ _ _ (action_path a)
      H0 (role_consumes _ _ _ _ _ _ _ _ _ H root Scope Consume)) as Later.
    now rewrite Forall_forall in Later; apply Later.
Qed.

Corollary code_history_chronology p X (c : Choreography.Choreo2.Choreo M p X)
    u s q events s' q' :
  role_history (Code [] c) s q events u s' q' ->
  StronglySorted
    (fun a b => consuming a -> fresh_after (action_path a) (action_path b))
    events.
Proof.
  intro H; eapply role_history_chronology; [exact H|apply path_prefix_refl].
Qed.

Lemma history_scoped p X (t u : @cursor M E p X) s q events s' q' root :
  role_history t s q events u s' q' ->
  scoped root t -> scoped root u.
Proof.
  intro H; induction H; intro Scope; [exact Scope|].
  apply IHrole_history. eapply role_scoped; eauto.
Qed.

End Chronology.

Print Assumptions silent_future.
Print Assumptions silent_scoped.
Print Assumptions role_future.
Print Assumptions role_scoped.
Print Assumptions role_consumes.
Print Assumptions role_history_chronology.
Print Assumptions code_history_chronology.
Print Assumptions history_scoped.
