From Stdlib Require Import Lists.List.
Require Import Choreography.Choreo2 Control.Monad.Tree Parkour.Symbol.
Require Import DeadlockSource DeadlockCoherence DeadlockReplay DeadlockOrder.
Import ListNotations.

(* A finite selected constructor tree. This is NOT an execution semantics:
   Completed below ties each selected continuation to its actual returned
   prefix, and each atomic completion to a real cursor history. *)
Inductive node_tree : Type :=
| Leaf
| Exchange (sender receiver : Symbol)
| Parallel (function argument : node_tree)
| Sequence (prefix body : node_tree)
| Choice (owner : Symbol) (body : node_tree).

Inductive site : node_tree -> occurrence -> delivery_kind -> Symbol -> Symbol -> Prop :=
| SiteExchange l r : l <> r -> site (Exchange l r) [] DataDelivery l r
| SiteChoice l r body : l <> r -> site (Choice l body) [] ChoiceDelivery l r
| SiteFunction f x o k l r :
    site f o k l r -> site (Parallel f x) (AppFunction :: o) k l r
| SiteArgument f x o k l r :
    site x o k l r -> site (Parallel f x) (AppArgument :: o) k l r
| SitePrefix t b o k l r :
    site t o k l r -> site (Sequence t b) (BindPrefix :: o) k l r
| SiteBody t b o k l r :
    site b o k l r -> site (Sequence t b) (BindBody :: o) k l r
| SiteChosen l b o k s d :
    site b o k s d -> site (Choice l b) (ChoiceBody :: o) k s d.

(* This is genuine constructor induction: arbitrary equal-session paths are
   NOT claimed compatible. Both sites must belong to the same selected tree. *)
Theorem shared_node_paths tree :
  forall o k l r, site tree o k l r ->
  forall b j s d, site tree b j s d -> compatible o b.
Proof.
  intros o k l r First. induction First; intros b0 j s0 d0 Other;
    inversion Other; subst; constructor; eauto.
Qed.

Corollary shared_key_paths tree o b k j l r sid :
  site tree o k l r -> site tree b j l r ->
  (l,r,session_at o sid) = (l,r,session_at b sid) ->
  compatible o b /\ source_lane o = source_lane b.
Proof.
  intros One Two Key. split.
  - eapply shared_node_paths; eassumption.
  - apply (proj1 (same_session_iff o b sid)). congruence.
Qed.

(* A trace observer retains the actual typed action, without comparing hidden
   payload types. Choice sends stand for the announcement to each peer. *)
Definition action_at {E S} kind o sender receiver p
    (a : @source_action E S) : Prop :=
  match kind, a with
  | DataDelivery, SendAction _ b s d _ =>
      b = o /\ s = sender /\ d = receiver /\ p = sender
  | DataDelivery, ReceiveAction _ b s d _ =>
      b = o /\ s = sender /\ d = receiver /\ p = receiver
  | ChoiceDelivery, AnnounceAction _ b s _ =>
      b = o /\ s = sender /\ p = sender /\ sender <> receiver
  | ChoiceDelivery, HearAction _ b s d _ =>
      b = o /\ s = sender /\ d = receiver /\ p = receiver
  | _, _ => False
  end.

Section Coverage.
Context {M E : Type -> Type} {Store : Type}.
Variable model : DeadlockLocal.local_model M E Symbol Store.
Variable configured : list Symbol.
Variable p : Symbol.

Definition waiting {A} o l r (t : @cursor M E p A) : Prop :=
  match t with
  | Code b (Perf (@Comm _ _ _ s d _ _ _ _ _ _ _)) =>
      b = o /\ s = l /\ d = r
  | _ => False
  end.

Lemma waiting_silent X A (C : @cursor_context M E p X A)
    before after o l r :
  primitive_silent model X before after ->
  waiting o l r (plug C before) ->
  l <> r -> (p = l \/ p = r) -> False.
Proof.
  destruct C; cbn [plug waiting]; try contradiction.
  intros Step. destruct Step; cbn [waiting]; try contradiction.
  all: intros (Eq & Sender & Receiver) Different Peer; subst;
    intuition congruence.
Qed.

Lemma waiting_action X A (C : @cursor_context M E p X A)
    before after s q a s' q' o l r :
  primitive_action model configured X before s q a after s' q' ->
  waiting o l r (plug C before) ->
  action_at DataDelivery o l r p a.
Proof.
  destruct C; cbn [plug waiting]; try contradiction.
  intros Step. destruct Step; cbn [waiting action_at]; try contradiction.
  all: intros (Eq & Sender & Receiver); subst; repeat split; reflexivity.
Qed.

(* A participating role cannot silently finish a remote Comm. The invariant
   is proved on the actual focused history, not on a presumed coverage list. *)
Theorem history_crossed_exchange A start tr t o l r :
  @cursor_history M E Store model configured p A start tr t ->
  waiting o l r start -> l <> r -> (p = l \/ p = r) ->
  waiting o l r t \/
    exists a, In a tr /\ action_at DataDelivery o l r p a.
Proof.
  intros Hist Initial Different Peer. induction Hist.
  - now left.
  - destruct IHHist as [Wait | (a & Member & At)].
    + exfalso. eapply waiting_silent; eassumption.
    + right. exists a; auto.
  - destruct IHHist as [Wait | (b & Member & At)].
    + right. exists a. split.
      * apply in_or_app. right. now left.
      * eapply waiting_action; eassumption.
    + right. exists b. split; [apply in_or_app; now left | exact At].
Qed.

Corollary completed_exchange X l r o sh rd kl kr sl input sr tr x :
  cursor_history model configured
    (Code o (Perf (@Comm M p X l r sh rd kl kr sl input sr)))
    tr (Returned x) ->
  l <> r -> (p = l \/ p = r) ->
  exists a, In a tr /\ action_at DataDelivery o l r p a.
Proof.
  intros Hist Different Peer.
  destruct (history_crossed_exchange _ _ _ _ o l r Hist
    (conj eq_refl (conj eq_refl eq_refl)) Different Peer) as [Impossible|Done].
  - contradiction.
  - exact Done.
Qed.

Definition atomic_tree {A} (c : Choreo M p A) : node_tree :=
  match c with
  | Perf (@Comm _ _ _ l r _ _ _ _ _ _ _) => Exchange l r
  | _ => Leaf
  end.

(* Completion retains both App branches and the returned value selecting a
   Bind body. Cond retains its actual announcement/hear transition. *)
Inductive completed : forall A, occurrence -> Choreo M p A -> A -> node_tree -> Prop :=
| CompletePure A o (x : A) : completed A o (Pure x) x Leaf
| CompleteAtom A o (c : Choreo M p A) tr x :
    atomic p A c ->
    cursor_history model configured (Code o c) tr (Returned x) ->
    completed A o c x (atomic_tree c)
| CompleteApp X Y o (f : Choreo M p (X -> Y)) x fv xv ft xt :
    completed (X -> Y) (child o AppFunction) f fv ft ->
    completed X (child o AppArgument) x xv xt ->
    completed Y o (App f x) (fv xv) (Parallel ft xt)
| CompleteBind X Y o (t : Choreo M p X) (k : X -> Choreo M p Y) x y tt bt :
    completed X (child o BindPrefix) t x tt ->
    completed Y (child o BindBody) (k x) y bt ->
    completed Y o (Bind t k) y (Sequence tt bt)
| CompleteChoice X Y l o sh rd kl sl input (k : X -> Choreo M p Y)
    x y bt s q a s' q' :
    primitive_action model configured Y
      (Code o (Perf (@Cond M p X l Y sh rd kl sl input k))) s q a
      (Code (child o ChoiceBody) (k x)) s' q' ->
    completed Y (child o ChoiceBody) (k x) y bt ->
    completed Y o (Perf (@Cond M p X l Y sh rd kl sl input k)) y (Choice l bt).

Definition cursor_value {A} (t : @cursor M E p A) : option A :=
  match t with Returned x => Some x | _ => None end.

(* In particular SyntaxBindBody's prefix is recursively proved complete.
   It is not replaced by a "prefix covered" hypothesis. *)
Theorem returned_cut_completed A o c t :
  syntax_cut model configured p A o c t ->
  forall x, cursor_value t = Some x -> exists tree, completed A o c x tree.
Proof.
  intro Cut. induction Cut; intros value Eq; cbn [cursor_value] in Eq;
    try discriminate.
  - injection Eq as <-. exists Leaf. constructor.
  - destruct t; try discriminate. injection Eq as <-. eexists. eapply CompleteAtom; eassumption.
  - injection Eq as <-.
    destruct (IHCut1 _ eq_refl) as [ft F].
    destruct (IHCut2 _ eq_refl) as [xt Arg].
    exists (Parallel ft xt). econstructor; eassumption.
  - destruct (IHCut1 _ eq_refl) as [tt T].
    destruct (IHCut2 _ Eq) as [bt B].
    exists (Sequence tt bt). econstructor; eassumption.
  - destruct (IHCut _ Eq) as [bt B].
    exists (Choice l bt). econstructor; eassumption.
Qed.

(* A witnessed action is an actual finite SUBTREE history. The enclosing
   actor trace/archive membership is a separate interface, stated in the
   accompanying notes; it is not silently asserted by this definition. *)
Definition witnessed kind o l r : Prop :=
  exists A (start finish : @cursor M E p A) tr a,
    cursor_history model configured start tr finish /\
    In a tr /\ action_at kind o l r p a.

Lemma choice_action X Y l o sh rd kl sl input (k : X -> Choreo M p Y)
    x s q a s' q' r :
  primitive_action model configured Y
    (Code o (Perf (@Cond M p X l Y sh rd kl sl input k))) s q a
    (Code (child o ChoiceBody) (k x)) s' q' ->
  l <> r -> (p = l \/ p = r) ->
  action_at ChoiceDelivery o l r p a.
Proof.
  intro Act.
  (* The result value of a Cond is not needed to observe its action. *)
  remember (Code o (Perf (@Cond M p X l Y sh rd kl sl input k))) as before eqn:Eq.
  destruct Act; inversion Eq; subst; cbn [action_at]; intuition congruence.
Qed.

Theorem completed_subtree_coverage A root c x tree :
  completed A root c x tree ->
  forall path kind l r, site tree path kind l r ->
    (p = l \/ p = r) -> witnessed kind (root ++ path) l r.
Proof.
  intro Done. induction Done; intros path kind sender receiver Site Peer.
  - inversion Site.
  - destruct H; cbn [atomic_tree] in Site.
    + inversion Site.
    + inversion Site; subst.
      destruct (completed_exchange _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H6 Peer)
        as (a & Member & At).
      unfold witnessed. do 3 eexists. exists tr, a.
      rewrite app_nil_r. split; [exact H0|now split].
  - inversion Site; subst; match goal with Hs : site _ _ _ _ _ |- _ =>
      first [pose proof (IHDone1 _ _ _ _ Hs Peer) as P
            |pose proof (IHDone2 _ _ _ _ Hs Peer) as P] end;
      unfold child in P; rewrite <- app_assoc in P; exact P.
  - inversion Site; subst; match goal with Hs : site _ _ _ _ _ |- _ =>
      first [pose proof (IHDone1 _ _ _ _ Hs Peer) as P
            |pose proof (IHDone2 _ _ _ _ Hs Peer) as P] end;
      unfold child in P; rewrite <- app_assoc in P; exact P.
  - inversion Site; subst.
    + match goal with Diff : _ <> _ |- _ =>
        pose proof (choice_action _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H Diff Peer) as At
      end.
      unfold witnessed. exists Y.
      exists (Code o (Perf (@Cond M p X sender Y sh rd kl sl input k))).
      exists (Code (child o ChoiceBody) (k x)), [a], a.
      rewrite app_nil_r. split.
      * change [a] with ([] ++ [a]).
        eapply HistoryAction with (C := @ContextHole M E p Y); [constructor | exact H].
      * split; [now left | exact At].
    + match goal with Hs : site _ _ _ _ _ |- _ => specialize (IHDone _ _ _ _ Hs Peer) end.
      unfold child in IHDone. rewrite <- app_assoc in IHDone. exact IHDone.
Qed.

End Coverage.
