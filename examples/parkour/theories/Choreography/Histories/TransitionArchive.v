From Stdlib Require Import Lists.List.
Require Import Choreography.Choreo2 Control.Monad.Tree Parkour.Symbol.
From ParkourTheories.Choreography Require Import Occurrences PendingDeliveries
  RoleSteps Execution Histories.CursorHistories.
Import ListNotations.

(* A persistent, occurrence-indexed archive of actual primitive transitions.
   Unlike a linear role history, the five children keep independent source
   branches. Events retain their typed before/after cursors and their actual
   transition evidence. In particular a PrimitiveBody retains the returned
   prefix value, even when the machine no longer has its Seq frame.

   This is an annotated cut, not a complete evaluator for source syntax.
   Structural joins have no occurrence in the Source machine; those events
   are filed under the current zipper route rather than inventing one. *)
Section Replay.
Context {M E : Type -> Type} {Store : Type}.
Variable model : LocalEffects.local_model M E Symbol Store.
Variable configured : list Symbol.
Variable p : Symbol.

Inductive replay_event : Type :=
| SilentEvent X (before after : @cursor M E p X) :
    primitive_silent model X before after -> replay_event
| ActionEvent X (before after : @cursor M E p X)
    s q a s' q' :
    primitive_action model configured X before s q a after s' q' ->
    replay_event.

Inductive replay_tree : Type :=
| Empty
| Node (events : list replay_event)
    (prefix body function argument choice : replay_tree).

Definition branch (e : source_edge) (t : replay_tree) : replay_tree :=
  match t with
  | Empty => Empty
  | Node _ a b c d f =>
    match e with
    | BindPrefix => a | BindBody => b | AppFunction => c
    | AppArgument => d | ChoiceBody => f
    end
  end.

Definition events (t : replay_tree) : list replay_event :=
  match t with Empty => [] | Node es _ _ _ _ _ => es end.

Definition replace_branch (e : source_edge) (u t : replay_tree) : replay_tree :=
  let es := events t in
  let a := branch BindPrefix t in
  let b := branch BindBody t in
  let c := branch AppFunction t in
  let d := branch AppArgument t in
  let f := branch ChoiceBody t in
  match e with
  | BindPrefix => Node es u b c d f
  | BindBody => Node es a u c d f
  | AppFunction => Node es a b u d f
  | AppArgument => Node es a b c u f
  | ChoiceBody => Node es a b c d u
  end.

Fixpoint insert (o : occurrence) (a : replay_event)
    (t : replay_tree) : replay_tree :=
  match o with
  | [] => Node (a :: events t)
      (branch BindPrefix t) (branch BindBody t)
      (branch AppFunction t) (branch AppArgument t) (branch ChoiceBody t)
  | e :: rest => replace_branch e (insert rest a (branch e t)) t
  end.

Fixpoint lookup (o : occurrence) (t : replay_tree) : list replay_event :=
  match o with
  | [] => events t
  | e :: rest => lookup rest (branch e t)
  end.

Lemma insert_here o a t : In a (lookup o (insert o a t)).
Proof.
  revert t. induction o as [|e o IH]; intro t; cbn.
  - now left.
  - destruct e; cbn; apply IH.
Qed.

Lemma insert_preserves o a t r b :
  In b (lookup r t) -> In b (lookup r (insert o a t)).
Proof.
  revert t r. induction o as [|e o IH]; intros t [|f r] H; cbn in *.
  - now right.
  - destruct f; exact H.
  - destruct e; cbn; exact H.
  - destruct e, f; cbn in *; try exact H; apply IH; exact H.
Qed.

Lemma insert_other o a t r :
  o <> r -> lookup r (insert o a t) = lookup r t.
Proof.
  revert t r. induction o as [|e o IH]; intros t [|f r] Ne; cbn.
  - exfalso. apply Ne. reflexivity.
  - destruct f; reflexivity.
  - destruct e; reflexivity.
  - destruct e, f; cbn; try reflexivity;
      apply IH; intro Eq; apply Ne; now f_equal.
Qed.

(* Real primitive positions survive discarded Seq and Cond frames. A Fork
   join is the sole primitive without such a position. *)
Definition position {X} (t : @cursor M E p X) : option occurrence :=
  match t with
  | Code o _ => Some o | Local o _ => Some o
  | Seq o _ _ => Some o | Returned _ | Fork _ _ => None
  end.

Fixpoint context_route {X A} (C : @cursor_context M E p X A) : occurrence :=
  match C with
  | ContextHole _ _ => []
  | ContextSeq _ _ _ _ _ _ C => BindPrefix :: context_route C
  | ContextLeft _ _ _ _ _ C => AppFunction :: context_route C
  | ContextRight _ _ _ _ _ C => AppArgument :: context_route C
  end.

Definition event_route {X A} (C : @cursor_context M E p X A)
    (before : @cursor M E p X) : occurrence :=
  match position before with Some o => o | None => context_route C end.

#[universes(template)]
Record annotated_cut (A : Type) : Type := Cut {
  erased_cursor : @cursor M E p A;
  archive : replay_tree
}.
Arguments Cut {A} _ _.
Arguments erased_cursor {A} _.
Arguments archive {A} _.

(* Validity is indexed by the original cursor and the actual finite action
   trace. It is in Prop: extracting the existential below never eliminates
   a history proof into Type. *)
#[universes(template)]
Inductive cut_history {A} (start : @cursor M E p A) :
    list (@source_action E Store) -> annotated_cut A -> Prop :=
| CutStart : cut_history start [] (Cut start Empty)
| CutSilent tr X (C : @cursor_context M E p X A) before after tree
    (step : primitive_silent model X before after) :
    cut_history start tr (Cut (plug C before) tree) ->
    cut_history start tr
      (Cut (plug C after)
        (insert (event_route C before) (SilentEvent X before after step) tree))
| CutAction tr X (C : @cursor_context M E p X A) before after tree
    s q a s' q'
    (step : primitive_action model configured X before s q a after s' q') :
    cut_history start tr (Cut (plug C before) tree) ->
    cut_history start (tr ++ [a])
      (Cut (plug C after)
        (insert (event_route C before)
          (ActionEvent X before after s q a s' q' step) tree)).

Theorem history_has_annotated_cut A start tr t :
  @cursor_history M E Store model configured p A start tr t ->
  exists cut, cut_history start tr cut /\ erased_cursor cut = t.
Proof.
  induction 1.
  - exists (Cut start Empty). split; [constructor | reflexivity].
  - destruct IHcursor_history as ([u tree] & Hist & Eq). cbn in Eq.
    subst u. eexists. split;
      [eapply CutSilent with (step := H0); exact Hist | reflexivity].
  - destruct IHcursor_history as ([u tree] & Hist & Eq). cbn in Eq.
    subst u. eexists. split;
      [eapply CutAction with (step := H0); exact Hist | reflexivity].
Qed.

Theorem cut_is_actual_history A start tr cut :
  @cut_history A start tr cut ->
  cursor_history model configured start tr (erased_cursor cut).
Proof.
  induction 1; cbn.
  - constructor.
  - eapply HistorySilent; eassumption.
  - eapply HistoryAction; eassumption.
Qed.

(* Persistent membership is what makes an actual Bind return or a chosen
   Cond value available after arbitrarily many later machine steps. *)
Lemma cut_silent_keeps_events A X
    (C : @cursor_context M E p X A) before after tree
    (step : primitive_silent model X before after) o a :
  In a (lookup o tree) ->
  In a (lookup o (archive
    (Cut (plug C after)
      (insert (event_route C before) (SilentEvent X before after step) tree)))).
Proof. cbn. apply insert_preserves. Qed.

Definition archive_extends (new old : replay_tree) : Prop :=
  forall o a, In a (lookup o old) -> In a (lookup o new).

Lemma cut_after_silent A start tr cut u :
  @cut_history A start tr cut ->
  silent model A (erased_cursor cut) u ->
  exists next, cut_history start tr next /\
    erased_cursor next = u /\ archive_extends (archive next) (archive cut).
Proof.
  intros Hist S.
  destruct (silent_focus model p A _ _ S)
    as (X & C & before & after & Eq & Prim & Eq').
  destruct cut as [t tree]. cbn in *. subst t u.
  eexists. split.
  - eapply CutSilent with (step := Prim). exact Hist.
  - split; [reflexivity |]. unfold archive_extends. cbn.
    intros. eapply insert_preserves. eassumption.
Qed.

Lemma cut_after_silent_prefix A start tr cut u :
  @cut_history A start tr cut ->
  silent_prefix model (erased_cursor cut) u ->
  exists next, cut_history start tr next /\
    erased_cursor next = u /\ archive_extends (archive next) (archive cut).
Proof.
  intros Hist S. remember (erased_cursor cut) as t eqn:Eq.
  revert cut Hist Eq. induction S; intros cut Hist Eq.
  - exists cut. split; [exact Hist |]. split; [symmetry; exact Eq |].
    intros o a H. exact H.
  - subst t. destruct (cut_after_silent _ _ _ _ _ Hist H)
      as (next & Next & Erase & Ext).
    destruct (IHS next Next (eq_sym Erase)) as (last & Last & End & More).
    exists last. split; [exact Last |]. split; [exact End |].
    intros o a InOld. apply More. apply Ext. exact InOld.
Qed.

Theorem cut_after_role_step A start tr cut s q a u s' q' :
  @cut_history A start tr cut ->
  role_step model configured A (erased_cursor cut) s q a u s' q' ->
  exists next, cut_history start (tr ++ [a]) next /\
    erased_cursor next = u /\ archive_extends (archive next) (archive cut).
Proof.
  intros Hist Step.
  destruct (role_step_focus model configured p A _ _ _ _ _ _ _ Step)
    as (X & C & before & after & Sil & Act & Eq).
  destruct (cut_after_silent_prefix _ _ _ _ _ Hist Sil)
    as ([t tree] & Mid & Erase & Ext).
  cbn in *. subst t u.
  eexists. split.
  - eapply CutAction with (step := Act). exact Mid.
  - split; [reflexivity |].
    intros o b InOld. cbn. apply insert_preserves. apply Ext. exact InOld.
Qed.

(* The completion evidence, including the actual x and k x, remains a typed
   object in the Bind node. No default value or serialization is involved. *)
Lemma bind_completion_recorded X Y o (x : X) (k : X -> Choreo M p Y) tree :
  In (SilentEvent Y (Seq o (Returned x) k) (Code (child o BindBody) (k x))
        (PrimitiveBody model X Y o x k))
    (lookup o
      (insert o
        (SilentEvent Y (Seq o (Returned x) k) (Code (child o BindBody) (k x))
          (PrimitiveBody model X Y o x k)) tree)).
Proof. apply insert_here. Qed.

Lemma app_histories_independent o a tree :
  lookup (child o AppArgument) (insert (child o AppFunction) a tree) =
  lookup (child o AppArgument) tree.
Proof.
  apply insert_other. unfold child. intro Eq.
  apply app_inv_head in Eq. discriminate.
Qed.

Corollary initial_run_has_annotated_cut A (c : forall r, Choreo M r (A r))
    s tr finish :
  Choreography.Execution.run model configured (initial c s) tr finish ->
  exists cut, cut_history (Code [] (c p)) (actor_actions p tr) cut /\
    erased_cursor cut = @positions M E Store A finish p.
Proof.
  intro Run. apply history_has_annotated_cut.
  exact (initial_actor_history model configured A c s tr finish Run p).
Qed.

End Replay.

(* A syntax cut retains a tree of the source constructors, not a list of
   transitions. Completed Bind prefixes and both App children remain present
   after their machine frames disappear. Only atomic Locally/Comm nodes use
   the already established focused history API. *)
Section SyntaxCuts.
Context {M E : Type -> Type} {Store : Type}.
Variable model : LocalEffects.local_model M E Symbol Store.
Variable configured : list Symbol.
Variable p : Symbol.

Inductive atomic : forall A, Choreo M p A -> Prop :=
| AtomicLocal X l ks ss f :
    atomic (At X l p) (Perf (@Locally M p X l ks ss f))
| AtomicComm X l r sh rd kl kr sl input sr :
    atomic (At X r p) (Perf (@Comm M p X l r sh rd kl kr sl input sr)).

Inductive syntax_cut : forall A, occurrence -> Choreo M p A ->
    @cursor M E p A -> Prop :=
| SyntaxCode A o (c : Choreo M p A) :
    syntax_cut A o c (Code o c)
| SyntaxPure A o (x : A) :
    syntax_cut A o (Pure x) (Returned x)
| SyntaxAtom A o (c : Choreo M p A) tr t :
    atomic A c ->
    cursor_history model configured (Code o c) tr t ->
    syntax_cut A o c t
| SyntaxApp X Y o (f : Choreo M p (X -> Y)) x cf cx :
    syntax_cut (X -> Y) (child o AppFunction) f cf ->
    syntax_cut X (child o AppArgument) x cx ->
    syntax_cut Y o (App f x) (Fork cf cx)
| SyntaxAppDone X Y o (f : Choreo M p (X -> Y)) x fv xv :
    syntax_cut (X -> Y) (child o AppFunction) f (Returned fv) ->
    syntax_cut X (child o AppArgument) x (Returned xv) ->
    syntax_cut Y o (App f x) (Returned (fv xv))
| SyntaxBind X Y o (t : Choreo M p X) (k : X -> Choreo M p Y) ct :
    syntax_cut X (child o BindPrefix) t ct ->
    syntax_cut Y o (Bind t k) (Seq o ct k)
| SyntaxBindBody X Y o (t : Choreo M p X) (k : X -> Choreo M p Y) x body :
    syntax_cut X (child o BindPrefix) t (Returned x) ->
    syntax_cut Y (child o BindBody) (k x) body ->
    syntax_cut Y o (Bind t k) body
| SyntaxChoice X Y l o sh rd kl sl input (k : X -> Choreo M p Y)
    x body s q a s' q' :
    ((exists e : l = p, x = unAt input e /\ a = AnnounceAction X o p x) \/
     (l <> p /\ a = HearAction X o l p x)) ->
    primitive_action model configured Y
      (Code o (Perf (@Cond M p X l Y sh rd kl sl input k))) s q a
      (Code (child o ChoiceBody) (k x)) s' q' ->
    syntax_cut Y (child o ChoiceBody) (k x) body ->
    syntax_cut Y o (Perf (@Cond M p X l Y sh rd kl sl input k)) body.

(* These views perform dependent elimination before specializing the source
   cursor. Ordinary inversion on indexed cursors would instead leave equality
   of existential Type packages and tempt the use of eq_rect_eq. *)
Definition silent_shape {A} (t : @cursor M E p A) : cursor p A -> Prop :=
  match t in cursor _ B return cursor p B -> Prop with
  | Code o c =>
    match c in Tree _ B return cursor p B -> Prop with
    | Pure x => fun u => u = Returned x
    | App f x => fun u =>
        u = Fork (Code (child o AppFunction) f) (Code (child o AppArgument) x)
    | Bind t k => fun u => u = Seq o (Code (child o BindPrefix) t) k
    | Perf e => fun _ => atomic _ (Perf e)
    end
  | Returned _ => fun _ => False
  | Local _ _ => fun _ => True
  | Seq o t k => fun u =>
      (exists x, t = Returned x /\ u = Code (child o BindBody) (k x)) \/
      (exists v, silent model _ t v /\ u = Seq o v k)
  | Fork f x => fun u =>
      (exists v, silent model _ f v /\ u = Fork v x) \/
      (exists v, silent model _ x v /\ u = Fork f v) \/
      (exists fv xv, f = Returned fv /\ x = Returned xv /\
        u = Returned (fv xv))
  end.

Lemma silent_shape_correct A t u :
  silent model A t u -> silent_shape t u.
Proof.
  destruct 1; cbn.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - left. eexists. split; reflexivity.
  - right. eexists. split; [eassumption | reflexivity].
  - left. eexists. split; [eassumption | reflexivity].
  - right. left. eexists. split; [eassumption | reflexivity].
  - right. right. do 2 eexists. repeat split; reflexivity.
  - apply AtomicLocal.
  - apply AtomicLocal.
  - exact I.
  - apply AtomicComm.
  - apply AtomicComm.
Qed.

Lemma syntax_cut_silent A o c t :
  syntax_cut A o c t ->
  forall u, silent model A t u -> syntax_cut A o c u.
Proof.
  intro Cut. induction Cut; intros u Step.
  - pose proof (silent_shape_correct _ _ _ Step) as Shape.
    destruct c as [A e|A x|X Y f x|X Y t k]; cbn in Shape.
    + eapply SyntaxAtom; [exact Shape |].
      eapply history_after_silent; [constructor | exact Step].
    + subst u. apply SyntaxPure.
    + subst u. apply SyntaxApp; apply SyntaxCode.
    + subst u. apply SyntaxBind. apply SyntaxCode.
  - exact (False_rect _ (silent_shape_correct _ _ _ Step)).
  - eapply SyntaxAtom; [exact H |].
    eapply history_after_silent; eassumption.
  - destruct (silent_shape_correct _ _ _ Step)
      as [(v & S & Eq) | [(v & S & Eq) | (fv & xv & Ef & Ex & Eq)]].
    + subst u. apply SyntaxApp; [apply IHCut1; exact S | exact Cut2].
    + subst u. apply SyntaxApp; [exact Cut1 | apply IHCut2; exact S].
    + subst cf cx u. apply SyntaxAppDone; assumption.
  - exact (False_rect _ (silent_shape_correct _ _ _ Step)).
  - destruct (silent_shape_correct _ _ _ Step)
      as [(x & Eq & End) | (v & S & End)].
    + subst ct u. eapply SyntaxBindBody; [exact Cut0 | apply SyntaxCode].
    + subst u. apply SyntaxBind. apply IHCut. exact S.
  - eapply SyntaxBindBody; [exact Cut1 | apply IHCut2; exact Step].
  - eapply SyntaxChoice; [exact H |exact H0 | apply IHCut; exact Step].
Qed.

Definition cut_map {A} (t u : @cursor M E p A) : Prop :=
  forall o c, syntax_cut A o c t -> syntax_cut A o c u.

(* A structural action carries the recursively established map on its actual
   child. This factors the proof without identifying existential Type indices.
   *)
Inductive preserving_step : forall A, cursor p A -> Store -> list pending ->
    @source_action E Store -> cursor p A -> Store -> list pending -> Prop :=
| PreservePrimitive A t s q a u s' q' :
    primitive_action model configured A t s q a u s' q' ->
    preserving_step A t s q a u s' q'
| PreserveSeq X Y o t u (k : X -> Choreo M p Y) s q a s' q' :
    role_step model configured X t s q a u s' q' ->
    cut_map t u ->
    preserving_step Y (Seq o t k) s q a (Seq o u k) s' q'
| PreserveLeft X Y (f g : cursor p (X -> Y)) x s q a s' q' :
    role_step model configured (X -> Y) f s q a g s' q' ->
    cut_map f g ->
    preserving_step Y (Fork f x) s q a (Fork g x) s' q'
| PreserveRight X Y (f : cursor p (X -> Y)) x y s q a s' q' :
    role_step model configured X x s q a y s' q' ->
    cut_map x y ->
    preserving_step Y (Fork f x) s q a (Fork f y) s' q'.

Lemma preserving_step_actual A t s q a u s' q' :
  preserving_step A t s q a u s' q' ->
  role_step model configured A t s q a u s' q'.
Proof.
  destruct 1.
  - apply primitive_is_role_step. exact H.
  - apply RSeq. exact H.
  - apply RLeft. exact H.
  - apply RRight. exact H.
Qed.

Definition preserving_shape {A} (t : @cursor M E p A)
    s q a s' q' : cursor p A -> Prop :=
  match t in cursor _ B return cursor p B -> Prop with
  | Code o c => fun u =>
      primitive_action model configured _ (Code o c) s q a u s' q'
  | Local o t => fun u =>
      primitive_action model configured _ (Local o t) s q a u s' q'
  | Returned _ => fun _ => False
  | Seq o t k => fun u =>
      exists v, cut_map t v /\ u = Seq o v k
  | Fork f x => fun u =>
      (exists v, cut_map f v /\ u = Fork v x) \/
      (exists v, cut_map x v /\ u = Fork f v)
  end.

Lemma preserving_shape_correct A t s q a u s' q' :
  preserving_step A t s q a u s' q' ->
  preserving_shape t s q a s' q' u.
Proof.
  destruct 1; cbn.
  - destruct H; cbn; econstructor; eassumption.
  - eexists. split; [eassumption | reflexivity].
  - left. eexists. split; [eassumption | reflexivity].
  - right. eexists. split; [eassumption | reflexivity].
Qed.

Definition primitive_shape {A} (t : @cursor M E p A)
    s q a s' q' : @cursor M E p A -> Prop :=
  match t in cursor _ B return @cursor M E p B -> Prop with
  | Code o c =>
    match c in Tree _ B return @cursor M E p B -> Prop with
    | Perf e =>
      match e in ChoreoSig _ _ B return @cursor M E p B -> Prop with
      | @Locally _ _ _ _ _ _ _ => fun _ => True
      | @Comm _ _ _ _ _ _ _ _ _ _ _ _ => fun _ => True
      | @Cond _ _ X l Y sh rd kl sl input k => fun u =>
        exists x,
          ((exists e : l = p, x = unAt input e /\ a = AnnounceAction X o p x) \/
           (l <> p /\ a = HearAction X o l p x)) /\
          primitive_action model configured Y
            (Code o (Perf (@Cond M p X l Y sh rd kl sl input k))) s q a
            (Code (child o ChoiceBody) (k x)) s' q' /\
          u = Code (child o ChoiceBody) (k x)
      end
    | _ => fun _ => False
    end
  | Local _ _ => fun _ => True
  | _ => fun _ => False
  end.

Lemma primitive_shape_correct A t s q a u s' q' :
  primitive_action model configured A t s q a u s' q' ->
  primitive_shape t s q a s' q' u.
Proof.
  destruct 1; cbn; try exact I.
  - eexists. split; [left; exists eq_refl; split; reflexivity|].
    split; [apply PrimitiveAnnounce | reflexivity].
  - eexists. split; [right; split; [eassumption|reflexivity]|].
    split; [eapply PrimitiveHear; eassumption | reflexivity].
Qed.

Lemma syntax_cut_preserving A o c t :
  syntax_cut A o c t ->
  forall s q a u s' q',
    preserving_step A t s q a u s' q' -> syntax_cut A o c u.
Proof.
  intro Cut. induction Cut; intros s0 q0 a0 u s1 q1 Step.
  - pose proof (preserving_shape_correct _ _ _ _ _ _ _ _ Step) as Prim.
    pose proof (primitive_shape_correct _ _ _ _ _ _ _ _ Prim) as Shape.
    destruct c as [A e|A x|X Y f x|X Y t k]; cbn in Shape.
    + destruct e; cbn in Shape.
      * eapply SyntaxAtom; [apply AtomicLocal |].
        eapply history_after_role_step; [constructor |].
        apply preserving_step_actual. exact Step.
      * eapply SyntaxAtom; [apply AtomicComm |].
        eapply history_after_role_step; [constructor |].
        apply preserving_step_actual. exact Step.
      * destruct Shape as (x & Selected & Choice & Eq). subst u.
        eapply SyntaxChoice; [exact Selected |exact Choice | apply SyntaxCode].
    + contradiction.
    + contradiction.
    + contradiction.
  - exact (False_rect _ (preserving_shape_correct _ _ _ _ _ _ _ _ Step)).
  - eapply SyntaxAtom; [exact H |].
    eapply history_after_role_step; [exact H0 |].
    apply preserving_step_actual. exact Step.
  - destruct (preserving_shape_correct _ _ _ _ _ _ _ _ Step)
      as [(v & Map & Eq) | (v & Map & Eq)]; subst u.
    + apply SyntaxApp; [apply Map; exact Cut1 | exact Cut2].
    + apply SyntaxApp; [exact Cut1 | apply Map; exact Cut2].
  - exact (False_rect _ (preserving_shape_correct _ _ _ _ _ _ _ _ Step)).
  - destruct (preserving_shape_correct _ _ _ _ _ _ _ _ Step)
      as (v & Map & Eq). subst u.
    apply SyntaxBind. apply Map. exact Cut0.
  - eapply SyntaxBindBody; [exact Cut1 |].
    eapply IHCut2. exact Step.
  - eapply SyntaxChoice; [exact H |exact H0 |].
    eapply IHCut. exact Step.
Qed.

Theorem syntax_cut_role_step A t s q a u s' q' :
  role_step model configured A t s q a u s' q' ->
  cut_map t u.
Proof.
  induction 1; intros root c Cut.
  - eapply syntax_cut_preserving; [exact Cut |].
    apply PreservePrimitive. apply PrimitiveLocal. exact H.
  - eapply syntax_cut_preserving; [exact Cut |].
    apply PreservePrimitive. apply PrimitiveSend.
  - eapply syntax_cut_preserving; [exact Cut |].
    apply PreservePrimitive. eapply PrimitiveReceive; eassumption.
  - eapply syntax_cut_preserving; [exact Cut |].
    apply PreservePrimitive. apply PrimitiveAnnounce.
  - eapply syntax_cut_preserving; [exact Cut |].
    apply PreservePrimitive. eapply PrimitiveHear; eassumption.
  - eapply syntax_cut_preserving; [exact Cut |].
    eapply PreserveSeq; eassumption.
  - eapply syntax_cut_preserving; [exact Cut |].
    eapply PreserveLeft; eassumption.
  - eapply syntax_cut_preserving; [exact Cut |].
    eapply PreserveRight; eassumption.
  - apply IHrole_step. eapply syntax_cut_silent; eassumption.
  Unshelve. all: assumption.
Qed.

Theorem history_preserves_syntax_cut A start tr t :
  cursor_history model configured start tr t ->
  forall o c, syntax_cut A o c start -> syntax_cut A o c t.
Proof.
  induction 1; intros root c Cut.
  - exact Cut.
  - eapply syntax_cut_silent.
    + apply IHcursor_history. exact Cut.
    + apply silent_plug. apply primitive_is_silent. exact H0.
  - eapply syntax_cut_role_step.
    + apply role_step_plug. apply primitive_is_role_step. exact H0.
    + apply IHcursor_history. exact Cut.
Qed.

Corollary code_history_has_syntax_cut A o (c : Choreo M p A) tr t :
  cursor_history model configured (Code o c) tr t ->
  syntax_cut A o c t.
Proof.
  intro Hist. eapply history_preserves_syntax_cut; [exact Hist |].
  apply SyntaxCode.
Qed.

Definition packed_program := {A : Type & Choreo M p A}.
Definition pack_program {A} (c : Choreo M p A) : packed_program :=
  existT _ A c.

(* The visitor traverses the derivation tree itself. In particular it cannot
   substitute a different history having the same erased final cursor. *)
Inductive visit_relative : forall {A o c t}, syntax_cut A o c t ->
    occurrence -> packed_program -> Prop :=
| VisitRoot A o c t (cut : syntax_cut A o c t) :
    visit_relative cut [] (pack_program c)
| VisitApp X Y o f x cf cx F T e path prog :
    ((e = AppFunction /\ visit_relative F path prog) \/
     (e = AppArgument /\ visit_relative T path prog)) ->
    visit_relative (SyntaxApp X Y o f x cf cx F T) (e :: path) prog
| VisitAppDone X Y o f x fv xv F T e path prog :
    ((e = AppFunction /\ visit_relative F path prog) \/
     (e = AppArgument /\ visit_relative T path prog)) ->
    visit_relative (SyntaxAppDone X Y o f x fv xv F T) (e :: path) prog
| VisitBind X Y o t k ct T path prog :
    visit_relative T path prog ->
    visit_relative (SyntaxBind X Y o t k ct T) (BindPrefix :: path) prog
| VisitBody X Y o t k x body P B e path prog :
    ((e = BindPrefix /\ visit_relative P path prog) \/
     (e = BindBody /\ visit_relative B path prog)) ->
    visit_relative (SyntaxBindBody X Y o t k x body P B) (e :: path) prog
| VisitChoice X Y l o sh rd kl sl input k x body s q a s' q' Selected Step B
  path prog :
    visit_relative B path prog ->
    visit_relative (SyntaxChoice X Y l o sh rd kl sl input k x body
      s q a s' q' Selected Step B) (ChoiceBody :: path) prog.

Definition visited {A o c t} (cut : syntax_cut A o c t)
    (where_ : occurrence) (program : packed_program) : Prop :=
  exists path, visit_relative cut path program /\ where_ = o ++ path.

Lemma visited_descends A o c t (cut : syntax_cut A o c t) where_ program :
  visited cut where_ program ->
  exists rest, where_ = o ++ rest.
Proof.
  intros (path & _ & Eq); now exists path.
Qed.

End SyntaxCuts.
