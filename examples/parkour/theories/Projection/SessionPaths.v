From Stdlib Require Import Lists.List Sorting.Sorted Arith.PeanoNat.
From ParkourTheories.Choreography Require Import Occurrences Precedence.
Require Import Choreography.Network.
Import ListNotations.

(* Only App extends the generated structural session. Bind and Cond retain
   their incoming session. This is a calculation on source positions, not
   an endpoint projector or a replacement for generated epp. *)
Fixpoint session_at (o : occurrence) (sid : SessionId) : SessionId :=
  match o with
  | [] => sid
  | AppFunction :: rest =>
      session_at rest (Nest (Data.Either.Left tt) sid)
  | AppArgument :: rest =>
      session_at rest (Nest (Data.Either.Right tt) sid)
  | _ :: rest => session_at rest sid
  end.

Lemma session_at_app p q sid :
  session_at (p ++ q) sid = session_at q (session_at p sid).
Proof.
  revert sid; induction p as [|e p IH]; intros sid; [reflexivity|].
  destruct e; cbn; apply IH.
Qed.

Lemma session_at_child o e sid :
  session_at (child o e) sid =
  match e with
  | AppFunction => Nest (Data.Either.Left tt) (session_at o sid)
  | AppArgument => Nest (Data.Either.Right tt) (session_at o sid)
  | _ => session_at o sid
  end.
Proof.
  unfold child; rewrite session_at_app; destruct e; reflexivity.
Qed.

(* Decode actual generated Nest constructors in source traversal order,
   visiting stored parents first. The outermost Nest is the latest App. *)
Fixpoint session_lane (sid : SessionId) : occurrence :=
  match sid with
  | Root => []
  | Nest (Data.Either.Left _) parent => session_lane parent ++ [AppFunction]
  | Nest (Data.Either.Right _) parent => session_lane parent ++ [AppArgument]
  end.

Lemma session_lane_at o sid :
  session_lane (session_at o sid) = session_lane sid ++ source_lane o.
Proof.
  revert sid; induction o as [|e o IH]; intros sid.
  - cbn; now rewrite app_nil_r.
  - destruct e; cbn; rewrite IH; cbn; try reflexivity;
      now rewrite <- app_assoc.
Qed.

Lemma session_at_source_lane o sid :
  session_at (source_lane o) sid = session_at o sid.
Proof.
  revert sid; induction o as [|e o IH]; intros sid; [reflexivity|].
  destruct e; cbn; apply IH.
Qed.

Theorem same_session_iff p q sid :
  session_at p sid = session_at q sid <->
  source_lane p = source_lane q.
Proof.
  split.
  - intro E; apply (f_equal session_lane) in E.
    rewrite !session_lane_at in E; now apply app_inv_head in E.
  - intro E; rewrite <- (session_at_source_lane p sid).
    rewrite <- (session_at_source_lane q sid); now rewrite E.
Qed.

Theorem app_branches_separate prefix p q sid :
  session_at (prefix ++ AppFunction :: p) sid <>
  session_at (prefix ++ AppArgument :: q) sid.
Proof.
  intro E; apply (proj1 (same_session_iff _ _ sid)) in E.
  unfold source_lane in E; rewrite !filter_app in E; cbn in E.
  apply app_inv_head in E; discriminate E.
Qed.

Theorem same_session_order p q sid :
  compatible p q -> p <> q ->
  session_at p sid = session_at q sid ->
  source_before p q \/ source_before q p.
Proof.
  intros C N E.
  apply (proj1 (same_session_iff p q sid)) in E.
  destruct (equal_lane_order p q C E) as [H|H].
  - contradiction.
  - exact H.
Qed.

Theorem same_session_sequence xs sid rank :
  StronglySorted (fun p q => rank p < rank q) xs ->
  (forall p q, In p xs -> In q xs -> compatible p q) ->
  (forall p q, In p xs -> In q xs ->
    session_at p sid = session_at q sid) ->
  respects xs rank ->
  StronglySorted source_before xs.
Proof.
  intros Sorted; induction Sorted as [|x xs Sorted IH Earlier];
    intros Compatible Session Chrono; [constructor|].
  constructor.
  - apply IH.
    + intros p q Hp Hq; apply Compatible; now right.
    + intros p q Hp Hq; apply Session; now right.
    + intros p q Hp Hq; apply Chrono; now right.
  - rewrite Forall_forall in Earlier |- *.
    intros y Hy.
    assert (InX : In x (x :: xs)) by now left.
    assert (InY : In y (x :: xs)) by now right.
    specialize (Earlier y Hy).
    assert (Different : x <> y).
    { intro E; subst; exact (Nat.lt_irrefl _ Earlier). }
    destruct (same_session_order x y sid (Compatible x y InX InY)
      Different (Session x y InX InY)) as [Before|After].
    + exact Before.
    + exfalso; exact (Nat.lt_asymm _ _ Earlier (Chrono y x InY InX After)).
Qed.

Theorem fifo_relative_order p q sid sender receiver :
  compatible p q -> p <> q ->
  session_at p sid = session_at q sid ->
  respects [p; q] sender -> respects [p; q] receiver ->
  (sender p < sender q <-> receiver p < receiver q).
Proof.
  intros C N E S R.
  assert (InP : In p [p; q]) by now left.
  assert (InQ : In q [p; q]) by (right; now left).
  destruct (same_session_order p q sid C N E) as [H|H].
  - split; intro; [apply R|apply S]; assumption.
  - pose proof (S q p InQ InP H) as HS.
    pose proof (R q p InQ InP H) as HR.
    split; intro Forward; exfalso.
    + exact (Nat.lt_asymm _ _ HS Forward).
    + exact (Nat.lt_asymm _ _ HR Forward).
Qed.

(* A combinatorial frontier lemma, NOT a cursor invariant theorem.
   q is the ghost outstanding sequence for ONE actual raw queue key,
   combining data and choice announcements. Raw queues need no source tags.

   The final premise is the unproved integration obligation: every
   outstanding mandatory predecessor of the next receive was received.
   Together with Outstanding this rules out an earlier outstanding head.
   No claim that actual cursors satisfy this premise is made here. *)
Theorem fifo_frontier_head
    (q : list occurrence) (y : occurrence) sid
    (sender : occurrence -> nat) (received : occurrence -> Prop) :
  StronglySorted (fun p q => sender p < sender q) q ->
  In y q ->
  (forall x, In x q -> compatible x y) ->
  (forall x, In x q -> session_at x sid = session_at y sid) ->
  respects q sender ->
  (forall x, In x q -> ~ received x) ->
  (forall x, In x q -> source_before x y -> received x) ->
  exists tail, q = y :: tail.
Proof.
  intros Sorted InY Compatible Session Chrono Outstanding Closed.
  destruct q as [|x tail]; [contradiction|].
  destruct InY as [E|InY].
  - subst; now exists tail.
  - assert (InX : In x (x :: tail)) by now left.
    assert (InY' : In y (x :: tail)) by now right.
    inversion Sorted as [|? ? SortTail Earlier]; subst.
    rewrite Forall_forall in Earlier.
    specialize (Earlier y InY).
    assert (Different : x <> y).
    { intro E; subst; exact (Nat.lt_irrefl _ Earlier). }
    destruct (same_session_order x y sid (Compatible x InX) Different
      (Session x InX)) as [Before|After].
    + exfalso; exact (Outstanding x InX (Closed x InX Before)).
    + exfalso; exact (Nat.lt_asymm _ _ Earlier (Chrono y x InY' InX After)).
Qed.

From ParkourTheories.Choreography Require Import Histories.RoleChronology
  RoleSteps.

Section ForkSessions.
Context {M E : Type -> Type} {Store : Type}.
Variable model : LocalEffects.local_model M E Parkour.Symbol.Symbol Store.
Variable roles : list Parkour.Symbol.Symbol.

(* Simultaneously live Fork children in a scoped cursor cannot share even a
   generated session, regardless of their independent scheduling. *)
Theorem scoped_fork_disjoint p X Y root
    (f : @cursor M E p (X -> Y)) (x : @cursor M E p X) a b sid :
  scoped root (Fork f x) -> future f a -> future x b ->
  session_at a sid <> session_at b sid.
Proof.
  intros [v [_ [Sf Sx]]] Fa Fx.
  destruct (scoped_future _ _ _ _ Sf a Fa) as [left ->].
  destruct (scoped_future _ _ _ _ Sx b Fx) as [right ->].
  unfold child; rewrite <- !app_assoc.
  apply app_branches_separate.
Qed.

Corollary code_history_fork_disjoint p X Y
    (c : Choreography.Choreo2.Choreo M p Y)
    (f : @cursor M E p (X -> Y)) (x : @cursor M E p X)
    s q events s' q' a b sid :
  role_history model roles (Code [] c) s q events (Fork f x) s' q' ->
  future f a -> future x b ->
  session_at a sid <> session_at b sid.
Proof.
  intros History Fa Fx.
  eapply scoped_fork_disjoint; [|exact Fa|exact Fx].
  eapply history_scoped; [exact History|apply path_prefix_refl].
Qed.

End ForkSessions.

Print Assumptions scoped_fork_disjoint.
Print Assumptions code_history_fork_disjoint.
