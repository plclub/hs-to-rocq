From Stdlib Require Import Lists.List Sorting.Sorted Arith.PeanoNat.
Require Import DeadlockSource Choreography.Network.
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

(* Structural compatibility is a certificate about coexisting ACTION
   positions. It must be established from the common source shape/history;
   arbitrary equal-session paths need not have this property.

   Bind and App themselves are not actions. A Cond action can be an
   ancestor of another action only through ChoiceBody. *)
Inductive compatible : occurrence -> occurrence -> Prop :=
| CEqual : compatible [] []
| CUnder e p q : compatible p q -> compatible (e :: p) (e :: q)
| CBindLR p q : compatible (BindPrefix :: p) (BindBody :: q)
| CBindRL p q : compatible (BindBody :: p) (BindPrefix :: q)
| CAppLR p q : compatible (AppFunction :: p) (AppArgument :: q)
| CAppRL p q : compatible (AppArgument :: p) (AppFunction :: q)
| CChoiceL p : compatible [] (ChoiceBody :: p)
| CChoiceR p : compatible (ChoiceBody :: p) [].

(* Mandatory structural order, not a scheduler's chosen App interleaving. *)
Inductive source_before : occurrence -> occurrence -> Prop :=
| BBind p q : source_before (BindPrefix :: p) (BindBody :: q)
| BChoice p : source_before [] (ChoiceBody :: p)
| BUnder e p q :
    source_before p q -> source_before (e :: p) (e :: q).

Lemma source_before_asymmetric p q :
  source_before p q -> ~ source_before q p.
Proof.
  intro H; induction H as [p q|p|e p q H IH];
    intro Reverse; inversion Reverse; subst.
  now apply IH.
Qed.

Lemma source_before_irreflexive p : ~ source_before p p.
Proof.
  intro H; exact (source_before_asymmetric p p H H).
Qed.

Lemma source_before_transitive p q r :
  source_before p q -> source_before q r -> source_before p r.
Proof.
  intro H; revert r; induction H as [p q|p|e p q H IH];
    intros r Next; inversion Next; subst; try constructor.
  now apply IH.
Qed.

Lemma compatible_reflexive p : compatible p p.
Proof.
  induction p as [|e p IH]; constructor; assumption.
Qed.

Lemma compatible_symmetric p q : compatible p q -> compatible q p.
Proof.
  intro H; induction H; constructor; assumption.
Qed.

Lemma compatible_context prefix p q :
  compatible p q -> compatible (prefix ++ p) (prefix ++ q).
Proof.
  intro H; induction prefix as [|e prefix IH]; cbn; [exact H|].
  now constructor.
Qed.

Lemma source_before_context prefix p q :
  source_before p q -> source_before (prefix ++ p) (prefix ++ q).
Proof.
  intro H; induction prefix as [|e prefix IH]; cbn; [exact H|].
  now constructor.
Qed.

Lemma source_lane_cancel e p q :
  source_lane (e :: p) = source_lane (e :: q) ->
  source_lane p = source_lane q.
Proof.
  destruct e; cbn; intro E; try exact E; now injection E.
Qed.

Theorem equal_lane_order p q :
  compatible p q -> source_lane p = source_lane q ->
  p = q \/ source_before p q \/ source_before q p.
Proof.
  intro C; induction C; intro E.
  - now left.
  - apply source_lane_cancel in E.
    destruct (IHC E) as [->|[H|H]].
    + now left.
    + right; left; now constructor.
    + right; right; now constructor.
  - right; left; constructor.
  - right; right; constructor.
  - discriminate E.
  - discriminate E.
  - right; left; constructor.
  - right; right; constructor.
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

(* Ranks describe finite history positions only. Requiring a natural-valued
   ranking of EVERY syntax position would be impossible: arbitrarily many
   ChoiceBody descendants in a Bind prefix precede its fixed body. *)
Definition respects (events : list occurrence) (rank : occurrence -> nat) :=
  forall p q, In p events -> In q events ->
    source_before p q -> rank p < rank q.

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
