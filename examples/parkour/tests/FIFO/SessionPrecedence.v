From Stdlib Require Import Lists.List Sorting.Sorted.
From ParkourTheories Require Import Choreography.Occurrences
  Choreography.Precedence Projection.SessionPaths.
Require Import Choreography.Network.
Import ListNotations.

(* Frozen before implementation: these statements use actual source positions
   and generated session constructors, not a substitute session datatype. *)
Check session_at_child :
  forall o e sid,
    session_at (child o e) sid =
    match e with
    | AppFunction => Nest (Data.Either.Left tt) (session_at o sid)
    | AppArgument => Nest (Data.Either.Right tt) (session_at o sid)
    | _ => session_at o sid
    end.

Check same_session_iff :
  forall p q sid,
    session_at p sid = session_at q sid <->
    source_lane p = source_lane q.

Check source_before_irreflexive :
  forall p, ~ source_before p p.

Check same_session_order :
  forall p q sid,
    compatible p q -> p <> q ->
    session_at p sid = session_at q sid ->
    source_before p q \/ source_before q p.

Check same_session_sequence :
  forall xs sid rank,
    StronglySorted (fun p q => rank p < rank q) xs ->
    (forall p q, In p xs -> In q xs -> compatible p q) ->
    (forall p q, In p xs -> In q xs ->
      session_at p sid = session_at q sid) ->
    respects xs rank ->
    StronglySorted source_before xs.

Check fifo_relative_order :
  forall p q sid sender receiver,
    compatible p q -> p <> q ->
    session_at p sid = session_at q sid ->
    respects [p; q] sender -> respects [p; q] receiver ->
    (sender p < sender q <-> receiver p < receiver q).

Check fifo_frontier_head :
  forall (q : list occurrence) (y : occurrence) sid
    (sender : occurrence -> nat) (received : occurrence -> Prop),
    StronglySorted (fun p q => sender p < sender q) q ->
    In y q ->
    (forall x, In x q -> compatible x y) ->
    (forall x, In x q -> session_at x sid = session_at y sid) ->
    respects q sender ->
    (forall x, In x q -> ~ received x) ->
    (forall x, In x q -> source_before x y -> received x) ->
    exists tail, q = y :: tail.

Example reused_nested_app :
  let p := [BindPrefix; AppFunction; ChoiceBody; AppArgument] in
  let q := [BindBody; AppFunction; AppArgument] in
  p <> q /\
  session_at p Root = Nest (Data.Either.Right tt)
    (Nest (Data.Either.Left tt) Root) /\
  session_at p Root = session_at q Root /\
  source_before p q.
Proof. cbn; repeat split; try discriminate; constructor. Qed.

Example cond_bind_overlap :
  source_before [ChoiceBody; BindPrefix] [ChoiceBody; BindBody].
Proof. constructor; constructor. Qed.

Example choice_ancestor :
  source_before [AppFunction]
    [AppFunction; ChoiceBody; AppArgument].
Proof. constructor; constructor. Qed.

Example opposite_app_sessions :
  session_at [BindPrefix; AppFunction; ChoiceBody] Root <>
  session_at [BindBody; AppArgument; ChoiceBody] Root.
Proof. discriminate. Qed.

Print Assumptions same_session_sequence.
Print Assumptions fifo_relative_order.
Print Assumptions fifo_frontier_head.
