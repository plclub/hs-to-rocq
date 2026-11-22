From Stdlib Require Import Lists.List.
Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree Choreography.Choreo2.
From Counterexample Require Import Family.
Import ListNotations.

(* This fragment has just the two constructors used below. Both rules
   constrain the actual family, including the dictionaries at each role. *)
Definition located {X l} (v : forall p, At X l p) (x : X) :=
  forall p (e : l = p), unAt (v p) e = x.

Inductive well_formed (R : list Symbol) (dst : Symbol) :
    (forall p, Choreo Id p (At unit dst p)) -> Prop :=
| wf_comm (src : Symbol) (v : forall p, At unit src p)
    (sh : Symbol -> Show unit) (rd : Symbol -> Read unit) :
    In src R -> In dst R -> located v tt ->
    (src <> dst -> forall x, @read unit (rd dst) (@show unit (sh src) x) = Some x) ->
    well_formed R dst (fun p => Perf
      (@Comm Id p unit src dst (sh p) (rd p) (known src) (known dst)
        MkSSymbol (v p) MkSSymbol))
| wf_cond (owner : Symbol) (v : forall p, At bool owner p)
    (sh : Symbol -> Show bool) (rd : Symbol -> Read bool)
    (k : forall p, bool -> Choreo Id p (At unit dst p)) :
    In owner R -> located v (unAt (v owner) eq_refl) ->
    (forall p, In p R -> owner <> p -> forall x,
      @read bool (rd p) (@show bool (sh owner) x) = Some x) ->
    (forall x, well_formed R dst (fun p => k p x)) ->
    well_formed R dst (fun p => Perf
      (@Cond Id p bool owner (At unit dst p) (sh p) (rd p) (known owner)
        MkSSymbol (v p) (k p))).

Lemma A_not_B : A <> B.
Proof. discriminate. Qed.

Theorem program_well_formed : NoDup roles /\ well_formed roles B program.
Proof.
  split.
  - repeat constructor; simpl; intuition discriminate.
  - apply (wf_cond roles B A choice (fun _ => show_bool) (fun _ => read_bool) branch).
    + simpl; auto.
    + intros p e; reflexivity.
    + intros p _ _ []; reflexivity.
    + intros x. apply (wf_comm roles B A payload
                         (fun _ => show_unit) (fun _ => read_unit)).
      * simpl; auto.
      * simpl; auto.
      * intros p e; reflexivity.
      * intros _ []; reflexivity.
Qed.

(* Role-local cursors for exactly these occurrences. Cond and Comm have
   separate typed delivery slots, independently of any transport/session.
   A chooses/enters its branch without waiting for B. B enters its own
   branch only with its delivered value. *)
Inductive cursor (p : Symbol) :=
| AtCond
| AtComm (chosen : bool)
| Done (result : At unit B p).
Arguments AtCond {p}.
Arguments AtComm {p} _.
Arguments Done {p} _.

Definition residual {p} (pos : cursor p) : Choreo Id p (At unit B p) :=
  match pos with
  | AtCond => program p
  | AtComm b => branch p b
  | Done r => Pure r
  end.

Definition announced := unAt (choice A) eq_refl.
Definition sent := unAt (payload A) eq_refl.
Definition off_B : At unit B A :=
  Mk_At (fun e => False_rect _ (A_not_B (eq_sym e))).
Definition at_B (v : unit) : At unit B B := Mk_At (fun _ => v).

(* Decode each cursor as actual generated source syntax. In particular,
   taking either Cond action substitutes that role's choice into its
   continuation; the communication then uses that same role's At input. *)
Lemma cond_cursor p :
  residual (@AtCond p) =
  Perf (@Cond Id p bool A (At unit B p) show_bool read_bool (known A)
    MkSSymbol (choice p) (fun b => residual (AtComm b))).
Proof. reflexivity. Qed.

Lemma comm_cursor p b :
  residual (@AtComm p b) =
  Perf (@Comm Id p unit A B show_unit read_unit (known A) (known B)
    MkSSymbol (payload p) MkSSymbol).
Proof. reflexivity. Qed.

Lemma done_cursor p (r : At unit B p) : residual (Done r) = Pure r.
Proof. reflexivity. Qed.

Lemma input_values : announced = true /\ sent = tt.
Proof. split; reflexivity. Qed.

Lemma received_value d : unAt (at_B d) eq_refl = d.
Proof. reflexivity. Qed.

Record state := State {
  posA : cursor A; posB : cursor B;
  pending_choice : option bool; pending_data : option unit
}.
Definition initial := State AtCond AtCond None None.
Inductive event := announce (v : bool) | hear (v : bool) | send (v : unit) | receive (v : unit).

Inductive cstep : state -> event -> state -> Prop :=
| do_announce b d :
    cstep (State AtCond b None d) (announce announced)
          (State (AtComm announced) b (Some announced) d)
| do_hear a v d :
    cstep (State a AtCond (Some v) d) (hear v)
          (State a (AtComm v) None d)
| do_send v b c :
    cstep (State (AtComm v) b c None) (send sent)
          (State (Done off_B) b c (Some sent))
| do_receive a v c d :
    cstep (State a (AtComm v) c (Some d)) (receive d)
          (State a (Done (at_B d)) c None).

Definition final s := exists x y, s = State (Done x) (Done y) None None.
Definition ready s := final s \/ exists e s', cstep s e s'.
Inductive run : list event -> state -> Prop :=
| start : run [] initial
| snoc t s e s' : run t s -> cstep s e s' -> run (t ++ [e]) s'.

(* Two independent actions are enabled after the announcement. The
   invariant retains each intermediate prefix, including both pending
   deliveries at once. *)
Inductive reachable_shape : state -> Prop :=
| start_shape : reachable_shape initial
| announced_shape : reachable_shape
    (State (AtComm announced) AtCond (Some announced) None)
| heard_shape : reachable_shape
    (State (AtComm announced) (AtComm announced) None None)
| both_pending_shape : reachable_shape
    (State (Done off_B) AtCond (Some announced) (Some sent))
| data_pending_shape : reachable_shape
    (State (Done off_B) (AtComm announced) None (Some sent))
| finished_shape : reachable_shape
    (State (Done off_B) (Done (at_B sent)) None None).

Lemma run_shape t s : run t s -> reachable_shape s.
Proof.
  induction 1 as [|t s e s' _ IH step].
  - constructor.
  - destruct IH; inversion step; constructor.
Qed.

Theorem source_deadlock_free : forall t s, run t s -> ready s.
Proof.
  intros t s H; destruct (run_shape t s H);
    first [right; do 2 eexists; constructor | left; do 2 eexists; reflexivity].
Qed.
