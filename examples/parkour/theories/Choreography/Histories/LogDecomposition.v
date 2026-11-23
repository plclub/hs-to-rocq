From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Choreography.Histories.LabelledSteps
  Semantics.LocalEffects Choreography.Occurrences Choreography.RoleSteps
  Choreography.Histories.CursorHistories.
Require Import Parkour.Symbol Choreography.Choreo2 Control.Monad.Tree.
Import ListNotations.
Set Universe Polymorphism.

(* A shuffle retains the order in each child, without sorting the parent's
   actual chronological log into a function-then-argument concatenation. *)
Inductive log_shuffle {Label : Type} : list Label -> list Label -> list Label ->
  Prop :=
| ShuffleEmpty : log_shuffle [] [] []
| ShuffleLeft xs ys zs e :
    log_shuffle xs ys zs -> log_shuffle (xs ++ [e]) ys (zs ++ [e])
| ShuffleRight xs ys zs e :
    log_shuffle xs ys zs -> log_shuffle xs (ys ++ [e]) (zs ++ [e]).

(* A label can quantify over program types and inhabit a
   higher universe than the monomorphic Stdlib list theorems. *)
Lemma log_append_member {Label} (e : Label) (xs ys : list Label) :
  In e (xs ++ ys) <-> In e xs \/ In e ys.
Proof.
  revert xs; fix IH 1; intros [|x xs]; cbn; [tauto|].
  specialize (IH xs). tauto.
Qed.

Lemma log_app_nil_r {Label} (xs : list Label) : xs ++ [] = xs.
Proof.
  revert xs; fix IH 1; intros [|a xs]; cbn;
    [reflexivity|apply f_equal; apply IH].
Qed.

Lemma log_app_assoc {Label} (xs ys zs : list Label) :
  xs ++ ys ++ zs = (xs ++ ys) ++ zs.
Proof.
  revert xs; fix IH 1; intros [|a xs]; cbn;
    [reflexivity|apply f_equal; apply IH].
Qed.

Lemma log_shuffle_member {Label} (xs ys zs : list Label) :
  log_shuffle xs ys zs -> forall e, In e zs <-> In e xs \/ In e ys.
Proof.
  induction 1; intro a; cbn.
  - tauto.
  - repeat rewrite log_append_member. cbn. rewrite IHlog_shuffle. tauto.
  - repeat rewrite log_append_member. cbn. rewrite IHlog_shuffle. tauto.
Qed.

Section Decompose.
Context {M E : Type -> Type} {S : Type}
  (model : local_model M E Symbol S) (p : Symbol) (Label : Type).
Local Notation cur := (@cursor M E p).
Variable leaf : forall B, cur B -> Label -> cur B -> Prop.
Local Notation step := (labelled_step model p Label leaf).
Local Notation log := (local_log model p Label leaf).

(* This is solely a source restriction; the actual stamped primitive steps
   supply it by inspecting primitive_action, without forgetting their tokens
   or imposing any value/reply determinism. *)
Definition primitive_cursor {B} (t : cur B) : Prop :=
  match t with
  | Code _ c =>
    match c with Perf _ => True | _ => False end
  | Local _ _ => True
  | _ => False
  end.
Hypothesis leaf_primitive :
  forall B (t : cur B) e u, leaf B t e u -> primitive_cursor t.

Lemma primitive_action_cursor R B t s q a u s' q' :
  primitive_action model R B t s q a u s' q' -> primitive_cursor t.
Proof. destruct 1; exact I. Qed.

Definition labelled_step_shape {B} (t : cur B) (label : option Label) : cur B ->
  Prop :=
  match t in cursor _ C return cur C -> Prop with
  | Code o c =>
    match c in Tree _ C return cur C -> Prop with
    | Pure x => fun u => label = None /\ u = Returned x
    | Bind a k => fun u =>
        label = None /\ u = Seq o (Code (child o BindPrefix) a) k
    | App f x => fun u =>
        label = None /\
        u = Fork (Code (child o AppFunction) f) (Code (child o AppArgument) x)
    | Perf _ => fun _ => True
    end
  | Returned _ => fun _ => False
  | Local _ _ => fun _ => True
  | Seq o t k => fun u =>
      (exists x, label = None /\ t = Returned x /\
        u = Code (child o BindBody) (k x)) \/
      (exists v, step _ t label v /\ u = Seq o v k)
  | Fork f x => fun u =>
      (exists v, step _ f label v /\ u = Fork v x) \/
      (exists v, step _ x label v /\ u = Fork f v) \/
      (exists fv xv, label = None /\ f = Returned fv /\ x = Returned xv /\
        u = Returned (fv xv))
  end.

Lemma labelled_step_shape_correct B t label u :
  step B t label u -> labelled_step_shape t label u.
Proof.
  destruct 1.
  - destruct H; cbn; auto.
    + left. eexists. repeat split; reflexivity.
    + right. right. do 2 eexists. repeat split; reflexivity.
  - pose proof (leaf_primitive _ _ _ _ H) as Primitive.
    destruct t; cbn in *; try contradiction; auto.
    destruct c; cbn in *; tauto.
  - cbn. right. eexists. split; [eassumption|reflexivity].
  - cbn. left. eexists. split; [eassumption|reflexivity].
  - cbn. right. left. eexists. split; [eassumption|reflexivity].
Qed.

Inductive bind_log_cut {X Y} (o : occurrence)
    (a : Choreo M p X) (k : X -> Choreo M p Y) :
    list Label -> cur Y -> Prop :=
| BindUnopened : bind_log_cut o a k [] (Code o (Bind a k))
| BindInPrefix tr t :
    log (Code (child o BindPrefix) a) tr t ->
    bind_log_cut o a k tr (Seq o t k)
| BindInBody prefix body x t :
    log (Code (child o BindPrefix) a) prefix (Returned x) ->
    log (Code (child o BindBody) (k x)) body t ->
    bind_log_cut o a k (prefix ++ body) t.

Lemma bind_log_cut_step X Y o (a : Choreo M p X) (k : X -> Choreo M p Y)
    tr t label u :
  bind_log_cut o a k tr t -> step Y t label u ->
  bind_log_cut o a k (snoc_token Label tr label) u.
Proof.
  intros Cut Step. destruct Cut.
  - destruct (labelled_step_shape_correct _ _ _ _ Step) as [-> ->].
    cbn. apply BindInPrefix. constructor.
  - destruct (labelled_step_shape_correct _ _ _ _ Step)
      as [(x & -> & Eq & ->)|(v & Move & ->)].
    + subst t. cbn. rewrite <- (log_app_nil_r tr).
      eapply BindInBody; [eassumption|constructor].
    + apply BindInPrefix. eapply LogStep; eassumption.
  - destruct label; cbn.
    + rewrite <- log_app_assoc. eapply BindInBody; [eassumption|].
      exact (LogStep _ _ _ _ _ _ _ _ _ H0 Step).
    + eapply BindInBody; [eassumption|].
      exact (LogStep _ _ _ _ _ _ _ _ _ H0 Step).
Qed.

Theorem local_log_bind X Y o (a : Choreo M p X)
    (k : X -> Choreo M p Y) tr t :
  log (Code o (Bind a k)) tr t -> bind_log_cut o a k tr t.
Proof.
  intro Run. induction Run.
  - constructor.
  - eapply bind_log_cut_step; eassumption.
Qed.

(* This elimination form exposes only equalities at the fixed outer type.
   In particular consumers need not inject existential cursor Type indices. *)
Corollary local_log_bind_cases X Y o (a : Choreo M p X)
    (k : X -> Choreo M p Y) tr t :
  log (Code o (Bind a k)) tr t ->
  (tr = [] /\ t = Code o (Bind a k)) \/
  (exists ct, log (Code (child o BindPrefix) a) tr ct /\ t = Seq o ct k) \/
  (exists prefix body x,
    tr = prefix ++ body /\
    log (Code (child o BindPrefix) a) prefix (Returned x) /\
    log (Code (child o BindBody) (k x)) body t).
Proof.
  intro Run. destruct (local_log_bind _ _ _ _ _ _ _ Run).
  - left. split; reflexivity.
  - right. left. eexists. split; [eassumption|reflexivity].
  - right. right. do 3 eexists. split; [reflexivity|].
    split; eassumption.
Qed.

Corollary local_log_bind_return X Y o (a : Choreo M p X)
    (k : X -> Choreo M p Y) tr (y : Y) :
  log (Code o (Bind a k)) tr (Returned y) ->
  exists prefix body x,
    tr = prefix ++ body /\
    log (Code (child o BindPrefix) a) prefix (Returned x) /\
    log (Code (child o BindBody) (k x)) body (Returned y).
Proof.
  intro Run. destruct (local_log_bind_cases _ _ _ _ _ _ _ Run)
    as [[_ Bad]|[(ct & _ & Bad)|Done]]; try discriminate; exact Done.
Qed.

Inductive app_log_cut {X Y} (o : occurrence)
    (f : Choreo M p (X -> Y)) (x : Choreo M p X) :
    list Label -> cur Y -> Prop :=
| AppUnopened : app_log_cut o f x [] (Code o (App f x))
| AppInChildren function_log argument_log tr cf cx :
    log (Code (child o AppFunction) f) function_log cf ->
    log (Code (child o AppArgument) x) argument_log cx ->
    log_shuffle function_log argument_log tr ->
    app_log_cut o f x tr (Fork cf cx)
| AppJoined function_log argument_log tr fv xv :
    log (Code (child o AppFunction) f) function_log (Returned fv) ->
    log (Code (child o AppArgument) x) argument_log (Returned xv) ->
    log_shuffle function_log argument_log tr ->
    app_log_cut o f x tr (Returned (fv xv)).

Lemma app_log_cut_step X Y o (f : Choreo M p (X -> Y))
    (x : Choreo M p X) tr t label u :
  app_log_cut o f x tr t -> step Y t label u ->
  app_log_cut o f x (snoc_token Label tr label) u.
Proof.
  intros Cut Step. destruct Cut.
  - destruct (labelled_step_shape_correct _ _ _ _ Step) as [-> ->].
    cbn. eapply AppInChildren; constructor.
  - destruct (labelled_step_shape_correct _ _ _ _ Step)
      as [(v & Move & ->)|[(v & Move & ->)|(fv & xv & -> & Ef & Ex & ->)]].
    + eapply AppInChildren; [eapply LogStep; eassumption|exact H0|].
      destruct label; cbn; auto using ShuffleLeft.
    + eapply AppInChildren; [exact H|eapply LogStep; eassumption|].
      destruct label; cbn; auto using ShuffleRight.
    + subst cf cx. cbn. eapply AppJoined; eassumption.
  - exact (False_rect _ (labelled_step_shape_correct _ _ _ _ Step)).
Qed.

Theorem local_log_app X Y o (f : Choreo M p (X -> Y))
    (x : Choreo M p X) tr t :
  log (Code o (App f x)) tr t -> app_log_cut o f x tr t.
Proof.
  intro Run. induction Run.
  - constructor.
  - eapply app_log_cut_step; eassumption.
Qed.

Corollary local_log_app_cases X Y o (f : Choreo M p (X -> Y))
    (x : Choreo M p X) tr t :
  log (Code o (App f x)) tr t ->
  (tr = [] /\ t = Code o (App f x)) \/
  (exists function_log argument_log cf cx,
    log (Code (child o AppFunction) f) function_log cf /\
    log (Code (child o AppArgument) x) argument_log cx /\
    log_shuffle function_log argument_log tr /\ t = Fork cf cx) \/
  (exists function_log argument_log fv xv,
    log (Code (child o AppFunction) f) function_log (Returned fv) /\
    log (Code (child o AppArgument) x) argument_log (Returned xv) /\
    log_shuffle function_log argument_log tr /\ t = Returned (fv xv)).
Proof.
  intro Run. destruct (local_log_app _ _ _ _ _ _ _ Run).
  - left. split; reflexivity.
  - right. left. do 4 eexists. repeat split; eassumption || reflexivity.
  - right. right. do 4 eexists. repeat split; eassumption || reflexivity.
Qed.

Definition cursor_result {B} (t : cur B) : option B :=
  match t in cursor _ C return option C with
  | Returned x => Some x
  | _ => None
  end.

Corollary local_log_app_return X Y o (f : Choreo M p (X -> Y))
    (x : Choreo M p X) tr (y : Y) :
  log (Code o (App f x)) tr (Returned y) ->
  exists function_log argument_log fv xv,
    log (Code (child o AppFunction) f) function_log (Returned fv) /\
    log (Code (child o AppArgument) x) argument_log (Returned xv) /\
    log_shuffle function_log argument_log tr /\ y = fv xv.
Proof.
  intro Run. destruct (local_log_app_cases _ _ _ _ _ _ _ Run)
    as [[_ Bad]|[(fl & al & cf & cx & _ & _ & _ & Bad)|
      (fl & al & fv & xv & F & Xv & Shuffle & Eq)]]; try discriminate.
  exists fl, al, fv, xv. repeat split; try assumption.
  pose proof (f_equal (@cursor_result Y) Eq) as Values.
  cbn in Values. now injection Values.
Qed.
End Decompose.
