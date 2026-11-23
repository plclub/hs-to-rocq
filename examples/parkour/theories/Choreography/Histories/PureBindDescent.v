From Stdlib Require Import Lists.List.
Require Import Choreography.Choreo2 Control.Monad.Tree Parkour.Symbol.
From ParkourTheories.Choreography Require Import Occurrences RoleSteps
  Histories.TransitionArchive WellFormedness Histories.SyntaxDecomposition
  Results.FiniteSelection.
Import ListNotations.

(* A concrete dynamic descent case. A Pure prefix requires no replay-family
   law: its actual returned cut determines its result. The entered roster and
   its values below are extracted from the supplied cuts, not chosen from the
   source result relation. *)
Section PureBind.
Context {M E : Type -> Type} {Store : Type}.
Variable model : LocalEffects.local_model M E Symbol Store.
Variable configured : list Symbol.

Definition pure_shape p A o (c : Choreo M p A) (t : @cursor M E p A) : Prop :=
  match c in Tree _ B return cursor p B -> Prop with
  | Pure x => fun t => t = Code o (Pure x) \/ t = Returned x
  | _ => fun _ => True
  end t.

Lemma pure_cut_shape p A o c t :
  syntax_cut model configured p A o c t -> pure_shape p A o c t.
Proof.
  destruct 1; cbn [pure_shape]; try exact I.
  - destruct c; cbn; try exact I. now left.
  - now right.
  - destruct H; exact I.
Qed.

Lemma pure_cut_returned p A o (x v : A) t :
  syntax_cut model configured p A o (Pure x) t ->
  cut_returned p t v -> v = x.
Proof.
  intros Cut Return.
  destruct (pure_cut_shape p A o _ t Cut) as [Initial|Final];
    subst t;
    cbn [cut_returned] in Return; [contradiction|exact Return].
Qed.

Theorem pure_bind_actual_descent S A B
    (input : values A S)
    (k : forall p, S p -> A p -> Choreo M p (B p))
    (K : forall D, values A D -> results B)
    active completed
    (inc : includes (fun p => In p active) S)
    o (cuts : cursor_family B active)
    (done : includes (fun p => In p completed) (fun p => In p active))
    (v : values B (fun p => In p completed)) :
  NoDup active -> NoDup completed ->
  (forall p (s t : S p), s = t) ->
  (forall D (x : values A D) (inside : includes D S),
    pure_results input D x ->
    structural configured M D B
      (fun p d => k p (inside p d) (x p d)) (K D x)) ->
  family_syntax_cuts model configured S B
    (fun p s => Bind (Pure (input p s)) (k p s)) active inc o cuts ->
  family_returned_values B active completed done cuts v ->
  exists entered
    (inside : includes (fun p => In p entered) (fun p => In p active))
    (finished : includes (fun p => In p completed) (fun p => In p entered))
    (prefix : cursor_family A active)
    (x : values A (fun p => In p entered))
    (body : cursor_family B entered),
    NoDup entered /\
    family_syntax_cuts model configured S A (fun p s => Pure (input p s))
      active inc (child o BindPrefix) prefix /\
    family_returned_values A active entered inside prefix x /\
    pure_results input (fun p => In p entered) x /\
    structural configured M (fun p => In p entered) B
      (fun p d => k p (inc p (inside p d)) (x p d))
      (K (fun p => In p entered) x) /\
    family_syntax_cuts model configured (fun p => In p entered) B
      (fun p d => k p (inc p (inside p d)) (x p d))
      entered (fun p d => d) (child o BindBody) body /\
    family_returned_values B entered completed finished body v.
Proof.
  intros NA NC PI Body At Ret.
  destruct (replay_bind_actual model configured S A B
    (fun p s => Pure (input p s)) k active completed inc o cuts done v
    NA NC At Ret)
    as (entered & inside & finished & prefix & x & body &
      NE & PrefixAt & PrefixRet & BodyAt & BodyRet).
  assert (Result : pure_results input (fun p => In p entered) x).
  { split.
    - intros p d. exact (inc p (inside p d)).
    - intros p d s.
      rewrite <- (PI p (inc p (inside p d)) s).
      eapply pure_cut_returned; [apply PrefixAt | apply PrefixRet]. }
  exists entered, inside, finished, prefix, x, body.
  split; [exact NE|].
  split; [exact PrefixAt|].
  split; [exact PrefixRet|].
  split; [exact Result|].
  split; [apply Body; exact Result|].
  split; [exact BodyAt|exact BodyRet].
Qed.
End PureBind.

Print Assumptions pure_cut_returned.
Print Assumptions pure_bind_actual_descent.
