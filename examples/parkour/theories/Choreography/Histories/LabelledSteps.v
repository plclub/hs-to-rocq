From Stdlib Require Import Lists.List.
Require Import Parkour.Symbol Choreography.Choreo2.
From ParkourTheories Require Import Semantics.LocalEffects
  Choreography.RoleSteps Choreography.Histories.CursorHistories.
Import ListNotations.

(* A labelled primitive step records the label supplied by its caller.
   Silent descent and interleaving preserve that label. *)
Section Log.
Context {M E : Type -> Type} {S : Type} (model : local_model M E Symbol S)
  (p : Symbol) (Label : Type).
Variable leaf :
  forall B, @cursor M E p B -> Label -> @cursor M E p B -> Prop.

Inductive labelled_step :
  forall B, @cursor M E p B -> option Label -> @cursor M E p B -> Prop :=
| LabelledSilent B t u : primitive_silent model B t u -> labelled_step B t None
  u
| LabelledLeaf B t token u : leaf B t token u -> labelled_step B t (Some token)
  u
| LabelledSeq X Y o t label u (k : X -> Choreo M p Y) :
    labelled_step X t label u -> labelled_step Y (Seq o t k) label (Seq o u k)
| LabelledForkLeft X Y (f g : @cursor M E p (X -> Y)) label t :
    labelled_step (X -> Y) f label g -> labelled_step Y (Fork f t) label (Fork g
      t)
| LabelledForkRight X Y (f : @cursor M E p (X -> Y)) t label u :
    labelled_step X t label u -> labelled_step Y (Fork f t) label (Fork f u).

Definition snoc_token (labels : list Label) (t : option Label) :=
  match t with None => labels | Some x => labels ++ [x] end.

#[universes(template)]
Inductive local_log {B} (start : @cursor M E p B) :
  list Label -> @cursor M E p B -> Prop :=
| LogStart : local_log start [] start
| LogStep tr t token u : local_log start tr t -> labelled_step B t token u ->
    local_log start (snoc_token tr token) u.

Lemma labelled_step_plug X B (C : @cursor_context M E p X B) t label u :
  labelled_step X t label u -> labelled_step B (plug C t) label (plug C u).
Proof. induction C; cbn; auto using
  LabelledSeq,LabelledForkLeft,LabelledForkRight. Qed.

Lemma silent_labelled_step B t u : @silent M E S model p B t u -> labelled_step
  B t None u.
Proof.
  intro Sstep. destruct (silent_focus model p B _ _ Sstep) as (X & C & f & g &
    -> & Act & ->).
  apply labelled_step_plug, LabelledSilent. exact Act.
Qed.

Lemma log_silent_prefix B (start : @cursor M E p B) labels t u :
  local_log start labels t -> silent_prefix model t u -> local_log start labels
    u.
Proof.
  intros Prior Steps; induction Steps; [exact Prior|].
  apply IHSteps. exact (LogStep _ _ _ None _ Prior (silent_labelled_step _ _ _
    H)).
Qed.
End Log.
