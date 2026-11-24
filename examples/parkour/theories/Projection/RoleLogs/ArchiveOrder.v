From Stdlib Require Import Lists.List.
From ParkourTheories Require Import Semantics.LocalEffects
  Choreography.RoleSteps Choreography.Execution
  Choreography.Histories.CursorHistories Choreography.Histories.LabelledSteps
  Choreography.Histories.LogDecomposition Projection.Matching.ObservationArchive
  Semantics.SharedState Network.Mailboxes Projection.Matching.PayloadHistory.
Require Import Parkour.Symbol Choreography.Choreo2.
Import ListNotations.

Section Stamped.
Context {M E Store Input} (model : local_model M E role (Store * Input))
  (stores : role -> Store) (input : Input) (R : list role) (A : role -> Type)
  (c : forall p, Choreo M p (A p)).
Local Arguments positions {M E Store A} _ _.
Local Arguments Choreography.Execution.shared_store {M E Store A} _.
Local Arguments deliveries {M E Store A} _.

Definition stamped p B (t : @cursor M E p B) (e : (observed_entry model stores
  input R A c) p) u :=
  let s := (entry_source model stores input R A c) p e in let s' :=
    (entry_source_after model stores input R A c) p e in
  let st := Choreography.Execution.shared_store s in let st' :=
    Choreography.Execution.shared_store s' in
  primitive_action (shared_model model) R B t st (deliveries s) ((entry_action
    model stores input R A c) p e) u st' (deliveries
    s') /\
  observed (shared_model model) R B t st (deliveries s) ((entry_action model
    stores input R A c) p e) u st' (deliveries s')
    (entry_network_action model stores input R A c p e)
    (entry_ghosts model stores input R A c p e) (entry_ghosts_after model stores
      input R A c p e)
    (entry_batch model stores input R A c p e).

Definition actor_log p := @local_log M E _ (shared_model model) p
  ((observed_entry model stores input R A c) p) (stamped p).

Fixpoint in_order p (items : list (located model stores input R A c p)) : list
  ((observed_entry model stores input R A c) p) :=
  match items with [] => [] | (_,e) :: tail => in_order p tail ++ [e] end.

Theorem archive_role_log tc s tn n gs past ar :
  (observed_archives model stores input R A c) tc s tn n gs past ar ->
  forall p, actor_log p (A p) (Code [] (c p))
    (in_order p (ar p))
    (positions s p).
Proof.
  induction 1 as [|tc s tn n gs past ar who e H IH Tc Source Tn Net Ghost Past
    Matched];
    intro p; [constructor|].
  destruct (role_eq_dec who p) as [->|Ne].
  - rewrite add_entry_same. cbn [in_order].
    pose proof (entry_end model stores input R A c p e) as End.
    rewrite End. eapply (LogStep _ _ _ _ _ _ _ (Some e)).
    + eapply log_silent_prefix; [|exact (entry_silent model stores input R A c p
      e)].
      rewrite Source. exact (IH p).
    + apply labelled_step_plug, LabelledLeaf. split.
      * exact (entry_primitive model stores input R A c p e).
      * exact (observation_at_focus model stores input R A c p e).
  - rewrite add_entry_other by exact Ne.
    pose proof (entry_pair model stores input R A c who e) as Pair.
    pose proof (entry_primitive model stores input R A c who e) as Prim.
    pose proof (CursorHistories.role_step_actor
      (shared_model model) R _ _ _ _ _ _ _ _ _
      (primitive_is_role_step (shared_model model) R _ _ _ _ _ _ _ _ _ Prim)) as
        Actor.
    destruct Pair as [r pre post t u s1 n1 a b gs1 ev Member Before After Obs
      Frame NS].
    pose proof (observed_decorated (shared_model model) R
      _ _ _ _ _ _ _ _ _ _ _ _ _ Obs) as D.
    pose proof (CursorHistories.role_step_actor
      (shared_model model) R _ _ _ _ _ _ _ _ _
      (PrefixRelation.decorated_source (shared_model model) R
        _ _ _ _ _ _ _ _ _ _ _ _ D)) as Same.
    rewrite <- Frame by congruence. rewrite Source. exact (IH p).
Qed.
End Stamped.

Set Universe Polymorphism.
Section StampedSource.
Context {M E Store Input}
  (model : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input : Input) (R : list Symbol)
  (A : Symbol -> Type) (c : forall p, Choreo M p (A p)).

Lemma stamped_primitive_cursor p B t e u :
  stamped model stores input R A c p B t e u -> primitive_cursor p t.
Proof.
  intros [Primitive _].
  eapply primitive_action_cursor. exact Primitive.
Qed.
End StampedSource.
