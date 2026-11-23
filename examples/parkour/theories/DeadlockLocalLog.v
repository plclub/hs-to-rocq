From Stdlib Require Import Lists.List.
Require Import DeadlockLocal DeadlockSource DeadlockCoherence DeadlockObservedCut
  DeadlockState DeadlockNetwork DeadlockPast Parkour.Symbol Choreography.Choreo2.
Import ListNotations.

(* Unlike a log of source labels, an L token may name a particular paired
   transition, including its before/after mailboxes and actual codec. Silent
   descent and interleaving never retag the token. *)
Section Log.
Context {M E : Type -> Type} {S : Type} (model : local_model M E role S)
  (p : role) (L : Type).
Local Notation cur := (@cursor M E p).
Variable leaf : forall B, cur B -> L -> cur B -> Prop.

Inductive micro : forall B, cur B -> option L -> cur B -> Prop :=
| MicroSilent B t u : primitive_silent model B t u -> micro B t None u
| MicroLeaf B t token u : leaf B t token u -> micro B t (Some token) u
| MicroSeq X Y o t tok u (k : X -> Choreo M p Y) :
    micro X t tok u -> micro Y (Seq o t k) tok (Seq o u k)
| MicroLeft X Y (f g : cur (X -> Y)) tok t :
    micro (X -> Y) f tok g -> micro Y (Fork f t) tok (Fork g t)
| MicroRight X Y (f : cur (X -> Y)) t tok u :
    micro X t tok u -> micro Y (Fork f t) tok (Fork f u).

Definition snoc_token (tr : list L) (t : option L) :=
  match t with None => tr | Some x => tr ++ [x] end.

#[universes(template)]
Inductive local_log {B} (start : cur B) : list L -> cur B -> Prop :=
| LogStart : local_log start [] start
| LogStep tr t token u : local_log start tr t -> micro B t token u ->
    local_log start (snoc_token tr token) u.

Lemma micro_plug X B (C : @cursor_context M E p X B) t tok u :
  micro X t tok u -> micro B (plug C t) tok (plug C u).
Proof. induction C; cbn; auto using MicroSeq,MicroLeft,MicroRight. Qed.

Lemma micro_silent B t u : @silent M E S model p B t u -> micro B t None u.
Proof.
  intro Sstep. destruct (silent_focus model p B _ _ Sstep) as (X & C & f & g & -> & Act & ->).
  apply micro_plug, MicroSilent. exact Act.
Qed.

Lemma log_silent_prefix B (start : @cursor M E p B) tr t u :
  local_log start tr t -> silent_prefix model t u -> local_log start tr u.
Proof.
  intros Prior Steps; induction Steps; [exact Prior|].
  apply IHSteps. exact (LogStep _ _ _ None _ Prior (micro_silent _ _ _ H)).
Qed.
End Log.

Section Stamped.
Context {M E Store Input} (model : local_model M E role (Store * Input))
  (stores : role -> Store) (input : Input) (R : list role) (A : role -> Type)
  (c : forall p, Choreo M p (A p)).
Local Notation sm := (shared_model model).
Local Notation entry := (observed_entry model stores input R A c).
Local Notation archives := (observed_archives model stores input R A c).
Local Notation action_of := (entry_action model stores input R A c).
Local Notation source_of := (entry_source model stores input R A c).
Local Notation after_of := (entry_source_after model stores input R A c).
Local Arguments positions {M E Store A} _ _.
Local Arguments DeadlockSource.shared_store {M E Store A} _.
Local Arguments deliveries {M E Store A} _.

Definition stamped p B (t : @cursor M E p B) (e : entry p) u :=
  let s := source_of p e in let s' := after_of p e in
  let st := DeadlockSource.shared_store s in let st' := DeadlockSource.shared_store s' in
  primitive_action sm R B t st (deliveries s) (action_of p e) u st' (deliveries s') /\
  observed sm R B t st (deliveries s) (action_of p e) u st' (deliveries s')
    (entry_network_action model stores input R A c p e)
    (entry_ghosts model stores input R A c p e) (entry_ghosts_after model stores input R A c p e)
    (entry_batch model stores input R A c p e).

Definition actor_log p := @local_log M E _ sm p (entry p) (stamped p).

Fixpoint in_order p (items : list (located model stores input R A c p)) : list (entry p) :=
  match items with [] => [] | (_,e) :: tail => in_order p tail ++ [e] end.

Theorem archive_role_log tc s tn n gs past ar :
  archives tc s tn n gs past ar ->
  forall p, actor_log p (A p) (Code [] (c p))
    (in_order p (ar p))
    (positions s p).
Proof.
  induction 1 as [|tc s tn n gs past ar who e H IH Tc Source Tn Net Ghost Past Matched];
    intro p; [constructor|].
  destruct (role_eq_dec who p) as [->|Ne].
  - rewrite add_entry_same. cbn [in_order].
    pose proof (entry_end model stores input R A c p e) as End.
    rewrite End. eapply (LogStep _ _ _ _ _ _ _ (Some e)).
    + eapply log_silent_prefix; [|exact (entry_silent model stores input R A c p e)].
      rewrite Source. exact (IH p).
    + apply micro_plug, MicroLeaf. split.
      * exact (entry_primitive model stores input R A c p e).
      * exact (observation_at_focus model stores input R A c p e).
  - rewrite add_entry_other by exact Ne.
    pose proof (entry_pair model stores input R A c who e) as Pair.
    pose proof (entry_primitive model stores input R A c who e) as Prim.
    pose proof (DeadlockCoherence.role_step_actor sm R _ _ _ _ _ _ _ _ _
      (primitive_is_role_step sm R _ _ _ _ _ _ _ _ _ Prim)) as Actor.
    destruct Pair as [r pre post t u s1 n1 a b gs1 ev Member Before After Obs Frame NS].
    pose proof (observed_decorated sm R _ _ _ _ _ _ _ _ _ _ _ _ _ Obs) as D.
    pose proof (DeadlockCoherence.role_step_actor sm R _ _ _ _ _ _ _ _ _
      (DeadlockMatch.decorated_source sm R _ _ _ _ _ _ _ _ _ _ _ _ D)) as Same.
    rewrite <- Frame by congruence. rewrite Source. exact (IH p).
Qed.
End Stamped.
