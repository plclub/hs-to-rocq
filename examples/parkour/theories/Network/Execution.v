From Stdlib Require Import Lists.List.
Require Import Choreography.Network.
From ParkourTheories Require Import Semantics.LocalEffects Network.Mailboxes
  Network.Endpoints.
Import ListNotations.

Section Machine.
Context {M E : Type -> Type} {Store : Type}.
Variable model : local_model M E role Store.
Variable participants : list role.

Local Arguments Endpoint {M E} A _ _.

Record configuration := {
  endpoints : list (@endpoint M E);
  mailboxes : queues;
  shared_store : Store
}.

Definition initialize {A : role -> Type}
    (program : forall p, Network M (A p)) (s : Store) : configuration :=
  {| endpoints := map (fun p => Endpoint (A p) p (load (program p)))
    participants;
     mailboxes := empty_queues;
     shared_store := s |}.

(* Every context receives the current shared store. No branch-private copy. *)
Inductive step : configuration -> (@action E Store) -> configuration ->
  Prop :=
| Schedule : forall pre post A p (t t' : @control M E A) q s a q' s',
    Endpoints.step model participants p A t q s a t' q' s' ->
    step {| endpoints := pre ++ Endpoint A p t :: post;
             mailboxes := q; shared_store := s |} a
          {| endpoints := pre ++ Endpoint A p t' :: post;
             mailboxes := q'; shared_store := s' |}.

Lemma nstep_possible n a n' :
  step n a n' ->
  endpoints_possible model (mailboxes n) (shared_store n) (endpoints n).
Proof.
  intros H. destruct H. cbn. revert pre.
  fix IH 1. intros [|e pre]; cbn.
  - left. cbn. eapply step_possible. eassumption.
  - right. apply IH.
Qed.

Definition final (n : configuration) : Prop :=
  Forall (endpoint_final model) (endpoints n) /\
  forall k, mailboxes n k = [].

Inductive run : configuration -> list (@action E Store) -> configuration -> Prop
  :=
| RunNil : forall n, run n [] n
| RunCons : forall n a u tr v,
    step n a u -> run u tr v -> run n (a :: tr) v.
End Machine.

Lemma orphan_not_final {M E Store} (model : local_model M E role Store)
    (n : @configuration M E Store) k w ws :
  @mailboxes M E Store n k = w :: ws -> ~ final model n.
Proof.
  intros H [_ Hempty]. specialize (Hempty k). congruence.
Qed.
