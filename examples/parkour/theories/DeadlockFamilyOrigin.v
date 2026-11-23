From Stdlib Require Import Lists.List Logic.Eqdep_dec.
Require Import DeadlockRootOrigin DeadlockWellFormed DeadlockNetwork DeadlockMessages
  DeadlockFamilyLog DeadlockObservedCut DeadlockPlayedValues DeadlockPast DeadlockCoherence
  DeadlockLocal DeadlockSource DeadlockMatch DeadlockState DeadlockChronology Parkour.Codec
  Parkour.Symbol Choreography.Choreo2 Control.Monad.Tree.
Import ListNotations.

(* A Bind body can be well-formed on only the roles that have entered.
   Its reader needs no value at an absent sender. If a packet exists there,
   the same execution archive supplies the sender membership witness. *)
Lemma partial_node_reader {M R S A c Q} :
  structural R M S A c Q ->
  forall p (member : S p) o,
  reader_contract (c p member) (fun X kind l reader =>
    forall here : S l, exists (value : X) (writer : Show X),
      outgoing (c l here) o p = Some (Message X kind o l p value writer) /\
      wire_law writer reader).
Proof.
  destruct 1; intros peer mem o;
    match goal with Shape : forall p s, _ p s = _ |- _ =>
      rewrite (Shape peer mem) end;
    cbn [reader_contract]; try exact I.
  - intros <- Ne here. exists (Choreography.Choreo2.unAt (x l here) eq_refl), (sh l here).
    rewrite H2; cbn [outgoing]. destruct (role_eq_dec l l) as [e|N]; [|contradiction].
    rewrite (UIP_dec role_eq_dec e eq_refl). split; [reflexivity|now apply H1].
  - intros Ne here. exists (Choreography.Choreo2.unAt (x l here) eq_refl), (sh l here).
    match goal with F : forall p s, c p s = _ |- _ => rewrite (F l here) end.
    cbn [outgoing]. destruct (role_eq_dec l l) as [e|N]; [|contradiction].
    rewrite (UIP_dec role_eq_dec e eq_refl). split; [reflexivity|now apply H0].
Qed.

Section Provenance.
Context {M E Store Input} (model : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input : Input) (R : list Symbol) (A : Symbol -> Type)
  (c : forall p, Choreo M p (A p)).
Local Notation Cut := (logged_cut model stores input R A c).
Local Notation tokens_at := (tokens model stores input R A c).
Local Notation batch_of := (entry_batch model stores input R A c).

Theorem produced_in_owner_log tc s tn n gs past ar F active o
    (cuts : forall p, In p active -> Cut p (F p)) kind sender recipient op :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  owns_region model stores input R A c ar F active o cuts ->
  In (Produced kind o sender recipient op) past ->
  exists (here : In sender active) token,
    In token (tokens_at sender (F sender) (cuts sender here)) /\
    In (Produced kind o sender recipient op) (batch_of sender token).
Proof.
  intros Archives [ND [Cover Exact]] Member.
  destruct (observed_past_event_archived model stores input R A c
    _ _ _ _ _ _ _ Archives _ Member) as (p & path & token & Seen & Batch).
  destruct (entry_produced_site model stores input R A c p token _ _ _ _ _ Batch) as [Eq Site].
  subst sender.
  destruct (observed_archives_valid model stores input R A c _ _ _ _ _ _ _ Archives p path token Seen)
    as [Route Stamp].
  assert (Within : in_region model stores input R A c ar p o token).
  { split; [now rewrite <- Route|rewrite Site; apply extends_refl]. }
  specialize (Cover p token Within) as Here. exists Here,token.
  split; [now apply Exact|exact Batch].
Qed.

Theorem queued_in_owner_log tc s tn n gs past ar F active o
    (cuts : forall p, In p active -> Cut p (F p))
    X kind sender recipient (x : X) sh :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  owns_region model stores input R A c ar F active o cuts ->
  In (Message X kind o sender recipient x sh) gs ->
  exists (here : In sender active) token,
    In token (tokens_at sender (F sender) (cuts sender here)) /\
    In (Produced kind o sender recipient (Operand X sh x)) (batch_of sender token).
Proof.
  intros Archives Own Pending.
  eapply produced_in_owner_log; [exact Archives|exact Own|].
  pose proof (observed_archives_history model stores input R A c _ _ _ _ _ _ _ Archives) as H.
  exact (proj1 (history_past_ok model stores input R A c _ _ _ _ _ _ H) _ Pending).
Qed.
End Provenance.
