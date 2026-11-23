From Stdlib Require Import Lists.List.
Require Import DeadlockWireChronology DeadlockPayloadLedger DeadlockRealized
  DeadlockCoverage DeadlockSource DeadlockNetwork DeadlockPast DeadlockMatch
  DeadlockLocal DeadlockState DeadlockMessages DeadlockFrontiers DeadlockHead
  DeadlockCoherence DeadlockOrder DeadlockObservedCut DeadlockFamilyLog
  DeadlockFirstSend DeadlockCutSafety DeadlockChronology DeadlockPlayedValues Parkour.Symbol.
Import ListNotations.

Lemma prior_send_counted {E S} R jk o sender receiver sid (a : @source_action E S) :
  In receiver R -> sender <> receiver -> session_at o Choreography.Network.Root = sid ->
  action_at jk o sender receiver sender a -> In o (emits R (sender,receiver,sid) a).
Proof.
  intros InR Ne <-. destruct jk,a; cbn [action_at]; try contradiction;
    intros H; decompose [and] H; subst; try contradiction.
  - cbn [emits]. destruct (key_eq_dec _ _); [now left|contradiction].
  - unfold emits,key_paths. apply in_map_iff.
    exists (Message unit ChoiceDelivery o sender receiver tt Parkour.Codec.show_unit). split; [reflexivity|].
    apply filter_In. split.
    + unfold announcement_messages. apply in_map_iff. exists receiver; split; [reflexivity|].
      apply filter_In. split; [exact InR|]. destruct (role_eq_dec receiver sender); [congruence|reflexivity].
    + cbn [message_key]. destruct (key_eq_dec _ _); [reflexivity|contradiction].
Qed.

Lemma prior_receive_counted {E S} jk o sender receiver sid (a : @source_action E S) :
  sender <> receiver -> session_at o Choreography.Network.Root = sid ->
  action_at jk o sender receiver receiver a -> In o (receives (sender,receiver,sid) a).
Proof.
  intros Ne <-. destruct jk,a; cbn [action_at]; try contradiction;
    intros H; decompose [and] H; subst; try contradiction;
    cbn [receives]; destruct (key_eq_dec _ _); [now left|contradiction|now left|contradiction].
Qed.

Section Head.
Context {M E Store Input} (m : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input : Input) (R : list Symbol) (A : Symbol -> Type)
  (c : forall p, Choreography.Choreo2.Choreo M p (A p)).
Local Notation ep := (observed_entry m stores input R A c).
Local Notation cuts_of := (logged_cut m stores input R A c).

(* Both the send and the waiting receive must be located in one tree. The
   only missing facts at this point are own-role witnesses for the strict
   predecessors in that tree. Neither traffic kind is baked into a key. *)
Theorem layout_head tc s tn n gs past ar tree cuts sender receiver X jk current rd g :
  observed_archives m stores input R A c tc s tn n gs past ar -> NoDup R ->
  owns_region m stores input R A c ar A R [] cuts ->
  realized m stores input R A c A R [] cuts tree ->
  In receiver R -> receive_site (shared_model m) receiver (A receiver)
    (positions s receiver) X jk current sender rd ->
  site tree current jk sender receiver ->
  (forall earlier kind, site tree earlier kind sender receiver ->
    source_before earlier current ->
    exists a, In a tc /\ action_at kind earlier sender receiver receiver a) ->
  (forall later kind op, In (Produced kind later sender receiver op) past ->
    source_before current later ->
    exists a, In a tc /\ action_at jk current sender receiver sender a) ->
  first_for (sender,receiver,session_at current Choreography.Network.Root) gs g ->
  message_path g = current.
Proof.
  intros Archives ND Own Layout Member Site Here PrevR PrevS Head.
  pose proof (observed_archives_history m stores input R A c _ _ _ _ _ _ _ Archives) as H.
  pose proof (history_is_matched m stores input R A c _ _ _ _ _ _ H) as P.
  assert (Ne : sender <> receiver).
  { destruct Site as (B & C & focus & Sil & F); destruct F; assumption. }
  pose (key := (sender,receiver,session_at current Choreography.Network.Root)).
  assert (PastSite : forall o, In o (sent R key tc) ->
    exists kind op, site tree o kind sender receiver /\ In (Produced kind o sender receiver op) past /\
      session_at o Choreography.Network.Root = session_at current Choreography.Network.Root).
  { intros o Seen. apply (sent_has_production m stores input R A c _ _ _ _ _ _ sender receiver _ _ H) in Seen.
    destruct Seen as [Id [kind [op Sent]]].
    destruct (realized_past_sites m stores input R A c past ar _ _ _ _ _ A R [] cuts tree
      Archives Own Layout _ Sent ltac:(now exists o)) as (path & Eq & Found).
    cbn in Eq; subst. exists kind, op; auto. }
  eapply (matched_head_identity m stores input R A c tc s tn n gs sender receiver current g);
    [exact ND|exact P|eapply receive_site_future; exact Site| | | | |exact Head].
  - intros x y Hx Hy. destruct (PastSite x Hx) as (k & v & Sx & _).
    destruct (PastSite y Hy) as (j & w & Sy & _). eapply shared_node_paths; eassumption.
  - intros x Hx. destruct (PastSite x Hx) as (k & v & Sx & _).
    eapply shared_node_paths; [exact Sx|exact Here].
  - intros x Hx Older. destruct (PastSite x Hx) as (k & v & Sx & Produced & Id).
    destruct (PrevR _ _ Sx Older) as [a [Seen At]].
    apply in_flat_map. exists a; split; [exact Seen|]. eapply prior_receive_counted; eassumption.
  - intros x Hx Later. destruct (PastSite x Hx) as (k & v & Sx & Produced & Id).
    destruct (PrevS _ _ _ Produced Later) as [a [Seen At]].
    apply in_flat_map. exists a; split; [exact Seen|].
    eapply prior_send_counted; [exact Member|exact Ne|reflexivity|exact At].
Qed.
End Head.
