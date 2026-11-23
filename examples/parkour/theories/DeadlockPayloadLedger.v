From Stdlib Require Import Lists.List.
Require Import DeadlockSource DeadlockNetwork DeadlockFrontiers DeadlockMessages
  DeadlockOrder DeadlockPast DeadlockMatch DeadlockLocal DeadlockPlayedValues
  DeadlockState Parkour.Symbol.
Import ListNotations.
Local Opaque key_eq_dec.

Definition on_wire sending k (event : payload_event) : list occurrence :=
  match sending,event with
  | true, Produced _ o s d _ | false, Consumed _ o s d _ =>
    if key_eq_dec (s,d,session_at o Choreography.Network.Root) k then [o] else []
  | _, _ => [] end.

Lemma produced_paths sending k ms :
  flat_map (on_wire sending k) (map produced_message ms) =
    if sending then key_paths k ms else [].
Proof.
  induction ms as [|[X jk o s d x dict] ms IH]; destruct sending;
    cbn [map flat_map on_wire produced_message] in *; try assumption; try reflexivity.
  rewrite IH.
  change ((if key_eq_dec (s,d,session_at o Choreography.Network.Root) k then [o] else []) ++
    key_paths k ms = key_paths k (Message X jk o s d x dict :: ms)).
  destruct (key_eq_dec (s,d,session_at o Choreography.Network.Root) k) as [<-|Ne].
  -
    symmetry; exact (key_paths_same (Message X jk o s d x dict) ms).
  - rewrite key_paths_other by exact Ne. reflexivity.
Qed.

Lemma observed_paths {M E Store} (m : local_model M E role Store) R p B
    t st q a u st' q' na gs gs' ev k sending :
  @observed M E Store m R p B t st q a u st' q' na gs gs' ev ->
  flat_map (on_wire sending k) ev =
    if sending then emits R k a else receives k a.
Proof.
  intro Obs. induction Obs; try assumption; destruct sending;
    cbn [flat_map on_wire emits receives]; try reflexivity; try apply app_nil_r.
  - rewrite produced_paths. apply announcement_paths.
  - apply produced_paths with (sending := false).
Qed.

Theorem payload_paths {M E Store Input} (m : local_model M E role (Store * Input))
    stores input R A c tc s tn n gs past k sending :
  payload_history m stores input R A c tc s tn n gs past ->
  flat_map (on_wire sending k) past =
    if sending then sent R k tc else received k tc.
Proof.
  induction 1; [destruct sending; reflexivity|]. destruct H0.
  rewrite flat_map_app, IHpayload_history.
  erewrite observed_paths by eassumption.
  destruct sending; unfold sent,received; rewrite flat_map_app;
    cbn [flat_map]; now rewrite app_nil_r.
Qed.

Theorem sent_has_production {M E Store Input} (m : local_model M E role (Store * Input))
    stores input R A c tc s tn n gs past sender recipient sid o :
  payload_history m stores input R A c tc s tn n gs past ->
  In o (sent R (sender,recipient,sid) tc) <->
    session_at o Choreography.Network.Root = sid /\
    exists kind op, In (Produced kind o sender recipient op) past.
Proof.
  intro H. rewrite <- (payload_paths _ _ _ _ _ _ _ _ _ _ _ _ (sender,recipient,sid) true H).
  rewrite in_flat_map. split.
  - intros [[jk path s0 d0 op|] [Seen At]]; [|contradiction].
    cbn [on_wire] in At.
    destruct (key_eq_dec _ _) as [Eq|Ne]; [|contradiction].
    destruct At as [<-|[]]. injection Eq as -> -> Sid. eauto.
  - intros [Sid [jk [op Seen]]]. eexists. split; [exact Seen|].
    cbn [on_wire]. rewrite Sid. destruct (key_eq_dec _ _); [now left|contradiction].
Qed.

Theorem receive_has_consumption {M E Store Input} (m : local_model M E role (Store * Input))
    stores input R A c tc s tn n gs past sender recipient sid o :
  payload_history m stores input R A c tc s tn n gs past ->
  In o (received (sender,recipient,sid) tc) <->
    session_at o Choreography.Network.Root = sid /\
    exists kind w, In (Consumed kind o sender recipient w) past.
Proof.
  intro H. rewrite <- (payload_paths _ _ _ _ _ _ _ _ _ _ _ _ (sender,recipient,sid) false H).
  rewrite in_flat_map. split.
  - intros [[|jk path s0 d0 w] [Seen At]]; [contradiction|].
    cbn [on_wire] in At. destruct (key_eq_dec _ _) as [Eq|Ne]; [|contradiction].
    destruct At as [<-|[]]. injection Eq as -> -> Sid. eauto.
  - intros [Sid [jk [w Seen]]]. eexists. split; [exact Seen|].
    cbn [on_wire]. rewrite Sid. destruct (key_eq_dec _ _); [now left|contradiction].
Qed.
