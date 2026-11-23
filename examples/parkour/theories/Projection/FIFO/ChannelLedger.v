From Stdlib Require Import Lists.List Sorting.Sorted.
From ParkourTheories Require Import Choreography.Occurrences
  Choreography.PendingDeliveries Choreography.RoleSteps Network.Mailboxes
  Projection.FIFO.MessageRepresentation Choreography.Precedence
  Projection.SessionPaths Projection.Matching.PrefixRelation
  Semantics.LocalEffects.
Require Import Parkour.Symbol Parkour.Codec Control.Monad.Tree.
Import ListNotations.
Local Opaque key_eq_dec role_eq_dec.

(* Count occurrence paths, not wire strings: different sends may have
   identical encodings. Data and choice share a single ledger per wire key. *)
Definition key_paths (k : key) (gs : list message) : list occurrence :=
  map message_path
    (filter (fun g => if key_eq_dec (message_key g) k then true else false) gs).

Lemma key_paths_app k xs ys :
  key_paths k (xs ++ ys) = key_paths k xs ++ key_paths k ys.
Proof. unfold key_paths; now rewrite filter_app, map_app. Qed.

Lemma key_paths_same m gs :
  key_paths (message_key m) (m :: gs) =
  message_path m :: key_paths (message_key m) gs.
Proof.
  unfold key_paths; cbn. destruct (key_eq_dec (message_key m) (message_key m));
    [reflexivity|contradiction].
Qed.

(* A receiver cannot be waiting for an occurrence it already consumed. If the
   head preceded the site, the receiver had to consume it before reaching the
   site. If the site preceded the head, the sender had to send it before the
   head. Both implications concern the source history, not network readiness. *)
Lemma ordered_head_coverage (consumed : list occurrence) head rest site :
  StronglySorted source_before (consumed ++ head :: rest) ->
  ~ In site consumed ->
  (site = head \/ source_before head site \/ source_before site head) ->
  (source_before head site -> In head consumed) ->
  (source_before site head -> In site (consumed ++ head :: rest)) ->
  head = site.
Proof.
  intros Order Fresh [<- | [Prior | Later]] CoveredR CoveredS;
    [reflexivity| |]; exfalso.
  - specialize (CoveredR Prior). clear -Order CoveredR.
    induction consumed as [|x xs IH]; [contradiction|].
    cbn in Order. inversion Order as [|? ? Sorted All]; subst.
    destruct CoveredR as [<-|Member].
    + rewrite Forall_forall in All. apply (source_before_irreflexive x).
      apply All, in_or_app. right; now left.
    + apply IH; assumption.
  - specialize (CoveredS Later).
    apply in_app_or in CoveredS. destruct CoveredS as [Old|[Eq|Tail]].
    + contradiction.
    + subst. exact (source_before_irreflexive _ Later).
    + assert (suffix : StronglySorted source_before (head :: rest)).
      { clear -Order. induction consumed; [exact Order|].
        apply IHconsumed. inversion Order; assumption. }
      inversion suffix as [|? ? _ All]; subst. rewrite Forall_forall in All.
      exact (source_before_asymmetric _ _ Later (All _ Tail)).
Qed.

Lemma key_paths_other k m gs :
  message_key m <> k -> key_paths k (m :: gs) = key_paths k gs.
Proof.
  intro Ne; unfold key_paths; cbn.
  destruct (key_eq_dec (message_key m) k); [contradiction|reflexivity].
Qed.

Lemma key_paths_absent k gs :
  Forall (fun g => message_key g <> k) gs -> key_paths k gs = [].
Proof.
  induction 1; [reflexivity|].
  now rewrite key_paths_other.
Qed.

Definition emits {E S} (R : list role) (k : key)
    (a : @source_action E S) : list occurrence :=
  match a with
  | SendAction _ o s d _ =>
      if key_eq_dec (s,d,session_at o Choreography.Network.Root) k
      then [o] else []
  | AnnounceAction _ o s _ =>
      key_paths k (announcement_messages unit o s tt show_unit R)
  | _ => []
  end.

Definition receives {E S} (k : key) (a : @source_action E S) : list occurrence
  :=
  match a with
  | ReceiveAction _ o s d _ | HearAction _ o s d _ =>
      if key_eq_dec (s,d,session_at o Choreography.Network.Root) k
      then [o] else []
  | _ => []
  end.

Definition sent {E S} R k (tr : list (@source_action E S)) :=
  flat_map (emits R k) tr.
Definition received {E S} k (tr : list (@source_action E S)) :=
  flat_map (receives k) tr.

Lemma delivery_paths X kind o sender receiver (x : X) rd gs w gs' k :
  delivery X kind o sender receiver x rd gs w gs' ->
  key_paths k gs =
    (if key_eq_dec (sender,receiver,session_at o Choreography.Network.Root) k
     then [o] else []) ++ key_paths k gs'.
Proof.
  intros [sh pre post Front Decode].
  rewrite !key_paths_app.
  destruct (key_eq_dec (sender,receiver,session_at o Choreography.Network.Root)
    k)
    as [Eq|Ne].
  - subst k. rewrite (key_paths_absent _ _ Front).
    change (key_paths (message_key (Message X kind o sender receiver x sh))
      (Message X kind o sender receiver x sh :: post) =
      o :: key_paths (sender,receiver,session_at o Choreography.Network.Root)
        post).
    now rewrite key_paths_same.
  - rewrite key_paths_other by exact Ne. reflexivity.
Qed.

Lemma announcement_paths X o owner (x : X) sh R k :
  key_paths k (announcement_messages X o owner x sh R) =
  @emits (fun _ => unit) unit R k (AnnounceAction X o owner x).
Proof.
  unfold emits, announcement_messages, key_paths.
  remember (filter (fun peer => if role_eq_dec peer owner then false else true)
    R) as peers.
  clear Heqpeers. induction peers as [|r peers IH]; cbn; [reflexivity|].
  cbn [message_key]. repeat match goal with
  | |- context [if ?b then _ else _] => destruct b eqn:?; cbn in *; try
    congruence
  end.
Qed.

Lemma decorated_ledger {M E S} (m : local_model M E role S) R p X
    c st sq a c' st' sq' b gs gs' k :
  @decorated M E S m R p X c st sq a c' st' sq' b gs gs' ->
  key_paths k gs ++ emits R k a = receives k a ++ key_paths k gs'.
Proof.
  induction 1; try assumption.
  - cbn. apply app_nil_r.
  - rewrite key_paths_app. cbn [emits receives].
    destruct (key_eq_dec (p,d,session_at o Choreography.Network.Root) k) as
      [<-|Ne].
    + cbn [app]. f_equal. symmetry. apply (key_paths_same
        (Message X DataDelivery o p d (Choreography.Choreo2.unAt v eq_refl) sh)
          []).
    + rewrite key_paths_other by exact Ne. reflexivity.
  - rewrite app_nil_r. eapply delivery_paths; eassumption.
  - rewrite key_paths_app, announcement_paths. reflexivity.
  - rewrite app_nil_r. eapply delivery_paths; eassumption.
Qed.

Theorem prefix_ledger {M E Store Input}
    (m : local_model M E role (Store * Input)) stores input R A c
    tc s tn n gs k :
  matched_prefix m stores input R A c tc s tn n gs ->
  sent R k tc = received k tc ++ key_paths k gs.
Proof.
  induction 1 as [|tc s tn n gs a s' b n' gs' H IH Pair State].
  - reflexivity.
  - unfold sent, received in *. rewrite !flat_map_app. cbn [flat_map].
    rewrite !app_nil_r, IH. rewrite <- !app_assoc.
    f_equal. destruct Pair. eapply decorated_ledger; eassumption.
Qed.

Theorem reachable_head_from_coverage {M E Store Input}
    (m : local_model M E role (Store * Input)) stores input R A c
    tc s tn n gs k head rest site :
  matched_prefix m stores input R A c tc s tn n gs ->
  key_paths k gs = head :: rest ->
  StronglySorted source_before (sent R k tc) ->
  ~ In site (received k tc) ->
  (site = head \/ source_before head site \/ source_before site head) ->
  (source_before head site -> In head (received k tc)) ->
  (source_before site head -> In site (sent R k tc)) ->
  head = site.
Proof.
  intros Run Pending.
  rewrite (prefix_ledger _ _ _ _ _ _ _ _ _ _ _ k Run), Pending.
  apply ordered_head_coverage.
Qed.
