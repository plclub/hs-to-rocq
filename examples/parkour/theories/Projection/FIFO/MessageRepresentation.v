From Stdlib Require Import Lists.List Sorting.Sorted Arith.PeanoNat.
From ParkourTheories Require Import Choreography.Occurrences
  Choreography.PendingDeliveries Choreography.RoleSteps Choreography.Precedence
  Projection.SessionPaths Network.Mailboxes Network.Endpoints.
Require Import Parkour.Codec.
Import ListNotations.

(* Ghosts retain the ACTUAL sender dictionary. Neither source pending entries
   nor raw network queues are changed. In particular kind is not a queue key. *)
Inductive message : Type :=
| Message : forall X, delivery_kind -> occurrence -> role -> role ->
    X -> Show X -> message.

Definition pending_of (m : message) : pending :=
  match m with Message X k o s d x _ => Pending X k o s d x end.
Definition message_key (m : message) : key :=
  match m with Message _ _ o s d _ _ => (s,d,session_at o
    Choreography.Network.Root) end.
Definition message_wire (m : message) : wire :=
  match m with Message X _ _ _ _ x sh => @show X sh x end.
Definition message_path (m : message) : occurrence :=
  match m with Message _ _ o _ _ _ _ => o end.

Fixpoint at_key (k : key) (gs : list message) : list wire :=
  match gs with
  | [] => []
  | g :: gs' =>
      if key_eq_dec (message_key g) k
      then message_wire g :: at_key k gs' else at_key k gs'
  end.

Definition represents (ps : list pending) (q : queues)
    (gs : list message) : Prop :=
  map pending_of gs = ps /\ forall k, q k = at_key k gs.

Lemma at_key_app k xs ys :
  at_key k (xs ++ ys) = at_key k xs ++ at_key k ys.
Proof.
  induction xs as [|x xs IH]; cbn; [reflexivity|].
  destruct (key_eq_dec (message_key x) k); cbn; now rewrite IH.
Qed.

Lemma at_key_same m gs :
  at_key (message_key m) (m :: gs) =
    message_wire m :: at_key (message_key m) gs.
Proof. cbn. destruct (key_eq_dec (message_key m) (message_key m)); congruence.
Qed.

Lemma at_key_other k m gs :
  message_key m <> k -> at_key k (m :: gs) = at_key k gs.
Proof. intro H. cbn. destruct (key_eq_dec (message_key m) k); congruence. Qed.

Lemma represents_empty : represents [] empty_queues [].
Proof. split; reflexivity. Qed.

(* Pointwise framing, with no functional extensionality. *)
Lemma represents_frame ps q q' gs :
  represents ps q gs -> (forall k, q' k = q k) -> represents ps q' gs.
Proof. intros [P Q] E. split; [exact P|intro k; now rewrite E, Q]. Qed.

Lemma send_other_key q k j w :
  j <> k -> enqueue q k w j = q j.
Proof. apply replace_other. Qed.

Lemma announcement_other_keys rs owner sid w q k :
  (forall r, In r rs -> owner <> r -> k <> (owner,r,sid)) ->
  announce rs owner sid w q k = q k.
Proof.
  revert q. induction rs as [|r rs IH]; intros q H; cbn; [reflexivity|].
  rewrite IH by (intros peer InPeer; apply H; now right).
  destruct (role_eq_dec owner r) as [E|E]; [reflexivity|].
  apply send_other_key. apply H; [now left|exact E].
Qed.

Corollary announcement_owner_queue rs owner sid w q sid' :
  announce rs owner sid w q (owner,owner,sid') = q (owner,owner,sid').
Proof.
  apply announcement_other_keys. intros r _ N Equal.
  apply N. congruence.
Qed.

Theorem represents_snoc ps q gs m :
  represents ps q gs ->
  represents (ps ++ [pending_of m])
    (enqueue q (message_key m) (message_wire m)) (gs ++ [m]).
Proof.
  intros [P Q]. split.
  - rewrite map_app, P. reflexivity.
  - intro k. rewrite at_key_app. unfold enqueue, replace_queue.
    destruct (key_eq_dec k (message_key m)) as [E|E].
    + subst k. rewrite at_key_same. cbn. rewrite Q. reflexivity.
    + rewrite at_key_other by congruence. cbn. rewrite app_nil_r. apply Q.
Qed.

Corollary represents_send X o s d (x : X) sh ps q gs :
  represents ps q gs ->
  represents (ps ++ [Pending X DataDelivery o s d x])
    (enqueue q (s,d,session_at o Choreography.Network.Root) (@show X sh x))
    (gs ++ [Message X DataDelivery o s d x sh]).
Proof. apply represents_snoc. Qed.

Definition announcement_messages X o owner (x : X) sh rs :=
  map (fun peer => Message X ChoiceDelivery o owner peer x sh)
    (filter (fun peer => if role_eq_dec peer owner then false else true) rs).

Lemma announcement_pending X o owner (x : X) sh rs :
  map pending_of (announcement_messages X o owner x sh rs) =
  announcement rs X o owner x.
Proof. unfold announcement_messages, announcement. rewrite map_map. reflexivity.
Qed.

Theorem represents_announcement X o owner (x : X) sh rs ps q gs :
  represents ps q gs ->
  represents (ps ++ announcement rs X o owner x)
    (announce rs owner (session_at o Choreography.Network.Root) (@show X sh x)
      q)
    (gs ++ announcement_messages X o owner x sh rs).
Proof.
  unfold announcement_messages, announcement.
  revert ps q gs. induction rs as [|r rs IH]; intros ps q gs H.
  - cbn. now rewrite !app_nil_r.
  - cbn [announce filter map].
    destruct (role_eq_dec owner r) as [E|E];
      destruct (role_eq_dec r owner) as [F|F];
      destruct (list_eq_dec BinNat.N.eq_dec r owner) as [G|G]; try congruence.
    + subst r. apply IH. exact H.
    + specialize (IH _ _ _ (represents_snoc _ _ _ (Message X ChoiceDelivery o
      owner r x sh) H)).
      cbn in IH. rewrite <- !app_assoc in IH. cbn in IH. exact IH.
Qed.

Lemma at_key_absent k pre :
  Forall (fun m => message_key m <> k) pre -> at_key k pre = [].
Proof.
  intro H. induction H; cbn; [reflexivity|].
  destruct (key_eq_dec (message_key x) k); [contradiction|assumption].
Qed.

(* The exact occurrence/type/value is retained in pending_of m. Even equal
   wire bytes at another occurrence do not authorize this consumption. *)
Theorem represents_consume pre m post ps q :
  represents ps q (pre ++ m :: post) ->
  Forall (fun g => message_key g <> message_key m) pre ->
  q (message_key m) = message_wire m :: at_key (message_key m) post /\
  represents (map pending_of (pre ++ post))
    (replace_queue q (message_key m) (at_key (message_key m) post))
    (pre ++ post).
Proof.
  intros [_ Q] Frontier. split.
  - rewrite Q, at_key_app, (at_key_absent _ _ Frontier), at_key_same.
  reflexivity.
  - split; [reflexivity|]. intro k. unfold replace_queue.
    destruct (key_eq_dec k (message_key m)) as [E|E].
    + subst k. rewrite at_key_app, (at_key_absent _ _ Frontier). reflexivity.
    + rewrite Q, !at_key_app, at_key_other by congruence. reflexivity.
Qed.

Corollary consume_other_key q m post k :
  k <> message_key m ->
  replace_queue q (message_key m) (at_key (message_key m) post) k = q k.
Proof. apply replace_other. Qed.

Lemma same_channel_key X kind o s d (x : X) sh m :
  same_channel kind o s d (pending_of m) ->
  message_key (Message X kind o s d x sh) = message_key m.
Proof.
  destruct m as [Y kind' o' s' d' y sh']; cbn.
  intros [K [L [S D]]]. subst. f_equal.
  apply (proj2 (same_session_iff o o' Choreography.Network.Root)). exact L.
Qed.

(* A source take can skip an opposite-kind entry on the SAME actual key.
   Thus the following frontier is an explicit integration obligation, not a
   theorem about arbitrary source cursors or an assumed global simulation. *)
Definition wire_frontier (target : pending) (gs : list message) : Prop :=
  forall pre m post, gs = pre ++ m :: post -> pending_of m = target ->
    Forall (fun g => message_key g <> message_key m) pre.

Definition pending_path (v : pending) :=
  match v with Pending _ _ o _ _ _ => o end.

Lemma pending_message_path m : pending_path (pending_of m) = message_path m.
Proof. destruct m; reflexivity. Qed.

Lemma sorted_prefix_rank (rank : occurrence -> nat) pre m post :
  StronglySorted (fun g h => rank (message_path g) < rank (message_path h))
    (pre ++ m :: post) ->
  forall g, In g pre -> rank (message_path g) < rank (message_path m).
Proof.
  induction pre as [|h pre IH]; cbn; intros S g InG; [contradiction|].
  inversion S as [|? ? Tail Earlier]; subst.
  destruct InG as [E|InG].
  - subst g. rewrite Forall_forall in Earlier. apply Earlier.
    apply in_or_app. right. now left.
  - exact (IH Tail g InG).
Qed.

(* This is the missing cursor/history obligation in usable local form.
   Chronology, compatibility, outstandingness, and predecessor closure are
   PREMISES; no theorem here establishes them for reachable configurations.
   Unlike a data-only frontier, this theorem compares BOTH kinds together. *)
Theorem frontier_from_history target gs rank received :
  StronglySorted (fun g h => rank (message_path g) < rank (message_path h)) gs
    ->
  (forall g h, In g gs -> In h gs ->
    compatible (message_path g) (message_path h)) ->
  respects (map message_path gs) rank ->
  (forall g, In g gs -> ~ received (message_path g)) ->
  (forall g, In g gs ->
    source_before (message_path g) (pending_path target) ->
    received (message_path g)) ->
  wire_frontier target gs.
Proof.
  intros Sorted Compat Chrono Outstanding Closed pre m post E P.
  subst gs. apply Forall_forall. intros g InG EqualKey.
  assert (InG' : In g (pre ++ m :: post)).
  { apply in_or_app. now left. }
  assert (InM : In m (pre ++ m :: post)).
  { apply in_or_app. right. now left. }
  pose proof (sorted_prefix_rank rank pre m post Sorted g InG) as Earlier.
  assert (Different : message_path g <> message_path m).
  { intro H. rewrite H in Earlier. exact (Nat.lt_irrefl _ Earlier). }
  assert (Session :
    session_at (message_path g) Choreography.Network.Root =
    session_at (message_path m) Choreography.Network.Root).
  { destruct g, m. cbn in *. now injection EqualKey. }
  destruct (same_session_order _ _ _ (Compat g m InG' InM) Different Session)
    as [Before|After].
  - apply (Outstanding g InG'). apply Closed; [exact InG'|].
    rewrite <- P, pending_message_path. exact Before.
  - specialize (Chrono _ _ (in_map message_path _ _ InM)
      (in_map message_path _ _ InG') After).
    exact (Nat.lt_asymm _ _ Earlier Chrono).
Qed.

Lemma take_pending_split X kind o s d (x : X) ps ps' :
  take_first_on_source_channel kind o s d x ps ps' ->
  forall gs, map pending_of gs = ps ->
  exists pre m post,
    gs = pre ++ m :: post /\
    pending_of m = Pending X kind o s d x /\
    ps' = map pending_of (pre ++ post).
Proof.
  intro T. induction T; intros gs G; destruct gs as [|g gs]; cbn in G;
    try discriminate.
  - injection G as A B. exists [], g, gs. cbn. auto.
  - injection G as A B.
    destruct (IHT gs B) as [pre [m [post [S [P Q]]]]].
    exists (g :: pre), m, post. cbn. subst. auto.
Qed.

Theorem source_take_exact_head X kind o s d (x : X) ps ps' q gs :
  represents ps q gs ->
  take_first_on_source_channel kind o s d x ps ps' ->
  wire_frontier (Pending X kind o s d x) gs ->
  exists pre m post,
    gs = pre ++ m :: post /\
    pending_of m = Pending X kind o s d x /\
    q (message_key m) = message_wire m :: at_key (message_key m) post /\
    represents ps'
      (replace_queue q (message_key m) (at_key (message_key m) post))
      (pre ++ post).
Proof.
  intros H T F.
  destruct (take_pending_split _ _ _ _ _ _ _ _ T gs (proj1 H))
    as [pre [m [post [G [P R]]]]].
  pose proof (F pre m post G P) as Frontier.
  subst gs. destruct (represents_consume pre m post ps q H Frontier) as [Head
    Inv].
  exists pre, m, post. repeat split; try assumption; try reflexivity.
  - rewrite R. exact (proj1 Inv).
  - exact (proj2 Inv).
Qed.

(* Conversely, different-key prefixes are legal source skips. This uses only
   actual source rules and the generated session/lane calculation. *)
Theorem source_take_different_keys X kind o s d (x : X) sh pre post :
  Forall
    (fun g => message_key g <> message_key (Message X kind o s d x sh)) pre ->
  take_first_on_source_channel kind o s d x
    (map pending_of (pre ++ Message X kind o s d x sh :: post))
    (map pending_of (pre ++ post)).
Proof.
  intro H. induction H; cbn.
  - constructor.
  - constructor; [|exact IHForall]. intro C.
    apply H. symmetry. now apply (same_channel_key X kind o s d x sh).
Qed.

(* The operational receive bridge additionally needs the receiver's actual
   Read dictionary to decode the sender's actual wire. No codec law is
   silently postulated, and no equality of heterogeneous payloads is used. *)
Theorem network_receive_at_occurrence
    {M E Store} (model : LocalEffects.local_model M E role Store) participants
    X kind o sender receiver (x : X) sh rd pre post ps q store :
  represents ps q (pre ++ Message X kind o sender receiver x sh :: post) ->
  Forall
    (fun g => message_key g <>
      (sender,receiver,session_at o Choreography.Network.Root)) pre ->
  @read X rd (@show X sh x) = Some x ->
  @Endpoints.step M E Store model participants receiver X
    (CPerf (@Choreography.Network.Recv M X rd
      (session_at o Choreography.Network.Root) sender))
    q store
    (@Received E Store sender receiver
      (session_at o Choreography.Network.Root) (@show X sh x))
    (CPure x)
    (replace_queue q (sender,receiver,session_at o Choreography.Network.Root)
      (at_key (sender,receiver,session_at o Choreography.Network.Root) post))
    store /\
  represents (map pending_of (pre ++ post))
    (replace_queue q (sender,receiver,session_at o Choreography.Network.Root)
      (at_key (sender,receiver,session_at o Choreography.Network.Root) post))
    (pre ++ post).
Proof.
  intros H F Decode.
  destruct (represents_consume pre
    (Message X kind o sender receiver x sh) post ps q H F) as [Head Inv].
  split; [eapply StepRecv; [exact Head|exact Decode]|exact Inv].
Qed.
