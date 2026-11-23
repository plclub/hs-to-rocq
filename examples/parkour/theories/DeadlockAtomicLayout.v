From Stdlib Require Import Lists.List.
Require Import DeadlockRealized DeadlockLayoutOrder DeadlockLogAtoms
  DeadlockFamilyLog DeadlockPlayedFamily DeadlockPlayedActual DeadlockLocalLog
  DeadlockObservedCut DeadlockSource DeadlockLocal DeadlockCoherence
  DeadlockReplay DeadlockCutSafety DeadlockCoverage DeadlockOrder
  DeadlockPast DeadlockMessages DeadlockChronology DeadlockState
  Parkour.Symbol Parkour.Codec Choreography.Choreo2 Control.Monad.Tree.
Import ListNotations.

Definition atomic_layout {M p B} (code : Choreo M p B) (tree : node_tree) : Prop :=
  match code with
  | Pure _ => tree = Leaf
  | Perf sig =>
      match sig with
      | @Locally _ _ _ _ _ _ _ => tree = Leaf
      | @Comm _ _ _ l r _ _ _ _ _ _ _ => tree = Exchange l r
      | _ => False
      end
  | _ => False
  end.

Definition atomic_cursor {M E p B} root tree (t : @cursor M E p B) : Prop :=
  match t with
  | Code o code => o = root /\ atomic_layout code tree
  | Local o _ => o = root /\ tree = Leaf
  | Returned _ => True
  | _ => False
  end.

Section Primitive.
Context {M E S} (model : local_model M E Symbol S) (R : list Symbol).

Lemma atomic_silent p B t u root tree :
  @primitive_silent M E S model p B t u ->
  atomic_cursor root tree t -> atomic_cursor root tree u.
Proof.
  destruct 1; cbn [atomic_cursor atomic_layout]; intros State;
    try contradiction; try exact I; intuition congruence.
Qed.

Lemma atomic_action p B t s q a u s' q' root tree :
  @primitive_action M E S model R p B t s q a u s' q' ->
  atomic_cursor root tree t -> atomic_cursor root tree u.
Proof.
  destruct 1; cbn [atomic_cursor atomic_layout]; intros State;
    try contradiction; try exact I; intuition congruence.
Qed.

Lemma atomic_silent_general p B t u root tree :
  @silent M E S model p B t u ->
  atomic_cursor root tree t -> atomic_cursor root tree u.
Proof.
  destruct 1; cbn [atomic_cursor atomic_layout]; intros State;
    try contradiction; try exact I; intuition congruence.
Qed.

Lemma atomic_silent_return p B t u root tree v path kind sender receiver :
  @primitive_silent M E S model p B t u ->
  atomic_cursor root tree t ->
  cut_returned p u v ->
  site tree path kind sender receiver ->
  (p = sender \/ p = receiver) -> False.
Proof.
  destruct 1; cbn [atomic_cursor atomic_layout]; intros State Done At Peer;
    try contradiction; destruct State as [-> ->];
    try solve [inversion At].
  - inversion At; subst. intuition congruence.
  - inversion At; subst. contradiction.
Qed.

Lemma atomic_action_site p B t s q a u s' q' root tree
    path kind sender receiver :
  @primitive_action M E S model R p B t s q a u s' q' ->
  atomic_cursor root tree t ->
  site tree path kind sender receiver ->
  (p = sender \/ p = receiver) ->
  action_at kind (root ++ path) sender receiver p a.
Proof.
  destruct 1; cbn [atomic_cursor atomic_layout]; intros State At Peer;
    try contradiction; destruct State as [-> Tree]; try contradiction;
    subst tree; inversion At; subst;
    rewrite app_nil_r; cbn [action_at]; repeat split; reflexivity.
Qed.
End Primitive.

Section Observations.
Context {M E S} (model : local_model M E Symbol S) (R : list Symbol).
Lemma atomic_observed p B t s q a u s' q' na gs gs' events root tree :
  @observed M E S model R p B t s q a u s' q' na gs gs' events ->
  atomic_cursor root tree t ->
  forall ev, In ev events -> payload_in_layout root tree ev.
Proof.
  induction 1; cbn [atomic_cursor atomic_layout]; intros State event Member;
    try contradiction.
  - destruct State as [-> Tree]. subst tree.
    destruct Member as [<-|[]]. cbn [payload_in_layout].
    exists []. rewrite app_nil_r. split; [reflexivity|].
    apply SiteExchange. congruence.
  - destruct State as [-> Tree]. subst tree.
    destruct Member as [<-|[]]. cbn [payload_in_layout].
    exists []. rewrite app_nil_r. split; [reflexivity|].
    apply SiteExchange. assumption.
  - destruct State as [_ []].
  - destruct State as [_ []].
  - apply IHobserved; [eapply atomic_silent_general; eassumption|exact Member].
Qed.
End Observations.

Section AtomicLog.
Context {M E Store Input} (model : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input : Input) (R : list Symbol)
  (A : Symbol -> Type) (c : forall p, Choreo M p (A p)).
Local Notation sm := (shared_model model).
Local Notation entry := (observed_entry model stores input R A c).
Local Notation stamp := (stamped model stores input R A c).
Local Notation log := (actor_log model stores input R A c).
Local Notation tok := (tokens model stores input R A c).
Local Notation cur := (cursor_at model stores input R A c).
Local Notation act := (entry_action model stores input R A c).
Local Notation batch := (entry_batch model stores input R A c).
Local Notation path_of := (entry_site model stores input R A c).
Local Notation cut := (logged_cut model stores input R A c).
Local Arguments tokens {M E Store Input} model stores input R A c {p B} _.
Local Arguments cursor_at {M E Store Input} model stores input R A c {p B} _.

Lemma atomic_primitive_path p B t e u root tree :
  stamp p B t e u ->
  atomic_cursor root tree t ->
  path_of p e = root.
Proof.
  intros [Prim Obs] State.
  assert (Path : path_of p e = action_path (act p e)).
  { pose proof (entry_primitive model stores input R A c p e) as Actual.
    unfold entry_site, event_route. destruct Actual; reflexivity. }
  rewrite Path.
  destruct Prim; cbn [atomic_cursor atomic_layout] in State;
    destruct State as [Eq Shape]; try contradiction; exact Eq.
Qed.

Lemma atomic_log_invariant p B root code tree tr t :
  log p B (Code root code) tr t ->
  atomic_layout code tree ->
  atomic_cursor root tree t /\
  (forall e, In e tr ->
    path_of p e = root /\
    forall ev, In ev (batch p e) -> payload_in_layout root tree ev) /\
  (forall v, cut_returned p t v ->
    forall path kind sender receiver, site tree path kind sender receiver ->
    (p = sender \/ p = receiver) ->
    exists e, In e tr /\
      action_at kind (root ++ path) sender receiver p (act p e)).
Proof.
  intros Run Shape. induction Run.
  - split; [now split|]. split; [intros e []|].
    intros v Done. contradiction Done.
  - destruct IHRun as [State [Tokens Returns]].
    assert (View :
      (token = None /\ primitive_silent sm B t u) \/
      exists e, token = Some e /\ stamp p B t e u).
    { destruct H; cbn [atomic_cursor] in State; try contradiction.
      - left. auto.
      - right. eauto. }
    destruct View as [[Tok Silent]|(e & Tok & Stamped)]; subst token.
    + split; [eapply atomic_silent; eassumption|].
      split; [exact Tokens|]. intros v Done path kind sender receiver At Peer.
      exfalso. eapply atomic_silent_return; eassumption.
    + split; [eapply atomic_action; [exact (proj1 Stamped)|exact State]|].
      split.
      * intros item Member. cbn [snoc_token] in Member.
        apply in_append_large in Member.
        destruct Member as [Old|[<-|[]]].
        -- exact (Tokens item Old).
        -- split.
           ++ eapply atomic_primitive_path; eassumption.
           ++ eapply atomic_observed; [exact (proj2 Stamped)|exact State].
      * intros v Done path kind sender receiver At Peer.
        exists e. split; [cbn [snoc_token]; apply in_append_large; right; now left|].
        eapply atomic_action_site;
          [exact (proj1 Stamped)|exact State|exact At|exact Peer].
Qed.
Lemma atomic_focus p B Z root tree (t : @cursor M E p B)
    (C : @cursor_context M E p Z B) focus X kind o sender rd :
  atomic_cursor root tree t ->
  t = plug C focus ->
  receive_focus p Z focus X kind o sender rd ->
  o = root /\ layout_site root tree o kind sender p.
Proof.
  intros State Eq Focus. subst t.
  destruct C; cbn [plug atomic_cursor] in State; try contradiction.
  destruct Focus; cbn [atomic_cursor atomic_layout] in State;
    destruct State as [Eq Shape]; try contradiction.
  subst o tree. split; [reflexivity|].
  exists []. rewrite app_nil_r. split; [reflexivity|].
  apply SiteExchange. assumption.
Qed.

Theorem realized_atomic S F code active inc root
    (cuts : family cut F active) past tree :
  family_at cut (at_node model stores input R A c past)
    S F code active inc root cuts ->
  (forall p d, atomic_layout (code p (inc p d)) tree) ->
  realized model stores input R A c F active root cuts tree.
Proof.
  intros At Shape. constructor.
  - intros p d e Token ev Event.
    destruct (atomic_log_invariant p _ root (code p (inc p d)) tree
      _ _ (proj1 (At p d)) (Shape p d)) as [_ [Tokens _]].
    exact (proj2 (Tokens e Token) ev Event).
  - intros p d B C focus X kind o sender rd Eq Focus.
    destruct (atomic_log_invariant p _ root (code p (inc p d)) tree
      _ _ (proj1 (At p d)) (Shape p d)) as [State _].
    exact (proj2 (atomic_focus p _ _ root tree _ C focus X kind o sender rd
      State Eq Focus)).
  - intros p d v Done path kind sender receiver Site Peer.
    destruct (atomic_log_invariant p _ root (code p (inc p d)) tree
      _ _ (proj1 (At p d)) (Shape p d)) as [_ [_ Returns]].
    exact (Returns v Done path kind sender receiver Site Peer).
Qed.

Theorem tracked_atomic S F code active inc root
    (cuts : family cut F active) past tree :
  family_at cut (at_node model stores input R A c past)
    S F code active inc root cuts ->
  (forall p d, atomic_layout (code p (inc p d)) tree) ->
  tracked_realization model stores input R A c F active root cuts tree.
Proof.
  intros At Shape. constructor.
  - eapply realized_atomic; eassumption.
  - intros p d.
    assert (Bounds : forall o,
      cut_reached model stores input R A c p (F p) (cuts p d) o -> o = root).
    { intros o [(e & Token & Path)|(X & kind & sender & rd & B & C & focus & Eq & Focus)].
      - destruct (atomic_log_invariant p _ root (code p (inc p d)) tree
          _ _ (proj1 (At p d)) (Shape p d)) as [_ [Tokens _]].
        rewrite <- Path. exact (proj1 (Tokens e Token)).
      - destruct (atomic_log_invariant p _ root (code p (inc p d)) tree
          _ _ (proj1 (At p d)) (Shape p d)) as [State _].
        exact (proj1 (atomic_focus p _ _ root tree _ C focus X kind o sender rd
          State Eq Focus)). }
    specialize (Shape p d).
    destruct (code p (inc p d)) as [B sig|B value| | ];
      cbn [atomic_layout] in Shape; try contradiction.
    + destruct sig; cbn [atomic_layout] in Shape; try contradiction; subst tree.
      * apply layout_order_leaf. intros o Reached.
        rewrite (Bounds o Reached). exists []. now rewrite app_nil_r.
      * apply layout_order_exchange. exact Bounds.
    + subst tree. apply layout_order_leaf. intros o Reached.
      rewrite (Bounds o Reached). exists []. now rewrite app_nil_r.
Qed.

Lemma atomic_layout_tree {p B} (code : Choreo M p B) tree :
  ((exists x, code = Pure x) \/ atomic p B code) ->
  atomic_tree p code = tree ->
  atomic_layout code tree.
Proof.
  intros [[x ->]|Atom] Eq.
  - cbn [atomic_tree] in Eq. now subst tree.
  - destruct Atom; cbn [atomic_tree] in Eq; subst tree; reflexivity.
Qed.

Theorem tracked_atomic_node S F code active inc root
    (cuts : family cut F active) past tree :
  family_at cut (at_node model stores input R A c past)
    S F code active inc root cuts ->
  (forall p d, (exists x, code p (inc p d) = Pure x) \/
    atomic p (F p) (code p (inc p d))) ->
  (forall p d, atomic_tree p (code p (inc p d)) = tree) ->
  tracked_realization model stores input R A c F active root cuts tree.
Proof.
  intros At Atoms Trees.
  eapply tracked_atomic; [exact At|].
  intros p d. apply atomic_layout_tree; [apply Atoms|apply Trees].
Qed.
End AtomicLog.

Print Assumptions realized_atomic.
Print Assumptions tracked_atomic.
Print Assumptions tracked_atomic_node.
