From Stdlib Require Import Lists.List Logic.Eqdep_dec.
Require Import DeadlockPlayedFamily DeadlockPlayedActual DeadlockLocalLog
  DeadlockObservedCut DeadlockSource DeadlockLocal DeadlockChronology
  DeadlockCoherence DeadlockPlayedValues DeadlockState DeadlockWellFormed
  DeadlockPartialValues DeadlockCutSafety Parkour.Symbol Choreography.Choreo2.
Import ListNotations.
Local Notation role_eq_dec := DeadlockNetwork.role_eq_dec.

Polymorphic Lemma in_append_large {U : Type} (x : U) (pre post : list U) :
  In x (pre ++ post) <-> In x pre \/ In x post.
Proof.
  revert pre; fix IH 1; intros [|a pre]; cbn; [tauto|].
  specialize (IH pre). tauto.
Qed.

Section FamilyLog.
Context {M E Store Input} (model : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input : Input) (R : list Symbol) (A : Symbol ->
    Type)
  (c : forall p, Choreo M p (A p)).
Local Notation entry := (observed_entry model stores input R A c).
Local Notation entry_path := (entry_site model stores input R A c).
Local Notation has_stamp := (entry_in_past model stores input R A c).
Local Notation alog := (actor_log model stores input R A c).
Local Arguments positions {M E Store A} _ _.

#[universes(template)]
Record logged_cut (p : Symbol) (B : Type) : Type := LoggedCut {
  cursor_at : @cursor M E p B;
  tokens : list (entry p)
}.
Arguments LoggedCut {p B} _ _.
Arguments cursor_at {p B} _.
Arguments tokens {p B} _.

Variable past : list payload_event.
Variable ar : actor_archive model stores input R A c.

Definition at_node p B o code (cut : logged_cut p B) :=
  alog p B (Code o code) (tokens cut) (cursor_at cut) /\
  forall e, In e (tokens cut) -> has_stamp p past e.
Definition finished p B (cut : logged_cut p B) v := cut_returned p (cursor_at
  cut) v.

(* Every role that did work inside the region is present. Its cut owns
   exactly its logged entries from that region. A blocked or merely entered
   role may also be present without having produced any entries yet. *)
Definition in_region p root (e : entry p) :=
  In (entry_path p e,e) (ar p) /\ DeadlockChronology.extends root (entry_path p
    e).

Definition owns_region F active root (cuts : family logged_cut F active) :=
  NoDup active /\
  (forall p e, in_region p root e -> In p active) /\
  (forall p d e, In e (tokens (cuts p d)) <-> in_region p root e).

Lemma in_order_member p e items :
  In e (in_order model stores input R A c p items) <->
  exists route, In (route,e) items.
Proof.
  revert items; fix IH 1; intros [|[path token] items]; cbn [in_order].
  - split; [contradiction|intros [? []]].
  - specialize (IH items). split.
    + intros Member; apply in_append_large in Member.
    destruct Member as [Old|[<-|[]]].
      * apply IH in Old as [r H]. exists r; now right.
      * exists path; now left.
    + intros [r [Eq|Old]]; apply in_append_large.
      * injection Eq as _ ->. right; now left.
      * left; apply IH. now exists r.
Qed.

Definition root_cuts (s : @configuration M E ((Symbol -> Store) * Input) A) :
    family logged_cut A R :=
  fun p _ => LoggedCut (positions s p) (in_order model stores input R A c p (ar
    p)).

Theorem root_log_family tc s tn n gs :
  observed_archives model stores input R A c tc s tn n gs past ar -> NoDup R ->
  owns_region A R [] (root_cuts s) /\
  (forall p d, at_node p (A p) [] (c p) (root_cuts s p d)).
Proof.
  intros Hist ND.
  pose proof (observed_archives_valid model stores input R A c _ _ _ _ _ _ _
    Hist) as Valid.
  split.
  - split; [exact ND|]. split.
    + intros p e _. exact (entry_actor model stores input R A c p e).
    + intros p d e. unfold root_cuts; cbn [tokens]. rewrite in_order_member.
      unfold in_region. split.
      * intros [r Seen]. destruct (Valid p r e Seen) as [-> Stamp].
        split; [exact Seen|]. now exists (entry_path p e).
      * intros [Seen _]. now exists (entry_path p e).
  - intros p d; split.
    + exact (archive_role_log model stores input R A c _ _ _ _ _ _ _ Hist p).
    + intros e Seen. apply in_order_member in Seen as [r Seen].
      exact (proj2 (Valid p r e Seen)).
Qed.

Theorem owns_sender_present tc s tn n gs F active root (cuts : family logged_cut
  F active) :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  owns_region F active root cuts ->
  forall kind sender recipient wire, past_receive past kind root sender
    recipient wire ->
    In sender active.
Proof.
  intros H [_ [Cover _]] kind sender recipient wire Consumed.
  eapply (past_receive_sender_present model stores input R A c _ _ _ _ _ _ _
    root active kind sender recipient wire H); [|exact Consumed].
  intros p Worked. apply worked_roster_spec in Worked.
  destruct (subarchive model stores input R A c p root (ar p)) as [|[path e] es]
    eqn:Slice;
    [contradiction|].
  assert (Seen : In (path,e) (subarchive model stores input R A c p root (ar
    p)))
    by (rewrite Slice; now left).
  apply subarchive_origin in Seen.
  destruct (observed_archives_valid model stores input R A c _ _ _ _ _ _ _ H p _
    e Seen)
    as [Location Stamp].
  eapply Cover with (e := e). split; [now rewrite <- Location|].
  exists path. symmetry; exact Location.
Qed.
Lemma node_silent p B o code (cut : logged_cut p B) u :
  at_node p B o code cut -> silent_prefix (shared_model model) (cursor_at cut) u
    ->
  at_node p B o code (LoggedCut u (tokens cut)).
Proof.
  intros [Log Stamps] Steps. split; [|exact Stamps].
  eapply log_silent_prefix; eassumption.
Qed.

Definition expose_root (s : @configuration M E ((Symbol -> Store) * Input) A)
    who (u : @cursor M E who (A who)) : family logged_cut A R :=
  fun p _ => LoggedCut
    (match role_eq_dec who p with
     | left eq => eq_rect who (fun r => @cursor M E r (A r)) u p eq
     | right _ => positions s p end)
    (in_order model stores input R A c p (ar p)).

Theorem expose_logged_receivers tc s tn n gs who X kind o sender rd :
  observed_archives model stores input R A c tc s tn n gs past ar -> NoDup R ->
  receive_site (shared_model model) who (A who) (positions s who) X kind o
    sender rd ->
  exists (cuts : family logged_cut A R) B (C : @cursor_context M E who B (A
    who)) focus,
    owns_region A R [] cuts /\
    (forall p d, at_node p (A p) [] (c p) (cuts p d)) /\
    (forall d, cursor_at (cuts who d) = plug C focus) /\
    receive_focus who B focus X kind o sender rd.
Proof.
  intros Hist ND (B & C & focus & Sil & Site).
  destruct (root_log_family _ _ _ _ _ Hist ND) as [Own Nodes].
  exists (expose_root s who (plug C focus)), B, C, focus.
  split; [exact Own|]. split.
  - intros p d. pose proof (Nodes p d) as Start. unfold expose_root.
    destruct (role_eq_dec who p) as [Eq|Ne]; [destruct Eq|exact Start].
    exact (node_silent who (A who) [] (c who) (root_cuts s who d) (plug C focus)
      Start Sil).
  - split; [|exact Site]. intros d. unfold expose_root; cbn [cursor_at].
    destruct (role_eq_dec who who) as [Eq|Ne]; [|contradiction].
    now rewrite (Eqdep_dec.UIP_dec role_eq_dec Eq eq_refl).
Qed.

End FamilyLog.
