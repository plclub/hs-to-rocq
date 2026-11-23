From Stdlib Require Import Lists.List Logic.Eqdep_dec.
From ParkourTheories Require Import Choreography.Occurrences
  Choreography.PendingDeliveries Choreography.RoleSteps Choreography.Execution
  Network.Mailboxes Network.Endpoints Network.Execution Semantics.SharedState
  Semantics.LocalEffects Projection.FIFO.MessageRepresentation
  Projection.Matching.PrefixRelation Projection.Matching.PayloadHistory
  Choreography.Histories.CursorHistories
  Choreography.Histories.TransitionArchive
  Choreography.Results.OperandObservations.
Require Import Parkour.Symbol.
Import ListNotations.
Local Arguments positions {M E Store A} _ _.
Local Arguments ContextHole {M E p X}.
Local Arguments ContextSeq {M E p X Y Z} _ _ _.
Local Arguments ContextLeft {M E p X Y Z} _ _.
Local Arguments ContextRight {M E p X Y Z} _ _.

Section Focus.
Context {M E : Type -> Type} {Store : Type}.
Variable model : local_model M E role Store.
Variable R : list role.

(* Focusing preserves the observed network action, its wire, the ghost queue,
   and the event batch. It does not replace an observed action by a source-only
   cursor history. *)
Theorem observed_primitive_focus_with_origin p A t s q a u s' q' na gs gs' ev :
  observed model R A t s q a u s' q' na gs gs' ev ->
  exists X (C : @cursor_context M E p X A) before after,
    silent_prefix model t (plug C before) /\
    primitive_action model R X before s q a after s' q' /\
    observed model R X before s q a after s' q' na gs gs' ev /\
    u = plug C after /\
    forall kind site sender recipient operand,
      In (Produced kind site sender recipient operand) ev ->
      sender = p /\ position p before = Some site.
Proof.
  induction 1.
  - exists _, ContextHole. do 2 eexists.
    split; [constructor|]. split; [apply PrimitiveLocal; exact H|].
    split; [apply OLocal; exact H|].
    split; [reflexivity|]. intros; contradiction.
  - exists _, ContextHole. do 2 eexists.
    split; [constructor|]. split.
    + rewrite map_app. cbn. apply PrimitiveSend.
    + split; [apply OSend|]. split; [reflexivity|].
      intros kind site sender recipient operand [Eq|No]; [|contradiction].
      inversion Eq; subst. split; reflexivity.
  - exists _, ContextHole. do 2 eexists.
    split; [constructor|]. split.
    + eapply PrimitiveReceive; [exact h|].
      apply take_pending_at. eapply delivery_source. exact H.
    + split; [eapply OReceive; eassumption|]. split; [reflexivity|].
      intros kind site sender recipient operand [Eq|No];
        [discriminate|contradiction].
  - exists _, ContextHole. do 2 eexists.
    split; [constructor|]. split.
    + rewrite map_app, announcement_pending. apply PrimitiveAnnounce.
    + split; [apply OAnnounce|]. split; [reflexivity|].
      intros kind site sender recipient operand InEvent.
      apply in_map_iff in InEvent. destruct InEvent as [m [Eq InM]].
      unfold announcement_messages in InM.
      apply in_map_iff in InM. destruct InM as [peer [Em InPeer]]. subst m.
      cbn in Eq. inversion Eq; subst. split; reflexivity.
  - exists _, ContextHole. do 2 eexists.
    split; [constructor|]. split.
    + eapply PrimitiveHear; [exact h|].
      apply take_pending_at. eapply delivery_source. exact H.
    + split; [eapply OHear; eassumption|]. split; [reflexivity|].
      intros kind site sender recipient operand [Eq|No];
        [discriminate|contradiction].
  - destruct IHobserved as (U & C & before & after & Sil & Prim & Obs & End &
    Origin).
    exists U, (ContextSeq o k C), before, after.
    split.
    + apply (silent_prefix_plug model p _ _ (ContextSeq o k ContextHole)).
      exact Sil.
    + split; [exact Prim|]. split; [exact Obs|].
      split; [cbn; now rewrite End|exact Origin].
  - destruct IHobserved as (U & C & before & after & Sil & Prim & Obs & End &
    Origin).
    exists U, (ContextLeft t C), before, after.
    split.
    + apply (silent_prefix_plug model p _ _ (ContextLeft t ContextHole)).
      exact Sil.
    + split; [exact Prim|]. split; [exact Obs|].
      split; [cbn; now rewrite End|exact Origin].
  - destruct IHobserved as (U & C & before & after & Sil & Prim & Obs & End &
    Origin).
    exists U, (ContextRight f C), before, after.
    split.
    + apply (silent_prefix_plug model p _ _ (ContextRight f ContextHole)).
      exact Sil.
    + split; [exact Prim|]. split; [exact Obs|].
      split; [cbn; now rewrite End|exact Origin].
  - destruct IHobserved as (U & C & before & after & Sil & Prim & Obs & End &
    Origin).
    exists U, C, before, after.
    split; [eapply PrefixCons; eassumption|].
    split; [exact Prim|]. split; [exact Obs|]. split; assumption.
Qed.

Theorem observed_primitive_focus p A t s q a u s' q' na gs gs' ev :
  observed model R A t s q a u s' q' na gs gs' ev ->
  exists X (C : @cursor_context M E p X A) before after,
    silent_prefix model t (plug C before) /\
    primitive_action model R X before s q a after s' q' /\
    observed model R X before s q a after s' q' na gs gs' ev /\
    u = plug C after.
Proof.
  intro Obs.
  destruct (observed_primitive_focus_with_origin p A t s q a u s' q' na gs gs'
    ev Obs)
    as (X & C & before & after & Sil & Prim & Focus & End & Origin).
  exists X,C,before,after. repeat split; assumption.
Qed.
End Focus.

Section MatchedArchives.
Context {M E : Type -> Type} {Store Input : Type}.
Variable model : local_model M E role (Store * Input).
Variable stores : role -> Store.
Variable input : Input.
Variable R : list role.
Variable A : role -> Type.
Variable c : forall p, Choreography.Choreo2.Choreo M p (A p).
Local Notation sm := (shared_model model).
Local Notation SC := (@Choreography.Execution.configuration M E ((role -> Store)
  *
  Input) A).
Local Notation NC := (@Network.Execution.configuration M E ((role -> Store) *
  Input)).
Local Notation history := (payload_history model stores input R A c).

(* Every entry retains its real matched prefix, its actual paired step, and
   the focused observation of that same step. All wire/decoder evidence is
   still available by eliminating observation_at_focus. *)
Record observed_entry (p : role) : Type := ObservedEntry {
  entry_tc : list (@source_action E ((role -> Store) * Input));
  entry_source : SC;
  entry_tn : list (@action E ((role -> Store) * Input));
  entry_network : NC;
  entry_ghosts : list message;
  entry_past : list payload_event;
  entry_action : @source_action E ((role -> Store) * Input);
  entry_source_after : SC;
  entry_network_action : @action E ((role -> Store) * Input);
  entry_network_after : NC;
  entry_ghosts_after : list message;
  entry_batch : list payload_event;
  entry_prefix : history entry_tc entry_source entry_tn entry_network
    entry_ghosts entry_past;
  entry_pair : paired_observed model R A entry_source entry_network entry_ghosts
    entry_action entry_source_after entry_network_action entry_network_after
    entry_ghosts_after entry_batch;
  entry_actor : In p R;
  entry_type : Type;
  entry_context : @cursor_context M E p entry_type (A p);
  entry_before : @cursor M E p entry_type;
  entry_after : @cursor M E p entry_type;
  entry_silent : silent_prefix sm (positions entry_source p)
    (plug entry_context entry_before);
  entry_primitive : primitive_action sm R entry_type entry_before
    (Choreography.Execution.shared_store entry_source) (deliveries entry_source)
    entry_action entry_after (Choreography.Execution.shared_store
      entry_source_after)
    (deliveries entry_source_after);
  observation_at_focus : observed sm R entry_type entry_before
    (Choreography.Execution.shared_store entry_source) (deliveries entry_source)
    entry_action entry_after (Choreography.Execution.shared_store
      entry_source_after)
    (deliveries entry_source_after) entry_network_action
    entry_ghosts entry_ghosts_after entry_batch;
  entry_end : positions entry_source_after p = plug entry_context entry_after;
  entry_production_origin : forall kind site sender recipient operand,
    In (Produced kind site sender recipient operand) entry_batch ->
    sender = p /\ position p entry_before = Some site
}.

Definition entry_site p (e : observed_entry p) : occurrence :=
  event_route p (entry_context p e) (entry_before p e).

Lemma entry_produced_site p (e : observed_entry p) kind site sender recipient
  operand :
  In (Produced kind site sender recipient operand) (entry_batch p e) ->
  sender = p /\ entry_site p e = site.
Proof.
  intro Produced.
  destruct (entry_production_origin p e _ _ _ _ _ Produced) as [Actor Site].
  split; [exact Actor|]. unfold entry_site, event_route. now rewrite Site.
Qed.

Definition located p := (occurrence * observed_entry p)%type.
Definition actor_archive := forall p, list (located p).

Definition entry_in_past p past (e : observed_entry p) : Prop :=
  exists suffix, past = entry_past p e ++ entry_batch p e ++ suffix.
Definition archive_valid past (archives : actor_archive) : Prop :=
  forall p path e, In (path,e) (archives p) ->
    path = entry_site p e /\ entry_in_past p past e.

Definition add_entry p (e : observed_entry p) (archives : actor_archive) :
    actor_archive :=
  fun r =>
    match role_eq_dec p r with
    | left same => eq_rect p (fun r => list (located r))
        ((entry_site p e,e) :: archives p) r same
    | right _ => archives r
    end.

Lemma add_entry_same p e archives :
  add_entry p e archives p = (entry_site p e,e) :: archives p.
Proof.
  unfold add_entry. destruct (role_eq_dec p p) as [same|Ne]; [|contradiction].
  rewrite (UIP_dec role_eq_dec same eq_refl). reflexivity.
Qed.

Lemma add_entry_other p e archives r : p <> r ->
  add_entry p e archives r = archives r.
Proof. intro Ne. unfold add_entry. destruct (role_eq_dec p r); congruence. Qed.

Lemma add_entry_keeps p e archives r path item :
  In (path,item) (archives r) ->
  In (path,item) (add_entry p e archives r).
Proof.
  intro Member. destruct (role_eq_dec p r) as [->|Ne].
  - rewrite add_entry_same. now right.
  - rewrite add_entry_other by exact Ne. exact Member.
Qed.

Lemma archive_valid_append past extra archives :
  archive_valid past archives -> archive_valid (past ++ extra) archives.
Proof.
  intros Valid p path e Member.
  destruct (Valid p path e Member) as [Site [suffix Eq]].
  split; [exact Site|]. exists (suffix ++ extra).
  rewrite Eq. now rewrite <- !app_assoc.
Qed.

Lemma add_entry_valid past batch p e archives :
  archive_valid past archives ->
  entry_past p e = past -> entry_batch p e = batch ->
  archive_valid (past ++ batch) (add_entry p e archives).
Proof.
  intros Valid Past Batch r path item Member.
  destruct (role_eq_dec p r) as [->|Ne].
  - rewrite add_entry_same in Member. destruct Member as [Eq|Old].
    + injection Eq as Path Item. subst path item.
      split; [reflexivity|]. exists []. rewrite Past, Batch, app_nil_r.
      reflexivity.
    + exact (archive_valid_append _ _ _ Valid _ _ _ Old).
  - rewrite add_entry_other in Member by exact Ne.
    exact (archive_valid_append _ _ _ Valid _ _ _ Member).
Qed.

(* This relation is constructed in lockstep with the global matched history.
   A role cannot choose a different path or a different wire history. *)
Inductive observed_archives :
    list (@source_action E ((role -> Store) * Input)) -> SC ->
    list (@action E ((role -> Store) * Input)) -> NC ->
    list message -> list payload_event -> actor_archive -> Prop :=
| ArchivesInitial :
    observed_archives [] (source_initial stores input A c)
      [] (network_initial stores input R A c) [] [] (fun _ => [])
| ArchivesSnoc tc s tn n gs past archives p (e : observed_entry p) :
    observed_archives tc s tn n gs past archives ->
    entry_tc p e = tc -> entry_source p e = s ->
    entry_tn p e = tn -> entry_network p e = n ->
    entry_ghosts p e = gs -> entry_past p e = past ->
    state_match model R A (entry_source_after p e) (entry_network_after p e)
      (entry_ghosts_after p e) ->
    observed_archives (tc ++ [entry_action p e]) (entry_source_after p e)
      (tn ++ [entry_network_action p e]) (entry_network_after p e)
      (entry_ghosts_after p e) (past ++ entry_batch p e)
      (add_entry p e archives).

Theorem observed_archives_valid tc s tn n gs past archives :
  observed_archives tc s tn n gs past archives -> archive_valid past archives.
Proof.
  induction 1.
  - intros p path e Member. contradiction.
  - eapply add_entry_valid; [exact IHobserved_archives|eassumption|reflexivity].
Qed.

Theorem payload_has_observed_archives tc s tn n gs past :
  history tc s tn n gs past ->
  exists archives, observed_archives tc s tn n gs past archives.
Proof.
  induction 1 as [|tc s tn n gs past a s' na n' gs' ev Hist IH Pair State].
  - exists (fun _ => []). constructor.
  - destruct IH as [archives Archives].
    destruct Pair as [p pre post t u s' n' a na gs' ev Member Before After Obs
      Frame Step].
    destruct (observed_primitive_focus_with_origin sm R p _ _ _ _ _ _ _ _ _ _ _
      _ Obs)
      as (X & C & before & after & Sil & Prim & Focus & End & Origin).
    set (entry := ObservedEntry p tc s tn n gs past a s' na n' gs' ev Hist
      (ObservedPair model R A s n gs p pre post t u s' n' a na gs' ev
        Member Before After Obs Frame Step)
      Member X C before after Sil Prim Focus End Origin).
    exists (add_entry p entry archives).
    eapply ArchivesSnoc with (p := p) (e := entry) (archives := archives)
      (tc := tc) (s := s) (tn := tn) (n := n) (gs := gs) (past := past);
      try reflexivity; eassumption.
Qed.

Theorem observed_archives_history tc s tn n gs past archives :
  observed_archives tc s tn n gs past archives -> history tc s tn n gs past.
Proof.
  induction 1 as [|tc s tn n gs past archives p e Prior IH Tc Source Tn Net
    Ghost Past Match].
  - constructor.
  - eapply PayloadSnoc; [exact IH| |exact Match].
    pose proof (entry_pair p e) as Pair.
    now rewrite Source, Net, Ghost in Pair.
Qed.

(* The current source syntax and the observed archive come from one global
   derivation. In particular no role supplies an independently guessed run. *)
Theorem observed_archives_syntax tc s tn n gs past archives :
  observed_archives tc s tn n gs past archives ->
  forall p, syntax_cut sm R p (A p) [] (c p) (positions s p).
Proof.
  intros Archives p.
  pose proof (observed_archives_history _ _ _ _ _ _ _ Archives) as Hist.
  pose proof (prefix_source_run model stores input R A c _ _ _ _ _
    (history_is_matched model stores input R A c _ _ _ _ _ _ Hist)) as Run.
  apply code_history_has_syntax_cut with (tr := actor_actions p tc).
  exact (initial_actor_history sm R A c (stores,input) tc s Run p).
Qed.

Definition archive_trace_valid tc (archives : actor_archive) : Prop :=
  forall p path e, In (path,e) (archives p) ->
    exists suffix, tc = entry_tc p e ++ [entry_action p e] ++ suffix.

Lemma archive_trace_append tc extra archives :
  archive_trace_valid tc archives -> archive_trace_valid (tc ++ extra) archives.
Proof.
  intros Valid p path e Member.
  destruct (Valid p path e Member) as [suffix Eq].
  exists (suffix ++ extra). rewrite Eq. now rewrite <- !app_assoc.
Qed.

Theorem observed_archives_trace tc s tn n gs past archives :
  observed_archives tc s tn n gs past archives -> archive_trace_valid tc
    archives.
Proof.
  induction 1 as [|tc s tn n gs past archives p e Prior IH Tc Source Tn Net
    Ghost Past Match].
  - intros p path e Member. contradiction.
  - intros r path item Member.
    destruct (role_eq_dec p r) as [->|Ne].
    + rewrite add_entry_same in Member. destruct Member as [Eq|Old].
      * injection Eq as Path Item. subst path item.
        exists []. rewrite Tc, app_nil_r. reflexivity.
      * exact (archive_trace_append _ _ _ IH _ _ _ Old).
    + rewrite add_entry_other in Member by exact Ne.
      exact (archive_trace_append _ _ _ IH _ _ _ Member).
Qed.

(* Coverage is important: an event in the global past cannot be justified
   using an unrelated observation that happened to have the same bytes. *)
Theorem observed_past_event_archived tc s tn n gs past archives :
  observed_archives tc s tn n gs past archives ->
  forall event, In event past ->
    exists p path e, In (path,e) (archives p) /\ In event (entry_batch p e).
Proof.
  induction 1 as [|tc s tn n gs past archives p e Prior IH Tc Source Tn Net
    Ghost Past Match];
    intros event Member; [contradiction|].
  apply in_app_or in Member. destruct Member as [Old|New].
  - destruct (IH event Old) as (r & path & item & Seen & Batch).
    exists r,path,item. split; [apply add_entry_keeps; exact Seen|exact Batch].
  - exists p,(entry_site p e),e.
  split; [rewrite add_entry_same; now left|exact New].
Qed.

Definition edge_eq_dec (a b : source_edge) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

(* Branch descent changes only relative paths. Each entry keeps its original
   global source occurrence, its paired observation, and its global past stamp.
   *)
Fixpoint branch_items p edge (items : list (located p)) : list (located p) :=
  match items with
  | [] => []
  | (path,e) :: tail =>
      match path with
      | [] => branch_items p edge tail
      | head :: rest =>
          if edge_eq_dec head edge
          then (rest,e) :: branch_items p edge tail
          else branch_items p edge tail
      end
  end.

Lemma branch_items_origin p edge items path e :
  In (path,e) (branch_items p edge items) -> In (edge :: path,e) items.
Proof.
  revert items. fix IH 1. intros [|[route item] tail]; cbn; [contradiction|].
  destruct route as [|head rest]; [intro H; right; now apply IH|].
  destruct (edge_eq_dec head edge) as [Same|Ne].
  - intros [Eq|Old].
    + injection Eq as Path Entry. subst rest item head. now left.
    + right. now apply IH.
  - intro Old. right. now apply IH.
Qed.

Lemma branch_items_complete p edge items path e :
  In (edge :: path,e) items -> In (path,e) (branch_items p edge items).
Proof.
  revert items. fix IH 1. intros [|[route item] tail]; cbn; [contradiction|].
  intros [Eq|Old].
  - injection Eq as Route Entry. subst route item. cbn.
    destruct (edge_eq_dec edge edge); [now left|contradiction].
  - destruct route as [|head rest]; [now apply IH|].
    destruct (edge_eq_dec head edge); [right; now apply IH|now apply IH].
Qed.

Lemma branch_items_iff p edge items path e :
  In (path,e) (branch_items p edge items) <-> In (edge :: path,e) items.
Proof. split; [apply branch_items_origin|apply branch_items_complete]. Qed.

Definition branch_valid p past root (items : list (located p)) : Prop :=
  forall path e, In (path,e) items ->
    entry_site p e = root ++ path /\ entry_in_past p past e.

Lemma branch_items_valid p past root items edge :
  branch_valid p past root items ->
  branch_valid p past (child root edge) (branch_items p edge items).
Proof.
  intros Valid path e Member.
  apply branch_items_origin in Member.
  destruct (Valid _ _ Member) as [Site Past].
  split; [|exact Past].
  unfold child. rewrite <- app_assoc. exact Site.
Qed.

Fixpoint subarchive p route (items : list (located p)) : list (located p) :=
  match route with
  | [] => items
  | edge :: rest => subarchive p rest (branch_items p edge items)
  end.

Lemma subarchive_origin p route :
  forall items path e, In (path,e) (subarchive p route items) ->
    In (route ++ path,e) items.
Proof.
  induction route as [|edge route IH]; intros items path e Member; cbn in *.
  - exact Member.
  - apply branch_items_origin. now apply IH.
Qed.

Lemma subarchive_complete p route :
  forall items path e, In (route ++ path,e) items ->
    In (path,e) (subarchive p route items).
Proof.
  induction route as [|edge route IH]; intros items path e Member; cbn in *.
  - exact Member.
  - apply IH. now apply branch_items_complete.
Qed.

Lemma subarchive_iff p route items path e :
  In (path,e) (subarchive p route items) <-> In (route ++ path,e) items.
Proof. split; [apply subarchive_origin|apply subarchive_complete]. Qed.

Lemma subarchive_app p left right :
  forall items, subarchive p (left ++ right) items =
    subarchive p right (subarchive p left items).
Proof.
  induction left as [|edge left IH]; intro items; cbn; [reflexivity|apply IH].
Qed.

Lemma subarchive_valid p past route :
  forall root items, branch_valid p past root items ->
    branch_valid p past (root ++ route) (subarchive p route items).
Proof.
  induction route as [|edge route IH]; intros root items Valid; cbn.
  - now rewrite app_nil_r.
  - replace (root ++ edge :: route) with (child root edge ++ route)
      by (unfold child; now rewrite <- app_assoc).
    apply IH. apply branch_items_valid. exact Valid.
Qed.

Theorem observed_subarchive_same_past tc s tn n gs past archives p route :
  observed_archives tc s tn n gs past archives ->
  branch_valid p past route (subarchive p route (archives p)).
Proof.
  intro Archives.
  change (branch_valid p past ([] ++ route) (subarchive p route (archives p))).
  apply subarchive_valid. intros path e Member.
  destruct (observed_archives_valid _ _ _ _ _ _ _ Archives p path e Member)
    as [Site Past].
  split; [symmetry; exact Site|exact Past].
Qed.

Theorem observed_subarchive_receive tc s tn n gs past archives p route path e
    kind site sender recipient wire :
  observed_archives tc s tn n gs past archives ->
  In (path,e) (subarchive p route (archives p)) ->
  In (Consumed kind site sender recipient wire) (entry_batch p e) ->
  past_receive past kind site sender recipient wire.
Proof.
  intros Archives Member Consumed.
  destruct (observed_subarchive_same_past _ _ _ _ _ _ _ _ _ Archives _ _ Member)
    as [_ [suffix Eq]].
  pose proof (observed_archives_history _ _ _ _ _ _ _ Archives) as Hist.
  apply (proj2 (history_past_ok model stores input R A c _ _ _ _ _ _ Hist)).
  rewrite Eq. apply in_or_app. right. apply in_or_app. now left.
Qed.

Theorem observed_subarchive_same_trace tc s tn n gs past archives p route path e
  :
  observed_archives tc s tn n gs past archives ->
  In (path,e) (subarchive p route (archives p)) ->
  exists suffix, tc = entry_tc p e ++ [entry_action p e] ++ suffix.
Proof.
  intros Archives Member.
  apply subarchive_origin in Member.
  exact (observed_archives_trace _ _ _ _ _ _ _ Archives p _ e Member).
Qed.

Theorem past_receive_sender_entry tc s tn n gs past archives
    kind route path sender recipient wire :
  observed_archives tc s tn n gs past archives ->
  past_receive past kind (route ++ path) sender recipient wire ->
  exists operand (e : observed_entry sender),
    In (path,e) (subarchive sender route (archives sender)) /\
    In (Produced kind (route ++ path) sender recipient operand) (entry_batch
      sender e) /\
    entry_site sender e = route ++ path /\
    wire = operand_wire operand.
Proof.
  intros Archives (operand & before & between & after & Past & Wire).
  assert (Produced : In (Produced kind (route ++ path) sender recipient operand)
    past).
  { rewrite Past. apply in_or_app. right. now left. }
  destruct (observed_past_event_archived _ _ _ _ _ _ _ Archives _ Produced)
    as (p & site & e & Member & Batch).
  destruct (entry_produced_site p e _ _ _ _ _ Batch) as [Actor Site].
  subst p.
  destruct (observed_archives_valid _ _ _ _ _ _ _ Archives sender site e Member)
    as [Location _].
  rewrite Site in Location. subst site.
  exists operand,e. split; [now apply subarchive_complete|].
  split; [exact Batch|]. split; assumption.
Qed.

(* The worked roster is decidable and minimal: a role belongs exactly when
   its branch archive is nonempty. Deduplication makes NoDup unconditional;
   membership in R comes from the actual recorded actor certificate. *)
Definition observed_region_roles (archives : actor_archive) route : list role :=
  filter (fun p =>
    match subarchive p route (archives p) with [] => false | _ => true end)
    (nodup role_eq_dec R).

Lemma observed_region_roles_nodup archives route : NoDup (observed_region_roles
  archives
  route).
Proof. apply NoDup_filter. apply NoDup_nodup. Qed.

Lemma observed_region_roles_included archives route p :
  In p (observed_region_roles archives route) -> In p R.
Proof.
  intro Member. apply filter_In in Member. destruct Member as [InRoster _].
  now apply nodup_In in InRoster.
Qed.

Lemma observed_region_roles_spec archives route p :
  In p (observed_region_roles archives route) <->
  subarchive p route (archives p) <> [].
Proof.
  split.
  - intro Member. apply filter_In in Member.
    intro Empty. rewrite Empty in Member. discriminate (proj2 Member).
  - intro Nonempty. apply filter_In.
    destruct (subarchive p route (archives p)) as [|[path e] tail] eqn:Items;
      [contradiction|].
    split; [apply nodup_In; exact (entry_actor p e)|reflexivity].
Qed.

Lemma observed_region_roles_minimal archives route active :
  (forall p, subarchive p route (archives p) <> [] -> In p active) ->
  forall p, In p (observed_region_roles archives route) -> In p active.
Proof.
  intros Covers p Member. apply Covers. now apply observed_region_roles_spec.
Qed.

Lemma observed_region_roles_descends archives route rest p :
  In p (observed_region_roles archives (route ++ rest)) ->
  In p (observed_region_roles archives route).
Proof.
  rewrite !observed_region_roles_spec.
  rewrite subarchive_app. intros Nonempty Empty.
  rewrite Empty in Nonempty.
  assert (Nil : forall r, subarchive p r [] = []).
  { induction r; cbn; assumption || reflexivity. }
  rewrite Nil in Nonempty. contradiction.
Qed.

Theorem past_receive_sender_worked tc s tn n gs past archives
    kind route path sender recipient wire :
  observed_archives tc s tn n gs past archives ->
  past_receive past kind (route ++ path) sender recipient wire ->
  In sender (observed_region_roles archives route).
Proof.
  intros Archives Receive.
  destruct (past_receive_sender_entry _ _ _ _ _ _ _ _ _ _ _ _ _ Archives
    Receive)
    as (operand & e & Member & Batch & Site & Wire).
  apply observed_region_roles_spec. intro Empty. rewrite Empty in Member.
    contradiction.
Qed.

Corollary past_receive_sender_present tc s tn n gs past archives
    route active kind sender recipient wire :
  observed_archives tc s tn n gs past archives ->
  (forall p, In p (observed_region_roles archives route) -> In p active) ->
  past_receive past kind route sender recipient wire ->
  In sender active.
Proof.
  intros Archives Covers Receive. apply Covers.
  eapply past_receive_sender_worked with (path := []); [exact Archives|].
  rewrite app_nil_r. exact Receive.
Qed.

Theorem matched_has_observed_archives tc s tn n gs :
  matched_prefix model stores input R A c tc s tn n gs ->
  exists past archives,
    history tc s tn n gs past /\
    observed_archives tc s tn n gs past archives /\
    archive_valid past archives.
Proof.
  intro Matched.
  destruct (matched_payload_history model stores input R A c _ _ _ _ _ Matched)
    as [past Hist].
  destruct (payload_has_observed_archives _ _ _ _ _ _ Hist) as [archives
    Archives].
  exists past,archives. split; [exact Hist|].
  split; [exact Archives|]. eapply observed_archives_valid; exact Archives.
Qed.

Definition actor_observed_cut p tc (s : SC) past (items : list (located p)) :
  Prop :=
  syntax_cut sm R p (A p) [] (c p) (positions s p) /\
  branch_valid p past [] items /\
  forall path e, In (path,e) items ->
    exists suffix, tc = entry_tc p e ++ [entry_action p e] ++ suffix.

Theorem matched_has_observed_cuts tc s tn n gs :
  matched_prefix model stores input R A c tc s tn n gs ->
  exists past archives,
    observed_archives tc s tn n gs past archives /\
    forall p, actor_observed_cut p tc s past (archives p).
Proof.
  intro Matched.
  destruct (matched_has_observed_archives _ _ _ _ _ Matched)
    as (past & archives & Hist & Archives & Valid).
  exists past,archives. split; [exact Archives|]. intro p.
  split; [eapply observed_archives_syntax; exact Archives|].
  split.
  - intros path e Member. destruct (Valid p path e Member) as [Site Past].
    split; [symmetry; exact Site|exact Past].
  - exact (observed_archives_trace _ _ _ _ _ _ _ Archives p).
Qed.

End MatchedArchives.

Print Assumptions observed_primitive_focus.
Print Assumptions matched_has_observed_archives.
Print Assumptions observed_archives_syntax.
Print Assumptions observed_archives_trace.
Print Assumptions observed_subarchive_same_past.
Print Assumptions observed_subarchive_receive.
Print Assumptions observed_subarchive_same_trace.
Print Assumptions observed_past_event_archived.
Print Assumptions matched_has_observed_cuts.
Print Assumptions branch_items_iff.
Print Assumptions subarchive_iff.
Print Assumptions entry_produced_site.
Print Assumptions past_receive_sender_entry.
Print Assumptions observed_region_roles_nodup.
Print Assumptions observed_region_roles_spec.
Print Assumptions observed_region_roles_descends.
Print Assumptions past_receive_sender_worked.
Print Assumptions past_receive_sender_present.
