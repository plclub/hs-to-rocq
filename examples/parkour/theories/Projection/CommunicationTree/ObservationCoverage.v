From Stdlib Require Import Lists.List Logic.Eqdep_dec.
From ParkourTheories Require Import
  Projection.CommunicationTree.CompletedSubtrees
  Projection.RoleLogs.Families.RegionOwnership
  Choreography.Results.CutFamilySoundness
  Choreography.Histories.SyntaxDecomposition
  Projection.Matching.ObservationArchive Projection.RoleLogs.ArchiveOrder
  Choreography.Histories.TransitionArchive Choreography.Occurrences
  Choreography.PendingDeliveries Choreography.RoleSteps Semantics.LocalEffects
  Choreography.Histories.CursorHistories Choreography.Histories.RoleChronology
  Choreography.Results.OperandObservations Choreography.ReceiveSites
  Projection.Matching.PayloadHistory Projection.FIFO.MessageRepresentation
  Semantics.SharedState Choreography.Precedence.
Require Import Parkour.Symbol Parkour.Codec Choreography.Choreo2
  Control.Monad.Tree.
From ParkourTheories.Choreography Require Import WellFormedness
  Results.FiniteSelection.
Import ListNotations.

Definition payload_path (ev : payload_event) : occurrence :=
  match ev with
  | Produced _ o _ _ _ => o
  | Consumed _ o _ _ _ => o
  end.

Definition layout_site root tree o kind sender receiver : Prop :=
  exists path, o = root ++ path /\ site tree path kind sender receiver.

Definition payload_in_layout root tree (ev : payload_event) : Prop :=
  match ev with
  | Produced kind o sender receiver _ =>
      layout_site root tree o kind sender receiver
  | Consumed kind o sender receiver _ =>
      layout_site root tree o kind sender receiver
  end.

Lemma layout_site_child root edge tree whole :
  (forall path kind sender receiver, site tree path kind sender receiver ->
    site whole (edge :: path) kind sender receiver) ->
  forall o kind sender receiver,
    layout_site (child root edge) tree o kind sender receiver ->
    layout_site root whole o kind sender receiver.
Proof.
  intros Lift o kind sender receiver (path & Eq & At).
  exists (edge :: path). split; [|now apply Lift].
  rewrite Eq. unfold child. now rewrite <- app_assoc.
Qed.

Lemma payload_layout_child root edge tree whole :
  (forall path kind sender receiver, site tree path kind sender receiver ->
    site whole (edge :: path) kind sender receiver) ->
  forall ev, payload_in_layout (child root edge) tree ev ->
    payload_in_layout root whole ev.
Proof.
  intros Lift []; cbn; eapply layout_site_child; exact Lift.
Qed.

Lemma observed_batch_path {M E S}
    (model : local_model M E Symbol S) R p B
    (t : @cursor M E p B) s q a u s' q' na gs gs' batch :
  observed model R B t s q a u s' q' na gs gs' batch ->
  forall ev, In ev batch -> payload_path ev = action_path a.
Proof.
  induction 1; intros event Member; cbn in *; try contradiction;
    try (destruct Member as [<-|[]]; reflexivity); try now apply IHobserved.
  apply in_map_iff in Member. destruct Member as [m [<- Member]].
  unfold announcement_messages in Member.
  apply in_map_iff in Member. destruct Member as [peer [<- Member]].
  reflexivity.
Qed.

Definition primitive_choice_coverage {M E S}
    (p : Symbol) {B} (t : @cursor M E p B) (a : @source_action E S) : Prop :=
  match t with
  | Code root code =>
    match code with
    | Perf (@Cond _ _ _ owner _ _ _ _ _ _ _) =>
      forall peer, owner <> peer -> (p = owner \/ p = peer) ->
        action_at ChoiceDelivery root owner peer p a
    | _ => True
    end
  | _ => True
  end.

Lemma primitive_choice_coverage_correct {M E S}
    (model : local_model M E Symbol S) R p B
    (t : @cursor M E p B) s q a u s' q' :
  primitive_action model R B t s q a u s' q' ->
  primitive_choice_coverage p t a.
Proof.
  destruct 1; cbn [primitive_choice_coverage]; try exact I.
  - intros peer Ne _. cbn [action_at]. repeat split; assumption || reflexivity.
  - intros peer Ne [Same|Same]; [congruence|].
    subst peer. cbn [action_at]. repeat split; reflexivity.
Qed.

Section Realized.
Context {M E Store Input}
  (model : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input : Input) (R : list Symbol)
  (A : Symbol -> Type) (c : forall p, Choreo M p (A p)).
Local Arguments tokens {M E Store Input} model stores input R A c {p B} _.
Local Arguments cursor_at {M E Store Input} model stores input R A c {p B} _.
Local Notation sm := (shared_model model).
Local Notation entry := (observed_entry model stores input R A c).
Local Notation cut := (logged_cut model stores input R A c).
Local Notation tok := (tokens model stores input R A c).
Local Notation cur := (cursor_at model stores input R A c).
Local Notation batch := (entry_batch model stores input R A c).
Local Notation act := (entry_action model stores input R A c).
Local Notation path_of := (entry_site model stores input R A c).
Local Notation ret := (finished model stores input R A c).

Lemma entry_batch_path p (e : entry p) ev :
  In ev (batch p e) -> payload_path ev = path_of p e.
Proof.
  intro Member.
  rewrite (observed_batch_path sm R p _ _ _ _ _ _ _ _ _ _ _ _
    (observation_at_focus model stores input R A c p e) ev Member).
  pose proof (entry_primitive model stores input R A c p e) as Primitive.
  unfold entry_site, event_route.
  destruct Primitive; reflexivity.
Qed.

Lemma stamped_choice_header p X Y owner root sh rd kl sl input_value k e u :
  stamped model stores input R A c p Y
    (Code root (Perf (@Cond M p X owner Y sh rd kl sl input_value k))) e u ->
  forall peer, owner <> peer -> (p = owner \/ p = peer) ->
    action_at ChoiceDelivery root owner peer p (act p e).
Proof.
  intros [Primitive _].
  exact (primitive_choice_coverage_correct sm R p _ _ _ _ _ _ _ _ Primitive).
Qed.

(* This excludes the merely existential layouts that cannot support the
   predecessor argument. Every coverage witness below is an OWN token of the
   returned role. Receive coverage concerns immediate zipper foci only; a
   selected receiver is silently advanced before applying this interface. *)
#[universes(template)]
Record realized F active root (cuts : family cut F active) tree : Prop := {
  realized_tokens : forall p d e,
    In e (tok (cuts p d)) ->
    forall ev, In ev (batch p e) -> payload_in_layout root tree ev;
  realized_receives : forall p d B
      (C : @cursor_context M E p B (F p)) focus X kind o sender rd,
    cur (cuts p d) = plug C focus ->
    receive_focus p B focus X kind o sender rd ->
    layout_site root tree o kind sender p;
  realized_returned : forall p d v,
    ret p (F p) (cuts p d) v ->
    forall path kind sender receiver,
    site tree path kind sender receiver ->
    (p = sender \/ p = receiver) ->
    exists e, In e (tok (cuts p d)) /\
      action_at kind (root ++ path) sender receiver p (act p e)
}.

Definition cut_receive p B (node : cut p B) X kind o sender rd : Prop :=
  exists Z (C : @cursor_context M E p Z B) focus,
    cur node = plug C focus /\ receive_focus p Z focus X kind o sender rd.

Lemma realized_receive_site F active root (cuts : family cut F active) tree :
  realized F active root cuts tree ->
  forall p d X kind o sender rd,
    cut_receive p (F p) (cuts p d) X kind o sender rd ->
    layout_site root tree o kind sender p.
Proof.
  intros Layout p d X kind o sender rd (B & C & focus & Eq & Focus).
  eapply realized_receives; eassumption.
Qed.

(* These premises are constructor decomposition facts about the concrete cuts,
   not coverage assumptions. In particular TokenSplit preserves the parent's
   actual entries, and ReturnSplit retains BOTH actual returned children.
   The child logs themselves may be chronologically interleaved. *)
Theorem realized_parallel F X active root
    (cuts : family cut F active)
    (functions : family cut (fun p => X p -> F p) active)
    (arguments : family cut X active) function_tree argument_tree :
  realized _ active (child root AppFunction) functions function_tree ->
  realized _ active (child root AppArgument) arguments argument_tree ->
  (forall p d e,
    In e (tok (cuts p d)) <->
    In e (tok (functions p d)) \/ In e (tok (arguments p d))) ->
  (forall p d v, ret p (F p) (cuts p d) v ->
    exists fv xv,
      ret p _ (functions p d) fv /\ ret p _ (arguments p d) xv) ->
  (forall p d Y kind o sender rd,
    cut_receive p (F p) (cuts p d) Y kind o sender rd ->
    cut_receive p _ (functions p d) Y kind o sender rd \/
    cut_receive p _ (arguments p d) Y kind o sender rd) ->
  realized F active root cuts (Parallel function_tree argument_tree).
Proof.
  intros Functions Arguments TokenSplit ReturnSplit FocusSplit. constructor.
  - intros p d e Token ev Event. apply TokenSplit in Token.
    destruct Token as [Token|Token].
    + eapply (payload_layout_child root AppFunction function_tree
        (Parallel function_tree argument_tree)); [intros; now apply
          SiteFunction|].
      exact (realized_tokens _ _ _ _ _ Functions p d e Token ev Event).
    + eapply (payload_layout_child root AppArgument argument_tree
        (Parallel function_tree argument_tree)); [intros; now apply
          SiteArgument|].
      exact (realized_tokens _ _ _ _ _ Arguments p d e Token ev Event).
  - intros p d B C focus Y kind o sender rd Eq Focus.
    destruct (FocusSplit p d Y kind o sender rd
      (ex_intro _ B (ex_intro _ C (ex_intro _ focus (conj Eq Focus)))))
      as [Function|Argument].
    + eapply (layout_site_child root AppFunction function_tree
        (Parallel function_tree argument_tree)); [intros; now apply
          SiteFunction|].
      exact (realized_receive_site _ _ _ _ _ Functions p d Y kind o sender rd
        Function).
    + eapply (layout_site_child root AppArgument argument_tree
        (Parallel function_tree argument_tree)); [intros; now apply
          SiteArgument|].
      exact (realized_receive_site _ _ _ _ _ Arguments p d Y kind o sender rd
        Argument).
  - intros p d v Done path kind sender receiver At Peer.
    destruct (ReturnSplit p d v Done) as (fv & xv & FDone & XDone).
    inversion At; subst.
    + match goal with Hs : site function_tree _ _ _ _ |- _ =>
        destruct (realized_returned _ _ _ _ _ Functions p d fv FDone
          _ _ _ _ Hs Peer) as (e & Member & Action)
      end.
      exists e. split.
      * apply TokenSplit. now left.
      * unfold child in Action. rewrite <- app_assoc in Action. exact Action.
    + match goal with Hs : site argument_tree _ _ _ _ |- _ =>
        destruct (realized_returned _ _ _ _ _ Arguments p d xv XDone
          _ _ _ _ Hs Peer) as (e & Member & Action)
      end.
      exists e. split.
      * apply TokenSplit. now right.
      * unfold child in Action. rewrite <- app_assoc in Action. exact Action.
Qed.

Theorem realized_sequence F X active entered root
    (cuts : family cut F active)
    (prefixes : family cut X active) (bodies : family cut F entered)
    prefix_tree body_tree :
  realized _ active (child root BindPrefix) prefixes prefix_tree ->
  realized _ entered (child root BindBody) bodies body_tree ->
  (forall p d e,
    In e (tok (cuts p d)) <->
    In e (tok (prefixes p d)) \/
    exists body_member, In e (tok (bodies p body_member))) ->
  (forall p d v, ret p (F p) (cuts p d) v ->
    exists x body_member y,
      ret p _ (prefixes p d) x /\ ret p _ (bodies p body_member) y) ->
  (forall p d Y kind o sender rd,
    cut_receive p (F p) (cuts p d) Y kind o sender rd ->
    cut_receive p _ (prefixes p d) Y kind o sender rd \/
    exists body_member, cut_receive p _ (bodies p body_member) Y kind o sender
      rd) ->
  realized F active root cuts (Sequence prefix_tree body_tree).
Proof.
  intros Prefixes Bodies TokenSplit ReturnSplit FocusSplit. constructor.
  - intros p d e Token ev Event. apply TokenSplit in Token.
    destruct Token as [Token|[body_member Token]].
    + eapply (payload_layout_child root BindPrefix prefix_tree
        (Sequence prefix_tree body_tree)); [intros; now apply SitePrefix|].
      exact (realized_tokens _ _ _ _ _ Prefixes p d e Token ev Event).
    + eapply (payload_layout_child root BindBody body_tree
        (Sequence prefix_tree body_tree)); [intros; now apply SiteBody|].
      exact (realized_tokens _ _ _ _ _ Bodies p body_member e Token ev Event).
  - intros p d B C focus Y kind o sender rd Eq Focus.
    destruct (FocusSplit p d Y kind o sender rd
      (ex_intro _ B (ex_intro _ C (ex_intro _ focus (conj Eq Focus)))))
      as [Prefix|[body_member Body]].
    + eapply (layout_site_child root BindPrefix prefix_tree
        (Sequence prefix_tree body_tree)); [intros; now apply SitePrefix|].
      exact (realized_receive_site _ _ _ _ _ Prefixes p d Y kind o sender rd
        Prefix).
    + eapply (layout_site_child root BindBody body_tree
        (Sequence prefix_tree body_tree)); [intros; now apply SiteBody|].
      exact (realized_receive_site _ _ _ _ _ Bodies p body_member Y kind o
        sender rd Body).
  - intros p d v Done path kind sender receiver At Peer.
    destruct (ReturnSplit p d v Done) as (x & body_member & y & PDone & BDone).
    inversion At; subst.
    + match goal with Hs : site prefix_tree _ _ _ _ |- _ =>
        destruct (realized_returned _ _ _ _ _ Prefixes p d x PDone
          _ _ _ _ Hs Peer) as (e & Member & Action)
      end.
      exists e. split; [apply TokenSplit; now left|].
      unfold child in Action. rewrite <- app_assoc in Action. exact Action.
    + match goal with Hs : site body_tree _ _ _ _ |- _ =>
        destruct (realized_returned _ _ _ _ _ Bodies p body_member y BDone
          _ _ _ _ Hs Peer) as (e & Member & Action)
      end.
      exists e. split; [apply TokenSplit; right; now exists body_member|].
      unfold child in Action. rewrite <- app_assoc in Action. exact Action.
Qed.

Definition choice_root_event root owner ev : Prop :=
  match ev with
  | Produced kind o sender receiver _ | Consumed kind o sender receiver _ =>
      kind = ChoiceDelivery /\ o = root /\ sender = owner /\ owner <> receiver
  end.

Lemma choice_root_layout root owner tree ev :
  choice_root_event root owner ev ->
  payload_in_layout root (Choice owner tree) ev.
Proof.
  destruct ev; intros (-> & -> & -> & Ne); cbn.
  all: exists []; rewrite app_nil_r; split; [reflexivity|now apply SiteChoice].
Qed.

(* The header witnesses are actual entries, not a claim that an arbitrary
   received value equals the owner value. Coherent branch selection must be
   established before the body realization can be supplied. *)
Theorem realized_choice F active entered root owner
    (cuts : family cut F active) (bodies : family cut F entered) body_tree :
  realized _ entered (child root ChoiceBody) bodies body_tree ->
  (forall p d e, In e (tok (cuts p d)) ->
    (forall ev, In ev (batch p e) -> choice_root_event root owner ev) \/
    exists body_member, In e (tok (bodies p body_member))) ->
  (forall p d body_member e,
    In e (tok (bodies p body_member)) -> In e (tok (cuts p d))) ->
  (forall p d v, ret p (F p) (cuts p d) v ->
    exists body_member y,
      ret p _ (bodies p body_member) y /\
      forall peer, owner <> peer -> (p = owner \/ p = peer) ->
        exists e, In e (tok (cuts p d)) /\
          action_at ChoiceDelivery root owner peer p (act p e)) ->
  (forall p d Y kind o sender rd,
    cut_receive p (F p) (cuts p d) Y kind o sender rd ->
    (kind = ChoiceDelivery /\ o = root /\ sender = owner /\ owner <> p) \/
    exists body_member, cut_receive p _ (bodies p body_member) Y kind o sender
      rd) ->
  realized F active root cuts (Choice owner body_tree).
Proof.
  intros Bodies TokenSplit BodyTokens ReturnSplit FocusSplit. constructor.
  - intros p d e Token ev Event.
    destruct (TokenSplit p d e Token) as [Header|[body_member TokenBody]].
    + apply choice_root_layout. now apply Header.
    + eapply (payload_layout_child root ChoiceBody body_tree
        (Choice owner body_tree)); [intros; now apply SiteChosen|].
      exact (realized_tokens _ _ _ _ _ Bodies p body_member e TokenBody ev
        Event).
  - intros p d B C focus Y kind o sender rd Eq Focus.
    destruct (FocusSplit p d Y kind o sender rd
      (ex_intro _ B (ex_intro _ C (ex_intro _ focus (conj Eq Focus)))))
      as [(-> & -> & -> & Ne)|[body_member Body]].
    + exists []. rewrite app_nil_r. split; [reflexivity|now apply SiteChoice].
    + eapply (layout_site_child root ChoiceBody body_tree
        (Choice owner body_tree)); [intros; now apply SiteChosen|].
      exact (realized_receive_site _ _ _ _ _ Bodies p body_member Y kind o
        sender rd Body).
  - intros p d v Done path kind sender receiver At Peer.
    destruct (ReturnSplit p d v Done) as (body_member & y & BDone & Header).
    inversion At; subst.
    + rewrite app_nil_r. apply Header; assumption.
    + match goal with Hs : site body_tree _ _ _ _ |- _ =>
        destruct (realized_returned _ _ _ _ _ Bodies p body_member y BDone
          _ _ _ _ Hs Peer) as (e & Member & Action)
      end.
      exists e. split; [eapply BodyTokens; eassumption|].
      unfold child in Action. rewrite <- app_assoc in Action. exact Action.
Qed.

Variable past : list payload_event.
Variable ar : actor_archive model stores input R A c.

Theorem realized_past_sites tc s tn n gs F active root
    (cuts : family cut F active) tree :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  owns_region model stores input R A c ar F active root cuts ->
  realized F active root cuts tree ->
  forall ev, In ev past -> path_prefix root (payload_path ev) ->
    payload_in_layout root tree ev.
Proof.
  intros Hist [_ [Present Own]] Layout ev Seen Below.
  destruct (observed_past_event_archived model stores input R A c
    _ _ _ _ _ _ _ Hist ev Seen) as (p & path & e & Archived & InBatch).
  pose proof (proj1 (observed_archives_valid model stores input R A c
    _ _ _ _ _ _ _ Hist p path e Archived)) as Location.
  assert (Region : in_region model stores input R A c ar p root e).
  { split.
    - now rewrite <- Location.
    - rewrite <- (entry_batch_path p e ev InBatch). exact Below. }
  pose proof (Present p e Region) as Member.
  exact (realized_tokens _ _ _ _ _ Layout p Member e
    (proj2 (Own p Member e) Region) ev InBatch).
Qed.

Theorem realized_returned_archive F active root (cuts : family cut F active)
  tree :
  owns_region model stores input R A c ar F active root cuts ->
  realized F active root cuts tree ->
  forall p d v, ret p (F p) (cuts p d) v ->
  forall path kind sender receiver,
    site tree path kind sender receiver -> (p = sender \/ p = receiver) ->
    exists e, In (path_of p e,e) (ar p) /\
      In e (tok (cuts p d)) /\
      action_at kind (root ++ path) sender receiver p (act p e).
Proof.
  intros [_ [_ Own]] Layout p d v Done path kind sender receiver At Peer.
  destruct (realized_returned _ _ _ _ _ Layout p d v Done
    path kind sender receiver At Peer) as (e & Token & Action).
  exists e. split; [|now split].
  exact (proj1 (proj1 (Own p d e) Token)).
Qed.

(* Coverage is in the SAME actual source trace, not a separately chosen
   completed_subtree history. This is the interface needed by a barrier proof.
   *)
Theorem realized_returned_trace tc s tn n gs F active root
    (cuts : family cut F active) tree :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  owns_region model stores input R A c ar F active root cuts ->
  realized F active root cuts tree ->
  forall p d v, ret p (F p) (cuts p d) v ->
  forall path kind sender receiver,
    site tree path kind sender receiver -> (p = sender \/ p = receiver) ->
    exists e suffix,
      In e (tok (cuts p d)) /\
      tc = entry_tc model stores input R A c p e ++ [act p e] ++ suffix /\
      action_at kind (root ++ path) sender receiver p (act p e).
Proof.
  intros Hist Own Layout p d v Done path kind sender receiver At Peer.
  destruct (realized_returned_archive _ _ _ _ _ Own Layout
    p d v Done path kind sender receiver At Peer) as (e & Seen & Token &
      Action).
  destruct (observed_archives_trace model stores input R A c
    _ _ _ _ _ _ _ Hist p _ e Seen) as [suffix Trace].
  exists e, suffix. now repeat split.
Qed.

Theorem realized_compatible F active root (cuts : family cut F active) tree :
  realized F active root cuts tree ->
  forall o kind sender receiver b other_kind other_sender other_receiver,
    layout_site root tree o kind sender receiver ->
    layout_site root tree b other_kind other_sender other_receiver ->
    exists left_path right_path,
      o = root ++ left_path /\ b = root ++ right_path /\
      compatible left_path right_path.
Proof.
  intros _ o kind sender receiver b other_kind other_sender other_receiver
    (left_path & Left & One) (right_path & Right & Two).
  exists left_path, right_path. repeat split; try assumption.
  eapply shared_node_paths; eassumption.
Qed.
End Realized.
