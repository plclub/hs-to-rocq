From Stdlib Require Import Lists.List.
Require Import Choreography.Choreo2 Control.Monad.Tree Parkour.Codec
  Parkour.Symbol.
From ParkourTheories Require Import Semantics.LocalEffects
  Choreography.RoleSteps Choreography.Histories.CursorHistories
  Choreography.Histories.TransitionArchive Projection.Matching.PrefixRelation
  Projection.Matching.PayloadHistory Semantics.SharedState
  Choreography.Results.OperandObservations
  Projection.Matching.ObservationArchive Choreography.Histories.LabelledSteps
  Projection.RoleLogs.ArchiveOrder Choreography.Histories.SyntaxDecomposition.
Import ListNotations.

Polymorphic Lemma token_in_app_left {T} (xs ys : list T) x :
  In x xs -> In x (xs ++ ys).
Proof.
  revert xs. fix IH 1. intros [|a xs] Member; cbn in *; [contradiction|].
  destruct Member as [Eq|Tail]; [now left|right; now apply IH].
Qed.

Section MicroViews.
Context {M E : Type -> Type} {S : Type}
  (model : local_model M E Symbol S) (p : Symbol) (L : Type).
Variable leaf : forall B, @cursor M E p B -> L -> @cursor M E p B -> Prop.

Definition labelled_atom_shape {B} (t : @cursor M E p B) token
    (u : @cursor M E p B) : Prop :=
  match t in cursor _ C return cursor p C -> Prop with
  | Code o c => fun u =>
      (token = None /\ primitive_silent model _ (Code o c) u) \/
      exists e, token = Some e /\ leaf _ (Code o c) e u
  | Returned x => fun u =>
      (token = None /\ primitive_silent model _ (Returned x) u) \/
      exists e, token = Some e /\ leaf _ (Returned x) e u
  | _ => fun _ => True
  end u.

Lemma labelled_atom_shape_correct B t token u :
  labelled_step model p L leaf B t token u -> labelled_atom_shape t token u.
Proof.
  destruct 1; cbn [labelled_atom_shape]; try exact I.
  - pose proof H as Prim. destruct H; cbn [labelled_atom_shape]; try exact I.
    all: left; split; [reflexivity|exact Prim].
  - destruct t; cbn [labelled_atom_shape]; try exact I.
    + right. eexists. split; [reflexivity|exact H].
    + right. eexists. split; [reflexivity|exact H].
Qed.
End MicroViews.

Section AtomicViews.
Context {M E : Type -> Type} {S : Type}
  (model : local_model M E Symbol S) (R : list Symbol) (p : Symbol).
Variable past : list payload_event.

Definition silent_atom_shape {B} (t : @cursor M E p B) (u : @cursor M E p B) :
  Prop :=
  match t in cursor _ C return @cursor M E p C -> Prop with
  | Code o c =>
      match c in Tree _ C return @cursor M E p C -> Prop with
      | Pure x => fun u => u = Returned x
      | Perf sig =>
          match sig in ChoreoSig _ _ C return @cursor M E p C -> Prop with
          | @Comm _ _ X l r sh rd kl kr sl input sr => fun u =>
              exists output, u = Returned output /\
                comm_observed past o rd p input output
          | _ => fun _ => True
          end
      | _ => fun _ => True
      end
  | _ => fun _ => True
  end u.

Lemma silent_atom_shape_correct B t u :
  primitive_silent model B t u -> silent_atom_shape t u.
Proof.
  destruct 1; cbn [silent_atom_shape]; try exact I; try reflexivity.
  - eexists. split; [reflexivity|]. right. split; [exact hne|].
    intros Same. contradiction.
  - eexists. split; [reflexivity|]. left. exists eq_refl.
    intro Same. destruct Same. reflexivity.
Qed.

Definition observed_atom_shape {B} (t : @cursor M E p B) (u : @cursor M E p B)
    (batch : list payload_event) : Prop :=
  match t in cursor _ C return @cursor M E p C -> Prop with
  | Code o c =>
      match c in Tree _ C return @cursor M E p C -> Prop with
      | Perf sig =>
          match sig in ChoreoSig _ _ C return @cursor M E p C -> Prop with
          | @Comm _ _ X l r sh rd kl kr sl input sr => fun u =>
              exists output, u = Returned output /\
                comm_observed past o rd p input output /\
                forall kind site sender recipient operand,
                  In (Produced kind site sender recipient operand) batch ->
                  site = o /\ sender = p /\
                  sender_operand
                    (Perf (@Comm M p X l r sh rd kl kr sl input sr)) = Some
                      operand
          | _ => fun _ => True
          end
      | Pure _ => fun _ => False
      | _ => fun _ => True
      end
  | Returned _ => fun _ => False
  | _ => fun _ => True
  end u.

Lemma observed_atom_shape_correct B t s q a u s' q' na gs gs' batch :
  observed model R B t s q a u s' q' na gs gs' batch ->
  (forall kind site sender recipient wire,
    In (Consumed kind site sender recipient wire) batch ->
    past_receive past kind site sender recipient wire) ->
  observed_atom_shape t u batch.
Proof.
  induction 1; intro Wires; cbn [observed_atom_shape]; try exact I.
  - eexists. split; [reflexivity|]. split.
    + right. split; [congruence|]. intros Same. contradiction.
    + intros kind site sender recipient operand [Eq|No]; [|contradiction].
      inversion Eq; subst. split; [reflexivity|]. split; [reflexivity|].
      apply comm_sender_operand.
  - eexists. split; [reflexivity|]. split.
    + right. split; [exact h|]. intro Same. exists w. split.
      * apply Wires. now left.
      * destruct H. exact H0.
    + intros kind site sender recipient operand [Eq|No];
      [discriminate|contradiction].
  - specialize (IHobserved Wires).
    destruct H; cbn [observed_atom_shape] in *; try exact I; contradiction.
Qed.
End AtomicViews.

Section StampedAtoms.
Context {M E Store Input} (model : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input : Input) (R : list Symbol) (A : Symbol ->
    Type)
  (c : forall p, Choreo M p (A p)).
Local Notation sm := (shared_model model).
Local Notation entry := (observed_entry model stores input R A c).
Local Notation stamp := (stamped model stores input R A c).
Local Notation log := (actor_log model stores input R A c).
Local Notation batch := (entry_batch model stores input R A c).
Variable past : list payload_event.

Definition token_wires p (e : entry p) : Prop :=
  forall kind site sender recipient wire,
    In (Consumed kind site sender recipient wire) (batch p e) ->
    past_receive past kind site sender recipient wire.

Theorem comm_log_shape p X l r o sh rd kl kr sl input_value sr tr t :
  log p _ (Code o (Perf (@Comm M p X l r sh rd kl kr sl input_value sr))) tr t
    ->
  (forall e, In e tr -> token_wires p e) ->
  (tr = [] /\ t = Code o (Perf (@Comm M p X l r sh rd kl kr sl input_value sr)))
    \/
  exists output, t = Returned output /\
    comm_observed past o rd p input_value output /\
    forall e, In e tr ->
      forall kind site sender recipient operand,
        In (Produced kind site sender recipient operand) (batch p e) ->
        site = o /\ sender = p /\
        sender_operand
          (Perf (@Comm M p X l r sh rd kl kr sl input_value sr)) = Some operand.
Proof.
  intro Run. induction Run; intro Wires.
  - left. split; reflexivity.
  - assert (Earlier : forall e, In e tr -> token_wires p e).
    { intros e Member. apply Wires. destruct token; cbn [snoc_token].
      - now apply token_in_app_left.
      - exact Member. }
    destruct (IHRun Earlier) as [[Empty Initial]|(output & End & Value &
      Original)].
    + subst tr t.
      pose proof (labelled_atom_shape_correct sm p (entry p) (stamp p) _ _ _ _
        H)
        as View.
      cbn [labelled_atom_shape] in View.
      destruct View as [[Tok Silent]|(e & Tok & Leaf)].
      * subst token.
        destruct (silent_atom_shape_correct sm p past _ _ _ Silent)
          as (output & End & Value).
        right. exists output. split; [exact End|]. split; [exact Value|].
        intros e Member. contradiction.
      * subst token.
        destruct Leaf as [Prim Obs].
        destruct (observed_atom_shape_correct sm R p past _ _ _ _ _ _ _ _ _ _ _
          _ Obs)
          as (output & End & Value & Original).
        -- apply Wires. cbn [snoc_token]. now left.
        -- right. exists output. split; [exact End|]. split; [exact Value|].
           intros item Member. cbn [snoc_token] in Member.
           destruct Member as [Eq|No]; [subst item; exact
             Original|contradiction].
    + subst t.
      pose proof (labelled_atom_shape_correct sm p (entry p) (stamp p) _ _ _ _
        H)
        as View.
      cbn [labelled_atom_shape] in View.
      destruct View as [[Tok Silent]|(e & Tok & [Prim Obs])].
      * pose proof (silent_shape_correct sm p _ _ _
          (primitive_is_silent sm _ _ _ _ Silent)) as Impossible.
        contradiction.
      * pose proof (primitive_shape_correct sm R p _ _ _ _ _ _ _ _ Prim) as
        Impossible.
        contradiction.
Qed.

Lemma returned_cursor_eq p B (x y : B) :
  @Returned M E p B x = Returned y -> x = y.
Proof.
  intro Eq. change (@cut_returned M E p B (Returned y) x).
  rewrite <- Eq. reflexivity.
Qed.

Theorem comm_log_observed p X l r o sh rd kl kr sl input_value sr tr output :
  log p _ (Code o (Perf (@Comm M p X l r sh rd kl kr sl input_value sr))) tr
    (Returned output) ->
  (forall e, In e tr -> token_wires p e) ->
  comm_observed past o rd p input_value output.
Proof.
  intros Run Wires.
  destruct (comm_log_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ Run Wires)
    as [[Empty Eq]|(v & Eq & Value & Original)].
  - discriminate.
  - apply returned_cursor_eq in Eq. now subst v.
Qed.

Theorem comm_log_original_tokens p X l r o sh rd kl kr sl input_value sr tr t :
  log p _ (Code o (Perf (@Comm M p X l r sh rd kl kr sl input_value sr))) tr t
    ->
  (forall e, In e tr -> token_wires p e) ->
  forall e, In e tr ->
    forall kind site sender recipient operand,
      In (Produced kind site sender recipient operand) (batch p e) ->
      site = o /\ sender = p /\
      sender_operand
        (Perf (@Comm M p X l r sh rd kl kr sl input_value sr)) = Some operand.
Proof.
  intros Run Wires.
  destruct (comm_log_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ Run Wires)
    as [[Empty Eq]|(v & Eq & Value & Original)].
  - subst tr. intros e Member. contradiction.
  - exact Original.
Qed.

Theorem archive_token_wires tc s tn n gs ar p root tr :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  (forall e, In e tr -> In ([],e)
    (subarchive model stores input R A c p root (ar p))) ->
  forall e, In e tr -> token_wires p e.
Proof.
  intros Archives Sound e Member kind site sender recipient wire Consumed.
  exact (observed_subarchive_receive model stores input R A c
    tc s tn n gs past ar p root [] e kind site sender recipient wire
    Archives (Sound e Member) Consumed).
Qed.

(* Soundness names the very same entry, not merely its erased source label.
   Its observed receive supplies the decoder proof; its archived batch supplies
   the matching consumed wire in this global past. *)
Theorem comm_log_observed_in_archive tc s tn n gs ar
    p X l r o sh rd kl kr sl input_value sr tr output :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  log p _ (Code o (Perf (@Comm M p X l r sh rd kl kr sl input_value sr))) tr
    (Returned output) ->
  (forall e, In e tr -> In ([],e)
    (subarchive model stores input R A c p o (ar p))) ->
  comm_observed past o rd p input_value output.
Proof.
  intros Archives Run Sound.
  eapply comm_log_observed; [exact Run|].
  eapply archive_token_wires; eassumption.
Qed.

(* Completeness is the reverse direction: a production at this occurrence
   must belong to this log. Without it a second, unrelated history at the same
   source occurrence could be substituted for the original operand. *)
Theorem comm_log_recorded_sender tc s tn n gs ar
    p X l r o sh rd kl kr sl input_value sr tr t kind recipient :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  log p _ (Code o (Perf (@Comm M p X l r sh rd kl kr sl input_value sr))) tr t
    ->
  (forall e, In e tr -> In ([],e)
    (subarchive model stores input R A c p o (ar p))) ->
  (forall e, In ([],e)
    (subarchive model stores input R A c p o (ar p)) -> In e tr) ->
  recorded_sender past kind o recipient
    (Perf (@Comm M p X l r sh rd kl kr sl input_value sr)).
Proof.
  intros Archives Run Sound Complete operand Produced.
  destruct (observed_past_event_archived model stores input R A c
    tc s tn n gs past ar Archives _ Produced)
    as (who & path & e & Member & Batch).
  destruct (entry_produced_site model stores input R A c who e _ _ _ _ _ Batch)
    as [Actor Site]. subst who.
  destruct (observed_archives_valid model stores input R A c
    tc s tn n gs past ar Archives p path e Member) as [Location _].
  rewrite Site in Location. subst path.
  assert (Seen : In ([],e) (subarchive model stores input R A c p o (ar p))).
  { apply subarchive_complete. now rewrite app_nil_r. }
  pose proof (comm_log_original_tokens _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Run (archive_token_wires tc s tn n gs ar p o tr Archives Sound)
    e (Complete e Seen) kind o p recipient operand Batch) as Original.
  exact (proj2 (proj2 Original)).
Qed.

Theorem comm_log_original_operand tc s tn n gs ar
    p X l r o sh rd kl kr sl input_value sr tr t kind recipient sent :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  log p _ (Code o (Perf (@Comm M p X l r sh rd kl kr sl input_value sr))) tr t
    ->
  (forall e, In e tr <-> In ([],e)
    (subarchive model stores input R A c p o (ar p))) ->
  sender_operand
    (Perf (@Comm M p X l r sh rd kl kr sl input_value sr)) = Some sent ->
  original_operand past kind o p recipient sent.
Proof.
  intros Archives Run Exact Sender b Member.
  pose proof (comm_log_recorded_sender tc s tn n gs ar
    p X l r o sh rd kl kr sl input_value sr tr t kind recipient Archives Run
    (fun e H => proj1 (Exact e) H) (fun e H => proj2 (Exact e) H) b Member) as
      Orig.
  rewrite Sender in Orig. now injection Orig.
Qed.

Theorem pure_log_shape p B o (x : B) tr t :
  log p B (Code o (Pure x)) tr t ->
  tr = [] /\ (t = Code o (Pure x) \/ t = Returned x).
Proof.
  intro Run. induction Run.
  - split; [reflexivity|now left].
  - destruct IHRun as [Empty [Initial|End]]; subst tr t;
      pose proof (labelled_atom_shape_correct sm p (entry p) (stamp p) _ _ _ _
        H)
        as View;
      cbn [labelled_atom_shape] in View;
      destruct View as [[Tok Silent]|(e & Tok & [Prim Obs])].
    + subst token. split; [reflexivity|]. right.
      exact (silent_atom_shape_correct sm p past _ _ _ Silent).
    + pose proof (primitive_shape_correct sm R p _ _ _ _ _ _ _ _ Prim) as
      Impossible.
      contradiction.
    + pose proof (silent_shape_correct sm p _ _ _
        (primitive_is_silent sm _ _ _ _ Silent)) as Impossible.
      contradiction.
    + pose proof (primitive_shape_correct sm R p _ _ _ _ _ _ _ _ Prim) as
      Impossible.
      contradiction.
Qed.

Theorem pure_log_returned p B o (x v : B) tr :
  log p B (Code o (Pure x)) tr (Returned v) -> v = x.
Proof.
  intro Run. destruct (pure_log_shape _ _ _ _ _ _ Run) as [Empty [Initial|End]].
  - discriminate.
  - now apply returned_cursor_eq in End.
Qed.

End StampedAtoms.
