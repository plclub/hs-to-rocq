From Stdlib Require Import Lists.List.
From ParkourTheories Require Import
  Projection.CommunicationTree.ObservationCoverage
  Projection.CommunicationTree.PredecessorCoverage
  Projection.RoleLogs.Families.RegionOwnership
  Projection.RoleLogs.Families.BranchPartition
  Projection.RoleLogs.Families.ChoicePartition Projection.Payloads.OwnedPackets
  Choreography.Results.CutFamilySoundness Projection.Matching.ReturnedValues
  Choreography.Results.OperandObservations
  Choreography.Histories.SyntaxDecomposition
  Choreography.Results.FiniteSelection Choreography.WellFormedness
  Projection.Matching.ObservationArchive Choreography.Occurrences
  Choreography.RoleSteps Choreography.Execution Semantics.LocalEffects
  Choreography.Histories.CursorHistories
  Projection.CommunicationTree.CompletedSubtrees
  Choreography.Histories.TransitionArchive.
Require Import Parkour.Symbol Parkour.Codec Choreography.Choreo2
  Control.Monad.Tree.
From ParkourTheories.Projection.CommunicationTree Require Import AtomicNodes
  ForkAndBind ChoiceNodes.
Import ListNotations.

(* Recursion constructs both coverage and predecessor closure on the SAME tree.
   Concrete decomposition supplies the children and a same-cut assembler.
   Bind's recursive WF premise uses the actual completed prefix family.
   No subtree coverage hypothesis appears in the theorem's contract. *)
Section Construction.
Context {M E Store Input}
  (model : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input0 : Input) (R : list Symbol)
  (A0 : Symbol -> Type) (c0 : forall p, Choreo M p (A0 p)).
Variables (tc : list (@source_action E ((Symbol -> Store) * Input)))
  (s : @Choreography.Execution.configuration M E ((Symbol -> Store) * Input) A0)
  (tn : list (@Endpoints.action E ((Symbol -> Store) * Input)))
  (n : @Network.Execution.configuration M E ((Symbol -> Store) * Input))
  (gs : list MessageRepresentation.message) (past : list payload_event)
  (ar : actor_archive model stores input0 R A0 c0).
Hypothesis Archives :
  observed_archives model stores input0 R A0 c0 tc s tn n gs past ar.
Local Notation Cut := (logged_cut model stores input0 R A0 c0).
Local Notation Node := (at_node model stores input0 R A0 c0 past).
Local Notation Done := (finished model stores input0 R A0 c0).
Local Notation Own := (owns_region model stores input0 R A0 c0 ar).
Local Notation Tracked := (tracked_realization model stores input0 R A0 c0).
Local Notation Laws :=
  (actual_replay_laws model stores input0 R A0 c0 _ _ _ _ _ _ _ Archives).

Theorem structural_tracked_layout S F code Q :
  structural R M S F code Q ->
  forall active (inc : includes (fun p => In p active) S) root
    (cuts : family Cut F active),
  (forall p (u v : S p), u = v) ->
  NoDup active -> Own F active root cuts ->
  family_at Cut Node S F code active inc root cuts ->
  exists tree, Tracked F active root cuts tree.
Proof.
  intro WF.
  induction WF as
    [S F input code Shape
    |S X owner f code Owner Shape
    |S X sender receiver sh rd input code Sender Receiver Codec Shape
    |S X owner F sh rd input k K code Owner Codec Branch IH Shape
    |S X F f x P Q code WFF IHF WFX IHX Shape
    |S X F prefix k P K code WFP IHP Body IHBody Shape];
    intros active inc root cuts PI ND Good At.
  - exists Leaf.
    eapply (tracked_atomic_node model stores input0 R A0 c0
      _ _ code active inc root cuts past Leaf At).
    + intros p d. left. eexists. apply Shape.
    + intros p d. rewrite Shape. reflexivity.
  - exists Leaf.
    eapply (tracked_atomic_node model stores input0 R A0 c0
      _ _ code active inc root cuts past Leaf At).
    + intros p d. right. rewrite Shape. apply AtomicLocal.
    + intros p d. rewrite Shape. reflexivity.
  - exists (Exchange sender receiver).
    eapply (tracked_atomic_node model stores input0 R A0 c0
      _ _ code active inc root cuts past (Exchange sender receiver) At).
    + intros p d. right. rewrite Shape. apply AtomicComm.
    + intros p d. rewrite Shape. reflexivity.
  - assert (Head : family_at Cut Node S F
      (fun p d => Perf (@Cond M p X owner (F p) (sh p d) (rd p d)
        (known owner) MkSSymbol (input p d) (k p d))) active inc root cuts).
    { intros p d. rewrite <- Shape. apply At. }
    destruct (coherent_choice_layout model stores input0 R A0 c0
      tc s tn n gs past ar S X owner F sh rd input k
      active inc root cuts Archives ND Good Head Codec)
      as [Dormant|(entered & inside & chosen & bodies & NE & GB & BodiesAt &
        Assemble)].
    + exists (Choice owner Leaf). exact Dormant.
    +
      assert (BodyAt : family_at Cut Node S F
        (fun p d => k p d chosen) entered
        (fun p d => inc p (inside p d)) (child root ChoiceBody) bodies).
      { exact BodiesAt. }
      destruct (IH chosen entered (fun p d => inc p (inside p d))
        (child root ChoiceBody) bodies PI NE GB BodyAt) as [bt Tree].
      exists (Choice owner bt). now apply Assemble.
  - assert (Head : family_at Cut Node S F
      (fun p d => App (f p d) (x p d)) active inc root cuts).
    { intros p d. rewrite <- Shape. apply At. }
    destruct (app_layout_children model stores input0 R A0 c0 past ar
      S X F f x active inc root cuts Good Head)
      as (fs & xs & GF & GX & NF & NX & Assemble).
    destruct (IHF active inc (child root AppFunction) fs PI ND GF NF) as [ft
      FT].
    destruct (IHX active inc (child root AppArgument) xs PI ND GX NX) as [xt
      XT].
    exists (Parallel ft xt). now apply Assemble.
  - assert (Head : family_at Cut Node S F
      (fun p d => Bind (prefix p d) (k p d)) active inc root cuts).
    { intros p d. rewrite <- Shape. apply At. }
    destruct (bind_layout_children model stores input0 R A0 c0 past ar
      S X F prefix k active inc root cuts Good Head)
      as (entered & inside & prefixes & vals & bodies &
        NE & GP & NP & RP & GB & NB & Assemble).
    assert (Values : P (fun p => In p entered) vals).
    { exact (structural_cut_family_results Cut Node Done past Own Laws
        R S X prefix P WFP active entered inc (child root BindPrefix)
        prefixes vals inside PI ND NE GP NP RP). }
    destruct (IHP active inc (child root BindPrefix) prefixes PI ND GP NP)
      as [pt PT].
    destruct (IHBody (fun p => In p entered) vals
      (fun p d => inc p (inside p d)) Values entered (fun p d => d)
      (child root BindBody) bodies (roster_member_unique entered NE) NE GB NB)
      as [bt BT].
    exists (Sequence pt bt). now apply Assemble.
Qed.
End Construction.

Theorem structural_root_layout {M E Store Input}
    (model : local_model M E Symbol (Store * Input))
    stores input R A (c : forall p, Choreo M p (A p))
    tc s tn n gs past ar (cuts : family (logged_cut model stores input R A c) A
      R) :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  well_formed R M A c ->
  owns_region model stores input R A c ar A R [] cuts ->
  (forall p d, at_node model stores input R A c past p (A p) [] (c p) (cuts p
    d)) ->
  exists tree, tracked_realization model stores input R A c A R [] cuts tree.
Proof.
  intros Hist [ND [Q WF]] Own Nodes.
  eapply (structural_tracked_layout model stores input R A c
    tc s tn n gs past ar Hist _ _ _ _ WF R (fun p d => d) [] cuts).
  - exact (roster_member_unique R ND).
  - exact ND.
  - exact Own.
  - exact Nodes.
Qed.
