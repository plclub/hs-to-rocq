From Stdlib Require Import Lists.List.
From ParkourTheories Require Import
  Projection.CommunicationTree.ObservationCoverage
  Projection.CommunicationTree.CompletedSubtrees Choreography.Occurrences
  Choreography.PendingDeliveries Choreography.Precedence
  Choreography.Histories.RoleChronology Choreography.Histories.CursorHistories
  Projection.Matching.ObservationArchive Projection.RoleLogs.ArchiveOrder
  Choreography.Histories.SyntaxDecomposition
  Choreography.Results.CutFamilySoundness
  Choreography.Results.OperandObservations Semantics.SharedState
  Projection.RoleLogs.Families.RegionOwnership
  Projection.Matching.ReceiveConditions.
Require Import Parkour.Symbol Choreography.Choreo2.
Import ListNotations.

(* Marks below are positions actually reached by one role, not all positions
   of a selected tree. The constructors transfer coverage from the very same
   child layouts that supply the selected parent tree. *)
Definition predecessor_coverage root tree p
    (reached : occurrence -> Prop)
    (covered : delivery_kind -> occurrence -> Symbol -> Symbol -> Prop) : Prop
      :=
  (forall later, reached later -> path_prefix root later) /\
  forall later, reached later ->
  forall path kind sender receiver,
    site tree path kind sender receiver ->
    (p = sender \/ p = receiver) ->
    source_before (root ++ path) later ->
    covered kind (root ++ path) sender receiver.

Lemma child_predecessor root edge path later :
  source_before (root ++ edge :: path) later ->
  source_before (child root edge ++ path) later.
Proof. unfold child; now rewrite <- app_assoc. Qed.

Lemma child_path root edge path :
  root ++ edge :: path = child root edge ++ path.
Proof. unfold child; now rewrite <- app_assoc. Qed.

Lemma branch_predecessor root e f path later :
  path_prefix (child root f) later ->
  source_before (root ++ e :: path) later ->
  e = f \/ (e = BindPrefix /\ f = BindBody).
Proof.
  intros [suffix ->] Before. unfold child in Before.
  rewrite <- app_assoc in Before. apply before_cancel in Before.
  inversion Before; subst; auto.
Qed.

Lemma no_predecessor_of_root root path :
  ~ source_before (root ++ path) root.
Proof.
  intro Before.
  assert (B : source_before (root ++ path) (root ++ []))
    by now rewrite app_nil_r.
  apply before_cancel in B. inversion B.
Qed.

Lemma predecessor_coverage_leaf root p reached covered :
  (forall o, reached o -> path_prefix root o) ->
  predecessor_coverage root Leaf p reached covered.
Proof. intro Bounds. split; [exact Bounds|].
intros o Mark path k s r At; inversion At. Qed.

Lemma predecessor_coverage_exchange root p s r reached covered :
  (forall o, reached o -> o = root) ->
  predecessor_coverage root (Exchange s r) p reached covered.
Proof.
  intro Root. split.
  - intros o H. rewrite (Root o H). apply path_prefix_refl.
  - intros o H path k a b At Peer Before.
    rewrite (Root o H) in Before.
    exfalso; exact (no_predecessor_of_root root path Before).
Qed.

Lemma predecessor_coverage_parallel root f x p mark left right covered left_cov
  right_cov :
  predecessor_coverage (child root AppFunction) f p left left_cov ->
  predecessor_coverage (child root AppArgument) x p right right_cov ->
  (forall o, mark o -> left o \/ right o) ->
  (forall k o s r, left_cov k o s r -> covered k o s r) ->
  (forall k o s r, right_cov k o s r -> covered k o s r) ->
  predecessor_coverage root (Parallel f x) p mark covered.
Proof.
  intros [LB LO] [RB RO] Split LiftL LiftR. split.
  - intros o Mark. destruct (Split o Mark) as [H|H].
    + apply path_prefix_parent with (e := AppFunction); now apply LB.
    + apply path_prefix_parent with (e := AppArgument); now apply RB.
  - intros o Mark path k s r At Peer Before.
    destruct (Split o Mark) as [Left|Right]; inversion At; subst.
    + apply LiftL. rewrite child_path.
      eapply LO; [exact Left|eassumption|exact Peer|].
      now apply child_predecessor.
    + destruct (branch_predecessor root AppArgument AppFunction _ _
        (LB o Left) Before) as [Eq|[Eq _]]; discriminate.
    + destruct (branch_predecessor root AppFunction AppArgument _ _
        (RB o Right) Before) as [Eq|[_ Eq]]; discriminate.
    + apply LiftR. rewrite child_path.
      eapply RO; [exact Right|eassumption|exact Peer|].
      now apply child_predecessor.
Qed.

(* Entered-prefix coverage is supplied only for marks in the body. It comes
   from the completed prefix of this chosen Sequence, not a fresh completion
   or an unrelated tree. *)
Lemma predecessor_coverage_sequence root pre body p mark left right covered
  left_cov
  right_cov :
  predecessor_coverage (child root BindPrefix) pre p left left_cov ->
  predecessor_coverage (child root BindBody) body p right right_cov ->
  (forall o, mark o -> left o \/ right o) ->
  (forall k o s r, left_cov k o s r -> covered k o s r) ->
  (forall k o s r, right_cov k o s r -> covered k o s r) ->
  (forall later, right later ->
    forall path k s r, site pre path k s r ->
    (p = s \/ p = r) -> left_cov k (child root BindPrefix ++ path) s r) ->
  predecessor_coverage root (Sequence pre body) p mark covered.
Proof.
  intros [LB LO] [RB RO] Split LiftL LiftR Completed. split.
  - intros o Mark. destruct (Split o Mark) as [H|H].
    + apply path_prefix_parent with (e := BindPrefix); now apply LB.
    + apply path_prefix_parent with (e := BindBody); now apply RB.
  - intros o Mark path k s r At Peer Before.
    destruct (Split o Mark) as [Left|Right]; inversion At; subst.
    + apply LiftL. rewrite child_path.
      eapply LO; [exact Left|eassumption|exact Peer|].
      now apply child_predecessor.
    + destruct (branch_predecessor root BindBody BindPrefix _ _
        (LB o Left) Before) as [Eq|[Eq _]]; discriminate.
    + apply LiftL. rewrite child_path.
      eapply Completed; eassumption.
    + apply LiftR. rewrite child_path.
      eapply RO; [exact Right|eassumption|exact Peer|].
      now apply child_predecessor.
Qed.

Lemma predecessor_coverage_choice root owner body p mark inside covered body_cov
  :
  predecessor_coverage (child root ChoiceBody) body p inside body_cov ->
  (forall o, mark o -> o = root \/ inside o) ->
  (forall k o s r, body_cov k o s r -> covered k o s r) ->
  (forall later, inside later ->
    forall peer, owner <> peer -> (p = owner \/ p = peer) ->
      covered ChoiceDelivery root owner peer) ->
  predecessor_coverage root (Choice owner body) p mark covered.
Proof.
  intros [Bounds Order] Split Lift Header. split.
  - intros o Mark. destruct (Split o Mark) as [->|Body].
    + apply path_prefix_refl.
    + apply path_prefix_parent with (e := ChoiceBody); now apply Bounds.
  - intros o Mark path k s r At Peer Before.
    destruct (Split o Mark) as [Eq|Body].
    + subst o. exfalso; exact (no_predecessor_of_root root path Before).
    + inversion At; subst.
      * rewrite app_nil_r. eapply Header; eassumption.
      * apply Lift. rewrite child_path.
        eapply Order; [exact Body|eassumption|exact Peer|].
        now apply child_predecessor.
Qed.

Section Tracked.
Context {M E Store Input}
  (model : LocalEffects.local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input : Input) (R : list Symbol)
  (A : Symbol -> Type) (c : forall p, Choreo M p (A p)).
Local Arguments tokens {M E Store Input} model stores input R A c {p B} _.

Definition cut_reached p B (node : (logged_cut model stores input R A c) p B) o
  : Prop :=
  (exists e, In e ((tokens model stores input R A c) node) /\ (entry_site model
    stores input R A c) p e = o) \/
  exists X kind sender rd, (cut_receive model stores input R A c) p B node X
    kind o sender rd.

Definition cut_covered p B (node : (logged_cut model stores input R A c) p B)
  kind o sender receiver : Prop :=
  exists e, In e ((tokens model stores input R A c) node) /\ action_at kind o
    sender receiver p ((entry_action model stores input R A c) p e).

#[universes(template)]
Record tracked_realization F active root (cuts : family (logged_cut model stores
  input R A c) F active) tree :
  Prop := {
  tracked_realized : (ObservationCoverage.realized model stores input R A c) F
    active root cuts tree;
  tracked_order : forall p d,
    predecessor_coverage root tree p (cut_reached p (F p) (cuts p d))
      (cut_covered p (F p) (cuts p d))
}.

Lemma tracked_completed F active root (cuts : family (logged_cut model stores
  input R A c) F active) tree :
  tracked_realization F active root cuts tree ->
  forall p d v, (finished model stores input R A c) p (F p) (cuts p d) v ->
  forall path kind sender receiver, site tree path kind sender receiver ->
    (p = sender \/ p = receiver) ->
    cut_covered p (F p) (cuts p d) kind (root ++ path) sender receiver.
Proof.
  intros [Layout _] p d v Done path kind sender receiver At Peer.
  exact (realized_returned model stores input R A c _ _ _ _ _ Layout
    p d v Done path kind sender receiver At Peer).
Qed.

Lemma cut_covered_lift p B C (one : (logged_cut model stores input R A c) p B)
  (two : (logged_cut model stores input R A c) p C) :
  (forall e, In e ((tokens model stores input R A c) one) -> In e ((tokens model
    stores input R A c) two)) ->
  forall k o s r, cut_covered p B one k o s r -> cut_covered p C two k o s r.
Proof. intros Lift k o s r (e & Member & Action). exists e; auto. Qed.

(* The atomic interface uses only position bounds and the existing realization.
   It does not assume any predecessor coverage. *)
Theorem tracked_exchange F active root (cuts : family (logged_cut model stores
  input R A c) F active) s r :
  (ObservationCoverage.realized model stores input R A c) F active root cuts
    (Exchange s r) ->
  (forall p d o, cut_reached p (F p) (cuts p d) o -> o = root) ->
  tracked_realization F active root cuts (Exchange s r).
Proof.
  intros Layout Bounds. constructor; [exact Layout|].
  intros p d. apply predecessor_coverage_exchange. exact (Bounds p d).
Qed.

Theorem tracked_leaf F active root (cuts : family (logged_cut model stores input
  R A c) F active) :
  (ObservationCoverage.realized model stores input R A c) F active root cuts
    Leaf ->
  (forall p d o, cut_reached p (F p) (cuts p d) o -> path_prefix root o) ->
  tracked_realization F active root cuts Leaf.
Proof.
  intros Layout Bounds. constructor; [exact Layout|].
  intros p d. apply predecessor_coverage_leaf. exact (Bounds p d).
Qed.

Theorem tracked_parallel F X active root
    (cuts : family (logged_cut model stores input R A c) F active)
    (functions : family (logged_cut model stores input R A c) (fun p => X p -> F
      p) active)
    (arguments : family (logged_cut model stores input R A c) X active)
      function_tree argument_tree :
  tracked_realization _ active (child root AppFunction)
    functions function_tree ->
  tracked_realization _ active (child root AppArgument)
    arguments argument_tree ->
  (forall p d e, In e ((tokens model stores input R A c) (cuts p d)) <->
    In e ((tokens model stores input R A c) (functions p d)) \/ In e ((tokens
      model stores input R A c) (arguments p d))) ->
  (forall p d v, (finished model stores input R A c) p (F p) (cuts p d) v ->
    exists fv xv, (finished model stores input R A c) p _ (functions p d) fv /\
      (finished model stores input R A c) p _ (arguments p d) xv) ->
  (forall p d Y kind o sender rd, (cut_receive model stores input R A c) p (F p)
    (cuts p d) Y kind o sender rd ->
    (cut_receive model stores input R A c) p _ (functions p d) Y kind o sender
      rd \/
    (cut_receive model stores input R A c) p _ (arguments p d) Y kind o sender
      rd) ->
  tracked_realization F active root cuts (Parallel function_tree argument_tree).
Proof.
  intros [Functions FO] [Arguments AO] Tokens Returns Focus. constructor.
  - eapply realized_parallel; eassumption.
  - intros p d. eapply predecessor_coverage_parallel; [exact (FO p d)|exact (AO
    p d)| |
    |].
    + intros o [(e & Member & Path)|(Y & kind & sender & rd & Recv)].
      * destruct (proj1 (Tokens p d e) Member) as [MemberF|MemberA].
        -- left; left; exists e; auto.
        -- right; left; exists e; auto.
      * destruct (Focus p d Y kind o sender rd Recv) as [RecvF|RecvA].
        -- left; right; exists Y, kind, sender, rd; exact RecvF.
        -- right; right; exists Y, kind, sender, rd; exact RecvA.
    + apply cut_covered_lift. intros e Member; apply Tokens; now left.
    + apply cut_covered_lift. intros e Member; apply Tokens; now right.
Qed.

(* Entered is the actual body-cut family. Its members retain a returned value
   of the corresponding prefix cut, so the SAME prefix_tree supplies coverage.
   *)
Theorem tracked_sequence F X active entered root
    (cuts : family (logged_cut model stores input R A c) F active) (prefixes :
      family (logged_cut model stores input R A c) X active)
    (bodies : family (logged_cut model stores input R A c) F entered)
      prefix_tree body_tree :
  tracked_realization _ active (child root BindPrefix) prefixes prefix_tree ->
  tracked_realization _ entered (child root BindBody) bodies body_tree ->
  (forall p d e, In e ((tokens model stores input R A c) (cuts p d)) <->
    In e ((tokens model stores input R A c) (prefixes p d)) \/
    exists body_member, In e ((tokens model stores input R A c) (bodies p
      body_member))) ->
  (forall p d v, (finished model stores input R A c) p (F p) (cuts p d) v ->
    exists x body_member y,
      (finished model stores input R A c) p _ (prefixes p d) x /\ (finished
        model stores input R A c) p _ (bodies p body_member) y) ->
  (forall p d Y kind o sender rd, (cut_receive model stores input R A c) p (F p)
    (cuts p d) Y kind o sender rd ->
    (cut_receive model stores input R A c) p _ (prefixes p d) Y kind o sender rd
      \/
    exists body_member, (cut_receive model stores input R A c) p _ (bodies p
      body_member) Y kind o sender rd) ->
  (forall p d (body_member : In p entered),
    exists x, (finished model stores input R A c) p _ (prefixes p d) x) ->
  tracked_realization F active root cuts (Sequence prefix_tree body_tree).
Proof.
  intros Prefixes Bodies Tokens Returns Focus Entered.
  destruct Prefixes as [PrefixLayout PO]. destruct Bodies as [BodyLayout BO].
  constructor.
  - eapply realized_sequence; eassumption.
  - intros p d.
    eapply predecessor_coverage_sequence with
      (left := cut_reached p _ (prefixes p d))
      (right := fun o => exists body_member, cut_reached p _ (bodies p
        body_member) o)
      (left_cov := cut_covered p _ (prefixes p d))
      (right_cov := fun k o s r => exists body_member,
        cut_covered p _ (bodies p body_member) k o s r).
    + exact (PO p d).
    + split.
      * intros o [body_member Mark]. exact (proj1 (BO p body_member) o Mark).
      * intros o [body_member Mark] path k s r At Peer Before.
        exists body_member. eapply (proj2 (BO p body_member)); eassumption.
    + intros o [(e & Member & Path)|(Y & kind & sender & rd & Recv)].
      * destruct (proj1 (Tokens p d e) Member) as [MemberP|[body_member
        MemberB]].
        -- left; left; exists e; auto.
        -- right; exists body_member; left; exists e; auto.
      * destruct (Focus p d Y kind o sender rd Recv) as [RecvP|[body_member
        RecvB]].
        -- left; right; exists Y, kind, sender, rd; exact RecvP.
        -- right; exists body_member; right; exists Y, kind, sender, rd; exact
          RecvB.
    + apply cut_covered_lift. intros e Member; apply Tokens; now left.
    + intros k o s r [body_member Cov]. eapply cut_covered_lift; [|exact Cov].
      intros e Member; apply Tokens; right; now exists body_member.
    + intros later [body_member Mark] path k s r At Peer.
      destruct (Entered p d body_member) as [x Done].
      exact (realized_returned model stores input R A c _ _ _ _ _ PrefixLayout
        p d x Done path k s r At Peer).
Qed.

(* The extra header premise is tied to actual body membership, including a
   role poised at a body receive. It is not a predecessor-coverage premise. *)
Theorem tracked_choice F active entered root owner
    (cuts : family (logged_cut model stores input R A c) F active) (bodies :
      family (logged_cut model stores input R A c) F entered) body_tree :
  tracked_realization _ entered (child root ChoiceBody) bodies body_tree ->
  (forall p d e, In e ((tokens model stores input R A c) (cuts p d)) ->
    ((entry_site model stores input R A c) p e = root /\
      forall ev, In ev (entry_batch model stores input R A c p e) ->
        choice_root_event root owner ev) \/
    exists body_member, In e ((tokens model stores input R A c) (bodies p
      body_member))) ->
  (forall p d body_member e,
    In e ((tokens model stores input R A c) (bodies p body_member)) -> In e
      ((tokens model stores input R A c) (cuts p d))) ->
  (forall p d v, (finished model stores input R A c) p (F p) (cuts p d) v ->
    exists body_member y, (finished model stores input R A c) p _ (bodies p
      body_member) y /\
      forall peer, owner <> peer -> (p = owner \/ p = peer) ->
        cut_covered p (F p) (cuts p d) ChoiceDelivery root owner peer) ->
  (forall p d Y kind o sender rd, (cut_receive model stores input R A c) p (F p)
    (cuts p d) Y kind o sender rd ->
    (kind = ChoiceDelivery /\ o = root /\ sender = owner /\ owner <> p) \/
    exists body_member, (cut_receive model stores input R A c) p _ (bodies p
      body_member) Y kind o sender rd) ->
  (forall p d (body_member : In p entered) peer,
    owner <> peer -> (p = owner \/ p = peer) ->
    cut_covered p (F p) (cuts p d) ChoiceDelivery root owner peer) ->
  tracked_realization F active root cuts (Choice owner body_tree).
Proof.
  intros [BodyLayout BO] Tokens BodyTokens Returns Focus Header. constructor.
  - eapply realized_choice; [exact BodyLayout| |exact BodyTokens|exact
    Returns|exact Focus].
    intros p d e Member. destruct (Tokens p d e Member) as [[_ H]|H]; auto.
  - intros p d.
    eapply predecessor_coverage_choice with
      (inside := fun o => exists body_member, cut_reached p _ (bodies p
        body_member) o)
      (body_cov := fun k o s r => exists body_member,
        cut_covered p _ (bodies p body_member) k o s r).
    + split.
      * intros o [body_member Mark]. exact (proj1 (BO p body_member) o Mark).
      * intros o [body_member Mark] path k s r At Peer Before.
        exists body_member. eapply (proj2 (BO p body_member)); eassumption.
    + intros o [(e & Member & Path)|(Y & kind & sender & rd & Recv)].
      * destruct (Tokens p d e Member) as [[Root _]|[body_member MemberB]].
        -- left; congruence.
        -- right; exists body_member; left; exists e; auto.
      * destruct (Focus p d Y kind o sender rd Recv)
          as [(_ & Root & _)|[body_member RecvB]].
        -- now left.
        -- right; exists body_member; right; exists Y, kind, sender, rd; exact
          RecvB.
    + intros k o s r [body_member Cov]. eapply cut_covered_lift; [|exact Cov].
      intros e Member; eapply BodyTokens; eassumption.
    + intros later [body_member Mark] peer Ne Peer.
      exact (Header p d body_member peer Ne Peer).
Qed.

Theorem tracked_predecessor_token F active root (cuts : family (logged_cut model
  stores input R A c) F active)
  tree :
  tracked_realization F active root cuts tree ->
  forall p d later, cut_reached p (F p) (cuts p d) later ->
  forall path kind sender receiver, site tree path kind sender receiver ->
    (p = sender \/ p = receiver) ->
    source_before (root ++ path) later ->
    exists e, In e ((tokens model stores input R A c) (cuts p d)) /\
      action_at kind (root ++ path) sender receiver p ((entry_action model
        stores input R A c) p e).
Proof.
  intros [_ Order] p d later Reached path kind sender receiver At Peer Before.
  exact (proj2 (Order p d) later Reached path kind sender receiver At Peer
    Before).
Qed.

Corollary tracked_acted_predecessor F active root (cuts : family (logged_cut
  model stores input R A c) F active)
  tree :
  tracked_realization F active root cuts tree ->
  forall p d later_entry, In later_entry ((tokens model stores input R A c)
    (cuts p d)) ->
  forall path kind sender receiver, site tree path kind sender receiver ->
    (p = sender \/ p = receiver) ->
    source_before (root ++ path) ((entry_site model stores input R A c) p
      later_entry) ->
    cut_covered p (F p) (cuts p d) kind (root ++ path) sender receiver.
Proof.
  intros Layout p d later_entry Member path kind sender receiver At Peer Before.
  eapply tracked_predecessor_token; [exact Layout| |exact At|exact Peer|exact
    Before].
  left; exists later_entry; auto.
Qed.

Corollary tracked_receive_predecessor F active root (cuts : family (logged_cut
  model stores input R A c) F active)
  tree :
  tracked_realization F active root cuts tree ->
  forall p d X later_kind later sender rd,
    (cut_receive model stores input R A c) p (F p) (cuts p d) X later_kind later
      sender rd ->
  forall path kind from peer, site tree path kind from peer ->
    (p = from \/ p = peer) ->
    source_before (root ++ path) later ->
    cut_covered p (F p) (cuts p d) kind (root ++ path) from peer.
Proof.
  intros Layout p d X later_kind later sender rd Focus path kind from peer At
    Peer Before.
  eapply tracked_predecessor_token; [exact Layout| |exact At|exact Peer|exact
    Before].
  right; exists X, later_kind, sender, rd; exact Focus.
Qed.

(* Archive ownership connects the OWN predecessor token to the exact matched
   source trace. No separately completed history is used for this extraction. *)
Theorem tracked_predecessor_trace tc s tn n gs past ar F active root
    (cuts : family (logged_cut model stores input R A c) F active) tree :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  owns_region model stores input R A c ar F active root cuts ->
  tracked_realization F active root cuts tree ->
  forall p d later, cut_reached p (F p) (cuts p d) later ->
  forall path kind sender receiver, site tree path kind sender receiver ->
    (p = sender \/ p = receiver) ->
    source_before (root ++ path) later ->
    exists e suffix,
      In e ((tokens model stores input R A c) (cuts p d)) /\
      tc = entry_tc model stores input R A c p e ++ [(entry_action model stores
        input R A c) p e] ++ suffix /\
      action_at kind (root ++ path) sender receiver p ((entry_action model
        stores input R A c) p e).
Proof.
  intros Hist [_ [_ Own]] Layout p d later Reached path kind sender receiver At
    Peer Before.
  destruct (tracked_predecessor_token F active root cuts tree Layout
    p d later Reached path kind sender receiver At Peer Before)
    as (e & Token & Action).
  pose proof (proj1 (proj1 (Own p d e) Token)) as Archived.
  destruct (observed_archives_trace model stores input R A c
    _ _ _ _ _ _ _ Hist p _ e Archived) as [suffix Trace].
  exists e, suffix; auto.
Qed.

(* Both certificates are existentially attached to one selected tree. *)
Theorem tracked_same_tree F active root (cuts : family (logged_cut model stores
  input R A c) F active) tree :
  tracked_realization F active root cuts tree ->
  (ObservationCoverage.realized model stores input R A c) F active root cuts
    tree /\
  forall p d, predecessor_coverage root tree p (cut_reached p (F p) (cuts p d))
    (cut_covered p (F p) (cuts p d)).
Proof. intros [Layout Order]; auto. Qed.
End Tracked.
