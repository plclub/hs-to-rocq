From Stdlib Require Import Lists.List.
Require Import DeadlockRealized DeadlockCoverage DeadlockSource DeadlockOrder
  DeadlockChronology DeadlockCoherence DeadlockObservedCut DeadlockLocalLog
  DeadlockPlayedActual DeadlockPlayedFamily DeadlockPlayedValues DeadlockState
    DeadlockFamilyLog
  DeadlockCutSafety Parkour.Symbol Choreography.Choreo2.
Import ListNotations.

(* Marks below are positions actually reached by one role, not all positions
   of a selected tree. The constructors transfer coverage from the very same
   child layouts that supply the selected parent tree. *)
Definition layout_order root tree p
    (reached : occurrence -> Prop)
    (covered : delivery_kind -> occurrence -> Symbol -> Symbol -> Prop) : Prop
      :=
  (forall later, reached later -> extends root later) /\
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
  extends (child root f) later ->
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

Lemma layout_order_leaf root p reached covered :
  (forall o, reached o -> extends root o) ->
  layout_order root Leaf p reached covered.
Proof. intro Bounds. split; [exact Bounds|].
intros o Mark path k s r At; inversion At. Qed.

Lemma layout_order_exchange root p s r reached covered :
  (forall o, reached o -> o = root) ->
  layout_order root (Exchange s r) p reached covered.
Proof.
  intro Root. split.
  - intros o H. rewrite (Root o H). apply extends_refl.
  - intros o H path k a b At Peer Before.
    rewrite (Root o H) in Before.
    exfalso; exact (no_predecessor_of_root root path Before).
Qed.

Lemma layout_order_parallel root f x p mark left right covered left_cov
  right_cov :
  layout_order (child root AppFunction) f p left left_cov ->
  layout_order (child root AppArgument) x p right right_cov ->
  (forall o, mark o -> left o \/ right o) ->
  (forall k o s r, left_cov k o s r -> covered k o s r) ->
  (forall k o s r, right_cov k o s r -> covered k o s r) ->
  layout_order root (Parallel f x) p mark covered.
Proof.
  intros [LB LO] [RB RO] Split LiftL LiftR. split.
  - intros o Mark. destruct (Split o Mark) as [H|H].
    + apply extends_child with (e := AppFunction); now apply LB.
    + apply extends_child with (e := AppArgument); now apply RB.
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
Lemma layout_order_sequence root pre body p mark left right covered left_cov
  right_cov :
  layout_order (child root BindPrefix) pre p left left_cov ->
  layout_order (child root BindBody) body p right right_cov ->
  (forall o, mark o -> left o \/ right o) ->
  (forall k o s r, left_cov k o s r -> covered k o s r) ->
  (forall k o s r, right_cov k o s r -> covered k o s r) ->
  (forall later, right later ->
    forall path k s r, site pre path k s r ->
    (p = s \/ p = r) -> left_cov k (child root BindPrefix ++ path) s r) ->
  layout_order root (Sequence pre body) p mark covered.
Proof.
  intros [LB LO] [RB RO] Split LiftL LiftR Completed. split.
  - intros o Mark. destruct (Split o Mark) as [H|H].
    + apply extends_child with (e := BindPrefix); now apply LB.
    + apply extends_child with (e := BindBody); now apply RB.
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

Lemma layout_order_choice root owner body p mark inside covered body_cov :
  layout_order (child root ChoiceBody) body p inside body_cov ->
  (forall o, mark o -> o = root \/ inside o) ->
  (forall k o s r, body_cov k o s r -> covered k o s r) ->
  (forall later, inside later ->
    forall peer, owner <> peer -> (p = owner \/ p = peer) ->
      covered ChoiceDelivery root owner peer) ->
  layout_order root (Choice owner body) p mark covered.
Proof.
  intros [Bounds Order] Split Lift Header. split.
  - intros o Mark. destruct (Split o Mark) as [->|Body].
    + apply extends_refl.
    + apply extends_child with (e := ChoiceBody); now apply Bounds.
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
  (model : DeadlockLocal.local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input : Input) (R : list Symbol)
  (A : Symbol -> Type) (c : forall p, Choreo M p (A p)).
Local Notation cut := (logged_cut model stores input R A c).
Local Notation entry := (observed_entry model stores input R A c).
Local Notation tok := (tokens model stores input R A c).
Local Notation path_of := (entry_site model stores input R A c).
Local Notation act := (entry_action model stores input R A c).
Local Notation ret := (finished model stores input R A c).
Local Notation realized := (DeadlockRealized.realized model stores input R A c).
Local Notation receive := (cut_receive model stores input R A c).
Local Arguments tokens {M E Store Input} model stores input R A c {p B} _.

Definition cut_reached p B (node : cut p B) o : Prop :=
  (exists e, In e (tok node) /\ path_of p e = o) \/
  exists X kind sender rd, receive p B node X kind o sender rd.

Definition cut_covered p B (node : cut p B) kind o sender receiver : Prop :=
  exists e, In e (tok node) /\ action_at kind o sender receiver p (act p e).

#[universes(template)]
Record tracked_realization F active root (cuts : family cut F active) tree :
  Prop := {
  tracked_realized : realized F active root cuts tree;
  tracked_order : forall p d,
    layout_order root tree p (cut_reached p (F p) (cuts p d))
      (cut_covered p (F p) (cuts p d))
}.

Lemma tracked_completed F active root (cuts : family cut F active) tree :
  tracked_realization F active root cuts tree ->
  forall p d v, ret p (F p) (cuts p d) v ->
  forall path kind sender receiver, site tree path kind sender receiver ->
    (p = sender \/ p = receiver) ->
    cut_covered p (F p) (cuts p d) kind (root ++ path) sender receiver.
Proof.
  intros [Layout _] p d v Done path kind sender receiver At Peer.
  exact (realized_returned model stores input R A c _ _ _ _ _ Layout
    p d v Done path kind sender receiver At Peer).
Qed.

Lemma cut_covered_lift p B C (one : cut p B) (two : cut p C) :
  (forall e, In e (tok one) -> In e (tok two)) ->
  forall k o s r, cut_covered p B one k o s r -> cut_covered p C two k o s r.
Proof. intros Lift k o s r (e & Member & Action). exists e; auto. Qed.

(* The atomic interface uses only position bounds and the existing realization.
   It does not assume any predecessor coverage. *)
Theorem tracked_exchange F active root (cuts : family cut F active) s r :
  realized F active root cuts (Exchange s r) ->
  (forall p d o, cut_reached p (F p) (cuts p d) o -> o = root) ->
  tracked_realization F active root cuts (Exchange s r).
Proof.
  intros Layout Bounds. constructor; [exact Layout|].
  intros p d. apply layout_order_exchange. exact (Bounds p d).
Qed.

Theorem tracked_leaf F active root (cuts : family cut F active) :
  realized F active root cuts Leaf ->
  (forall p d o, cut_reached p (F p) (cuts p d) o -> extends root o) ->
  tracked_realization F active root cuts Leaf.
Proof.
  intros Layout Bounds. constructor; [exact Layout|].
  intros p d. apply layout_order_leaf. exact (Bounds p d).
Qed.

Theorem tracked_parallel F X active root
    (cuts : family cut F active)
    (functions : family cut (fun p => X p -> F p) active)
    (arguments : family cut X active) function_tree argument_tree :
  tracked_realization _ active (child root AppFunction) functions function_tree
    ->
  tracked_realization _ active (child root AppArgument) arguments argument_tree
    ->
  (forall p d e, In e (tok (cuts p d)) <->
    In e (tok (functions p d)) \/ In e (tok (arguments p d))) ->
  (forall p d v, ret p (F p) (cuts p d) v ->
    exists fv xv, ret p _ (functions p d) fv /\ ret p _ (arguments p d) xv) ->
  (forall p d Y kind o sender rd, receive p (F p) (cuts p d) Y kind o sender rd
    ->
    receive p _ (functions p d) Y kind o sender rd \/
    receive p _ (arguments p d) Y kind o sender rd) ->
  tracked_realization F active root cuts (Parallel function_tree argument_tree).
Proof.
  intros [Functions FO] [Arguments AO] Tokens Returns Focus. constructor.
  - eapply realized_parallel; eassumption.
  - intros p d. eapply layout_order_parallel; [exact (FO p d)|exact (AO p d)| |
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
    (cuts : family cut F active) (prefixes : family cut X active)
    (bodies : family cut F entered) prefix_tree body_tree :
  tracked_realization _ active (child root BindPrefix) prefixes prefix_tree ->
  tracked_realization _ entered (child root BindBody) bodies body_tree ->
  (forall p d e, In e (tok (cuts p d)) <->
    In e (tok (prefixes p d)) \/
    exists body_member, In e (tok (bodies p body_member))) ->
  (forall p d v, ret p (F p) (cuts p d) v ->
    exists x body_member y,
      ret p _ (prefixes p d) x /\ ret p _ (bodies p body_member) y) ->
  (forall p d Y kind o sender rd, receive p (F p) (cuts p d) Y kind o sender rd
    ->
    receive p _ (prefixes p d) Y kind o sender rd \/
    exists body_member, receive p _ (bodies p body_member) Y kind o sender rd)
      ->
  (forall p d (body_member : In p entered),
    exists x, ret p _ (prefixes p d) x) ->
  tracked_realization F active root cuts (Sequence prefix_tree body_tree).
Proof.
  intros Prefixes Bodies Tokens Returns Focus Entered.
  destruct Prefixes as [PrefixLayout PO]. destruct Bodies as [BodyLayout BO].
  constructor.
  - eapply realized_sequence; eassumption.
  - intros p d.
    eapply layout_order_sequence with
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
    (cuts : family cut F active) (bodies : family cut F entered) body_tree :
  tracked_realization _ entered (child root ChoiceBody) bodies body_tree ->
  (forall p d e, In e (tok (cuts p d)) ->
    (path_of p e = root /\
      forall ev, In ev (entry_batch model stores input R A c p e) ->
        choice_root_event root owner ev) \/
    exists body_member, In e (tok (bodies p body_member))) ->
  (forall p d body_member e,
    In e (tok (bodies p body_member)) -> In e (tok (cuts p d))) ->
  (forall p d v, ret p (F p) (cuts p d) v ->
    exists body_member y, ret p _ (bodies p body_member) y /\
      forall peer, owner <> peer -> (p = owner \/ p = peer) ->
        cut_covered p (F p) (cuts p d) ChoiceDelivery root owner peer) ->
  (forall p d Y kind o sender rd, receive p (F p) (cuts p d) Y kind o sender rd
    ->
    (kind = ChoiceDelivery /\ o = root /\ sender = owner /\ owner <> p) \/
    exists body_member, receive p _ (bodies p body_member) Y kind o sender rd)
      ->
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
    eapply layout_order_choice with
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

Theorem tracked_predecessor_token F active root (cuts : family cut F active)
  tree :
  tracked_realization F active root cuts tree ->
  forall p d later, cut_reached p (F p) (cuts p d) later ->
  forall path kind sender receiver, site tree path kind sender receiver ->
    (p = sender \/ p = receiver) ->
    source_before (root ++ path) later ->
    exists e, In e (tok (cuts p d)) /\
      action_at kind (root ++ path) sender receiver p (act p e).
Proof.
  intros [_ Order] p d later Reached path kind sender receiver At Peer Before.
  exact (proj2 (Order p d) later Reached path kind sender receiver At Peer
    Before).
Qed.

Corollary tracked_acted_predecessor F active root (cuts : family cut F active)
  tree :
  tracked_realization F active root cuts tree ->
  forall p d later_entry, In later_entry (tok (cuts p d)) ->
  forall path kind sender receiver, site tree path kind sender receiver ->
    (p = sender \/ p = receiver) ->
    source_before (root ++ path) (path_of p later_entry) ->
    cut_covered p (F p) (cuts p d) kind (root ++ path) sender receiver.
Proof.
  intros Layout p d later_entry Member path kind sender receiver At Peer Before.
  eapply tracked_predecessor_token; [exact Layout| |exact At|exact Peer|exact
    Before].
  left; exists later_entry; auto.
Qed.

Corollary tracked_receive_predecessor F active root (cuts : family cut F active)
  tree :
  tracked_realization F active root cuts tree ->
  forall p d X later_kind later sender rd,
    receive p (F p) (cuts p d) X later_kind later sender rd ->
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
    (cuts : family cut F active) tree :
  observed_archives model stores input R A c tc s tn n gs past ar ->
  owns_region model stores input R A c ar F active root cuts ->
  tracked_realization F active root cuts tree ->
  forall p d later, cut_reached p (F p) (cuts p d) later ->
  forall path kind sender receiver, site tree path kind sender receiver ->
    (p = sender \/ p = receiver) ->
    source_before (root ++ path) later ->
    exists e suffix,
      In e (tok (cuts p d)) /\
      tc = entry_tc model stores input R A c p e ++ [act p e] ++ suffix /\
      action_at kind (root ++ path) sender receiver p (act p e).
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
Theorem tracked_same_tree F active root (cuts : family cut F active) tree :
  tracked_realization F active root cuts tree ->
  realized F active root cuts tree /\
  forall p d, layout_order root tree p (cut_reached p (F p) (cuts p d))
    (cut_covered p (F p) (cuts p d)).
Proof. intros [Layout Order]; auto. Qed.
End Tracked.

Print Assumptions tracked_parallel.
Print Assumptions tracked_sequence.
Print Assumptions tracked_choice.
Print Assumptions tracked_predecessor_token.
Print Assumptions tracked_predecessor_trace.
