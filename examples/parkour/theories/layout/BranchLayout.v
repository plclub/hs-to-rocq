From Stdlib Require Import Lists.List.
Require Import DeadlockRealized DeadlockLayoutOrder DeadlockFamilyBranches
  DeadlockCoverage DeadlockState
  DeadlockFamilyLog DeadlockPlayedFamily DeadlockPlayedActual
  DeadlockLogDecompose DeadlockLogScope DeadlockLocalLog DeadlockObservedCut
  DeadlockCutSafety DeadlockSource DeadlockLocal DeadlockCoherence
  DeadlockChronology DeadlockPlayedValues DeadlockPartialValues
  DeadlockWellFormed Parkour.Symbol Parkour.Codec Choreography.Choreo2
  Control.Monad.Tree.
Import ListNotations.
Set Universe Polymorphism.

Section FocusRouting.
Context {M E : Type -> Type} (p : Symbol).
Local Arguments ContextHole {M E p X}.
Local Arguments ContextSeq {M E p X Y Z} _ _ _.
Local Arguments ContextLeft {M E p X Y Z} _ _.
Local Arguments ContextRight {M E p X Y Z} _ _.

Fixpoint branch_receive {B} (t : @cursor M E p B)
    X kind o sender (rd : Read X) : Prop :=
  match t with
  | Code root code => @receive_focus M E p _ (Code root code) X kind o sender rd
  | Seq _ prefix _ => branch_receive prefix X kind o sender rd
  | Fork f x => branch_receive f X kind o sender rd \/
      branch_receive x X kind o sender rd
  | _ => False
  end.

Lemma branch_receive_here B (t : @cursor M E p B) X kind o sender rd :
  receive_focus p B t X kind o sender rd ->
  branch_receive t X kind o sender rd.
Proof. destruct 1; cbn; constructor; assumption. Qed.

Lemma branch_receive_plug B F (C : @cursor_context M E p B F)
    focus X kind o sender rd :
  receive_focus p B focus X kind o sender rd ->
  branch_receive (plug C focus) X kind o sender rd.
Proof.
  intro Focus. induction C; cbn; auto using branch_receive_here.
Qed.

Lemma branch_receive_focus B (t : @cursor M E p B) X kind o sender rd :
  branch_receive t X kind o sender rd ->
  exists Z (C : @cursor_context M E p Z B) focus,
    t = plug C focus /\ receive_focus p Z focus X kind o sender rd.
Proof.
  induction t as [B root code|B value|B root local|X0 Y root pre IH k|
      X0 Y f IHf x IHx]; cbn; intro Recv; try contradiction.
  - exists B, ContextHole, (Code root code). auto.
  - destruct (IH Recv) as (Z & C & focus & Eq & Focus).
    exists Z, (ContextSeq root k C), focus. cbn.
    split; [now rewrite <- Eq|exact Focus].
  - destruct Recv as [Left|Right].
    + destruct (IHf Left) as (Z & C & focus & Eq & Focus).
      exists Z, (ContextLeft x C), focus. cbn.
      split; [now rewrite <- Eq|exact Focus].
    + destruct (IHx Right) as (Z & C & focus & Eq & Focus).
      exists Z, (ContextRight f C), focus. cbn.
      split; [now rewrite <- Eq|exact Focus].
Qed.

Definition receiver_head {B} (t : @cursor M E p B) : Prop :=
  match t with
  | Code _ (Perf _) => True
  | _ => False
  end.

Lemma receive_focus_head B (t : @cursor M E p B) X kind o sender rd :
  receive_focus p B t X kind o sender rd -> receiver_head t.
Proof. destruct 1; exact I. Qed.

Lemma branch_receive_app X Y root (f : Choreo M p (X -> Y)) x
    Z kind o sender rd :
  ~ branch_receive (Code root (App f x)) Z kind o sender rd.
Proof. cbn. intro H. exact (receive_focus_head _ _ _ _ _ _ _ H). Qed.

Lemma branch_receive_bind X Y root (t : Choreo M p X) (k : X -> Choreo M p Y)
    Z kind o sender rd :
  ~ branch_receive (Code root (Bind t k)) Z kind o sender rd.
Proof. cbn. intro H. exact (receive_focus_head _ _ _ _ _ _ _ H). Qed.
End FocusRouting.

Section BranchLayout.
Context {M E Store Input}
  (model : local_model M E Symbol (Store * Input))
  (stores : Symbol -> Store) (input : Input) (R : list Symbol)
  (A : Symbol -> Type) (c : forall p, Choreo M p (A p)).
Local Notation cut := (logged_cut model stores input R A c).
Local Notation tok := (tokens model stores input R A c).
Local Notation cur := (cursor_at model stores input R A c).
Local Notation ret := (finished model stores input R A c).
Local Notation recv := (cut_receive model stores input R A c).
Local Notation tracked := (tracked_realization model stores input R A c).
Local Notation entry := (observed_entry model stores input R A c).
Local Notation path_of := (entry_site model stores input R A c).
Local Arguments tokens {M E Store Input} model stores input R A c {p B} _.
Local Arguments cursor_at {M E Store Input} model stores input R A c {p B} _.

Lemma cut_receive_branch p B (node : cut p B) X kind o sender rd :
  recv p B node X kind o sender rd <->
  branch_receive p (cur node) X kind o sender rd.
Proof.
  split.
  - intros (Z & C & focus & Eq & Focus). rewrite Eq.
    now apply branch_receive_plug.
  - apply branch_receive_focus.
Qed.

Lemma app_current_focus p X F root f x (parent : cut p F)
    (fc : cut p (X -> F)) (xc : cut p X) :
  app_cursor_shape model stores input R A c p X F root f x parent fc xc ->
  forall Y kind o sender rd, recv p F parent Y kind o sender rd ->
    recv p _ fc Y kind o sender rd \/ recv p _ xc Y kind o sender rd.
Proof.
  intros Shape Y kind o sender rd Recv. apply cut_receive_branch in Recv.
  destruct Shape as [[Parent _]|[Parent|(g & a & FRet & XRet & Parent)]].
  - rewrite Parent in Recv. exfalso; eapply branch_receive_app; exact Recv.
  - rewrite Parent in Recv. cbn in Recv. destruct Recv as [FRecv|XRecv].
    + left; now apply cut_receive_branch.
    + right; now apply cut_receive_branch.
  - rewrite Parent in Recv. exact (False_rect _ Recv).
Qed.

Theorem tracked_app_logged S X F
    (f : programs M (fun p => X p -> F p) S) (x : programs M X S)
    active inc root (cuts : family cut F active)
    (fs : family cut (fun p => X p -> F p) active)
    (xs : family cut X active) ft xt :
  (forall p d, app_cursor_shape model stores input R A c p (X p) (F p)
    root (f p (inc p d)) (x p (inc p d)) (cuts p d) (fs p d) (xs p d)) ->
  (forall p d e, In e (tok (cuts p d)) <->
    In e (tok (fs p d)) \/ In e (tok (xs p d))) ->
  tracked _ active (child root AppFunction) fs ft ->
  tracked _ active (child root AppArgument) xs xt ->
  tracked F active root cuts (Parallel ft xt).
Proof.
  intros Shape Partition FTracked XTracked.
  eapply tracked_parallel; [exact FTracked|exact XTracked|exact Partition| |].
  - intros p d v Done.
    destruct (app_children_return model stores input R A c p _ _ root
      _ _ _ _ _ (Shape p d) v Done) as (g & a & FG & XA & Eq).
    exists g,a. auto.
  - intros p d. eapply app_current_focus. exact (Shape p d).
Qed.

Variable past : list payload_event.
Variable ar : actor_archive model stores input R A c.
Local Notation node := (at_node model stores input R A c past).
Local Notation good := (owns_region model stores input R A c ar).

Lemma bind_subtree_paths p X F root (t : Choreo M p X) k (parent : cut p F) :
  node p F root (Bind t k) parent ->
  forall e, In e (tok parent) ->
    extends (child root BindPrefix) (path_of p e) \/
    extends (child root BindBody) (path_of p e).
Proof.
  intros [Run _].
  destruct (local_log_bind_cases (shared_model model) p (entry p)
    (stamped model stores input R A c p)
    (stamped_primitive_cursor model stores input R A c p) X F root t k
    (tok parent) (cur parent) Run)
    as [[Empty Shape]|[(ct & Prefix & Shape)|
      (pl & bl & x & Part & Prefix & Body)]]; intros e Member.
  - rewrite Empty in Member. contradiction.
  - left. eapply log_entry_scope; eassumption.
  - rewrite Part in Member. apply in_append_large in Member as [Member|Member].
    + left. eapply log_entry_scope; eassumption.
    + right. eapply log_entry_scope; eassumption.
Qed.

Lemma bind_owned_partition S X F (t : programs M X S)
    (k : forall p, S p -> X p -> Choreo M p (F p))
    active entered inc root (cuts : family cut F active)
    (prefixes : family cut X active) (bodies : family cut F entered) :
  good F active root cuts ->
  good X active (child root BindPrefix) prefixes ->
  good F entered (child root BindBody) bodies ->
  family_at cut node S F (fun p s => Bind (t p s) (k p s)) active inc root cuts
    ->
  forall p d e, In e (tok (cuts p d)) <->
    In e (tok (prefixes p d)) \/
    exists body_member, In e (tok (bodies p body_member)).
Proof.
  intros [_ [_ Parent]] [_ [_ Prefix]] [_ [BodyCover Body]] At p d e.
  split.
  - intro Member.
    pose proof (proj1 (Parent p d e) Member) as [Seen Scope].
    destruct (bind_subtree_paths p _ _ root _ _ _ (At p d) e Member)
      as [Pre|Post].
    + left. apply Prefix. now split.
    + right. assert (Region : in_region model stores input R A c ar p
        (child root BindBody) e) by now split.
      exists (BodyCover p e Region). now apply Body.
  - intros [Member|[body_member Member]].
    + apply Parent. destruct (proj1 (Prefix p d e) Member) as [Seen Scope].
      split; [exact Seen|now apply extends_child in Scope].
    + apply Parent. destruct (proj1 (Body p body_member e) Member) as [Seen
      Scope].
      split; [exact Seen|now apply extends_child in Scope].
Qed.

Definition bind_layout_shape S X F (t : programs M X S)
    (k : forall p, S p -> X p -> Choreo M p (F p))
    active entered inc root (cuts : family cut F active)
    (inside : includes (fun p => In p entered) (fun p => In p active))
    (prefixes : family cut X active) (bodies : family cut F entered) :=
  forall p d,
    (exists e : In p entered, inside p e = d /\
      cur (cuts p d) = cur (bodies p e)) \/
    (cur (cuts p d) = Code root (Bind (t p (inc p d)) (k p (inc p d))) /\
      cur (prefixes p d) = Code (child root BindPrefix) (t p (inc p d))) \/
    cur (cuts p d) = Seq root (cur (prefixes p d)) (k p (inc p d)).

Lemma bind_current_focus S X F t k active entered inc root cuts inside prefixes
  bodies :
  bind_layout_shape S X F t k active entered inc root cuts inside prefixes
    bodies ->
  forall p d Y kind o sender rd, recv p (F p) (cuts p d) Y kind o sender rd ->
    recv p _ (prefixes p d) Y kind o sender rd \/
    exists body_member, recv p _ (bodies p body_member) Y kind o sender rd.
Proof.
  intros Shape p d Y kind o sender rd Recv.
  destruct (Shape p d) as [(here & Eq & Parent)|[[Parent _]|Parent]].
  - right. exists here. unfold cut_receive in *.
    now rewrite <- Parent.
  - apply cut_receive_branch in Recv. rewrite Parent in Recv.
    exfalso; eapply branch_receive_bind; exact Recv.
  - left. apply cut_receive_branch.
    apply cut_receive_branch in Recv. rewrite Parent in Recv. exact Recv.
Qed.

Theorem tracked_bind_logged S X F (t : programs M X S)
    (k : forall p, S p -> X p -> Choreo M p (F p))
    active entered inc root (cuts : family cut F active)
    (inside : includes (fun p => In p entered) (fun p => In p active))
    (prefixes : family cut X active)
    (vals : values X (fun p => In p entered))
    (bodies : family cut F entered) pt bt :
  good F active root cuts ->
  good X active (child root BindPrefix) prefixes ->
  good F entered (child root BindBody) bodies ->
  family_at cut node S F (fun p s => Bind (t p s) (k p s)) active inc root cuts
    ->
  family_returned cut ret X active entered inside prefixes vals ->
  bind_layout_shape S X F t k active entered inc root cuts inside prefixes
    bodies ->
  tracked _ active (child root BindPrefix) prefixes pt ->
  tracked _ entered (child root BindBody) bodies bt ->
  tracked F active root cuts (Sequence pt bt).
Proof.
  intros Good PrefixGood BodyGood At PrefixReturned Shape PrefixTracked
    BodyTracked.
  pose proof (proj1 Good) as ND.
  eapply tracked_sequence; [exact PrefixTracked|exact BodyTracked| | | |].
  - eapply bind_owned_partition; eassumption.
  - intros p d v Done.
    destruct (Shape p d) as [(here & Eq & Parent)|[[Parent _]|Parent]].
    + exists (vals p here), here, v. split.
      * rewrite <- Eq. apply PrefixReturned.
      * unfold finished in *. now rewrite <- Parent.
    + unfold finished in Done. rewrite Parent in Done. contradiction.
    + unfold finished in Done. rewrite Parent in Done. contradiction.
  - eapply bind_current_focus. exact Shape.
  - intros p d here. exists (vals p here).
    rewrite <- (roster_member_unique active ND p (inside p here) d).
    apply PrefixReturned.
Qed.

Theorem app_layout_children S X F
    (f : programs M (fun p => X p -> F p) S) (x : programs M X S)
    active inc root (cuts : family cut F active) :
  good F active root cuts ->
  family_at cut node S F (fun p s => App (f p s) (x p s)) active inc root cuts
    ->
  exists (fs : family cut (fun p => X p -> F p) active)
    (xs : family cut X active),
    good _ active (child root AppFunction) fs /\
    good _ active (child root AppArgument) xs /\
    family_at cut node S _ f active inc (child root AppFunction) fs /\
    family_at cut node S _ x active inc (child root AppArgument) xs /\
    forall ft xt,
      tracked _ active (child root AppFunction) fs ft ->
      tracked _ active (child root AppArgument) xs xt ->
      tracked F active root cuts (Parallel ft xt).
Proof.
  intros Good At.
  destruct (logged_replay_app_partition model stores input R A c past ar
    S X F f x active inc root cuts Good At)
    as (fs & xs & GF & GX & FA & XA & Shape & Partition).
  exists fs,xs. split; [exact GF|]. split; [exact GX|].
  split; [exact FA|]. split; [exact XA|].
  intros ft xt. eapply tracked_app_logged; eassumption.
Qed.

Theorem bind_layout_children S X F (t : programs M X S)
    (k : forall p, S p -> X p -> Choreo M p (F p))
    active inc root (cuts : family cut F active) :
  good F active root cuts ->
  family_at cut node S F (fun p s => Bind (t p s) (k p s)) active inc root cuts
    ->
  exists entered
    (inside : includes (fun p => In p entered) (fun p => In p active))
    (prefixes : family cut X active)
    (vals : values X (fun p => In p entered))
    (bodies : family cut F entered),
    NoDup entered /\
    good X active (child root BindPrefix) prefixes /\
    family_at cut node S X t active inc (child root BindPrefix) prefixes /\
    family_returned cut ret X active entered inside prefixes vals /\
    good F entered (child root BindBody) bodies /\
    (forall p d, node p _ (child root BindBody)
      (k p (inc p (inside p d)) (vals p d)) (bodies p d)) /\
    forall pt bt,
      tracked _ active (child root BindPrefix) prefixes pt ->
      tracked _ entered (child root BindBody) bodies bt ->
      tracked F active root cuts (Sequence pt bt).
Proof.
  intros Good At.
  destruct (logged_replay_bind model stores input R A c past ar
    S X F t k active [] inc root cuts (fun p d => False_rect _ d)
    (fun p d => False_rect _ d) (proj1 Good) (NoDup_nil _) Good At
    (fun p d => False_rect _ d))
    as (entered & inside & finished & prefixes & vals & bodies &
      NE & GP & PA & PR & GB & BA & BR & Shape).
  exists entered,inside,prefixes,vals,bodies.
  split; [exact NE|]. split; [exact GP|]. split; [exact PA|].
  split; [exact PR|]. split; [exact GB|]. split; [exact BA|].
  intros pt bt. eapply tracked_bind_logged; eassumption.
Qed.
End BranchLayout.

Print Assumptions app_layout_children.
Print Assumptions bind_layout_children.
