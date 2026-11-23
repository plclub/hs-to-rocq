From Stdlib Require Import Lists.List.
From ITree Require Import ITree.
Require Import DeadlockLocal DeadlockSource DeadlockEnabled DeadlockProjection
  DeadlockAlignment
  Parkour.Symbol Parkour.Codec Control.Monad.Tree.
Require Choreography.Choreo2.
Local Notation At := Choreography.Choreo2.At.
Local Notation Mk_At := Choreography.Choreo2.Mk_At.
Local Notation Choreo := Choreography.Choreo2.Choreo.
Local Notation ChoreoSig := Choreography.Choreo2.ChoreoSig.

Lemma off_at_canonical X l p (h h' : l <> p) :
  @off_at X l p h = off_at h'.
Proof.
  unfold off_at. destruct (decide (@MkSSymbol l) (@MkSSymbol p)).
  - contradiction.
  - reflexivity.
Qed.

Section Views.
Context {M E : Type -> Type} {Store : Type}.
Variable model : local_model M E Symbol Store.

(* Compositional observations, not a projector. A communication or choice
   cannot return merely because its continuation ignores its result. *)
Definition primitive_result p X (e : ChoreoSig M p X) : X -> Prop :=
  match e in ChoreoSig _ _ Y return Y -> Prop with
  | @Choreography.Choreo2.Locally _ _ Z l _ _ body =>
      match symbol_eq_dec l p with
      | left pf => fun y => exists x,
          local_return (interpret_local _ _ _ _ model Z
            (body (Choreography.Choreo2.unwrap pf))) x /\
          y = Mk_At (fun _ => x)
      | right neq => fun y => y = off_at neq
      end
  | @Choreography.Choreo2.Comm _ _ Z l d _ _ _ _ _ v _ =>
      match symbol_eq_dec l d with
      | left pf => fun y =>
          y = eq_rect l (fun r => At Z r p) v d pf
      | right _ =>
          match symbol_eq_dec l p, symbol_eq_dec d p with
          | right _, right hd => fun y => y = off_at hd
          | _, _ => fun _ => False
          end
      end
  | @Choreography.Choreo2.Cond _ _ _ _ _ _ _ _ _ _ _ => fun _ => False
  end.

Fixpoint code_result p X (c : Choreo M p X) : X -> Prop :=
  match c in Tree _ Y return Y -> Prop with
  | Pure x => fun y => y = x
  | Perf e => primitive_result p _ e
  | Bind t k => fun y =>
      exists x, code_result p _ t x /\ code_result p _ (k x) y
  | App f t => fun y =>
      exists g x, code_result p _ f g /\ code_result p _ t x /\ y = g x
  end.

Fixpoint cursor_result p X (c : @cursor M E p X) : X -> Prop :=
  match c in cursor _ Y return Y -> Prop with
  | Code _ c => code_result p _ c
  | Returned x => fun y => y = x
  | DeadlockSource.Local _ t => fun y =>
      exists x, local_return t x /\ y = here_at x
  | Seq _ t k => fun y =>
      exists x, cursor_result p _ t x /\ code_result p _ (k x) y
  | Fork f t => fun y =>
      exists g x, cursor_result p _ f g /\ cursor_result p _ t x /\ y = g x
  end.

(* Source readiness follows take_at, not the stronger network-lane helper. *)
Definition primitive_live o p X (e : ChoreoSig M p X)
    (s : Store) (sq : list pending) : Prop :=
  match e with
  | @Choreography.Choreo2.Locally _ _ Z l _ _ body =>
      match symbol_eq_dec l p with
      | left pf => exists a t s',
          local_step (reply_local _ _ _ _ model) p
            (interpret_local _ _ _ _ model Z
              (body (Choreography.Choreo2.unwrap pf))) s a t s'
      | right _ => False
      end
  | @Choreography.Choreo2.Comm _ _ Z l d _ _ _ _ _ _ _ =>
      match symbol_eq_dec l d with
      | left _ => False
      | right _ =>
          match symbol_eq_dec l p, symbol_eq_dec d p with
          | left _, right _ => True
          | right _, left _ =>
              exists (x : Z) sq', take_at DataDelivery o l p x sq sq'
          | _, _ => False
          end
      end
  | @Choreography.Choreo2.Cond _ _ Z l _ _ _ _ _ _ _ =>
      match symbol_eq_dec l p with
      | left _ => True
      | right _ =>
          exists (x : Z) sq', take_at ChoiceDelivery o l p x sq sq'
      end
  end.

(* Occurrences matter only at primitive sites. Bind and App retain all
   branches, while a continuation is inspected only after a prefix result. *)
Fixpoint code_live p X o (c : Choreo M p X) s sq : Prop :=
  match c with
  | Pure _ => False
  | Perf e => primitive_live o p _ e s sq
  | Bind t k =>
      code_live p _ (child o BindPrefix) t s sq \/
      exists x, code_result p _ t x /\
        code_live p _ (child o BindBody) (k x) s sq
  | App f t =>
      code_live p _ (child o AppFunction) f s sq \/
      code_live p _ (child o AppArgument) t s sq
  end.

Fixpoint cursor_live p X (c : @cursor M E p X) s sq : Prop :=
  match c with
  | Code o c => code_live p _ o c s sq
  | Returned _ => False
  | DeadlockSource.Local _ t =>
      exists a t' s', local_step (reply_local _ _ _ _ model) p t s a t' s'
  | Seq o t k =>
      cursor_live p _ t s sq \/
      exists x, cursor_result p _ t x /\
        code_live p _ (child o BindBody) (k x) s sq
  | Fork f t => cursor_live p _ f s sq \/ cursor_live p _ t s sq
  end.

Lemma locally_owner_result p X ks ss body y :
  primitive_result p _ (@Choreography.Choreo2.Locally M p X p ks ss body) y <->
  exists x, local_return
    (interpret_local _ _ _ _ model X (body (owner_unwrap p))) x /\
    y = here_at x.
Proof.
  unfold primitive_result.
  destruct (symbol_eq_dec p p) as [pf | npf]; [|contradiction].
  rewrite (symbol_uip _ _ pf eq_refl). reflexivity.
Qed.

Lemma locally_owner_live p X ks ss body o s sq :
  primitive_live o p _ (@Choreography.Choreo2.Locally M p X p ks ss body) s sq
    <->
  exists a t s', local_step (reply_local _ _ _ _ model) p
    (interpret_local _ _ _ _ model X (body (owner_unwrap p))) s a t s'.
Proof.
  unfold primitive_live.
  destruct (symbol_eq_dec p p) as [pf | npf]; [|contradiction].
  rewrite (symbol_uip _ _ pf eq_refl). reflexivity.
Qed.

Lemma locally_other_result p X l ks ss body (h : l <> p) y :
  primitive_result p _ (@Choreography.Choreo2.Locally M p X l ks ss body) y <->
  y = off_at h.
Proof.
  unfold primitive_result.
  destruct (symbol_eq_dec l p) as [pf | npf]; [contradiction|].
  rewrite (off_at_canonical X l p npf h). reflexivity.
Qed.

Lemma comm_self_result p X l sh rd kl kd sl v sd y :
  primitive_result p _
    (@Choreography.Choreo2.Comm M p X l l sh rd kl kd sl v sd) y <->
  y = v.
Proof.
  unfold primitive_result.
  destruct (symbol_eq_dec l l) as [pf | npf]; [|contradiction].
  rewrite (symbol_uip _ _ pf eq_refl). reflexivity.
Qed.

Lemma comm_other_result p X l d sh rd kl kd sl v sd
    (hl : l <> p) (hd : d <> p) (hne : l <> d) y :
  primitive_result p _
    (@Choreography.Choreo2.Comm M p X l d sh rd kl kd sl v sd) y <->
  y = off_at hd.
Proof.
  unfold primitive_result.
  destruct (symbol_eq_dec l d) as [pf | npf]; [contradiction|].
  destruct (symbol_eq_dec l p) as [pf | npf']; [contradiction|].
  destruct (symbol_eq_dec d p) as [pf | npf'']; [contradiction|].
  rewrite (off_at_canonical X d p npf'' hd). reflexivity.
Qed.

Theorem silent_result p X (t u : @cursor M E p X) :
  silent model X t u ->
  forall y, cursor_result p X t y <-> cursor_result p X u y.
Proof.
  intros H. induction H; intro y; cbn [cursor_result code_result].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - split.
    + intros [z [-> Hz]]. exact Hz.
    + intro Hy. exists x. split; [reflexivity | exact Hy].
  - split; intros [z [Hz Hy]]; exists z; split; try assumption;
      [apply IHsilent | apply IHsilent]; assumption.
  - split; intros [g [z [Hg [Hz Hy]]]]; exists g, z;
      repeat split; try assumption; [apply IHsilent | apply IHsilent];
        assumption.
  - split; intros [g [z [Hg [Hz Hy]]]]; exists g, z;
      repeat split; try assumption; [apply IHsilent | apply IHsilent];
        assumption.
  - split.
    + intros [g [z [-> [-> Hy]]]]. exact Hy.
    + intro Hy. exists f, x. repeat split; reflexivity || exact Hy.
  - apply locally_owner_result.
  - apply locally_other_result.
  - split.
    + intros [z [Hz Hy]].
      pose proof (local_return_unique _ _ _ H Hz). subst z. exact Hy.
    + intro Hy. exists x. split; assumption.
  - apply comm_other_result; assumption.
  - apply comm_self_result.
Qed.

Theorem silent_live p X (t u : @cursor M E p X) :
  silent model X t u ->
  forall s sq, cursor_live p X t s sq <-> cursor_live p X u s sq.
Proof.
  intros H. induction H; intros s sq; cbn [cursor_live code_live].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - split.
    + intros [Hfalse | [z [-> Hz]]]; [contradiction | exact Hz].
    + intro Hy. right. exists x. split; [reflexivity | exact Hy].
  - rewrite (IHsilent s sq).
    assert (forall z, cursor_result p X t z <-> cursor_result p X t' z) as Hr.
    { intro z. eapply silent_result. exact H. }
    split; intros [Hlive | [z [Hz Hk]]]; try (left; exact Hlive);
      right; exists z; split; try exact Hk;
      [apply (proj1 (Hr z)) | apply (proj2 (Hr z))]; assumption.
  - rewrite IHsilent. reflexivity.
  - rewrite IHsilent. reflexivity.
  - tauto.
  - apply locally_owner_live.
  - unfold primitive_live. destruct (symbol_eq_dec l p);
    [contradiction|reflexivity].
  - split; [|contradiction].
    intros [a [t' [s' Hs]]]. exfalso.
    eapply local_return_no_event; eassumption.
  - unfold primitive_live.
    destruct (symbol_eq_dec l d); [contradiction|].
    destruct (symbol_eq_dec l p); [contradiction|].
    destruct (symbol_eq_dec d p); [contradiction|reflexivity].
  - unfold primitive_live.
    destruct (symbol_eq_dec l l); [reflexivity|contradiction].
Qed.

Theorem source_returns_result p X (t : @cursor M E p X) y :
  DeadlockSource.returns model t y -> cursor_result p X t y.
Proof.
  intros H. induction H.
  - reflexivity.
  - apply (proj2 (silent_result _ _ _ _ H _)). exact IHreturns.
Qed.

Lemma code_result_returns p X (c : Choreo M p X) :
  forall o y, code_result p X c y ->
    DeadlockSource.returns model (Code o c) y.
Proof.
  induction c as [X e | X x | X Y f IHF t IHT | X Y t IHT k IHK];
    intros o y Hr; cbn [code_result] in Hr.
  - destruct e as [X l kl sl body | X l d sh rd kl kd sl v sd |
                   X l Y sh rd kl sl v k].
    + unfold primitive_result in Hr.
      destruct (symbol_eq_dec l p) as [pf | neq].
      * subst l.
        destruct Hr as [x [Ht ->]].
        eapply ReturnsSilent; [apply SLocalStart |].
        eapply ReturnsSilent; [apply SLocalReturn; exact Ht | apply Returns].
      * subst y. eapply ReturnsSilent; [apply SLocalOther | apply Returns].
    + unfold primitive_result in Hr.
      destruct (symbol_eq_dec l d) as [pf | neq].
      * subst d. cbn in Hr.
        subst y. eapply ReturnsSilent; [apply SCommSelf | apply Returns].
      * destruct (symbol_eq_dec l p) as [hl | hl].
        -- destruct (symbol_eq_dec d p); contradiction.
        -- destruct (symbol_eq_dec d p) as [hd | hd]; [contradiction|].
           subst y. eapply ReturnsSilent; [eapply SCommOther; eassumption |
             apply Returns].
    + exact (False_rect _ Hr).
  - subst y. eapply ReturnsSilent; [apply SPure | apply Returns].
  - destruct Hr as [g [x [Hf [Ht ->]]]].
    eapply ReturnsSilent; [apply SApp |].
    eapply source_fork_returns; [apply IHF; exact Hf | apply IHT; exact Ht].
  - destruct Hr as [x [Ht Hk]].
    eapply ReturnsSilent; [apply SBind |].
    eapply source_seq_returns; [apply IHT; exact Ht | apply IHK; exact Hk].
Qed.

Theorem result_source_returns p X (t : @cursor M E p X) y :
  cursor_result p X t y -> DeadlockSource.returns model t y.
Proof.
  revert y.
  induction t as [X o c | X x | X o t | X Y o t IH k | X Y f IHF t IHT];
    intros y Hr; cbn [cursor_result] in Hr.
  - apply code_result_returns. exact Hr.
  - subst y. apply Returns.
  - destruct Hr as [x [Ht ->]].
    eapply ReturnsSilent; [apply SLocalReturn; exact Ht | apply Returns].
  - destruct Hr as [x [Ht Hk]].
    eapply source_seq_returns; [apply IH; exact Ht | apply code_result_returns;
      exact Hk].
  - destruct Hr as [g [x [Hf [Ht ->]]]].
    eapply source_fork_returns; [apply IHF; exact Hf | apply IHT; exact Ht].
Qed.

Corollary cursor_result_exact p X (t : @cursor M E p X) y :
  cursor_result p X t y <-> DeadlockSource.returns model t y.
Proof. split; [apply result_source_returns | apply source_returns_result]. Qed.

Theorem source_step_live roles p X (t t' : @cursor M E p X)
    s sq a s' sq' :
  role_step model roles X t s sq a t' s' sq' -> cursor_live p X t s sq.
Proof.
  intros H. induction H; cbn [cursor_live code_live].
  - exists a, t', s'. exact H.
  - unfold primitive_live.
    destruct (symbol_eq_dec p d); [congruence|].
    destruct (symbol_eq_dec p p); [|contradiction].
    destruct (symbol_eq_dec d p); [contradiction|exact I].
  - unfold primitive_live.
    destruct (symbol_eq_dec l p); [contradiction|].
    destruct (symbol_eq_dec l p); [contradiction|].
    destruct (symbol_eq_dec p p); [|contradiction].
    exists x, q'. exact H.
  - unfold primitive_live.
    destruct (symbol_eq_dec p p); [exact I|contradiction].
  - unfold primitive_live.
    destruct (symbol_eq_dec l p); [contradiction|].
    exists x, q'. exact H.
  - left. exact IHrole_step.
  - left. exact IHrole_step.
  - right. exact IHrole_step.
  - apply (proj2 (silent_live _ _ _ _ H _ _)). exact IHrole_step.
Qed.

Lemma code_live_step roles p X (c : Choreo M p X) :
  forall o s sq, code_live p X o c s sq ->
  exists a t' s' sq', role_step model roles X (Code o c) s sq a t' s' sq'.
Proof.
  induction c as [X e | X x | X Y f IHF t IHT | X Y t IHT k IHK];
    intros o s sq Hlive; cbn [code_live] in Hlive.
  - destruct e as [X l kl sl body | X l d sh rd kl kd sl v sd |
                   X l Y sh rd kl sl v k]; unfold primitive_live in Hlive.
    + destruct (symbol_eq_dec l p) as [pf | neq]; [|contradiction].
      subst l. destruct Hlive as [a [t' [s' Hlocal]]].
      exists (LocalAction o a), (DeadlockSource.Local o t'), s', sq.
      eapply RSilent; [apply SLocalStart | apply RLocal; exact Hlocal].
    + destruct (symbol_eq_dec l d) as [pf | distinct]; [contradiction|].
      destruct (symbol_eq_dec l p) as [hl | hl].
      * subst l. destruct (symbol_eq_dec d p) as [hd | hd]; [contradiction|].
        do 4 eexists. apply RSend with (h := hd).
      * destruct (symbol_eq_dec d p) as [hd | hd]; [|contradiction].
        subst d. destruct Hlive as [x [sq' Htake]].
        do 4 eexists. eapply RReceive; eassumption.
    + destruct (symbol_eq_dec l p) as [pf | neq].
      * subst l. do 4 eexists. apply RAnnounce.
      * destruct Hlive as [x [sq' Htake]].
        do 4 eexists. eapply RHear; eassumption.
  - contradiction.
  - destruct Hlive as [Hf | Ht].
    + destruct (IHF _ _ _ Hf) as (a & t' & s' & sq' & Hstep).
      do 4 eexists. eapply RSilent; [apply SApp | apply RLeft; exact Hstep].
    + destruct (IHT _ _ _ Ht) as (a & t' & s' & sq' & Hstep).
      do 4 eexists. eapply RSilent; [apply SApp | apply RRight; exact Hstep].
  - destruct Hlive as [Ht | [x [Hr Hk]]].
    + destruct (IHT _ _ _ Ht) as (a & t' & s' & sq' & Hstep).
      do 4 eexists. eapply RSilent; [apply SBind | apply RSeq; exact Hstep].
    + destruct (IHK x _ _ _ Hk) as (a & t' & s' & sq' & Hstep).
      do 4 eexists. eapply RSilent; [apply SBind |].
      eapply source_seq_step; [apply code_result_returns; exact Hr | exact
        Hstep].
Qed.

Theorem live_source_step roles p X (t : @cursor M E p X) s sq :
  cursor_live p X t s sq ->
  exists a t' s' sq', role_step model roles X t s sq a t' s' sq'.
Proof.
  induction t as [X o c | X x | X o t | X Y o t IH k | X Y f IHF t IHT];
    intro Hlive; cbn [cursor_live] in Hlive.
  - apply code_live_step. exact Hlive.
  - contradiction.
  - destruct Hlive as [a [t' [s' Hlocal]]].
    do 4 eexists. apply RLocal. exact Hlocal.
  - destruct Hlive as [Ht | [x [Hr Hk]]].
    + destruct (IH Ht) as (a & t' & s' & sq' & Hstep).
      do 4 eexists. apply RSeq. exact Hstep.
    + destruct (code_live_step roles _ _ _ _ _ _ Hk) as (a & t' & s' & sq' &
      Hstep).
      do 4 eexists. eapply source_seq_step;
        [apply result_source_returns; exact Hr | exact Hstep].
  - destruct Hlive as [Hf | Ht].
    + destruct (IHF Hf) as (a & t' & s' & sq' & Hstep).
      do 4 eexists. apply RLeft. exact Hstep.
    + destruct (IHT Ht) as (a & t' & s' & sq' & Hstep).
      do 4 eexists. apply RRight. exact Hstep.
Qed.

Corollary cursor_live_exact roles p X (t : @cursor M E p X) s sq :
  cursor_live p X t s sq <->
  exists a t' s' sq', role_step model roles X t s sq a t' s' sq'.
Proof.
  split; [apply live_source_step |].
  intros (a & t' & s' & sq' & Hstep). eapply source_step_live. exact Hstep.
Qed.

Corollary silent_returns_iff p X (t u : @cursor M E p X) y :
  silent model X t u ->
  (DeadlockSource.returns model t y <-> DeadlockSource.returns model u y).
Proof.
  intro H. rewrite <- !cursor_result_exact. apply silent_result. exact H.
Qed.

Corollary silent_actions_iff roles p X (t u : @cursor M E p X) s sq :
  silent model X t u ->
  ((exists a t' s' sq', role_step model roles X t s sq a t' s' sq') <->
   (exists a u' s' sq', role_step model roles X u s sq a u' s' sq')).
Proof.
  intro H. rewrite <- !cursor_live_exact. apply silent_live. exact H.
Qed.
End Views.
