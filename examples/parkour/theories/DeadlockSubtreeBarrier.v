From Stdlib Require Import Lists.List.
Require Import DeadlockStaticBarrier DeadlockStaticOrigin DeadlockRootHead
  DeadlockChronology DeadlockSource DeadlockNetwork DeadlockFrontiers
  DeadlockCoherence DeadlockMessages DeadlockOrder DeadlockLocal DeadlockRuns
  Control.Monad.Tree Choreography.Choreo2 Parkour.Symbol.
Import ListNotations.

(* [sending] selects the ledger, not a new operational semantics. Absolute
   occurrences retain the dynamic prefix of the actual reached subtree. *)
Definition mandatory_ready {M p B} (sending : bool) R peer (c : Choreo M p B) :=
  if sending then sender_ready R c peer else receiver_ready c peer.

Definition mandatory_packed {M p} sending R peer (c : option (packed M p)) :=
  match c with
  | Some (existT _ _ t) => mandatory_ready sending R peer t
  | None => False
  end.

Definition mandatory_ledger {E S} (sending : bool) R p peer site (a : @source_action E S) :=
  if sending then emits R (p,peer,session_at site Choreography.Network.Root) a
  else receives (peer,p,session_at site Choreography.Network.Root) a.

Section Guard.
Context {M E : Type -> Type} {S : Type}.
Variable m : local_model M E role S.
Variable R : list role.
Variable sending : bool.
Variable p peer : role.
Variable site : occurrence.

Fixpoint mandatory_guard {B} (t : @cursor M E p B) : Prop :=
  match t with
  | Code o c => exists path, site = o ++ path /\
      mandatory_packed sending R peer (descend path c)
  | Seq _ u _ => mandatory_guard u
  | Fork f x => mandatory_guard f \/ mandatory_guard x
  | _ => False
  end.

Lemma mandatory_perf B o (sig : ChoreoSig M p B) :
  mandatory_guard (Code o (Perf sig)) ->
  site = o /\ mandatory_ready sending R peer (Perf sig).
Proof.
  intros ([|edge path] & Eq & Ready).
  - rewrite app_nil_r in Eq; auto.
  - destruct edge; contradiction.
Qed.

Lemma mandatory_future B (t : @cursor M E p B) :
  mandatory_guard t -> future t site.
Proof.
  induction t; cbn [mandatory_guard future]; try tauto.
  intros (path & -> & _); now exists path.
Qed.

Lemma mandatory_silent B t u :
  @silent M E S m p B t u -> mandatory_guard t -> mandatory_guard u.
Proof.
  induction 1; cbn [mandatory_guard] in *; try tauto.
  - intros ([|e path] & Eq & Ready); [destruct sending; contradiction|].
    destruct e; contradiction.
  - intros ([|e path] & Eq & Ready); [destruct sending; contradiction|].
    destruct e; try contradiction.
    exists path. split; [unfold child; now rewrite <- app_assoc|exact Ready].
  - intros ([|e path] & Eq & Ready); [destruct sending; contradiction|].
    destruct e; try contradiction; [left|right]; exists path; split;
      try exact Ready; unfold child; now rewrite <- app_assoc.
  - intros ([|e path] & Eq & Ready); [destruct sending; contradiction|].
    destruct e; contradiction.
  - intros ([|e path] & Eq & Ready); [destruct sending; contradiction|].
    destruct e; contradiction.
  - intros ([|e path] & Eq & Ready).
    + destruct sending; cbn [mandatory_packed descend mandatory_ready sender_ready receiver_ready]
        in Ready; intuition congruence.
    + destruct e; contradiction.
  - intros ([|e path] & Eq & Ready).
    + destruct sending; cbn [mandatory_packed descend mandatory_ready sender_ready receiver_ready]
        in Ready; intuition congruence.
    + destruct e; contradiction.
Qed.

Lemma mandatory_step B t st q a u st' q' :
  @role_step M E S m R p B t st q a u st' q' ->
  mandatory_guard t ->
  In site (mandatory_ledger sending R p peer site a) \/ mandatory_guard u.
Proof.
  intro Step. induction Step; intro Guard; cbn [mandatory_guard] in *;
    try contradiction.
  - destruct (mandatory_perf _ _ _ Guard) as [-> Ready].
    destruct sending; cbn [mandatory_ready sender_ready receiver_ready] in Ready.
    + destruct Ready as [_ [<- Ne]]. left. cbn [mandatory_ledger emits].
      destruct (key_eq_dec _ _); [now left|contradiction].
    + intuition congruence.
  - destruct (mandatory_perf _ _ _ Guard) as [-> Ready].
    destruct sending; cbn [mandatory_ready sender_ready receiver_ready] in Ready.
    + intuition congruence.
    + destruct Ready as [<- _]. left. cbn [mandatory_ledger receives].
      destruct (key_eq_dec _ _); [now left|contradiction].
  - destruct (mandatory_perf _ _ _ Guard) as [-> Ready].
    destruct sending; cbn [mandatory_ready sender_ready receiver_ready] in Ready.
    + destruct Ready as [_ [Ne Member]]. left.
      cbn [mandatory_ledger emits]. unfold key_paths, announcement_messages.
      apply in_map_iff.
      exists (Message unit ChoiceDelivery o p peer tt Parkour.Codec.show_unit).
      split; [reflexivity|]. apply filter_In; split.
      * apply in_map_iff. exists peer; split; [reflexivity|].
        apply filter_In; split; [exact Member|].
        destruct (role_eq_dec peer p); [congruence|reflexivity].
      * cbn [message_key]. destruct (key_eq_dec _ _); [reflexivity|contradiction].
    + intuition congruence.
  - destruct (mandatory_perf _ _ _ Guard) as [-> Ready].
    destruct sending; cbn [mandatory_ready sender_ready receiver_ready] in Ready.
    + intuition congruence.
    + destruct Ready as [<- _]. left. cbn [mandatory_ledger receives].
      destruct (key_eq_dec _ _); [now left|contradiction].
  - destruct (IHStep Guard); auto.
  - destruct Guard as [Guard|Guard]; [destruct (IHStep Guard)|]; auto.
  - destruct Guard as [Guard|Guard]; [|destruct (IHStep Guard)]; auto.
  - apply IHStep. eapply mandatory_silent; eassumption.
Qed.

Lemma mandatory_run A start tr finish :
  @DeadlockSource.crun M E S m R A start tr finish ->
  mandatory_guard (positions start p) ->
  In site (flat_map (mandatory_ledger sending R p peer site) tr) \/
  mandatory_guard (positions finish p).
Proof.
  induction 1 as [s|s tr middle a finish Run IH Step]; intro Guard.
  - right; exact Guard.
  - rewrite flat_map_app. destruct (IH Guard) as [Issued|Now].
    + left; apply in_or_app; auto.
    + destruct Step as [who act u Member Act Frame].
      destruct (role_eq_dec who p) as [->|Ne].
      * destruct (mandatory_step _ _ _ _ _ _ _ _ Act Now) as [Issued|Rest].
        -- left; apply in_or_app; right. cbn; now rewrite app_nil_r.
        -- right; exact Rest.
      * right; rewrite <- Frame by congruence; exact Now.
Qed.
End Guard.

Lemma mandatory_sender_guard {M E} R p peer site B (t : @cursor M E p B) :
  mandatory_guard R true p peer site t <-> guarding R p peer site t.
Proof.
  induction t; cbn [mandatory_guard guarding]; tauto.
Qed.

Lemma mandatory_ledger_path {E S} sending R p peer site z (a : @source_action E S) :
  In z (mandatory_ledger sending R p peer site a) -> z = action_path a.
Proof.
  destruct sending; cbn [mandatory_ledger].
  - apply emitted_path.
  - destruct a; cbn [receives]; try contradiction;
      destruct (key_eq_dec _ _); cbn; intuition congruence.
Qed.

(* Start is an arbitrary reached cut. Its enclosing occurrence may contain
   BindBody or ChoiceBody. Only descent WITHIN the current subtree is static. *)
Theorem subtree_predecessor_history {M E S}
    (m : local_model M E role S) R sending A start tr finish p peer site root
    st q a u st' q' :
  @DeadlockSource.crun M E S m R A start tr finish ->
  mandatory_guard R sending p peer site (positions start p) ->
  scoped root (positions start p) ->
  role_step m R (A p) (positions finish p) st q a u st' q' ->
  consuming a -> source_before site (action_path a) ->
  In site (flat_map (mandatory_ledger sending R p peer site) tr).
Proof.
  intros Run Guard Scope Step Consume Before.
  destruct (mandatory_run m R sending p peer site A _ _ _ Run Guard) as [Issued|Now];
    [exact Issued|].
  destruct (mandatory_step m R sending p peer site _ _ _ _ _ _ _ _ Step Now)
    as [Issued|Rest].
  - apply mandatory_ledger_path in Issued. subst site.
    exfalso; exact (source_before_irreflexive _ Before).
  - exfalso.
    pose proof (run_role_scoped m R A _ _ _ p root Run Scope) as Bound.
    exact (proj2 (role_consumes m R p _ _ _ _ _ _ _ _ Step root Bound
      Consume site (mandatory_future R sending p peer site _ u Rest)) Before).
Qed.

Theorem subtree_predecessor_cstep {M E S}
    (m : local_model M E role S) R sending A start tr finish p peer site root a after :
  @DeadlockSource.crun M E S m R A start tr finish ->
  mandatory_guard R sending p peer site (positions start p) ->
  scoped root (positions start p) ->
  cstep m R finish a after -> action_actor a = p ->
  consuming a -> source_before site (action_path a) ->
  In site (flat_map (mandatory_ledger sending R p peer site) tr).
Proof.
  intros Run Guard Scope [who act u Member Step Frame] Actor Consume Before.
  pose proof (role_step_actor m R _ _ _ _ _ _ _ _ _ Step) as Who.
  rewrite Actor in Who; subst who.
  eapply subtree_predecessor_history; eassumption.
Qed.

Print Assumptions subtree_predecessor_history.
Print Assumptions subtree_predecessor_cstep.

Lemma mandatory_plug_future {M E p B A}
    (C : @cursor_context M E p B A) (t : @cursor M E p B) b :
  future t b -> future (plug C t) b.
Proof.
  induction C; cbn; intro F;
    first [exact F|left; now apply IHC|right; now apply IHC].
Qed.

(* A coarse future region does not identify a poised action. An actual
   focused Perf does: another live Fork branch cannot be its predecessor. *)
Lemma mandatory_not_before_focus {M E} R sending p peer site B A
    (C : @cursor_context M E p B A) b (sig : ChoreoSig M p B) root :
  scoped root (plug C (Code b (Perf sig))) ->
  mandatory_guard R sending p peer site (plug C (Code b (Perf sig))) ->
  ~ source_before site b.
Proof.
  revert root. induction C; intros root Scope Guard Before.
  - destruct (mandatory_perf R sending p peer site _ _ _ Guard) as [-> _].
    exact (source_before_irreflexive _ Before).
  - cbn in Scope, Guard. destruct Scope as [_ Scope].
    eapply IHC; eassumption.
  - cbn in Scope, Guard. destruct Scope as (v & Bound & Sf & Sx).
    destruct Guard as [Guard|Guard].
    + eapply IHC; eassumption.
    + assert (Fresh : fresh_after b site).
      { eapply siblings_fresh with (o := v) (e := AppFunction) (f := AppArgument).
        - discriminate.
        - left; discriminate.
        - eapply scoped_future; [exact Sf|].
          apply mandatory_plug_future. apply extends_refl.
        - eapply scoped_future; [exact Sx|].
          eapply mandatory_future; exact Guard. }
      exact (proj2 Fresh Before).
  - cbn in Scope, Guard. destruct Scope as (v & Bound & Sf & Sx).
    destruct Guard as [Guard|Guard].
    + assert (Fresh : fresh_after b site).
      { eapply siblings_fresh with (o := v) (e := AppArgument) (f := AppFunction).
        - discriminate.
        - left; discriminate.
        - eapply scoped_future; [exact Sx|].
          apply mandatory_plug_future. apply extends_refl.
        - eapply scoped_future; [exact Sf|].
          eapply mandatory_future; exact Guard. }
      exact (proj2 Fresh Before).
    + eapply IHC; eassumption.
Qed.

Theorem subtree_predecessor_poised {M E S}
    (m : local_model M E role S) R sending A start tr finish p peer site root
    B (C : @cursor_context M E p B (A p)) b (sig : ChoreoSig M p B) :
  @DeadlockSource.crun M E S m R A start tr finish ->
  mandatory_guard R sending p peer site (positions start p) ->
  scoped root (positions start p) ->
  silent_prefix m (positions finish p) (plug C (Code b (Perf sig))) ->
  source_before site b ->
  In site (flat_map (mandatory_ledger sending R p peer site) tr).
Proof.
  intros Run Guard Scope Sil Before.
  destruct (mandatory_run m R sending p peer site A _ _ _ Run Guard)
    as [Issued|Now]; [exact Issued|].
  exfalso.
  assert (Bound : scoped root (positions finish p)).
  { eapply run_role_scoped; eassumption. }
  assert (End : scoped root (plug C (Code b (Perf sig))) /\
      mandatory_guard R sending p peer site (plug C (Code b (Perf sig)))).
  { clear -Bound Now Sil. induction Sil; [auto|].
    apply IHSil.
    - eapply mandatory_silent; eassumption.
    - eapply silent_scoped; eassumption. }
  destruct End as [BoundEnd GuardEnd].
  exact (mandatory_not_before_focus R sending p peer site B (A p) C b sig root
    BoundEnd GuardEnd Before).
Qed.

Print Assumptions subtree_predecessor_poised.
