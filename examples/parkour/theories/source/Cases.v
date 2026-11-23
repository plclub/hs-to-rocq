From Stdlib Require Import Lists.List.
From ITree Require Import ITree.
Require Import DeadlockLocal DeadlockRuns DeadlockSource DeadlockSourceExpect
  DeadlockSourceExtraExpect.
Require Import DeadlockSourceOccurrenceExpect.
Require DeadlockWellFormed.
Import ListNotations.

(* Queue rejection does not depend on source well-formedness or projection. *)
Lemma fifo : fifo_contract.
Proof.
  intros q' H. inversion H; subst; try discriminate.
  match goal with
  | Hblocked : ~ same_channel _ _ _ _ _ |- _ =>
      apply Hblocked; repeat split; reflexivity
  end.
Qed.

Lemma independent_action : independent_contract.
Proof.
  eexists. unfold independent.
  eapply RSilent; [apply SBind |].
  eapply RSilent; [apply SSeqUnder; apply SLocalOther; discriminate |].
  eapply RSilent; [apply SSeq |].
  eapply RSilent; [apply SLocalStart |].
  apply RLocal.
  eapply LocalStep with (e := Act) (x := true) (s' := 0).
  - apply ViewNow. reflexivity.
  - split; reflexivity.
  Unshelve. discriminate.
Qed.

Lemma parallel_action : parallel_contract.
Proof.
  eexists. unfold parallel.
  eapply RSilent; [apply SApp |].
  apply RRight.
  eapply RSilent; [apply SLocalStart |].
  apply RLocal.
  eapply LocalStep with (e := Act) (x := true) (s' := 0).
  - apply ViewNow. reflexivity.
  - split; reflexivity.
Qed.

Lemma sends : sends_contract.
Proof.
  do 2 eexists. split.
  - unfold two_sends.
    eapply RSilent; [apply SBind |].
    apply RSeq. apply RSend.
  - eapply RSilent; [apply SSeq |].
    apply RSend.
  Unshelve. all: discriminate.
Qed.

Lemma receive_blocks : receive_blocks_contract.
Proof.
  intros a t' s' q' H.
  eapply empty_queue_barrier; [exact H | reflexivity |].
  split; [discriminate | reflexivity].
Qed.

Lemma forward_blocks : forward_blocks_contract.
Proof.
  intros a t' s' q' H.
  eapply empty_queue_barrier; [exact H | reflexivity |].
  split; [discriminate | reflexivity].
Qed.

Lemma self_other : self_other_contract.
Proof. unfold self_other_contract. intros. apply SCommSelf. Qed.

Lemma one_role_announcement : one_role_announcement_contract.
Proof. apply RAnnounce. Qed.

Lemma multi_role_announcement : multi_role_announcement_contract.
Proof. apply RAnnounce. Qed.

Lemma separate_hear : separate_hear_contract.
Proof.
  eapply RHear; [discriminate | apply TakeAtHead].
Qed.

Lemma occurrence_exact : occurrence_exact_contract.
Proof.
  unfold occurrence_exact_contract. intros X k o s d x q q'. split.
  - apply take_at_split.
  - intros [front [back [-> ->]]].
    induction front as [|v front IH]; cbn.
    + apply TakeAtHead.
    + apply TakeAtOther. exact IH.
Qed.

Lemma old_take_inclusion : old_take_inclusion_contract.
Proof. exact @take_pending_at. Qed.

Definition test_cursors p := @cursor (ITreeDefinition.itree request) request p
  (result_family p).
Definition after_first_cursor : test_cursors A :=
  Seq [] (Returned (off_at (X := bool) B_not_A))
    (fun _ => comm A A B (located false)).
Definition after_last_cursor : test_cursors A :=
  Returned (off_at (X := bool) B_not_A).

Lemma replace_A_other {T} (v : T A) old p :
  p <> A -> replace_A v old p = old p.
Proof.
  intros H. unfold replace_A.
  destruct (List.list_eq_dec BinNat.N.eq_dec A p); [congruence | reflexivity].
Qed.

Lemma first_source_send (c : forall p, Choreo2.Choreo (itree request) p
  (result_family p)) :
  c A = good_family A ->
  cstep model roles (start c) send_true (sent_once c).
Proof.
  intros HA. eapply CStep with (p := A).
  - cbn. auto.
  - change (role_step model roles (result_family A)
      (Code [] (c A)) 0 [] send_true after_first_cursor 0
      [Pending bool DataDelivery first_path A B true]).
    rewrite HA. unfold good_family, send_true, after_first_cursor.
    eapply RSilent; [apply SBind |]. apply RSeq. apply RSend.
  - intros r H.
    change (positions _ (start c) r =
      @replace_A test_cursors after_first_cursor (positions _ (start c)) r).
    symmetry. exact (@replace_A_other test_cursors _ _ r H).
Qed.

Lemma second_source_send (c : forall p, Choreo2.Choreo (itree request) p
  (result_family p)) :
  cstep model roles (sent_once c) send_false (sent_twice c).
Proof.
  eapply CStep with (p := A).
  - cbn. auto.
  - cbn. eapply RSilent; [apply SSeq |].
    apply RSend with (h := B_not_A).
  - intros r H.
    change (@replace_A test_cursors after_first_cursor (positions _ (start c)) r
      =
      @replace_A test_cursors after_last_cursor (positions _ (start c)) r).
    transitivity (positions _ (start c) r).
    + exact (@replace_A_other test_cursors _ _ r H).
    + symmetry. exact (@replace_A_other test_cursors _ _ r H).
Qed.

Lemma two_source_sends (c : forall p, Choreo2.Choreo (itree request) p
  (result_family p)) :
  c A = good_family A ->
  crun model roles (start c) [send_true; send_false] (sent_twice c).
Proof.
  intros HA.
  change (crun model roles (start c) ([send_true] ++ [send_false]) (sent_twice
    c)).
  eapply RunSnoc; [|exact (second_source_send c)].
  change (crun model roles (start c) ([] ++ [send_true]) (sent_once c)).
  eapply RunSnoc; [constructor | apply first_source_send; exact HA].
Qed.

Lemma delayed_run : delayed_run_contract.
Proof. apply two_source_sends. reflexivity. Qed.

Lemma discrepancy_run : discrepancy_run_contract.
Proof. apply two_source_sends. reflexivity. Qed.

Lemma delayed_second_negative : delayed_second_negative_contract.
Proof.
  intros c' H. inversion H as [p a c'' Hp Hstep Hothers]; subst.
  pose proof (role_step_actor model roles _ _ _ _ _ _ _ _ _ Hstep) as Hactor.
  change (B = p) in Hactor. subst p.
  pose proof (waiting_action_at model roles _ _ _ _ _ _ _ _ _ Hstep first_path)
    as Hpos.
  assert (Hwait : waiting_at_cursor
      (positions _ (sent_twice good_family) B) first_path).
  { cbn. repeat split; discriminate. }
  specialize (Hpos Hwait). discriminate.
Qed.

Definition replace_B {T : Symbol.Symbol -> Type} (v : T B) (old : forall p, T p)
  p : T p :=
  match List.list_eq_dec BinNat.N.eq_dec B p with
  | left e => eq_rect B T v p e
  | right _ => old p
  end.

Lemma replace_B_other {T} (v : T B) old p :
  p <> B -> replace_B v old p = old p.
Proof.
  intros H. unfold replace_B.
  destruct (List.list_eq_dec BinNat.N.eq_dec B p); [congruence | reflexivity].
Qed.

Lemma receive_B_after_two
    (c : forall p, Choreo2.Choreo (itree request) p (result_family p)) a t' q' :
  role_step model roles (result_family B) (Code [] (c B)) 0 two_pending a t' 0
    q' ->
  exists c', cstep model roles (sent_twice c) a c' /\ deliveries _ c' = q'.
Proof.
  intros Hstep.
  exists ({| positions := @replace_B test_cursors t' (positions _ (sent_twice
    c));
             shared_store := 0; deliveries := q' |} : state_type).
  split; [|reflexivity]. eapply CStep with (p := B).
  - cbn. auto.
  - exact Hstep.
  - intros r H.
    change (positions _ (sent_twice c) r =
      @replace_B test_cursors t' (positions _ (sent_twice c)) r).
    symmetry. exact (@replace_B_other test_cursors _ _ r H).
Qed.

Lemma delayed_first_positive : delayed_first_positive_contract.
Proof.
  eapply receive_B_after_two.
  unfold good_family, receive_true.
  eapply RSilent; [apply SBind |]. apply RSeq.
  eapply RReceive; [discriminate | apply TakeAtHead].
Qed.

Lemma discrepancy_receive : discrepancy_receive_contract.
Proof.
  eapply receive_B_after_two.
  cbn [bad_family].
  eapply RSilent; [apply SBind |].
  eapply RSilent; [apply SSeqUnder; apply SCommSelf |].
  eapply RSilent; [apply SSeq |].
  eapply RReceive; [discriminate |].
  apply TakeAtOther. apply TakeAtHead.
Qed.

Lemma discrepancy_old_rejects : discrepancy_old_rejects_contract.
Proof. exact fifo. Qed.

Fixpoint leading_communication {M p X} (c : Choreo2.Choreo M p X)
    : option (Symbol.Symbol * Symbol.Symbol) :=
  match c with
  | Tree.Perf (@Choreo2.Comm _ _ _ l d _ _ _ _ _ _ _) => Some (l,d)
  | Tree.Bind t _ => leading_communication t
  | _ => None
  end.

Lemma structural_leading R M S X c Q :
  DeadlockWellFormed.structural R M S X c Q ->
  forall p q (s : S p) (t : S q),
    leading_communication (c p s) = leading_communication (c q t).
Proof.
  intros H. induction H; intros p q ps qt;
    repeat match goal with
    | E : forall p s, _ = _ |- _ => rewrite (E p ps), (E q qt)
    end; cbn; try reflexivity.
  apply IHstructural.
Qed.

Lemma discrepancy_not_wf : discrepancy_not_wf_contract.
Proof.
  intros [_ [Q H]].
  pose proof (structural_leading _ _ _ _ _ _ H A B
    (or_introl eq_refl) (or_intror (or_introl eq_refl))) as E.
  change (Some (A,B) = Some (A,A)) in E. discriminate.
Qed.

Lemma delayed_wf : delayed_wf_contract.
Proof.
  split.
  - repeat constructor; cbn; intuition discriminate.
  - eexists. eapply DeadlockWellFormed.WFBind with
      (t := fun p _ => comm p A B (located true))
      (k := fun p _ (_ : Choreo2.At bool B p) => comm p A B (located false)).
    + eapply DeadlockWellFormed.WFComm with (l := A) (r := B)
        (x := fun p _ => located true)
        (sh := fun _ _ => DeadlockSourceExpect.show_bool)
        (rd := fun _ _ => DeadlockSourceExpect.read_bool).
      * cbn; auto.
      * cbn; auto.
      * intros s t Hne []; reflexivity.
      * intros; reflexivity.
    + intros D v inc HP.
      eapply DeadlockWellFormed.WFComm with (l := A) (r := B)
        (x := fun p _ => located false)
        (sh := fun _ _ => DeadlockSourceExpect.show_bool)
        (rd := fun _ _ => DeadlockSourceExpect.read_bool).
      * cbn; auto.
      * cbn; auto.
      * intros s t Hne []; reflexivity.
      * intros; reflexivity.
    + intros; reflexivity.
Qed.
