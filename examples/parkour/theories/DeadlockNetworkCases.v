From ITree Require Import ITree.
From Stdlib Require Import Lists.List.
Require Import DeadlockLocal DeadlockNetwork DeadlockNetworkExpect.
Require Import Control.Monad.Tree Choreography.Network Parkour.Codec.
Require Import DeadlockNetworkMoreExpect.
Require Import DeadlockNetworkSilentExpect.
Import ListNotations.

Lemma send_first : send_first_contract.
Proof. apply StepSend. Qed.

Lemma receive_exact : receive_exact_contract.
Proof.
  apply StepRecv.
  - apply enqueue_same.
  - reflexivity.
Qed.

Lemma left_send : left_send_contract.
Proof. apply StepLeft. apply StepBind. apply StepSend. Qed.

Lemma right_send : right_send_contract.
Proof. apply StepRight. apply StepSend. Qed.

Lemma two_receive : two_receive_contract.
Proof.
  intros a t q s H. apply step_possible in H.
  cbn in H. destruct H as [[H | [x [Hr H]]] | H].
  - destruct H as [w [ws [x [H _]]]]. discriminate.
  - apply returns_shape in Hr. contradiction.
  - destruct H as [w [ws [x [H _]]]]. discriminate.
Qed.

Lemma fifo : fifo_contract.
Proof. unfold fifo_contract. repeat rewrite enqueue_same. reflexivity. Qed.

Lemma pure_join : pure_join_contract.
Proof.
  eapply ReturnBind.
  - eapply ReturnApp; apply ReturnPure.
  - apply ReturnPure.
Qed.

Lemma pure_no_action : pure_no_action_contract.
Proof. intros a t q s H. apply step_possible in H. exact H. Qed.

Lemma set_event s :
  local_step flag_reply alice set s
    (LocalEvent alice SetFlag s tt true) (Ret tt) true.
Proof.
  apply (LocalStep _ _ _ _ _ SetFlag (fun _ : unit => Ret tt) tt true).
  - apply ViewNow. reflexivity.
  - reflexivity.
Qed.

Lemma wait_event :
  local_step flag_reply alice wait true
    (LocalEvent alice Wait true tt true) (Ret tt) true.
Proof.
  apply (LocalStep _ _ _ _ _ Wait (fun _ : unit => Ret tt) tt true).
  - apply ViewNow. reflexivity.
  - split; reflexivity.
Qed.

Lemma shared_right : shared_right_contract.
Proof.
  unfold shared_right_contract. cbn.
  do 2 eexists. split.
  - apply StepRight. apply StepExec. apply set_event.
  - apply StepLeft. apply StepRight. apply StepExec. apply wait_event.
Qed.

Lemma shared_left : shared_left_contract.
Proof.
  unfold shared_left_contract. cbn.
  do 2 eexists. split.
  - apply StepLeft. apply StepRight. apply StepExec. apply set_event.
  - apply StepRight. apply StepExec. apply wait_event.
Qed.

Lemma both_sends : both_sends_contract.
Proof.
  split; eexists.
  - apply StepLeft. apply StepBind. apply StepSend.
  - apply StepRight. apply StepSend.
Qed.

Lemma wrong_session : wrong_session_contract.
Proof.
  intros a t q s H. apply step_possible in H.
  cbn in H. destruct H as [w [ws [x [H _]]]]. discriminate.
Qed.

Lemma wrong_sender : wrong_sender_contract.
Proof.
  intros a t q s H. apply step_possible in H.
  cbn in H. destruct H as [w [ws [x [H _]]]]. discriminate.
Qed.

Lemma wrong_receiver : wrong_receiver_contract.
Proof.
  intros a t q s H. apply step_possible in H.
  cbn in H. destruct H as [w [ws [x [H _]]]]. discriminate.
Qed.

Lemma bad_head : bad_head_contract.
Proof.
  intros a t q s H. apply step_possible in H.
  cbn in H. destruct H as [w [ws [x [H Hd]]]].
  injection H as Hw Hws. subst w. discriminate.
Qed.

Lemma announcement : announcement_contract.
Proof. split; [apply StepBCast | repeat split; reflexivity]. Qed.

Lemma singleton_announcement : singleton_announcement_contract.
Proof. intros k. reflexivity. Qed.

Lemma orphan_stuck : orphan_contract.
Proof.
  split.
  - apply (orphan_not_final flag_model orphan (alice,bob,Root)
      (@show bool show_bool true) []). apply enqueue_same.
  - intros a n H. apply nstep_possible in H. cbn in H. tauto.
Qed.

Lemma two_roles_ready : two_roles_contract.
Proof.
  split; eexists.
  - apply (Schedule _ _ [] [_]). apply StepSend.
  - apply (Schedule _ _ [_] []). apply StepSend.
Qed.

Lemma spin_only_tau v :
  local_view spin v -> exists u, v = TauF u.
Proof.
  intros H. remember spin as t eqn:Ht.
  induction H as [t v Hobs | t u v Hobs Hv IH].
  - subst t. exists spin. symmetry. exact Hobs.
  - subst t. cbn in Hobs. injection Hobs as Hu.
    apply IH. symmetry. exact Hu.
Qed.

Lemma spin_no_event p s a t s' :
  ~ local_step flag_reply p spin s a t s'.
Proof.
  intros H. destruct H as [X e k x s' Hv Hr].
  destruct (spin_only_tau _ Hv) as [u Hu]. discriminate.
Qed.

Lemma spin_silent : spin_contract.
Proof.
  split.
  - intros a t q s H. apply step_possible in H.
    cbn in H. destruct H as [a' [t' [s' H]]].
    eapply spin_no_event. exact H.
  - intros x H. apply returns_shape in H.
    destruct H as [y Hy]. destruct (spin_only_tau _ Hy) as [u Hu]. discriminate.
Qed.

Lemma returned_no_event p s a t s' :
  ~ local_step flag_reply p (Tau (Ret tt)) s a t s'.
Proof.
  intros H. destruct H as [X e k x s' Hv Hr].
  inversion Hv as [t0 v Hobs | t0 u v Hobs Hu]; subst; [discriminate |].
  cbn in Hobs. injection Hobs as Heq. subst u.
  inversion Hu; discriminate.
Qed.

Lemma local_return_silent : local_return_contract.
Proof.
  split.
  - apply ReturnLocal. eapply ViewTau; [reflexivity |].
    apply ViewNow. reflexivity.
  - intros a t q s H. apply step_possible in H.
    cbn in H. destruct H as [a' [t' [s' H]]].
    eapply returned_no_event. exact H.
Qed.

Lemma wait_not_return x : ~ done (CLocal wait) x.
Proof.
  intros H. apply returns_shape in H. destruct H as [y Hy].
  inversion Hy; discriminate.
Qed.

Lemma one_event_only : one_event_only_contract.
Proof.
  split.
  - apply StepExec.
    apply (LocalStep _ _ _ _ _ SetFlag (fun _ : unit => wait) tt true).
    + apply ViewNow. reflexivity.
    + reflexivity.
  - split.
    + exact wait_not_return.
    + apply StepLocal. apply wait_event.
Qed.

Lemma bookkeeping : bookkeeping_contract.
Proof.
  split; [exact pure_join |].
  intros a t q s H. apply step_possible in H. cbn in H. firstorder.
Qed.

Lemma after_bookkeeping : after_bookkeeping_contract.
Proof.
  eapply StepContinue; [exact pure_join | apply StepSend].
Qed.

Lemma wait_blocked : wait_blocked_contract.
Proof.
  intros a t q s H. apply step_possible in H. cbn in H.
  destruct H as [a' [t' [s' H]]].
  destruct H as [X e k x s' Hv Hr]. destruct e.
  - destruct Hr as [H _]. discriminate.
  - inversion Hv; discriminate.
Qed.

Lemma empty_endpoints : empty_endpoints_contract.
Proof.
  split.
  - intros [H _]. inversion H as [|e es He Hrest]; subst.
    destruct He as [x Hr]. apply returns_shape in Hr. exact Hr.
  - intros a n H. apply nstep_possible in H. cbn in H.
    destruct H as [[w [ws [x [H _]]]] | [[w [ws [x [H _]]]] | H]];
      discriminate || contradiction.
Qed.

Lemma all_finished : finished_contract.
Proof.
  split.
  - constructor; [|constructor]. exists 6. exact pure_join.
  - intros k. reflexivity.
Qed.
