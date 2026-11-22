From Stdlib Require Import Lists.List.
From ITree Require Import ITree.
Require Import DeadlockLocal DeadlockSource DeadlockSourceExpect DeadlockSourceExtraExpect.
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
  eapply RHear; [discriminate | apply TakeHead].
Qed.
