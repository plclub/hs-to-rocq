From ITree Require Import ITree.
Require Import DeadlockLocal DeadlockLocalExpect.

Lemma finite_return : finite_return_contract.
Proof.
  intros n. induction n as [|n IH].
  - apply ViewNow. reflexivity.
  - eapply ViewTau; [reflexivity | exact IH].
Qed.

Lemma finite_action : finite_action_contract.
Proof.
  intros n. apply (LocalStep _ _ _ _ _ Get
    (fun b : bool => Ret (if b then 11 else 22)) true 4).
  - induction n as [|n IH].
    + apply ViewNow. reflexivity.
    + eapply ViewTau; [reflexivity | exact IH].
  - repeat split; reflexivity.
Qed.

Lemma one_event : one_event_contract.
Proof.
  apply (LocalStep _ _ _ _ _ Get (fun _ : bool => ask) true 4).
  - apply ViewNow. reflexivity.
  - repeat split; reflexivity.
Qed.

Lemma untick {A} n (t : itree request A) v :
  (forall u, v <> TauF u) ->
  local_view (ticks n t) v -> local_view t v.
Proof.
  intros Hnot. induction n as [|n IH]; intros H.
  - exact H.
  - inversion H as [t0 v0 Heq | t0 u v0 Heq Hv]; subst.
    + exfalso. apply (Hnot (ticks n t)). reflexivity.
    + cbn in Heq. injection Heq as Heq. subst u. apply IH. exact Hv.
Qed.

Lemma visible_view v :
  local_view ask v -> observe ask = v.
Proof.
  intros H. inversion H; subst; [reflexivity | discriminate].
Qed.

Lemma no_reply p s :
  (forall X (e : request X) x s', ~ reply X p e s x s') ->
  forall n a t s', ~ local_step reply p (ticks n ask) s a t s'.
Proof.
  intros Hnone n a t s' H. destruct H.
  eapply Hnone. eassumption.
Qed.

Lemma blocked_store : blocked_store_contract.
Proof.
  unfold blocked_store_contract. intros n a t s.
  apply (no_reply 7 0). intros X e x s' H. destruct e.
  unfold reply in H. destruct H as [_ [H _]]. discriminate.
Qed.

Lemma blocked_role : blocked_role_contract.
Proof.
  unfold blocked_role_contract. intros n a t s.
  apply (no_reply 8 3). intros X e x s' H. destruct e.
  unfold reply in H. destruct H as [H _]. discriminate.
Qed.

Definition true_reply (a : local_event request nat nat) : Prop :=
  match a with
  | LocalEvent _ e _ x _ =>
      match e in request X return X -> Prop with
      | Get => fun b => b = true
      end x
  end.

Lemma step_true_reply p (t : itree request nat) s a t' s' :
  local_step reply p t s a t' s' -> true_reply a.
Proof.
  intros H. destruct H as [X e k x s' Hv Hr].
  destruct e. exact (proj1 (proj2 (proj2 Hr))).
Qed.

Lemma no_invented_reply : no_invented_reply_contract.
Proof.
  intros H. apply step_true_reply in H. discriminate.
Qed.

Lemma visible_not_return : visible_not_return_contract.
Proof.
  intros n x H. unfold local_return in H.
  apply untick in H; [|intros u; discriminate].
  apply visible_view in H. discriminate.
Qed.

Lemma return_not_action : return_not_action_contract.
Proof.
  intros n a t s H. destruct H as [X e k x s' Hv Hr].
  apply untick in Hv; [|intros u; discriminate].
  inversion Hv; discriminate.
Qed.

Lemma forever_only_tau v :
  local_view forever v -> exists u, v = TauF u.
Proof.
  intros H. remember forever as t eqn:Ht.
  induction H as [t v Hobs | t u v Hobs Hv IH].
  - subst t. exists forever. symmetry. exact Hobs.
  - subst t. cbn in Hobs. injection Hobs as Hu.
    apply IH. symmetry. exact Hu.
Qed.

Lemma infinite_not_return : infinite_not_return_contract.
Proof.
  intros x H. destruct (forever_only_tau _ H) as [u Hu]. discriminate.
Qed.

Lemma infinite_not_action : infinite_not_action_contract.
Proof.
  intros a t s H. destruct H as [X e k x s' Hv Hr].
  destruct (forever_only_tau _ Hv) as [u Hu]. discriminate.
Qed.

Lemma typed_trace : typed_trace_contract.
Proof.
  exact @local_step_typed_trace.
Qed.

Lemma view_exact : view_exact_contract.
Proof.
  intros E A t v. split; intros H; induction H.
  - apply ExpectedNow. assumption.
  - eapply ExpectedTau; eassumption.
  - apply ViewNow. assumption.
  - eapply ViewTau; eassumption.
Qed.
