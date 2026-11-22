From ITree Require Import ITree.
Require Import DeadlockLocal DeadlockLocalExpect DeadlockLocalCases
  DeadlockLocalExactExpect.

Lemma return_exact : return_exact_contract.
Proof.
  intros E A t x. apply view_exact.
Qed.

Lemma step_exact : step_exact_contract.
Proof.
  intros E Role Store A r p t s a t' s'. split.
  - intros H. apply local_step_typed_trace in H.
    destruct H as [X [e [x [k [Hv [Hr [Ha Ht]]]]]]].
    exists X, e, x, k. repeat split; try assumption.
    apply view_exact. exact Hv.
  - intros [X [e [x [k [Hv [Hr [Ha Ht]]]]]]].
    subst a t'. apply LocalStep.
    + apply view_exact. exact Hv.
    + exact Hr.
Qed.
