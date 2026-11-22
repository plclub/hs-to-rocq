Require Import DeadlockLocal DeadlockState DeadlockStateExpect.

Lemma shared_model_exact {M E Role Store Input}
    (m : local_model M E Role (Store * Input)) :
  state_contract m (shared_model m).
Proof. split; intros; reflexivity. Qed.
