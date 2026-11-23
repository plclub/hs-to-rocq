From ParkourTheories Require Import Semantics.Runs
  Tests.Semantics.FiniteRunContracts.

Section Cases.
Context {S A : Type}.
Variable step : S -> A -> S -> Prop.
Variable final : S -> Prop.

Lemma ready_exact : ready_equation step final (ready step final).
Proof. intros s. reflexivity. Qed.

Lemma stuck_exact : stuck_equation step final (stuck step final).
Proof. intros s. reflexivity. Qed.

Lemma DF_exact : DF_equation step final (finite_run step) (deadlock_free step
  final).
Proof. intros s. reflexivity. Qed.

Lemma run_empty_exact : run_empty (finite_run step).
Proof.
  intros s y. split.
  - exact (run_nil step s y).
  - intros H. subst y. exact (RunRefl step s).
Qed.

Definition run_extension_exact : run_extension step (finite_run step) :=
  run_snoc_iff step.

Definition run_composition_exact : run_composition (finite_run step) :=
  run_append_iff step.
End Cases.
