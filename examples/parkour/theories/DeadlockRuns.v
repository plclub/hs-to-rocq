From Stdlib Require Import Lists.List.
Import ListNotations.

(* Internal relational glue only. These definitions assert no relationship
   between choreography semantics and generated endpoints. Lists record actions
   in execution order; induction extends a completed prefix by one action. *)
Section Runs.
Context {S A : Type}.
Variable step : S -> A -> S -> Prop.

Inductive finite_run : S -> list A -> S -> Prop :=
| RunRefl s : finite_run s [] s
| RunSnoc s tr x a y :
    finite_run s tr x -> step x a y ->
    finite_run s (tr ++ [a]) y.

Lemma run_nil s y : finite_run s [] y -> s = y.
Proof.
  intros H. remember [] as tr eqn:Heq in H.
  destruct H as [s | s tr x a y Hrun Hstep]; [reflexivity |].
  destruct tr; discriminate.
Qed.

Lemma run_snoc_iff s tr a y :
  finite_run s (tr ++ [a]) y <->
  exists x, finite_run s tr x /\ step x a y.
Proof.
  split.
  - intros H. remember (tr ++ [a]) as trace eqn:Heq in H.
    destruct H as [s | s prefix x b y Hrun Hstep].
    + destruct tr; discriminate.
    + apply app_inj_tail in Heq. destruct Heq as [-> ->].
      exists x. split; assumption.
  - intros [x [Hrun Hstep]]. exact (RunSnoc s tr x a y Hrun Hstep).
Qed.

Lemma run_singleton s a y :
  finite_run s [a] y <-> step s a y.
Proof.
  change (finite_run s ([] ++ [a]) y <-> step s a y).
  rewrite run_snoc_iff. split.
  - intros [x [Hrun Hstep]]. apply run_nil in Hrun. subst x. exact Hstep.
  - intros H. exists s. split; [constructor | exact H].
Qed.

Lemma run_append s tr x tr' y :
  finite_run s tr x -> finite_run x tr' y ->
  finite_run s (tr ++ tr') y.
Proof.
  intros Hprefix Hsuffix. induction Hsuffix as
    [x | x suffix z a y Hsuffix IH Hstep].
  - rewrite app_nil_r. exact Hprefix.
  - rewrite app_assoc.
    exact (RunSnoc s (tr ++ suffix) z a y (IH Hprefix) Hstep).
Qed.

Lemma run_append_iff s tr tr' y :
  finite_run s (tr ++ tr') y <->
  exists x, finite_run s tr x /\ finite_run x tr' y.
Proof.
  split.
  - revert y. induction tr' as [| a suffix IH] using rev_ind; intros y H.
    + rewrite app_nil_r in H. exists y. split; [exact H | constructor].
    + rewrite app_assoc in H. apply run_snoc_iff in H.
      destruct H as [z [Hprefix Hstep]].
      destruct (IH z Hprefix) as [x [Hleft Hright]].
      exists x. split; [exact Hleft |].
      exact (RunSnoc x suffix z a y Hright Hstep).
  - intros [x [Hleft Hright]]. exact (run_append s tr x tr' y Hleft Hright).
Qed.

Lemma run_cons_iff s a tr y :
  finite_run s (a :: tr) y <->
  exists x, step s a x /\ finite_run x tr y.
Proof.
  change (finite_run s ([a] ++ tr) y <->
    exists x, step s a x /\ finite_run x tr y).
  rewrite run_append_iff. setoid_rewrite run_singleton. reflexivity.
Qed.

Variable final : S -> Prop.

Definition ready (s : S) : Prop :=
  final s \/ exists a y, step s a y.

Definition stuck (s : S) : Prop :=
  ~ final s /\ forall a y, ~ step s a y.

Definition DF (s : S) : Prop :=
  forall tr y, finite_run s tr y -> ready y.

Lemma stuck_iff_not_ready s : stuck s <-> ~ ready s.
Proof.
  split.
  - intros [Hfinal Hstep] [Hdone | [a [y Hact]]].
    + exact (Hfinal Hdone).
    + exact (Hstep a y Hact).
  - intros H. split.
    + intros Hdone. apply H. left. exact Hdone.
    + intros a y Hact. apply H. right. exists a, y. exact Hact.
Qed.

Lemma DF_ready s : DF s -> ready s.
Proof.
  intros H. exact (H [] s (RunRefl s)).
Qed.

Lemma DF_after_run s tr x :
  DF s -> finite_run s tr x -> DF x.
Proof.
  intros Hdf Hprefix suffix y Hsuffix.
  exact (Hdf (tr ++ suffix) y (run_append s tr x suffix y Hprefix Hsuffix)).
Qed.

Lemma DF_no_stuck s :
  DF s -> forall tr y, finite_run s tr y -> ~ stuck y.
Proof.
  intros Hdf tr y Hrun Hstuck.
  apply (proj1 (stuck_iff_not_ready y) Hstuck).
  exact (Hdf tr y Hrun).
Qed.
End Runs.

(* Contraposition here is constructive: both notions of stuckness are negative.
   A caller must supply the readiness implication explicitly. *)
Section Reflection.
Context {S A T B : Type}.
Variable source_step : S -> A -> S -> Prop.
Variable source_final : S -> Prop.
Variable target_step : T -> B -> T -> Prop.
Variable target_final : T -> Prop.

Lemma ready_stuck_reflection s t :
  (ready source_step source_final s -> ready target_step target_final t) ->
  stuck target_step target_final t ->
  stuck source_step source_final s.
Proof.
  intros Hready Hstuck.
  apply (proj2 (stuck_iff_not_ready source_step source_final s)).
  intros Hsource.
  exact (proj1 (stuck_iff_not_ready target_step target_final t)
    Hstuck (Hready Hsource)).
Qed.
End Reflection.
