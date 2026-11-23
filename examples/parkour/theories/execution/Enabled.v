From ITree Require Import ITree.
From Stdlib Require Import Lists.List.
Require Import Choreography.Network DeadlockLocal DeadlockNetwork.
Import ListNotations.

(* Only terminal views are unique: a finite derivation may stop at TauF
   before another derivation crosses the same Tau. *)
Lemma terminal_view_unique {E A} (t : itree E A) v w :
  local_view t v -> local_view t w ->
  (forall u, v <> TauF u) -> (forall u, w <> TauF u) -> v = w.
Proof.
  intros H. revert w. induction H as [t v Hv | t u v Htau H IH];
    intros w Hw Nv Nw; inversion Hw; subst; try reflexivity.
  - exfalso. apply (Nv u). assumption.
  - exfalso. apply (Nw u). assumption.
  - apply IH; try assumption. congruence.
Qed.

Lemma local_return_unique {E A} (t : itree E A) x y :
  local_return t x -> local_return t y -> x = y.
Proof.
  intros Hx Hy.
  assert (RetF x = (RetF y : itreeF E A (itree E A))) as H.
  { eapply terminal_view_unique; eauto; discriminate. }
  now injection H.
Qed.

Lemma local_return_no_event {E Role S A} reply p (t : itree E A) x s a t' s' :
  local_return t x -> ~ @local_step E Role S A reply p t s a t' s'.
Proof.
  intros Hr Hs. destruct Hs as [X e k v s' Hv Hreply].
  assert (RetF x = (VisF e k : itreeF E A (itree E A))) as H.
  { eapply terminal_view_unique; eauto; discriminate. }
  discriminate.
Qed.

Section Machine.
Context {M E : Type -> Type} {S : Type} (m : local_model M E role S).

(* Invert returns by computation on the control, not by injection on
   existential intermediates of App or Bind. *)
Fixpoint result_of {A} (t : @control M E A) : A -> Prop :=
  match t with
  | CPure v => fun x => x = v
  | CPerf e =>
      match e with
      | Exec e => fun x => local_return (interpret_local _ _ _ _ m _ e) x
      | _ => fun _ => False
      end
  | CLocal u => local_return u
  | CBind u k => fun y => exists x, result_of u x /\ result_of (k x) y
  | CApp f u => fun y => exists g x, result_of f g /\ result_of u x /\ y = g x
  end.

Lemma returns_result A (t : control A) x : returns m A t x -> result_of t x.
Proof. induction 1; cbn; eauto 7. Qed.

Lemma return_result_unique A (t : control A) x y :
  returns m A t x -> result_of t y -> x = y.
Proof.
  intro H. revert y. induction H; intros z Hz; cbn in Hz.
  - symmetry; exact Hz.
  - eapply local_return_unique; eassumption.
  - eapply local_return_unique; eassumption.
  - destruct Hz as [v [Hv Hw]]. apply IHreturns1 in Hv. subst v.
    now apply IHreturns2.
  - destruct Hz as [h [v [Hh [Hv ->]]]].
    now rewrite (IHreturns1 h Hh), (IHreturns2 v Hv).
Qed.

Lemma return_unique A (t : control A) x y :
  returns m A t x -> returns m A t y -> x = y.
Proof. intros H G. eapply return_result_unique; [exact H | now apply
  returns_result]. Qed.

Variable roles : list role.

Lemma return_no_possible A (t : control A) x :
  returns m A t x -> forall p q s, ~ possible m p t q s.
Proof.
  intro H. induction H; intros p q s Hs; cbn in Hs.
  - exact Hs.
  - destruct Hs as [act [v [s0 Hv]]]. eapply local_return_no_event; eassumption.
  - destruct Hs as [act [v [s0 Hv]]]. eapply local_return_no_event; eassumption.
  - destruct Hs as [Ht | [v [Hv Hk]]].
    + exact (IHreturns1 p q s Ht).
    + apply (return_unique _ _ _ _ H) in Hv. subst v.
    exact (IHreturns2 p q s Hk).
  - destruct Hs as [Hf | Hx]; [exact (IHreturns1 p q s Hf) | exact (IHreturns2 p
    q s Hx)].
Qed.

Lemma return_no_action A (t : control A) x :
  returns m A t x -> forall p q s a u q' s', ~ step m roles p A t q s a u q' s'.
Proof.
  intros Hr p q s a u q' s' Hs. apply step_possible in Hs.
  exact (return_no_possible _ _ _ Hr _ _ _ Hs).
Qed.

Lemma possible_step p A (t : control A) q s :
  possible m p t q s ->
  exists a u q' s', step m roles p A t q s a u q' s'.
Proof.
  induction t as [A v|A e|A B t IH k KH|A B f FH x XH|A t]; cbn.
  - contradiction.
  - destruct e; cbn; intro live.
    + destruct live as [obs [next [s' Hlocal]]].
    do 4 eexists; apply StepExec; exact Hlocal.
    + do 4 eexists; apply StepSend.
    + destruct live as [w [ws [v [Hq Hd]]]].
    do 4 eexists; eapply StepRecv; eassumption.
    + do 4 eexists; apply StepBCast.
  - intros [H | [v [Hr H]]].
    + destruct (IH H) as [a [u [r [s' Hu]]]].
    do 4 eexists; apply StepBind; exact Hu.
    + destruct (KH v H) as [a [u [r [s' Hu]]]].
    do 4 eexists; eapply StepContinue; eassumption.
  - intros [H | H].
    + destruct (FH H) as [a [u [r [s' Hu]]]].
    do 4 eexists; apply StepLeft; exact Hu.
    + destruct (XH H) as [a [u [r [s' Hu]]]].
    do 4 eexists; apply StepRight; exact Hu.
  - intros [a [t' [s' H]]]. do 4 eexists; apply StepLocal; exact H.
Qed.

Lemma endpoint_witness es q s :
  endpoints_possible m q s es ->
  exists pre post A p (t t' : control A) a q' s',
    es = pre ++ Endpoint _ p t :: post /\ step m roles p A t q s a t' q' s'.
Proof.
  revert es. fix IH 1. intros [|[A p t] es]; cbn; [contradiction|].
  intros [H | H].
  - destruct (possible_step _ _ _ _ _ H) as [a [u [r [s' Hu]]]].
    exists [], es, A, p, t, u, a, r, s'. auto.
  - destruct (IH es H) as (pre & post & B & p' & u & u' & a & r & s' & -> & Hu).
    exists (Endpoint _ p t :: pre), post, B, p', u, u', a, r, s'. auto.
Qed.

Lemma network_enabled_exact c :
  endpoints_possible m (mailboxes c) (shared_store c) (endpoints c) <->
  exists a d, nstep m roles c a d.
Proof.
  split.
  - destruct c as [es q s]; cbn. intro H.
    destruct (endpoint_witness _ _ _ H) as (pre & post & A & p & t & u & a & r &
      s' & -> & Hu).
    do 2 eexists; apply Schedule; exact Hu.
  - intros [a [d H]]. eapply nstep_possible; exact H.
Qed.
End Machine.
