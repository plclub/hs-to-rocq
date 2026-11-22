From Stdlib Require Import Lists.List Logic.Eqdep_dec.
Require Import DeadlockNetwork DeadlockLocal.
Import ListNotations.

(* Stdlib's monomorphic in_split cannot instantiate the larger universe of
   existentially packaged network endpoints. *)
Polymorphic Lemma in_split_large {T : Type} (x : T) xs :
  In x xs -> exists pre post, xs = pre ++ x :: post.
Proof.
  revert xs. fix IH 1. intros [|y ys] H; [contradiction|].
  destruct H as [->|Hy]; [exists [], ys; reflexivity|].
  specialize (IH ys Hy) as [pre [post ->]]. exists (y :: pre), post. reflexivity.
Qed.

Section Roster.
Context {M E : Type -> Type} {Store : Type} (m : local_model M E role Store)
        (rs : list role) (A : role -> Type).

Definition controls := forall p, @control M E (A p).
Definition entry (f : controls) p := Endpoint (A p) p (f p).
Definition assembled (f : controls) (q : queues) (s : Store) : configuration :=
  {| endpoints := map (entry f) rs; mailboxes := q; shared_store := s |}.

(* Inspect an existential endpoint by eliminating the package itself.
   Inverting equality between two packages of programs at type Type
   would incorrectly presuppose UIP for the universe of result types. *)
Definition at_endpoint (e : @endpoint M E) q s a e' q' s' : Prop :=
  match e with Endpoint X p t =>
    exists u : control X, step m rs p X t q s a u q' s' /\ e' = Endpoint X p u
  end.

Lemma selection c a d : nstep m rs c a d ->
  exists pre e e' post,
    endpoints c = pre ++ e :: post /\ endpoints d = pre ++ e' :: post /\
    at_endpoint e (mailboxes c) (shared_store c) a e' (mailboxes d) (shared_store d).
Proof.
  destruct 1. do 4 eexists. split; [reflexivity|].
  split; [reflexivity|]. cbn. eexists; eauto.
Qed.

Lemma split_entries (f : controls) pre xs e post :
  map (entry f) xs = pre ++ e :: post ->
  exists before p after, xs = before ++ p :: after /\
    pre = map (entry f) before /\ e = entry f p /\ post = map (entry f) after.
Proof.
  revert pre xs. fix IH 1. intros [|b pre] [|p xs]; cbn; intro H; try discriminate.
  - injection H as He Hpost. exists [], p, xs. cbn. auto.
  - injection H as He Htail. specialize (IH pre xs Htail).
    destruct IH as (u & r & v & -> & -> & -> & ->).
    exists (p :: u), r, v. cbn. subst b. auto.
Qed.

Definition set_control (f : controls) p (u : control (A p)) : controls :=
  fun r => match role_eq_dec p r with
           | left h => eq_rect p (fun i => control (A i)) u r h
           | right _ => f r
           end.

Lemma set_here f p u : set_control f p u p = u.
Proof.
  unfold set_control; destruct (role_eq_dec p p) as [h|n]; [|contradiction].
  rewrite (UIP_dec role_eq_dec h eq_refl). reflexivity.
Qed.
Lemma set_other f p u r : p <> r -> set_control f p u r = f r.
Proof. intros H; unfold set_control; destruct (role_eq_dec p r); congruence. Qed.

Lemma set_entries f p u pre post :
  NoDup (pre ++ p :: post) ->
  map (entry (set_control f p u)) (pre ++ p :: post) =
  map (entry f) pre ++ Endpoint (A p) p u :: map (entry f) post.
Proof.
  assert (frame : forall xs, ~ In p xs ->
    map (entry (set_control f p u)) xs = map (entry f) xs).
  { induction xs as [|r xs IH]; cbn; intro N; [reflexivity|].
    unfold entry at 1 3. rewrite set_other by (intro e; subst; apply N; now left).
    f_equal. apply IH. intro I; apply N; now right. }
  induction pre as [|r pre IH]; cbn; intro H; inversion H; subst.
  - unfold entry at 1. rewrite set_here. f_equal. now apply frame.
  - unfold entry at 1 3. rewrite set_other.
    + f_equal; auto.
    + intro e; subst. apply H2. apply in_or_app. right; now left.
Qed.

Theorem roster_step f q s a d :
  NoDup rs -> nstep m rs (assembled f q s) a d ->
  exists p (u : control (A p)) q' s',
    In p rs /\ step m rs p (A p) (f p) q s a u q' s' /\
    d = assembled (set_control f p u) q' s'.
Proof.
  intros ND H. apply selection in H.
  destruct H as (pre & e & e' & post & Hbefore & Hafter & Hstep).
  cbn in Hbefore,Hstep.
  destruct (split_entries f pre rs e post Hbefore) as (left & p & right & Hrs & -> & -> & ->).
  cbn [entry at_endpoint] in Hstep.
  destruct Hstep as [u [Hstep ->]].
  exists p, u, (mailboxes d), (shared_store d).
  split; [rewrite Hrs; apply in_or_app; right; now left|].
  split; [exact Hstep|].
  destruct d as [es r t]; unfold assembled; cbn in *.
  rewrite Hrs in ND |- *. rewrite (set_entries _ _ _ _ _ ND). now rewrite Hafter.
Qed.

Theorem schedule_role f p u q s a q' s' :
  NoDup rs -> In p rs -> step m rs p (A p) (f p) q s a u q' s' ->
  nstep m rs (assembled f q s) a (assembled (set_control f p u) q' s').
Proof.
  intros ND Member H. apply in_split in Member. destruct Member as (pre & post & Er).
  assert (old : map (entry f) rs =
    map (entry f) pre ++ entry f p :: map (entry f) post).
  { rewrite Er. clear ND H Er. induction pre; cbn; congruence. }
  assert (new : map (entry (set_control f p u)) rs =
    map (entry f) pre ++ Endpoint (A p) p u :: map (entry f) post).
  { rewrite Er in ND |- *. now apply set_entries. }
  unfold assembled; rewrite old, new. now apply Schedule.
Qed.

Lemma all_returns f q s :
  nfinal m (assembled f q s) <->
  (forall p, In p rs -> exists x, returns m (A p) (f p) x) /\
  (forall k, q k = []).
Proof.
  unfold nfinal, assembled; cbn.
  assert (iff_all : forall xs,
    Forall (endpoint_final m) (map (entry f) xs) <->
    forall p, In p xs -> exists x, returns m (A p) (f p) x).
  { induction xs as [|r xs IH]; cbn.
    - split; [contradiction|constructor].
    - split.
      + intros H p [<-|I]; inversion H; subst; [assumption|]. now apply IH.
      + intro H; constructor; [apply H; now left|]. apply IH.
        intros p I. apply H. now right. }
  now rewrite iff_all.
Qed.
End Roster.
