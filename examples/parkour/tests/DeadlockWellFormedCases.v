From Stdlib Require Import Lists.List.
Require Import Choreography.Choreo2 Control.Monad.Tree Parkour.Codec Parkour.Symbol.
Require Import DeadlockWellFormed DeadlockWellFormedExpect.
Require Import DeadlockWellFormedPartialExpect.
Import ListNotations.

Lemma participants_distinct : NoDup participants.
Proof.
  repeat constructor; cbn; intuition discriminate.
Qed.

(* These observations do not recover the existential type of a Bind by
   injectivity. They inspect its prefix and run only an off-owner local step. *)
Definition local_head {M p A} (c : Choreo M p A) : bool :=
  match c with
  | Perf (@Locally _ _ _ _ _ _ _) => true
  | _ => false
  end.

Definition bind_local_head {M p A} (c : Choreo M p A) : bool :=
  match c with
  | Bind t _ => local_head t
  | _ => false
  end.

Definition silent_local_result {M p A} (c : Choreo M p A) : option A :=
  match c with
  | Perf s =>
      match s in ChoreoSig _ _ X return option X with
      | @Locally _ _ X l _ _ _ =>
          match @decide l p MkSSymbol MkSSymbol with
          | Proved _ => None
          | Disproved ne => Some (Mk_At (fun e => match ne e with end))
          end
      | _ => None
      end
  | _ => None
  end.

Definition head_after_bind {M p A} (c : Choreo M p A)
    : option (Symbol * Symbol) :=
  match c with
  | Bind t k =>
      match silent_local_result t with
      | Some x => communication_head (k x)
      | None => None
      end
  | _ => None
  end.

Lemma local_prefix_results R M S A c P :
  structural R M S A c P ->
  (exists p, exists s : S p, local_head (c p s) = true) ->
  forall D (v : values A D), includes D S -> P D v.
Proof.
  intros H; destruct H; intros [p [s E]] D v inc;
    match goal with
    | H : forall p s, _ = _ |- _ => rewrite (H p s) in E
    end; cbn in E; try discriminate.
  exact inc.
Qed.

Lemma opposed_bind_heads R M S A c Q (sb : S bob) (sc : S carol) :
  structural R M S A c Q ->
  bind_local_head (c bob sb) = true ->
  head_after_bind (c bob sb) = Some (alice, bob) ->
  head_after_bind (c carol sc) = Some (alice, carol) ->
  False.
Proof.
  intros H LB HB HC.
  destruct H;
    match goal with E : forall p s, _ = _ |- _ =>
      rewrite (E bob sb) in LB, HB; rewrite (E carol sc) in HC
    end; cbn in LB; try discriminate.
  cbn [head_after_bind] in HB, HC.
  destruct (silent_local_result (t bob sb)) as [vb|]; [|discriminate].
  destruct (silent_local_result (t carol sc)) as [vc|]; [|discriminate].
  pose (other := fun p (h : off_owner p) (ne : p <> bob) =>
    match h with
    | or_introl e => False_rect (p = carol) (ne e)
    | or_intror e => e
    end).
  pose (v := (fun p (h : off_owner p) =>
    match List.list_eq_dec BinNat.N.eq_dec p bob with
    | left e => eq_rect bob A vb p (eq_sym e)
    | right ne => eq_rect carol A vc p (eq_sym (other p h ne))
    end) : values A off_owner).
  pose (inc := (fun p (h : off_owner p) => match h with
    | or_introl e => eq_rect bob S sb p (eq_sym e)
    | or_intror e => eq_rect carol S sc p (eq_sym e)
    end) : includes off_owner S).
  assert (related : P off_owner v).
  { eapply local_prefix_results; [exact H| |exact inc].
    exists bob, sb; exact LB. }
  pose proof (H0 off_owner v inc related) as HK.
  pose proof (structural_head _ _ _ _ _ _ HK bob carol
    (or_introl eq_refl) (or_intror eq_refl)) as E.
  unfold v, inc, other in E.
  change (communication_head (k bob sb vb) =
    communication_head (k carol sc vc)) in E.
  rewrite HB, HC in E. discriminate.
Qed.

Lemma empty_bind_rejected : rejects_empty_bind well_formed.
Proof.
  intros [_ [Q H]].
  eapply (opposed_bind_heads participants effect
    (fun p => In p participants) _ _ Q
    (or_intror (or_introl eq_refl))
    (or_intror (or_intror (or_introl eq_refl))) H).
  - reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

Lemma bool_wire : wire_law show_bool read_bool.
Proof. intros []; vm_compute; reflexivity. Qed.

Lemma communicating_accepted : accepts_communicating well_formed.
Proof.
  split; [exact participants_distinct|].
  eexists. eapply WFComm with
    (x := fun p _ => truth alice p)
    (sh := fun _ _ => show_bool) (rd := fun _ _ => read_bool).
  - cbn; auto.
  - cbn; auto.
  - intros; exact bool_wire.
  - intros; reflexivity.
Qed.

Lemma located_accepted : accepts_located well_formed.
Proof.
  split; [exact participants_distinct|].
  eexists. eapply WFLocally with (f := fun _ _ _ => tt).
  - cbn; auto.
  - intros; reflexivity.
Qed.

Lemma two_receivers_rejected : rejects_receivers well_formed.
Proof.
  intros [_ [Q H]].
  pose proof (structural_head _ _ _ _ _ _ H alice bob
    (or_introl eq_refl) (or_intror (or_introl eq_refl))) as E.
  vm_compute in E. discriminate.
Qed.

Lemma absent_receiver_rejected : rejects_absent well_formed.
Proof.
  intros [_ [Q H]].
  pose proof (structural_head_roles _ _ _ _ _ _ H alice
    (or_introl eq_refl) alice bob eq_refl) as [_ E].
  cbn in E. destruct E as [E|E]; [discriminate|contradiction].
Qed.

Lemma wrong_codec_rejected : rejects_codec well_formed.
Proof.
  intros [_ [Q H]].
  pose proof (structural_wire _ _ _ _ _ _ H alice bob
    (or_introl eq_refl) (or_intror (or_introl eq_refl))
    (@show bool show_bool true) eq_refl) as E.
  assert (ne : alice <> bob) by discriminate.
  specialize (E ne).
  assert (payload : encodes (wrong_codec alice) (@show bool show_bool true)).
  { exists true; reflexivity. }
  specialize (E payload).
  destruct E as [x E]. discriminate.
Qed.

Lemma self_accepted : accepts_self well_formed.
Proof.
  split; [exact participants_distinct|].
  eexists. eapply WFComm with
    (x := fun p _ => truth alice p)
    (sh := fun _ _ => show_bool) (rd := fun _ _ => broken_read).
  - cbn; auto.
  - cbn; auto.
  - intros s t ne; contradiction.
  - intros; reflexivity.
Qed.

Lemma empty_complete_impossible : no_complete_empty_result.
Proof. intro v. destruct (unAt (v alice) eq_refl). Qed.

Lemma empty_partial_related :
  partial_empty_result_is_related
    (located_results Empty_set alice (fun p => In p participants)).
Proof.
  intros p [E|E]; subst p; cbn; auto.
Qed.

Lemma empty_partial_continuations_disagree :
  forall Q, ~ structural participants effect off_owner
    (fun p => At bool p p) (fun p _ => two_receivers p) Q.
Proof.
  intros Q H.
  pose proof (structural_head _ _ _ _ _ _ H bob carol
    (or_introl eq_refl) (or_intror eq_refl)) as E.
  vm_compute in E. discriminate.
Qed.

Lemma empty_bind_partial_obligation_rejected :
  rejects_partial_empty_continuation
    (located_results Empty_set alice (fun p => In p participants))
    (fun D c => exists Q, structural participants effect D
      (fun p => At bool p p) c Q).
Proof.
  intro H.
  assert (inc : includes off_owner (fun p => In p participants)).
  { intros p [E|E]; subst p; cbn; auto. }
  destruct (H off_owner partial_empty inc empty_partial_related) as [Q HQ].
  exact (empty_partial_continuations_disagree Q HQ).
Qed.

Lemma other_constructors_accepted :
  accepts_pure_app_bind_cond well_formed.
Proof.
  repeat split; try exact participants_distinct.
  - eexists. eapply WFPure with (x := fun p _ => truth alice p).
    intros; reflexivity.
  - eexists. eapply WFApp with
      (f := fun p _ => Pure (fun x : At bool alice p => x))
      (x := fun p _ => pure_case p).
    + apply WFPure; intros; reflexivity.
    + eapply WFPure with (x := fun p _ => truth alice p).
      intros; reflexivity.
    + intros; reflexivity.
  - eexists. eapply WFBind with
      (t := fun p _ => pure_case p)
      (k := fun p _ x => Pure x)
      (K := fun D v => pure_results v).
    + eapply WFPure with (x := fun p _ => truth alice p).
      intros; reflexivity.
    + intros. apply WFPure; intros; reflexivity.
    + intros; reflexivity.
  - eexists. eapply WFCond with
      (sh := fun _ _ => show_bool) (rd := fun _ _ => read_bool)
      (x := fun p _ => truth alice p)
      (k := fun p _ b => Pure (@Mk_At bool alice p (fun _ => b)))
      (K := fun b => pure_results
        (fun p (_ : In p participants) =>
          @Mk_At bool alice p (fun _ => b))).
    + cbn; auto.
    + intros; exact bool_wire.
    + intros. apply WFPure; intros; reflexivity.
    + intros; reflexivity.
Qed.
