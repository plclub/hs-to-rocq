From Stdlib Require Import Lists.List Logic.Eqdep_dec.
Require Import Choreography.Choreo2 Control.Monad.Tree Parkour.Symbol.
From ParkourTheories.Choreography Require Import RoleSteps Occurrences
  WellFormedness.
Import ListNotations.

(* A deliberately executable slice of source coherence. This evaluator performs
   bookkeeping only: it neither supplies local results nor fabricates messages.
   In particular it cannot cross Cond, a send, or a receive. Its fuel is not a
   progress hypothesis. Every successful result has an actual Source returns
   derivation, and partial families of these results satisfy structural's
   result relation, including its partial Bind-prefix obligation. *)
Fixpoint silent_value {M p A} (fuel : nat) (c : Choreo M p A) : option A :=
  match fuel with
  | O => None
  | S n =>
    match c with
    | Pure x => Some x
    | App f x =>
      match silent_value n f, silent_value n x with
      | Some g, Some y => Some (g y)
      | _, _ => None
      end
    | Bind t k =>
      match silent_value n t with
      | Some x => silent_value n (k x)
      | None => None
      end
    | Perf e =>
      match e with
      | @Locally _ _ X l _ _ _ =>
        match @Symbol.decide l p MkSSymbol MkSSymbol with
        | Proved _ => None
        | Disproved h => Some (RoleSteps.off_at (fun e =>
          GHC.Base.absurd
          (h e)))
        end
      | @Comm _ _ X l r _ _ _ _ _ v _ =>
        match @Symbol.decide l r MkSSymbol MkSSymbol with
        | Proved h =>
          match h in _ = r' return option (At X r' p) with
          | eq_refl => Some v
          end
        | Disproved _ =>
          match @Symbol.decide l p MkSSymbol MkSSymbol,
                @Symbol.decide r p MkSSymbol MkSSymbol with
          | Disproved _, Disproved hr =>
            Some (RoleSteps.off_at (fun e => GHC.Base.absurd (hr
              e)))
          | _, _ => None
          end
        end
      | @Cond _ _ _ _ _ _ _ _ _ _ _ => None
      end
    end
  end.

Section Execution.
Context {M E : Type -> Type} {Store : Type}.
Variable model : LocalEffects.local_model M E Symbol Store.

Lemma returns_seq p X Y o (t : @cursor M E p X)
    (k : X -> Choreo M p Y) x y :
  returns model t x ->
  returns model (Code (child o BindBody) (k x)) y ->
  returns model (Seq o t k) y.
Proof.
  intros H. induction H; intro K.
  - eapply ReturnsSilent; [apply SSeq | exact K].
  - eapply ReturnsSilent; [apply SSeqUnder; exact H | apply IHreturns; exact K].
Qed.

End Execution.

Section ExecutionRemainder.
Context {M E : Type -> Type} {Store : Type}.
Variable model : LocalEffects.local_model M E Symbol Store.

Lemma returns_fork_left p X Y (f : @cursor M E p (X -> Y))
    (x : @cursor M E p X) g y :
  returns model f g -> returns model x y ->
  returns model (Fork f x) (g y).
Proof.
  intros H. induction H; intro K.
  - induction K.
    + eapply ReturnsSilent; [apply SJoin | constructor].
    + eapply ReturnsSilent; [apply SForkRight; exact H | exact IHK].
  - eapply ReturnsSilent; [apply SForkLeft; exact H | apply IHreturns; exact K].
Qed.

Lemma silent_value_returns fuel p A (c : Choreo M p A) x o :
  silent_value fuel c = Some x ->
  returns model (Code o c) x.
Proof.
  revert p A c x o. induction fuel as [|n IH]; intros p A c x o H;
    [discriminate |].
  destruct c as [A e | A y | X A f t | X A t k]; cbn in H.
  - destruct e as [X l kl sl f | X l r sh rd kl kr sl v sr |
                   X l A sh rd kl sl v k].
    + destruct (@Symbol.decide l p MkSSymbol MkSSymbol) as [eq|ne];
        [discriminate |].
      inversion H; subst x.
      eapply ReturnsSilent; [apply SLocalOther | constructor].
    + destruct (@Symbol.decide l r MkSSymbol MkSSymbol) as [eq|ne].
      * destruct eq. inversion H; subst x.
        eapply ReturnsSilent; [apply SCommSelf | constructor].
      * destruct (@Symbol.decide l p MkSSymbol MkSSymbol) as [eq|nl];
          [discriminate |].
        destruct (@Symbol.decide r p MkSSymbol MkSSymbol) as [eq|nr];
          [discriminate |].
        inversion H; subst x.
        eapply ReturnsSilent.
        -- eapply SCommOther; intro eq; apply GHC.Base.absurd;
             first [exact (nl eq) | exact (nr eq) | exact (ne eq)].
        -- constructor.
    + discriminate.
  - inversion H; subst x. eapply ReturnsSilent; [apply SPure | constructor].
  - destruct (silent_value n f) as [g|] eqn:F; [|discriminate].
    destruct (silent_value n t) as [y|] eqn:T; [|discriminate].
    inversion H; subst x.
    eapply ReturnsSilent; [apply SApp |].
    eapply returns_fork_left; apply IH; eassumption.
  - destruct (silent_value n t) as [y|] eqn:T; [|discriminate].
    eapply ReturnsSilent; [apply SBind |].
    eapply returns_seq; apply IH; eassumption.
Qed.
End ExecutionRemainder.

(* Extracting witnesses from a successful computation needs neither choice nor
   an inhabitant of the source result type. *)
Definition option_value {A} (o : option A) (ok : o <> None) : A :=
  match o as z return z <> None -> A with
  | Some x => fun _ => x
  | None => fun h => False_rect A (h eq_refl)
  end ok.

Lemma option_value_spec {A} (o : option A) (ok : o <> None) :
  o = Some (option_value o ok).
Proof. destruct o; [reflexivity | contradiction]. Qed.

(* Proof-index independence is explicit, rather than using the axiom of proof
   irrelevance. This is only a condition on evidence for role-set membership,
   not a causal or next-step condition. *)
Definition role_evidence_irrelevant (S : roles) :=
  forall p (s t : S p), s = t.

Lemma structural_empty_results roster M S A c Q :
  structural roster M S A c Q ->
  forall D (v : values A D), (forall p, ~ D p) -> Q D v.
Proof.
  intro W. induction W; intros D v Empty.
  - split; intros p d; exact (False_rect _ (Empty p d)).
  - intros p d. exact (False_rect _ (Empty p d)).
  - split; [intros p d; exact (False_rect _ (Empty p d)) |].
    intros s d. exact (False_rect _ (Empty r d)).
  - left. exact Empty.
  - exists (fun p d => False_rect _ (Empty p d)),
      (fun p d => False_rect _ (Empty p d)).
    repeat split; try (apply IHW1 || apply IHW2); try exact Empty.
    intros p d. exact (False_rect _ (Empty p d)).
  - unfold bind_results.
    exists D, (fun p d => False_rect _ (Empty p d)).
    split; [apply IHW; exact Empty |].
    eapply H0.
    + intros p d. exact (False_rect _ (Empty p d)).
    + apply IHW. exact Empty.
    + exact Empty.
Qed.

Lemma structural_silent_values roster M S A c Q :
  structural roster M S A c Q ->
  role_evidence_irrelevant S ->
  forall fuel D (v : values A D) (inc : includes D S),
    role_evidence_irrelevant D ->
    (forall p d, silent_value fuel (c p (inc p d)) = Some (v p d)) ->
    Q D v.
Proof.
  intros W. pose proof W as Original.
  induction W; intros PI fuel D v inc PId Eval;
    destruct fuel as [|n];
    try solve [eapply (structural_empty_results _ _ _ _ _ _ Original);
      intros p d; specialize (Eval p d); discriminate].
  - split; [exact inc |].
    intros p d s.
    specialize (Eval p d). rewrite H in Eval. cbn in Eval.
    rewrite (PI p (inc p d) s) in Eval. inversion Eval. reflexivity.
  - exact inc.
  - split; [exact inc |].
    intros s d.
    specialize (Eval r d). rewrite H2 in Eval. cbn in Eval.
    destruct (@Symbol.decide l r MkSSymbol MkSSymbol) as [eq|ne].
    + destruct eq. cbn in Eval. inversion Eval; subst.
      rewrite (PI l (inc l d) s). reflexivity.
    + destruct (@Symbol.decide r r MkSSymbol MkSSymbol) as [eq|nr].
      * discriminate.
      * exfalso. exact (GHC.Base.absurd (nr eq_refl)).
  - left. intros p d. specialize (Eval p d). rewrite H3 in Eval. discriminate.
  - assert (NF : forall p d, silent_value n (f p (inc p d)) <> None).
    { intros p d Z. specialize (Eval p d). rewrite H in Eval.
      cbn in Eval. rewrite Z in Eval. discriminate. }
    assert (NX : forall p d, silent_value n (x p (inc p d)) <> None).
    { intros p d Z. specialize (Eval p d). rewrite H in Eval.
      cbn in Eval. rewrite Z in Eval.
      destruct (silent_value n (f p (inc p d))); discriminate. }
    exists (fun p d => option_value _ (NF p d)),
      (fun p d => option_value _ (NX p d)).
    split.
    + eapply IHW1; [exact W1 | exact PI | exact PId |].
      intros p d. apply option_value_spec.
    + split.
      * eapply IHW2; [exact W2 | exact PI | exact PId |].
        intros p d. apply option_value_spec.
      * intros p d. specialize (Eval p d). rewrite H in Eval. cbn in Eval.
        rewrite (option_value_spec _ (NF p d)),
          (option_value_spec _ (NX p d)) in Eval.
        inversion Eval. reflexivity.
  - assert (NT : forall p d, silent_value n (t p (inc p d)) <> None).
    { intros p d Z. specialize (Eval p d). rewrite H1 in Eval.
      cbn in Eval. rewrite Z in Eval. discriminate. }
    set (a := (fun p d => option_value _ (NT p d)) : values A D).
    assert (Prefix : P D a).
    { eapply IHW; [exact W | exact PI | exact PId |].
      intros p d. apply option_value_spec. }
    unfold bind_results. exists D, a. split; [exact Prefix |].
    apply (H0 D a inc Prefix (H D a inc Prefix) PId n D v
      (fun p d => d) PId).
    intros p d. specialize (Eval p d). rewrite H1 in Eval. cbn in Eval.
    rewrite (option_value_spec _ (NT p d)) in Eval.
    exact Eval.
Qed.

Lemma list_role_evidence_irrelevant roster :
  NoDup roster -> role_evidence_irrelevant (fun p => In p roster).
Proof.
  induction roster as [|r roster IH]; intro ND.
  - intros p s. inversion s.
  - inversion ND as [|? ? NotIn Tail]; subst.
    intros p [e|s] [f|t].
    + f_equal. apply UIP_dec. apply List.list_eq_dec. exact BinNat.N.eq_dec.
    + subst p. contradiction.
    + subst p. contradiction.
    + f_equal. exact (IH Tail p s t).
Qed.

(* This public slice has no proof-irrelevance premise or axiom: NoDup lists
   supply unique membership evidence constructively. The completed roles may
   be a strict subset, and no value is required at any other role. *)
Theorem structural_partial_silent_results roster M A c Q completed
    (v : values A (fun p => In p completed))
    (inc : includes (fun p => In p completed) (fun p => In p roster)) fuel :
  structural roster M (fun p => In p roster) A c Q ->
  NoDup roster -> NoDup completed ->
  (forall p d, silent_value fuel (c p (inc p d)) = Some (v p d)) ->
  Q (fun p => In p completed) v.
Proof.
  intros W NR NC Eval.
  eapply structural_silent_values.
  - exact W.
  - apply list_role_evidence_irrelevant. exact NR.
  - apply list_role_evidence_irrelevant. exact NC.
  - exact Eval.
Qed.

Theorem well_formed_computed_partial_returns {M E Store}
    (model : LocalEffects.local_model M E Symbol Store)
    roster A (program : forall p, Choreo M p (A p)) completed
    (v : values A (fun p => In p completed)) fuel :
  well_formed roster M A program ->
  NoDup completed ->
  includes (fun p => In p completed) (fun p => In p roster) ->
  (forall p d, silent_value fuel (program p) = Some (v p d)) ->
  exists Q,
    structural roster M (fun p => In p roster) A (fun p _ => program p) Q /\
    Q (fun p => In p completed) v /\
    forall p (d : In p completed) o, returns model (Code o (program p)) (v p d).
Proof.
  intros [NR [Q W]] NC inc Eval. exists Q. split; [exact W |]. split.
  - exact (structural_partial_silent_results roster M A (fun p _ => program p) Q
      completed v inc fuel W NR NC Eval).
  - intros p d o.
    exact (silent_value_returns model fuel p (A p) (program p) (v p d) o (Eval p
      d)).
Qed.
