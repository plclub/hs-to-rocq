From Stdlib Require Import Lists.List Logic.Eqdep_dec.
Require Import Choreography.Choreo2 Control.Monad.Tree Parkour.Codec Parkour.Symbol.
Require Import DeadlockSource DeadlockWellFormed DeadlockPartialValues DeadlockPlayedValues.
Import ListNotations.

(* Interface to syntax-indexed annotated cuts. All inversion obligations below
   concern actual subcuts, actual returned operands, or concrete past packets.
   None mentions structural, its result relation, coherence, or progress. *)
Section Families.
Context {M : Type -> Type}.
Variable Cut : Symbol -> Type -> Type.
Variable at_code : forall p A, occurrence -> Choreo M p A -> Cut p A -> Prop.
Variable returned : forall p A, Cut p A -> A -> Prop.
Variable past : list payload_event.
Definition family A (rs : list Symbol) := forall p, In p rs -> Cut p (A p).
Variable good : forall A rs, occurrence -> family A rs -> Prop.

Definition family_at S A (c : programs M A S) rs
    (inc : includes (fun p => In p rs) S) o (cuts : family A rs) :=
  forall p s, at_code p (A p) o (c p (inc p s)) (cuts p s).
Definition family_returned A active completed
    (inc : includes (fun p => In p completed) (fun p => In p active))
    (cuts : family A active) (v : values A (fun p => In p completed)) :=
  forall p d, returned p (A p) (cuts p (inc p d)) (v p d).

Definition choice_observation X l p (rd : Read X) (input : At X l p) o (a : X) :=
  (exists e : l = p, a = unAt input e) \/
  (l <> p /\ exists wire, past_receive past ChoiceDelivery o l p wire /\
    @read X rd wire = Some a).

Record replay_family_laws : Prop := {
  replay_pure : forall p A o (x v : A) cut,
    at_code p A o (Pure x) cut -> returned p A cut v -> v = x;

  replay_comm : forall p X l r sh rd kl kr sl input sr o cut output,
    at_code p _ o (Perf (@Comm M p X l r sh rd kl kr sl input sr)) cut ->
    returned p _ cut output ->
    comm_observed past o rd p input output;

  (* Causal closure of the ACTIVE scope, not a typed payload equation. *)
  replay_sender_present : forall A active o (cuts : family A active),
    good A active o cuts ->
    forall kind sender recipient wire,
    In recipient active -> past_receive past kind o sender recipient wire ->
    In sender active;

  (* Past productions use the ORIGINAL operand at this syntax occurrence.
     The package equality is observed through sender_operand; there is no
     equality premise about a receiver's result or hidden payload Type. *)
  replay_original : forall S A (c : programs M A S) active inc o cuts,
    good A active o cuts -> family_at S A c active inc o cuts ->
    forall p (s : In p active) kind recipient a,
    sender_operand (c p (inc p s)) = Some a ->
    original_operand past kind o p recipient a;

  replay_app : forall S A B
      (f : programs M (fun p => A p -> B p) S) (x : programs M A S)
      active inc o (cuts : family B active),
    good B active o cuts ->
    family_at S B (fun p s => App (f p s) (x p s)) active inc o cuts ->
    exists (fs : family (fun p => A p -> B p) active) (xs : family A active),
      good _ active (child o AppFunction) fs /\
      good _ active (child o AppArgument) xs /\
      family_at S _ f active inc (child o AppFunction) fs /\
      family_at S _ x active inc (child o AppArgument) xs /\
      forall p d v, returned p _ (cuts p d) v ->
        exists g a, returned p _ (fs p d) g /\
          returned p _ (xs p d) a /\ v = g a;

  (* Combining per-role Bind states yields exactly a finite roster of entered
     bodies. It includes past senders needed by those body subcuts. The prefix
     values are the actual values stored in those states, not arbitrary values
     satisfying a source-level result relation. *)
  replay_bind : forall S A B (t : programs M A S)
      (k : forall p, S p -> A p -> Choreo M p (B p))
      active completed inc o (cuts : family B active)
      (done : includes (fun p => In p completed) (fun p => In p active))
      (v : values B (fun p => In p completed)),
    NoDup active -> NoDup completed ->
    good B active o cuts ->
    family_at S B (fun p s => Bind (t p s) (k p s)) active inc o cuts ->
    family_returned B active completed done cuts v ->
    exists entered
      (inside : includes (fun p => In p entered) (fun p => In p active))
      (finished : includes (fun p => In p completed) (fun p => In p entered))
      (prefix : family A active)
      (x : values A (fun p => In p entered))
      (body : family B entered),
      NoDup entered /\
      good A active (child o BindPrefix) prefix /\
      family_at S A t active inc (child o BindPrefix) prefix /\
      family_returned A active entered inside prefix x /\
      good B entered (child o BindBody) body /\
      (forall p d, at_code p _ (child o BindBody)
        (k p (inc p (inside p d)) (x p d)) (body p d)) /\
      family_returned B entered completed finished body v;

  (* Choice inversion exposes DIFFERENT per-role arguments. The theorem below
     derives their equality from the actual owner/past wire observations. *)
  replay_cond : forall S X l A
      (sh : forall p, S p -> Show X) (rd : forall p, S p -> Read X)
      (input : values (fun p => At X l p) S)
      (k : forall p, S p -> X -> Choreo M p (A p))
      active completed inc o (cuts : family A active)
      (done : includes (fun p => In p completed) (fun p => In p active))
      (v : values A (fun p => In p completed)),
    NoDup active -> NoDup completed ->
    good A active o cuts ->
    family_at S A (fun p s => Perf (@Cond M p X l (A p)
      (sh p s) (rd p s) (known l) MkSSymbol (input p s) (k p s)))
      active inc o cuts ->
    family_returned A active completed done cuts v ->
    exists entered
      (inside : includes (fun p => In p entered) (fun p => In p active))
      (finished : includes (fun p => In p completed) (fun p => In p entered))
      (choices : values (fun _ => X) (fun p => In p entered))
      (body : family A entered),
      NoDup entered /\
      good A entered (child o ChoiceBody) body /\
      (forall p d, choice_observation X l p (rd p (inc p (inside p d)))
        (input p (inc p (inside p d))) o (choices p d)) /\
      (forall p d, at_code p _ (child o ChoiceBody)
        (k p (inc p (inside p d)) (choices p d)) (body p d)) /\
      family_returned A entered completed finished body v
}.

Theorem structural_played_family (L : replay_family_laws) R S A c Q :
  structural R M S A c Q ->
  forall active completed (inc : includes (fun p => In p active) S)
    o (cuts : family A active) (v : values A (fun p => In p completed))
    (done : includes (fun p => In p completed) (fun p => In p active)),
  (forall p (s t : S p), s = t) ->
  NoDup active -> NoDup completed ->
  good A active o cuts ->
  family_at S A c active inc o cuts ->
  family_returned A active completed done cuts v ->
  Q (fun p => In p completed) v.
Proof.
  destruct L as [PureLaw CommLaw SenderLaw OriginalLaw AppLaw BindLaw CondLaw].
  intro W.
  induction W as
    [S A input c Shape
    |S X l f c Owner Shape
    |S X l r sh rd input c Sender Receiver Codec Shape
    |S X l A sh rd input k K c Owner Codec Branch IH Shape
    |S A B f x F X c WFf IHf WFx IHx Shape
    |S A B t k P K c WFt IHt Body IHbody Shape];
    intros active completed inc o cuts v done PI NA ND Good At Ret.
  - split; [intros p d; exact (inc p (done p d))|].
    intros p d s.
    assert (Value : v p d = input p (inc p (done p d))).
    { eapply PureLaw.
      - rewrite <- Shape. apply At.
      - apply Ret. }
    now rewrite (PI p (inc p (done p d)) s) in Value.
  - intros p d. exact (inc p (done p d)).
  - assert (Head : family_at S _ (fun p s =>
      Perf (@Comm M p X l r (sh p s) (rd p s)
        (known l) (known r) MkSSymbol (input p s) MkSSymbol))
      active inc o cuts).
    { intros p s. rewrite <- Shape. apply At. }
    split; [intros p d; exact (inc p (done p d))|].
    intros s d.
    assert (Observe : comm_observed past o (rd r (inc r (done r d))) r
      (input r (inc r (done r d))) (v r d)).
    { eapply CommLaw; [apply Head|apply Ret]. }
    destruct Observe as [(same & Self)|(Different & Remote)].
    + destruct same. specialize (Self eq_refl).
      now rewrite (PI l (inc l (done l d)) s) in Self.
    + destruct (Remote eq_refl) as (wire & Past & Read).
      pose proof (SenderLaw _ _ _ cuts Good DataDelivery l r wire
        (done r d) Past) as Present.
      assert (Origin : original_operand past DataDelivery o l r
        (Operand X (sh l s) (unAt (input l s) eq_refl))).
      { rewrite <- (PI l (inc l Present) s).
        eapply (OriginalLaw S _ _ active inc o cuts Good Head l Present
          DataDelivery r).
        apply comm_sender_operand. }
      eapply received_original_value.
      * apply Codec. exact Different.
      * exact Origin.
      * exact Past.
      * exact Read.
  - destruct completed as [|first rest].
    { left. intros p d. contradiction. }
    assert (Head : family_at S A (fun p s =>
      Perf (@Cond M p X l (A p) (sh p s) (rd p s)
        (known l) MkSSymbol (input p s) (k p s))) active inc o cuts).
    { intros p s. rewrite <- Shape. apply At. }
    destruct (CondLaw S X l A sh rd input k active (first :: rest)
      inc o cuts done v NA ND Good Head Ret)
      as (entered & inside & finished & choices & branch &
        NE & BranchGood & Observe & BranchAt & BranchRet).
    assert (Present : In l active).
    { destruct (Observe first (finished first (or_introl eq_refl)))
        as [(same & Local)|(Different & wire & Past & Read)].
      - destruct same. apply inside. apply finished. now left.
      - eapply SenderLaw; [exact Good| |exact Past].
        apply inside. apply finished. now left. }
    set (owner := inc l Present).
    set (a := unAt (input l owner) eq_refl).
    assert (SenderOperand : sender_operand
      (Perf (@Cond M l X l (A l) (sh l owner) (rd l owner)
        (known l) MkSSymbol (input l owner) (k l owner))) =
      Some (Operand X (sh l owner) a)).
    { cbn [sender_operand].
      destruct (List.list_eq_dec BinNat.N.eq_dec l l) as [same|Different].
      - assert (same = eq_refl).
        { apply UIP_dec. apply List.list_eq_dec. exact BinNat.N.eq_dec. }
        subst same. reflexivity.
      - contradiction. }
    assert (Common : forall p d, choices p d = a).
    { intros p d. destruct (Observe p d) as [(same & Local)|Remote].
      - destruct same. unfold a, owner.
        now rewrite (PI l (inc l (inside l d)) (inc l Present)) in Local.
      - destruct Remote as (Different & wire & Past & Read).
        eapply received_original_value.
        + apply (Codec p owner (inc p (inside p d))).
          intro Eq. apply Different. now symmetry.
        + exact (OriginalLaw S _ _ active inc o cuts Good Head l Present
            ChoiceDelivery p _ SenderOperand).
        + exact Past.
        + exact Read. }
    right. exists a. split.
    + eapply (IH a entered (first :: rest)
        (fun p d => inc p (inside p d)) (child o ChoiceBody)
        branch v finished PI NE ND BranchGood).
      * intros p d. rewrite <- (Common p d). apply BranchAt.
      * exact BranchRet.
    + intro s. unfold a. now rewrite (PI l s owner).
  - assert (Head : family_at S B (fun p s => App (f p s) (x p s))
      active inc o cuts).
    { intros p s. rewrite <- Shape. apply At. }
    destruct (AppLaw S A B f x active inc o cuts Good Head)
      as (fs & xs & FGood & XGood & FAt & XAt & Split).
    destruct (app_completed_values A B completed v
      (fun p g => forall d : In p completed,
        returned p _ (fs p (done p d)) g)
      (fun p a => forall d : In p completed,
        returned p _ (xs p (done p d)) a)
      (roster_member_unique completed ND))
      as (fv & xv & Valid).
    { intros p d.
      destruct (Split p (done p d) (v p d) (Ret p d))
        as (g & a & FRet & XRet & Eq).
      exists g,a. repeat split; try exact Eq; intro e;
        rewrite <- (roster_member_unique active NA p (done p d) (done p e));
        assumption. }
    exists fv,xv. split.
    + eapply (IHf active completed inc (child o AppFunction)
        fs fv done PI NA ND FGood FAt).
      intros p d. exact (proj1 (Valid p d) d).
    + split.
      * eapply (IHx active completed inc (child o AppArgument)
          xs xv done PI NA ND XGood XAt).
        intros p d. exact (proj1 (proj2 (Valid p d)) d).
      * intros p d. exact (proj2 (proj2 (Valid p d))).
  - assert (Head : family_at S B (fun p s => Bind (t p s) (k p s))
      active inc o cuts).
    { intros p s. rewrite <- Shape. apply At. }
    destruct (BindLaw S A B t k active completed inc o cuts done v
      NA ND Good Head Ret)
      as (entered & inside & finished & prefix & x & body &
        NE & PrefixGood & PrefixAt & PrefixRet & BodyGood & BodyAt & BodyRet).
    assert (Prefix : P (fun p => In p entered) x).
    { exact (IHt active entered inc (child o BindPrefix)
        prefix x inside PI NA NE PrefixGood PrefixAt PrefixRet). }
    unfold bind_results. exists (fun p => In p entered),x.
    split; [exact Prefix|].
    eapply (IHbody (fun p => In p entered) x
      (fun p d => inc p (inside p d)) Prefix
      entered completed (fun p d => d) (child o BindBody)
      body v finished (roster_member_unique entered NE) NE ND BodyGood).
    + exact BodyAt.
    + exact BodyRet.
Qed.

End Families.

Print Assumptions structural_played_family.
