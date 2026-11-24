From Stdlib Require Import Lists.List Arith.PeanoNat micromega.Lia.
Require Import Data.FingerTree FingerTreeProofs.CoreModel FingerTreeProofs.CoreOperations
  FingerTreeProofs.CoreSize.
Import ListNotations.

Section Search.
Context {v : Type} `{GHC.Base.Monoid v}.
Hypothesis assoc : forall x y z : v, GHC.Base.mappend (GHC.Base.mappend x y) z =
  GHC.Base.mappend x (GHC.Base.mappend y z).
Hypothesis left_id : forall x : v, GHC.Base.mappend GHC.Base.mempty x = x.
Hypothesis right_id : forall x : v, GHC.Base.mappend x GHC.Base.mempty = x.

Definition cutTest {a} (mu : a -> v) (p : v -> v -> bool) (xs : list a) (i : nat) : bool :=
  p (listMeasure mu (List.firstn i xs)) (listMeasure mu (List.skipn i xs)).

Definition cutDomain {a} (mu : a -> v) (xs : list a) (l r : v) : Prop :=
  exists i, i <= Datatypes.length xs /\
    l = listMeasure mu (List.firstn i xs) /\ r = listMeasure mu (List.skipn i xs).

Definition nonemptyPrefixDomain {a} (mu : a -> v) (xs : list a) (w : v) : Prop :=
  exists i, 0 < i /\ i <= Datatypes.length xs /\ w = listMeasure mu (List.firstn i xs).

Definition optionDigitMeasure {a} (M : Measured v a) (d : option (Digit a)) : v :=
  match d with None => GHC.Base.mempty | Some d => digitMeasure (@measure v a _ _ M) d end.

Definition optionDigitValidity {a} (P : a -> Prop) (d : option (Digit a)) : Prop :=
  match d with None => True | Some d => digitValidity P d end.

Local Ltac monoid := repeat rewrite ?assoc, ?left_id, ?right_id in *.

Lemma searchDigit_boundaries {a} (M : Measured v a) p vl d vr :
  p vl (GHC.Base.mappend (measure d) vr) = false ->
  p (GHC.Base.mappend vl (measure d)) vr = true ->
  let '(MkSplit l x r) := searchDigit p vl d vr in
  p (GHC.Base.mappend vl (optionDigitMeasure M l))
    (GHC.Base.mappend (measure x) (GHC.Base.mappend (optionDigitMeasure M r) vr)) = false /\
  p (GHC.Base.mappend (GHC.Base.mappend vl (optionDigitMeasure M l)) (measure x))
    (GHC.Base.mappend (optionDigitMeasure M r) vr) = true.
Proof.
  intros E0 E1; rewrite measure_digit_model in E0, E1.
  destruct d; cbn [searchDigit GHC.Prim.seq optionDigitMeasure digitMeasure] in *;
    repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:? end;
    cbn [optionDigitMeasure digitMeasure]; monoid; tauto.
Qed.

Lemma searchDigit_validity {a} (M : Measured v a) P p vl d vr :
  digitValidity P d ->
  let '(MkSplit l x r) := searchDigit p vl d vr in
  optionDigitValidity P l /\ P x /\ optionDigitValidity P r.
Proof.
  intro V; destruct d; cbn [searchDigit GHC.Prim.seq];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn [optionDigitValidity digitValidity] in *; tauto.
Qed.

Lemma searchDigit_contentsWith {a b} (M : Measured v a) (f : a -> list b) p vl d vr :
  let '(MkSplit l x r) := searchDigit p vl d vr in
  digitContentsWith f d =
    (match l with None => [] | Some d => digitContentsWith f d end) ++ f x ++
    (match r with None => [] | Some d => digitContentsWith f d end).
Proof.
  destruct d; cbn [searchDigit GHC.Prim.seq digitContentsWith];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn [digitContentsWith]; rewrite ?List.app_nil_r;
    repeat rewrite <- List.app_assoc; reflexivity.
Qed.

Lemma searchNode_as_digit {a} (M : Measured v a) p vl (n : Node v a) vr :
  searchNode p vl n vr = searchDigit p vl (nodeToDigit n) vr.
Proof. destruct n; reflexivity. Qed.

Lemma valid_measure_list {a} (M : Measured v a) P (t : FingerTree v a) :
  validityWith (@measure v a _ _ M) P t ->
  measure t = listMeasure (@measure v a _ _ M) (contents t).
Proof.
  intro V; rewrite measure_tree_model.
  eapply valid_tree_measure; [exact assoc|exact left_id| |exact V].
  intros; cbn [listMeasure List.fold_right]; symmetry; apply right_id.
Qed.

Lemma deepL_measure {a} (M : Measured v a) P pr m sf :
  optionDigitValidity P pr ->
  validityWith nodeCache (nodeValidity (@measure v a _ _ M) P) m -> digitValidity P sf ->
  measure (deepL pr m sf) = GHC.Base.mappend
    (GHC.Base.mappend (optionDigitMeasure M pr) (measure m)) (measure sf).
Proof.
  intros Vp Vm Vs.
  rewrite (valid_measure_list M P (deepL pr m sf)) by
    (apply deepL_validityWith; assumption).
  unfold contents; rewrite deepL_contentsWith.
  rewrite !listMeasure_app by assumption.
  rewrite <- (valid_tree_measure assoc left_id _ m nodeCache
    (nodeValidity (@measure v a _ _ M) P) a (nodeContentsWith (fun x => [x])) measure).
  - destruct pr; cbn [optionDigitMeasure];
      rewrite <- ?digitMeasure_contents by assumption;
      rewrite <- ?measure_digit_model; cbn [listMeasure List.fold_right]; monoid; reflexivity.
  - intros n Vn; eapply valid_node_measure; [exact assoc|exact left_id| |exact Vn].
    intros; cbn [listMeasure List.fold_right]; symmetry; apply right_id.
  - exact Vm.
Qed.

Lemma deepR_measure {a} (M : Measured v a) P pr m sf :
  digitValidity P pr ->
  validityWith nodeCache (nodeValidity (@measure v a _ _ M) P) m -> optionDigitValidity P sf ->
  measure (deepR pr m sf) = GHC.Base.mappend
    (GHC.Base.mappend (measure pr) (measure m)) (optionDigitMeasure M sf).
Proof.
  intros Vp Vm Vs.
  rewrite (valid_measure_list M P (deepR pr m sf)) by
    (apply deepR_validityWith; assumption).
  unfold contents; rewrite deepR_contentsWith.
  rewrite !listMeasure_app by assumption.
  rewrite <- (valid_tree_measure assoc left_id _ m nodeCache
    (nodeValidity (@measure v a _ _ M) P) a (nodeContentsWith (fun x => [x])) measure).
  - destruct sf; cbn [optionDigitMeasure];
      rewrite <- ?digitMeasure_contents by assumption;
      rewrite <- ?measure_digit_model; cbn [listMeasure List.fold_right]; monoid; reflexivity.
  - intros n Vn; eapply valid_node_measure; [exact assoc|exact left_id| |exact Vn].
    intros; cbn [listMeasure List.fold_right]; symmetry; apply right_id.
  - exact Vm.
Qed.
Lemma maybeDigit_measure {a} (M : Measured v a) d :
  measure (Data.Maybe.maybe Empty digitToTree d) = optionDigitMeasure M d.
Proof.
  destruct d; cbn [Data.Maybe.maybe optionDigitMeasure]; [|reflexivity].
  rewrite measure_tree_model, digitToTree_cache by assumption; reflexivity.
Qed.

Lemma maybeDigit_validity {a} (M : Measured v a) P d :
  optionDigitValidity P d ->
  validityWith (@measure v a _ _ M) P (Data.Maybe.maybe Empty digitToTree d).
Proof.
  destruct d; cbn [Data.Maybe.maybe optionDigitValidity];
    [apply digitToTree_validityWith|intros; exact I].
Qed.

Lemma maybeDigit_contentsWith {a b} (M : Measured v a) (f : a -> list b) d :
  contentsWith f (Data.Maybe.maybe Empty digitToTree d) =
    match d with None => [] | Some d => digitContentsWith f d end.
Proof. destruct d; cbn [Data.Maybe.maybe]; [apply digitToTree_contentsWith|reflexivity]. Qed.

Lemma searchTree_contract : forall a (t : FingerTree v a) (M : Measured v a)
  (D : HsToRocq.Err.Default a) P b (f : a -> list b) p vl vr,
  validityWith (@measure v a _ _ M) P t -> t <> Empty ->
  p vl (GHC.Base.mappend (measure t) vr) = false ->
  p (GHC.Base.mappend vl (measure t)) vr = true ->
  let '(MkSplit l x r) := @searchTree v a _ _ M D p vl t vr in
  validityWith (@measure v a _ _ M) P l /\ P x /\ validityWith (@measure v a _ _ M) P r /\
  contentsWith f t = contentsWith f l ++ f x ++ contentsWith f r /\
  p (GHC.Base.mappend vl (measure l))
    (GHC.Base.mappend (measure x) (GHC.Base.mappend (measure r) vr)) = false /\
  p (GHC.Base.mappend (GHC.Base.mappend vl (measure l)) (measure x))
    (GHC.Base.mappend (measure r) vr) = true.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    (D : HsToRocq.Err.Default a) P b (f : a -> list b) p vl vr,
    validityWith (@measure v a _ _ M) P t -> t <> Empty ->
    p vl (GHC.Base.mappend (measure t) vr) = false ->
    p (GHC.Base.mappend vl (measure t)) vr = true ->
    let '(MkSplit l x r) := @searchTree v a _ _ M D p vl t vr in
    validityWith (@measure v a _ _ M) P l /\ P x /\ validityWith (@measure v a _ _ M) P r /\
    contentsWith f t = contentsWith f l ++ f x ++ contentsWith f r /\
    p (GHC.Base.mappend vl (measure l))
      (GHC.Base.mappend (measure x) (GHC.Base.mappend (measure r) vr)) = false /\
    p (GHC.Base.mappend (GHC.Base.mappend vl (measure l)) (measure x))
      (GHC.Base.mappend (measure r) vr) = true) _ _ _).
  - intros; contradiction.
  - intros a x M D P b f p vl vr V NE E0 E1.
    cbn [searchTree contentsWith validityWith]; repeat split; try exact V;
      try (rewrite List.app_nil_r; reflexivity).
    + change (p (GHC.Base.mappend vl GHC.Base.mempty)
        (GHC.Base.mappend (measure x) (GHC.Base.mappend GHC.Base.mempty vr)) = false).
      monoid; exact E0.
    + change (p (GHC.Base.mappend (GHC.Base.mappend vl GHC.Base.mempty) (measure x))
        (GHC.Base.mappend GHC.Base.mempty vr) = true).
      monoid; exact E1.
  - intros a c pr m IH sf M D P b f p vl vr [Vp [Vm [Vs Ec]]] NE E0 E1.
    change (p vl (GHC.Base.mappend c vr) = false) in E0.
    change (p (GHC.Base.mappend vl c) vr = true) in E1.
    change (c = GHC.Base.mappend (GHC.Base.mappend (measure pr) (measure m)) (measure sf)) in Ec.
    rewrite Ec in E0, E1.
    cbn [searchTree].
    destruct (p (GHC.Base.mappend vl (measure pr))
      (GHC.Base.mappend (measure m) (GHC.Base.mappend (measure sf) vr))) eqn:Epr.
    + pose proof (searchDigit_boundaries M p vl pr
        (GHC.Base.mappend (measure m) (GHC.Base.mappend (measure sf) vr))
        ltac:(monoid; exact E0) Epr) as Eb.
      pose proof (searchDigit_validity M P p vl pr
        (GHC.Base.mappend (measure m) (GHC.Base.mappend (measure sf) vr)) Vp) as Vd.
      pose proof (searchDigit_contentsWith M f p vl pr
        (GHC.Base.mappend (measure m) (GHC.Base.mappend (measure sf) vr))) as Ed.
      destruct (searchDigit p vl pr
        (GHC.Base.mappend (measure m) (GHC.Base.mappend (measure sf) vr))) as [l x r].
      destruct Vd as [Vl [Vx Vr]], Eb as [Eb0 Eb1].
      split; [apply maybeDigit_validity; exact Vl|].
      split; [exact Vx|].
      split; [apply deepL_validityWith; assumption|].
      split.
      * cbn [contentsWith]; rewrite maybeDigit_contentsWith, deepL_contentsWith, Ed;
          repeat rewrite <- List.app_assoc; reflexivity.
      * rewrite maybeDigit_measure, (deepL_measure M P r m sf Vr Vm Vs).
        monoid; tauto.
    + destruct (p (GHC.Base.mappend (GHC.Base.mappend vl (measure pr)) (measure m))
        (GHC.Base.mappend (measure sf) vr)) eqn:Em.
      * assert (Nm : m <> Empty).
        { intro E; subst m.
          change (p (GHC.Base.mappend vl (measure pr))
            (GHC.Base.mappend GHC.Base.mempty (GHC.Base.mappend (measure sf) vr)) = false) in Epr.
          change (p (GHC.Base.mappend (GHC.Base.mappend vl (measure pr)) GHC.Base.mempty)
            (GHC.Base.mappend (measure sf) vr) = true) in Em.
          monoid; congruence. }
        specialize (IH Measured__Node__5 DefaultNode (nodeValidity (@measure v a _ _ M) P)
          b (nodeContentsWith f) p (GHC.Base.mappend vl (measure pr))
          (GHC.Base.mappend (measure sf) vr) Vm Nm Epr Em).
        destruct (searchTree p (GHC.Base.mappend vl (measure pr)) m
          (GHC.Base.mappend (measure sf) vr)) as [ml n mr].
        destruct IH as [Vml [Vn [Vmr [Et [En0 En1]]]]].
        destruct (nodeToDigit_validity M P n Vn) as [Vnd Enc].
        change (measure n = measure (nodeToDigit n)) in Enc.
        pose proof (searchDigit_boundaries M p
          (GHC.Base.mappend (GHC.Base.mappend vl (measure pr)) (measure ml))
          (nodeToDigit n) (GHC.Base.mappend (measure mr) (GHC.Base.mappend (measure sf) vr))
          ltac:(rewrite <- Enc; exact En0) ltac:(rewrite <- Enc; exact En1)) as Eb.
        pose proof (searchDigit_validity M P p
          (GHC.Base.mappend (GHC.Base.mappend vl (measure pr)) (measure ml))
          (nodeToDigit n) (GHC.Base.mappend (measure mr) (GHC.Base.mappend (measure sf) vr)) Vnd) as Vd.
        pose proof (searchDigit_contentsWith M f p
          (GHC.Base.mappend (GHC.Base.mappend vl (measure pr)) (measure ml))
          (nodeToDigit n) (GHC.Base.mappend (measure mr) (GHC.Base.mappend (measure sf) vr))) as Ed.
        rewrite <- searchNode_as_digit in Eb, Vd, Ed.
        destruct (searchNode p
          (GHC.Base.mappend (GHC.Base.mappend vl (measure pr)) (measure ml)) n
          (GHC.Base.mappend (measure mr) (GHC.Base.mappend (measure sf) vr))) as [l x r].
        destruct Vd as [Vl [Vx Vr]], Eb as [Eb0 Eb1].
        split; [apply deepR_validityWith; assumption|].
        split; [exact Vx|].
        split; [apply deepL_validityWith; assumption|].
        split.
        -- cbn [contentsWith]; rewrite deepL_contentsWith, deepR_contentsWith, Et.
           rewrite nodeToDigit_contentsWith in Ed; rewrite Ed;
             repeat rewrite <- List.app_assoc; reflexivity.
        -- rewrite (deepR_measure M P pr ml l Vp Vml Vl), (deepL_measure M P r mr sf Vr Vmr Vs).
           monoid; tauto.
      * pose proof (searchDigit_boundaries M p
          (GHC.Base.mappend (GHC.Base.mappend vl (measure pr)) (measure m)) sf vr Em
          ltac:(monoid; exact E1)) as Eb.
        pose proof (searchDigit_validity M P p
          (GHC.Base.mappend (GHC.Base.mappend vl (measure pr)) (measure m)) sf vr Vs) as Vd.
        pose proof (searchDigit_contentsWith M f p
          (GHC.Base.mappend (GHC.Base.mappend vl (measure pr)) (measure m)) sf vr) as Ed.
        destruct (searchDigit p
          (GHC.Base.mappend (GHC.Base.mappend vl (measure pr)) (measure m)) sf vr) as [l x r].
        destruct Vd as [Vl [Vx Vr]], Eb as [Eb0 Eb1].
        split; [apply deepR_validityWith; assumption|].
        split; [exact Vx|].
        split; [apply maybeDigit_validity; exact Vr|].
        split.
        -- cbn [contentsWith]; rewrite maybeDigit_contentsWith, deepR_contentsWith, Ed;
             repeat rewrite <- List.app_assoc; reflexivity.
        -- rewrite maybeDigit_measure, (deepR_measure M P pr m l Vp Vm Vl).
           monoid; tauto.
Qed.
Lemma cutTest_app {a} (mu : a -> v) p (l r : list a) :
  cutTest mu p (l ++ r) (Datatypes.length l) = p (listMeasure mu l) (listMeasure mu r).
Proof.
  unfold cutTest; rewrite List.firstn_app, List.skipn_app, List.firstn_all, List.skipn_all,
    Nat.sub_diag; cbn; rewrite List.app_nil_r; reflexivity.
Qed.

Lemma listMeasure_cons {a} (mu : a -> v) x xs :
  listMeasure mu (x :: xs) = GHC.Base.mappend (mu x) (listMeasure mu xs).
Proof. reflexivity. Qed.

Lemma listMeasure_singleton {a} (mu : a -> v) x : listMeasure mu [x] = mu x.
Proof. cbn [listMeasure List.fold_right]; apply right_id. Qed.

Lemma cutTest_zero {a} (mu : a -> v) p xs :
  cutTest mu p xs 0 = p GHC.Base.mempty (listMeasure mu xs).
Proof. reflexivity. Qed.

Lemma cutTest_length {a} (mu : a -> v) p xs :
  cutTest mu p xs (Datatypes.length xs) = p (listMeasure mu xs) GHC.Base.mempty.
Proof. unfold cutTest; rewrite List.firstn_all, List.skipn_all; reflexivity. Qed.

Definition searchResultSpec {a} (M : Measured v a) p (t : FingerTree v a)
  (s : SearchResult v a) : Prop :=
  let xs := contents t in
  let b0 := cutTest (@measure v a _ _ M) p xs 0 in
  let bn := cutTest (@measure v a _ _ M) p xs (Datatypes.length xs) in
  match s with
  | OnLeft => b0 = true /\ bn = true
  | OnRight => b0 = false /\ bn = false
  | Nowhere => b0 = true /\ bn = false
  | Position l x r => b0 = false /\ bn = true /\ validity M l /\ validity M r /\
      xs = contents l ++ x :: contents r /\
      cutTest (@measure v a _ _ M) p xs (Datatypes.length (contents l)) = false /\
      cutTest (@measure v a _ _ M) p xs (S (Datatypes.length (contents l))) = true
  end.

Lemma search_correct {a} (M : Measured v a) p (t : FingerTree v a) :
  validity M t -> searchResultSpec M p t (search p t).
Proof.
  intro V.
  assert (Emeasure : measure t = listMeasure (@measure v a _ _ M) (contents t)).
  { apply measure_contents; assumption. }
  unfold search.
  destruct (Bool.Sumbool.sumbool_of_bool
    (andb (p GHC.Base.mempty (measure t)) (p (measure t) GHC.Base.mempty))) as [EL|EL].
  - apply Bool.andb_true_iff in EL; cbn [searchResultSpec].
    rewrite cutTest_zero, cutTest_length, <- Emeasure; exact EL.
  - destruct (Bool.Sumbool.sumbool_of_bool
      (andb (negb (p GHC.Base.mempty (measure t))) (p (measure t) GHC.Base.mempty))) as [EP|EP].
    + pose proof (proj1 (Bool.andb_true_iff _ _) EP) as [PL PR]; apply Bool.negb_true_iff in PL.
      assert (NE : t <> Empty).
      { intro E; subst t; cbn [contents contentsWith listMeasure List.fold_right] in Emeasure.
        change (p GHC.Base.mempty GHC.Base.mempty = false) in PL.
        change (p GHC.Base.mempty GHC.Base.mempty = true) in PR; congruence. }
      match goal with
      | |- context [@searchTree v a _ _ M ?D p GHC.Base.mempty t GHC.Base.mempty] =>
          pose proof (searchTree_contract a t M D (fun _ => True) a (fun x => [x]) p
            GHC.Base.mempty GHC.Base.mempty V NE
            ltac:(rewrite right_id; exact PL) ltac:(rewrite left_id; exact PR)) as C;
          destruct (@searchTree v a _ _ M D p GHC.Base.mempty t GHC.Base.mempty) as [l x r]
      end.
      destruct C as [Vl [_ [Vr [Et [Eb0 Eb1]]]]].
      change (contents t = contents l ++ x :: contents r) in Et.
      cbn [searchResultSpec]; rewrite cutTest_zero, cutTest_length, <- Emeasure.
      split; [exact PL|]; split; [exact PR|]; split; [exact Vl|]; split; [exact Vr|].
      split; [exact Et|].
      assert (Ml : measure l = listMeasure (@measure v a _ _ M) (contents l))
        by (apply measure_contents; assumption).
      assert (Mr : measure r = listMeasure (@measure v a _ _ M) (contents r))
        by (apply measure_contents; assumption).
      monoid; rewrite Et; split.
      * rewrite cutTest_app, listMeasure_cons, <- Ml, <- Mr; exact Eb0.
      * replace (contents l ++ x :: contents r) with ((contents l ++ [x]) ++ contents r)
          by (rewrite <- List.app_assoc; reflexivity).
        replace (S (Datatypes.length (contents l))) with (Datatypes.length (contents l ++ [x]))
          by (rewrite List.length_app; cbn; lia).
        rewrite cutTest_app, listMeasure_app by assumption.
        rewrite listMeasure_singleton, <- Ml, <- Mr; exact Eb1.
    + destruct (Bool.Sumbool.sumbool_of_bool
        (andb (negb (p GHC.Base.mempty (measure t))) (negb (p (measure t) GHC.Base.mempty)))) as [ER|ER].
      * apply Bool.andb_true_iff in ER; destruct ER as [PL PR].
        apply Bool.negb_true_iff in PL, PR.
        cbn [searchResultSpec]; rewrite cutTest_zero, cutTest_length, <- Emeasure; tauto.
      * cbn [searchResultSpec]; rewrite cutTest_zero, cutTest_length, <- Emeasure.
        destruct (p GHC.Base.mempty (measure t)), (p (measure t) GHC.Base.mempty);
          cbn in *; intuition discriminate.
Qed.
Lemma splitDigit_boundaries {a} (M : Measured v a) p i d :
  p (GHC.Base.mappend i (measure d)) = true ->
  let '(MkSplit l x r) := splitDigit p i d in
  (l = None \/ p (GHC.Base.mappend i (optionDigitMeasure M l)) = false) /\
  p (GHC.Base.mappend (GHC.Base.mappend i (optionDigitMeasure M l)) (measure x)) = true.
Proof.
  intro E; rewrite measure_digit_model in E.
  destruct d; cbn [splitDigit GHC.Prim.seq optionDigitMeasure digitMeasure] in *;
    repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:? end;
    cbn [optionDigitMeasure digitMeasure]; monoid; intuition discriminate.
Qed.

Lemma splitNode_as_digit {a} (M : Measured v a) p i (n : Node v a) :
  splitNode p i n = splitDigit p i (nodeToDigit n).
Proof. destruct n; reflexivity. Qed.

Lemma splitTree_boundaries : forall a (t : FingerTree v a) (M : Measured v a)
  (D : HsToRocq.Err.Default a) P p i,
  validityWith (@measure v a _ _ M) P t -> t <> Empty ->
  p (GHC.Base.mappend i (measure t)) = true ->
  let '(MkSplit l x r) := @splitTree v a _ _ M D p i t in
  (l = Empty \/ p (GHC.Base.mappend i (measure l)) = false) /\
  p (GHC.Base.mappend (GHC.Base.mappend i (measure l)) (measure x)) = true.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    (D : HsToRocq.Err.Default a) P p i,
    validityWith (@measure v a _ _ M) P t -> t <> Empty ->
    p (GHC.Base.mappend i (measure t)) = true ->
    let '(MkSplit l x r) := @splitTree v a _ _ M D p i t in
    (l = Empty \/ p (GHC.Base.mappend i (measure l)) = false) /\
    p (GHC.Base.mappend (GHC.Base.mappend i (measure l)) (measure x)) = true) _ _ _).
  - intros; contradiction.
  - intros a x M D P p i V NE E; cbn [splitTree]; split; [left; reflexivity|].
    change (p (GHC.Base.mappend (GHC.Base.mappend i GHC.Base.mempty) (measure x)) = true).
    rewrite right_id; exact E.
  - intros a c pr m IH sf M D P p i [Vp [Vm [Vs Ec]]] NE E.
    change (p (GHC.Base.mappend i c) = true) in E.
    change (c = GHC.Base.mappend (GHC.Base.mappend (measure pr) (measure m)) (measure sf)) in Ec.
    rewrite Ec in E; cbn [splitTree].
    destruct (p (GHC.Base.mappend i (measure pr))) eqn:Epr.
    + pose proof (splitDigit_boundaries M p i pr Epr) as Eb.
      destruct (splitDigit p i pr) as [l x r].
      destruct Eb as [Eb0 Eb1]; rewrite maybeDigit_measure.
      split; [destruct Eb0 as [->|Eb0]; [left; reflexivity|right; exact Eb0]|exact Eb1].
    + destruct (p (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure m))) eqn:Em.
      * assert (Nm : m <> Empty) by (eapply split_middle_nonempty; eassumption).
        pose proof (splitTree_validityWith assoc left_id right_id _ m Measured__Node__5 DefaultNode
          (nodeValidity (@measure v a _ _ M) P) p (GHC.Base.mappend i (measure pr)) Nm Vm) as Vmid.
        specialize (IH Measured__Node__5 DefaultNode (nodeValidity (@measure v a _ _ M) P)
          p (GHC.Base.mappend i (measure pr)) Vm Nm Em).
        destruct (splitTree p (GHC.Base.mappend i (measure pr)) m) as [ml n mr].
        destruct IH as [Eb0 Eb1], Vmid as [Vml [Vn Vmr]].
        destruct (nodeToDigit_validity M P n Vn) as [Vnd Enc].
        change (measure n = measure (nodeToDigit n)) in Enc.
        pose proof (splitDigit_boundaries M p
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure ml))
          (nodeToDigit n) ltac:(rewrite <- Enc; exact Eb1)) as En.
        pose proof (splitNode_validity M P p
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure ml)) n Vn) as Vd.
        rewrite <- splitNode_as_digit in En.
        destruct (splitNode p
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure ml)) n) as [l x r].
        destruct En as [En0 En1], Vd as [Vl [Vx Vr]].
        rewrite (deepR_measure M P pr ml l Vp Vml Vl).
        split.
        -- right; destruct En0 as [El|En0]; [subst l|monoid; exact En0].
           cbn [optionDigitMeasure]; monoid.
           destruct Eb0 as [El|Eb0]; [subst ml|exact Eb0].
           change (p (GHC.Base.mappend i (GHC.Base.mappend (measure pr) GHC.Base.mempty)) = false).
           rewrite right_id; exact Epr.
        -- monoid; exact En1.
      * pose proof (splitDigit_boundaries M p
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure m)) sf
          ltac:(monoid; exact E)) as Eb.
        pose proof (splitDigit_validity M P p
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure m)) sf Vs) as Vd.
        destruct (splitDigit p
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure m)) sf) as [l x r].
        destruct Eb as [Eb0 Eb1], Vd as [Vl [Vx Vr]].
        rewrite (deepR_measure M P pr m l Vp Vm Vl).
        split.
        -- right; destruct Eb0 as [->|Eb0]; [cbn [optionDigitMeasure]; monoid; exact Em|monoid; exact Eb0].
        -- monoid; exact Eb1.
Qed.
Fixpoint splitListFrom {a} (mu : a -> v) (p : v -> bool) (i : v) (xs : list a)
  : list a * list a :=
  match xs with
  | [] => ([], [])
  | x :: xs =>
      let j := GHC.Base.mappend i (mu x) in
      if p j then ([], x :: xs)
      else let '(l, r) := splitListFrom mu p j xs in (x :: l, r)
  end.

Definition splitReference {a} (mu : a -> v) p xs := splitListFrom mu p GHC.Base.mempty xs.

Definition prefixMonotone {a} (mu : a -> v) p (xs : list a) : Prop :=
  forall i j, 0 < i -> i <= j -> j <= Datatypes.length xs ->
  p (listMeasure mu (List.firstn i xs)) = true ->
  p (listMeasure mu (List.firstn j xs)) = true.

Definition prefixesFalse {a} (mu : a -> v) p i (xs : list a) : Prop :=
  forall l x r, xs = l ++ x :: r ->
    p (GHC.Base.mappend i (listMeasure mu (l ++ [x]))) = false.

Lemma splitListFrom_cut {a} (mu : a -> v) p : forall l x r i,
  prefixesFalse mu p i l ->
  p (GHC.Base.mappend i (listMeasure mu (l ++ [x]))) = true ->
  splitListFrom mu p i (l ++ x :: r) = (l, x :: r).
Proof.
  induction l as [|y l IH]; intros x r i F E.
  - cbn [List.app splitListFrom] in *; rewrite listMeasure_singleton in E; rewrite E; reflexivity.
  - cbn [List.app splitListFrom].
    pose proof (F [] y l eq_refl) as Fy; cbn [List.app] in Fy.
    rewrite listMeasure_singleton in Fy; rewrite Fy.
    rewrite IH; [reflexivity| |].
    + intros u z w El.
      pose proof (F (y :: u) z w ltac:(cbn; rewrite El; reflexivity)) as Fu.
      cbn [List.app] in Fu; rewrite listMeasure_cons in Fu; monoid; exact Fu.
    + cbn [List.app] in E; rewrite listMeasure_cons in E; monoid; exact E.
Qed.

Lemma splitListFrom_none {a} (mu : a -> v) p : forall xs i,
  prefixesFalse mu p i xs -> splitListFrom mu p i xs = (xs, []).
Proof.
  induction xs as [|y xs IH]; intros i F; [reflexivity|].
  cbn [splitListFrom].
  pose proof (F [] y xs eq_refl) as Fy; cbn [List.app] in Fy.
  rewrite listMeasure_singleton in Fy; rewrite Fy.
  rewrite IH; [reflexivity|].
  intros u z w E; pose proof (F (y :: u) z w ltac:(cbn; rewrite E; reflexivity)) as Fu.
  cbn [List.app] in Fu; rewrite listMeasure_cons in Fu; monoid; exact Fu.
Qed.

Lemma firstn_prefix {a} (l r : list a) : List.firstn (Datatypes.length l) (l ++ r) = l.
Proof. rewrite List.firstn_app, List.firstn_all, Nat.sub_diag; cbn; apply List.app_nil_r. Qed.

Lemma prefixMonotone_false_before {a} (mu : a -> v) p l r :
  prefixMonotone mu p (l ++ r) ->
  (l = [] \/ p (listMeasure mu l) = false) ->
  prefixesFalse mu p GHC.Base.mempty l.
Proof.
  intros Mono F u x w E; rewrite left_id.
  destruct F as [->|F]; [destruct u; discriminate|].
  destruct (p (listMeasure mu (u ++ [x]))) eqn:Ep; [|reflexivity].
  assert (B : Datatypes.length (u ++ [x]) <= Datatypes.length l).
  { rewrite E, !List.length_app; cbn; lia. }
  assert (B0 : 0 < Datatypes.length (u ++ [x])) by (rewrite List.length_app; cbn; lia).
  pose proof (Mono (Datatypes.length (u ++ [x])) (Datatypes.length l) B0 B
    ltac:(rewrite List.length_app; lia)) as Hm.
  rewrite firstn_prefix in Hm.
  assert (Efirst : List.firstn (Datatypes.length (u ++ [x])) (l ++ r) = u ++ [x]).
  { replace (l ++ r) with ((u ++ [x]) ++ (w ++ r)) by
      (rewrite E; repeat rewrite <- List.app_assoc; reflexivity).
    apply firstn_prefix. }
  rewrite Efirst in Hm; specialize (Hm Ep); congruence.
Qed.

Lemma split_true_contract {a} (M : Measured v a) p (t : FingerTree v a) l r :
  validity M t -> t <> Empty -> p (measure t) = true -> split p t = (l, r) ->
  exists x rr, r = consTree x rr /\ validity M l /\ validity M rr /\
    contents t = contents l ++ x :: contents rr /\
    (l = Empty \/ p (measure l) = false) /\ p (GHC.Base.mappend (measure l) (measure x)) = true.
Proof.
  intros V NE E Es; unfold split in Es; destruct t as [|u|c pr m sf]; [contradiction|..];
    match type of Es with
    | context [@splitTree v a _ _ M ?D p GHC.Base.mempty ?t] =>
      pose proof (splitTree_boundaries a t M D (fun _ => True) p GHC.Base.mempty V
        ltac:(discriminate) ltac:(rewrite left_id; exact E)) as Eb;
      pose proof (splitTree_validityWith assoc left_id right_id a t M D (fun _ => True)
        p GHC.Base.mempty ltac:(discriminate) V) as Ev;
      pose proof (splitTree_contentsWith right_id a t M D a (fun x => [x])
        p GHC.Base.mempty ltac:(discriminate)) as Ec;
      destruct (@splitTree v a _ _ M D p GHC.Base.mempty t) as [ll x rr]
    end;
    destruct (Bool.Sumbool.sumbool_of_bool _) as [Et|Et]; try congruence;
    inversion Es; subst l r; exists x, rr;
    destruct Ev as [Vl [_ Vr]], Eb as [Eb0 Eb1];
    repeat split; try assumption; monoid; assumption.
Qed.

Lemma split_false_contract {a} (M : Measured v a) p (t : FingerTree v a) :
  p (measure t) = false -> split p t = (t, Empty).
Proof.
  intro E; unfold split; destruct t as [|u|c pr m sf]; [reflexivity|..];
    match goal with |- context [@splitTree v a _ _ M ?D ?p ?i ?t] =>
      destruct (@splitTree v a _ _ M D p i t) end;
    destruct (Bool.Sumbool.sumbool_of_bool _); congruence.
Qed.

Lemma split_correct {a} (M : Measured v a) p (t : FingerTree v a) l r :
  validity M t -> prefixMonotone (@measure v a _ _ M) p (contents t) ->
  split p t = (l, r) ->
  splitReference (@measure v a _ _ M) p (contents t) = (contents l, contents r).
Proof.
  intros V Mono Es.
  assert (Et : t = Empty \/ t <> Empty) by
    (destruct t; [left; reflexivity|right; discriminate|right; discriminate]).
  destruct Et as [->|NE].
  - inversion Es; reflexivity.
  - destruct (p (measure t)) eqn:Ep.
    + destruct (split_true_contract M p t l r V NE Ep Es)
        as [x [rr [Er [Vl [Vr [Ec [Eb0 Eb1]]]]]]].
      unfold splitReference; rewrite Ec, Er, consTree_contents; apply splitListFrom_cut.
      * apply prefixMonotone_false_before with (r := x :: contents rr).
        -- rewrite <- Ec; exact Mono.
        -- destruct Eb0 as [->|Eb0]; [left; reflexivity|right].
           rewrite <- (measure_contents assoc left_id right_id M l Vl); exact Eb0.
      * rewrite listMeasure_app by assumption; rewrite listMeasure_singleton, left_id.
        rewrite <- (measure_contents assoc left_id right_id M l Vl); exact Eb1.
    + rewrite (split_false_contract M p t Ep) in Es; inversion Es; subst l r.
      unfold splitReference; apply splitListFrom_none.
      apply prefixMonotone_false_before with (r := []).
      * rewrite List.app_nil_r; exact Mono.
      * right; rewrite <- (measure_contents assoc left_id right_id M t V); exact Ep.
Qed.
Lemma search_classification {a} (M : Measured v a) p (t : FingerTree v a) :
  validity M t ->
  let b0 := cutTest (@measure v a _ _ M) p (contents t) 0 in
  let bn := cutTest (@measure v a _ _ M) p (contents t) (Datatypes.length (contents t)) in
  (search p t = OnLeft <-> b0 = true /\ bn = true) /\
  (search p t = OnRight <-> b0 = false /\ bn = false) /\
  (search p t = Nowhere <-> b0 = true /\ bn = false) /\
  ((exists l x r, search p t = Position l x r) <-> b0 = false /\ bn = true).
Proof.
  intro V; pose proof (search_correct M p t V) as C.
  destruct (search p t) as [l x r| | |]; cbn [searchResultSpec] in C;
    decompose [and] C; cbn;
    intuition (try congruence; try (exists l, x, r; reflexivity));
    match goal with Hex : exists l x r, _ |- _ =>
      destruct Hex as [ll [xx [rr E]]]; discriminate E end.
Qed.

Definition cutMonotone {a} (mu : a -> v) p (xs : list a) : Prop :=
  forall i j, i <= j -> j <= Datatypes.length xs ->
    cutTest mu p xs i = true -> cutTest mu p xs j = true.

Lemma crossing_unique {a} (mu : a -> v) p xs i j :
  cutMonotone mu p xs -> S i <= Datatypes.length xs -> S j <= Datatypes.length xs ->
  cutTest mu p xs i = false -> cutTest mu p xs (S i) = true ->
  cutTest mu p xs j = false -> cutTest mu p xs (S j) = true -> i = j.
Proof.
  intros Mono Bi Bj Fi Ti Fj Tj.
  destruct (Nat.lt_trichotomy i j) as [Hij|[->|Hji]]; [|reflexivity|].
  - pose proof (Mono (S i) j ltac:(lia) ltac:(lia) Ti); congruence.
  - pose proof (Mono (S j) i ltac:(lia) ltac:(lia) Tj); congruence.
Qed.

Lemma takeUntil_correct {a} (M : Measured v a) p (t : FingerTree v a) :
  validity M t -> prefixMonotone (@measure v a _ _ M) p (contents t) ->
  contents (takeUntil p t) = fst (splitReference (@measure v a _ _ M) p (contents t)).
Proof.
  intros V Mono; unfold takeUntil, GHC.Base.op_z2218U__, Data.Tuple.fst.
  destruct (split p t) as [l r] eqn:E.
  rewrite (split_correct M p t l r V Mono E); reflexivity.
Qed.

Lemma dropUntil_correct {a} (M : Measured v a) p (t : FingerTree v a) :
  validity M t -> prefixMonotone (@measure v a _ _ M) p (contents t) ->
  contents (dropUntil p t) = snd (splitReference (@measure v a _ _ M) p (contents t)).
Proof.
  intros V Mono; unfold dropUntil, GHC.Base.op_z2218U__, Data.Tuple.snd.
  destruct (split p t) as [l r] eqn:E.
  rewrite (split_correct M p t l r V Mono E); reflexivity.
Qed.

Lemma split_trigger_contract {a} (M : Measured v a) p (t : FingerTree v a) l r :
  validity M t -> p GHC.Base.mempty = false -> p (measure t) = true -> split p t = (l, r) ->
  validity M l /\ validity M r /\ r <> Empty /\ p (measure l) = false /\
  exists x rr, contents r = x :: contents rr /\ validity M rr /\
    contents t = contents l ++ x :: contents rr /\ p (GHC.Base.mappend (measure l) (measure x)) = true.
Proof.
  intros V E0 E1 Es.
  assert (NE : t <> Empty) by (intro E; subst t; change (p GHC.Base.mempty = true) in E1; congruence).
  destruct (split_true_contract M p t l r V NE E1 Es)
    as [x [rr [Er [Vl [Vr [Ec [Eb0 Eb1]]]]]]].
  split; [exact Vl|]; split.
  - subst r; apply consTree_validity; assumption.
  - split.
    + intro E; pose proof (f_equal (@contents v a) Er) as Hc.
      rewrite E, consTree_contents in Hc; discriminate.
    + split.
      * destruct Eb0 as [->|Eb0]; [exact E0|exact Eb0].
      * exists x, rr; rewrite Er, consTree_contents; tauto.
Qed.
Definition allCuts {a} (D : v -> v -> Prop) (mu : a -> v) vl (xs : list a) vr : Prop :=
  forall l r, xs = l ++ r ->
    D (GHC.Base.mappend vl (listMeasure mu l)) (GHC.Base.mappend (listMeasure mu r) vr).

Definition allPrefixes {a} (D : v -> Prop) (mu : a -> v) i (xs : list a) : Prop :=
  forall l r, xs = l ++ r -> l <> [] -> D (GHC.Base.mappend i (listMeasure mu l)).

Lemma allCuts_block {a} D (mu : a -> v) vl l xs r vr :
  allCuts D mu vl (l ++ xs ++ r) vr ->
  allCuts D mu (GHC.Base.mappend vl (listMeasure mu l)) xs (GHC.Base.mappend (listMeasure mu r) vr).
Proof.
  intros C u w E; pose proof (C (l ++ u) (w ++ r)
    ltac:(rewrite E; repeat rewrite <- List.app_assoc; reflexivity)) as Cu.
  rewrite !listMeasure_app in Cu by assumption; monoid; exact Cu.
Qed.

Lemma allPrefixes_block {a} D (mu : a -> v) i l xs r :
  allPrefixes D mu i (l ++ xs ++ r) ->
  allPrefixes D mu (GHC.Base.mappend i (listMeasure mu l)) xs.
Proof.
  intros C u w E NE; pose proof (C (l ++ u) (w ++ r)
    ltac:(rewrite E; repeat rewrite <- List.app_assoc; reflexivity)
    ltac:(intro E0; apply List.app_eq_nil in E0; tauto)) as Cu.
  rewrite listMeasure_app in Cu by assumption; monoid; exact Cu.
Qed.

Lemma listMeasure_blocks {a b} (mu : a -> v) P (nu : b -> v) (f : a -> list b) xs :
  (forall x, P x -> mu x = listMeasure nu (f x)) -> List.Forall P xs ->
  listMeasure mu xs = listMeasure nu (List.flat_map f xs).
Proof.
  intros E V; induction V as [|x xs Vx Vxs IH]; [reflexivity|].
  cbn [List.flat_map]; rewrite listMeasure_app by assumption.
  rewrite listMeasure_cons, IH, (E x Vx); reflexivity.
Qed.

Lemma allCuts_flatten {a b} D (mu : a -> v) P (nu : b -> v) (f : a -> list b) vl xs vr :
  (forall x, P x -> mu x = listMeasure nu (f x)) -> List.Forall P xs ->
  allCuts D nu vl (List.flat_map f xs) vr -> allCuts D mu vl xs vr.
Proof.
  intros E V C l r Exs; subst xs; rewrite List.Forall_app in V; destruct V as [Vl Vr].
  specialize (C (List.flat_map f l) (List.flat_map f r) ltac:(apply List.flat_map_app)).
  rewrite <- (listMeasure_blocks mu P nu f l E Vl), <- (listMeasure_blocks mu P nu f r E Vr) in C.
  exact C.
Qed.

Lemma allPrefixes_flatten {a b} D (mu : a -> v) P (nu : b -> v) (f : a -> list b) i xs :
  (forall x, P x -> mu x = listMeasure nu (f x) /\ f x <> []) -> List.Forall P xs ->
  allPrefixes D nu i (List.flat_map f xs) -> allPrefixes D mu i xs.
Proof.
  intros E V C l r Exs NE; subst xs; rewrite List.Forall_app in V; destruct V as [Vl Vr].
  specialize (C (List.flat_map f l) (List.flat_map f r) ltac:(apply List.flat_map_app)).
  rewrite <- (listMeasure_blocks mu P nu f l ltac:(intros; apply E; assumption) Vl) in C.
  apply C; destruct l as [|x l]; [contradiction|].
  inversion Vl as [|xx ll Vx Vll]; subst; cbn [List.flat_map].
  intro E0; apply List.app_eq_nil in E0; destruct E0 as [Ex _]; eapply (proj2 (E x Vx)); exact Ex.
Qed.

Lemma digit_flatten {a b} (f : a -> list b) d :
  digitContentsWith f d = List.flat_map f (digitContentsWith (fun x => [x]) d).
Proof.
  destruct d; cbn [digitContentsWith List.flat_map List.app];
    repeat rewrite List.app_nil_r; reflexivity.
Qed.

Lemma node_flatten {a b} (f : a -> list b) (n : Node v a) :
  nodeContentsWith f n = List.flat_map f (nodeContentsWith (fun x => [x]) n).
Proof.
  destruct n; cbn [nodeContentsWith List.flat_map List.app];
    repeat rewrite List.app_nil_r; reflexivity.
Qed.

Lemma digit_elements {a} P (d : Digit a) :
  digitValidity P d -> List.Forall P (digitContentsWith (fun x => [x]) d).
Proof. destruct d; cbn [digitValidity digitContentsWith List.app]; intros; repeat constructor; tauto. Qed.

Lemma node_elements {a} (mu : a -> v) P n :
  nodeValidity mu P n -> List.Forall P (nodeContentsWith (fun x => [x]) n).
Proof. destruct n; cbn [nodeValidity nodeContentsWith List.app]; intros; repeat constructor; tauto. Qed.

(* This external instrumentation overapproximates each small helper by all of
   its local cuts. At Empty it records False, so a certificate also excludes the
   source's partial searchTree branch. It does not change the source algorithm. *)
Fixpoint searchCalls {a} (M : Measured v a) (D : v -> v -> Prop) (p : v -> v -> bool) (vl : v)
  (t : FingerTree v a) (vr : v) : Prop :=
  match t with
  | Empty => False
  | Single _ => True
  | Deep _ pr m sf =>
      let vm := measure m in
      let vsr := GHC.Base.mappend (measure sf) vr in
      let vlp := GHC.Base.mappend vl (measure pr) in
      D vlp (GHC.Base.mappend vm vsr) /\
      if p vlp (GHC.Base.mappend vm vsr) then
        allCuts D (@measure v a _ _ M) vl (digitContentsWith (fun x => [x]) pr)
          (GHC.Base.mappend vm vsr)
      else D (GHC.Base.mappend vlp vm) vsr /\
        if p (GHC.Base.mappend vlp vm) vsr then
          searchCalls Measured__Node__5 D p vlp m vsr /\
          forall Dn : HsToRocq.Err.Default (Node v a),
          let '(MkSplit ml n mr) := @searchTree v (Node v a) _ _ Measured__Node__5 Dn p vlp m vsr in
          allCuts D (@measure v a _ _ M) (GHC.Base.mappend vlp (measure ml))
            (nodeContentsWith (fun x => [x]) n) (GHC.Base.mappend (measure mr) vsr)
        else allCuts D (@measure v a _ _ M) (GHC.Base.mappend vlp vm)
          (digitContentsWith (fun x => [x]) sf) vr
  end.

Lemma searchCalls_domain : forall a (t : FingerTree v a) (M : Measured v a) P b
  (f : a -> list b) (nu : b -> v) D p vl vr,
  (forall x, P x -> @measure v a _ _ M x = listMeasure nu (f x)) ->
  validityWith (@measure v a _ _ M) P t -> t <> Empty ->
  allCuts D nu vl (contentsWith f t) vr -> searchCalls M D p vl t vr.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a) P b
    (f : a -> list b) (nu : b -> v) D p vl vr,
    (forall x, P x -> @measure v a _ _ M x = listMeasure nu (f x)) ->
    validityWith (@measure v a _ _ M) P t -> t <> Empty ->
    allCuts D nu vl (contentsWith f t) vr -> searchCalls M D p vl t vr) _ _ _).
  - intros; contradiction.
  - intros; exact I.
  - intros a c pr m IH sf M P b f nu D p vl vr Ef [Vp [Vm [Vs Ec]]] NE C.
    assert (Ep : measure pr = listMeasure nu (digitContentsWith f pr)) by
      (change (digitMeasure (@measure v a _ _ M) pr = listMeasure nu (digitContentsWith f pr)); eapply valid_digit_measure; eassumption).
    assert (Em : measure m = listMeasure nu (contentsWith (nodeContentsWith f) m)).
    { change (treeCacheWith nodeCache m = listMeasure nu (contentsWith (nodeContentsWith f) m)); eapply valid_tree_measure; [exact assoc|exact left_id| |exact Vm].
      intros n Vn; eapply valid_node_measure; eassumption. }
    assert (Es : measure sf = listMeasure nu (digitContentsWith f sf)) by
      (change (digitMeasure (@measure v a _ _ M) sf = listMeasure nu (digitContentsWith f sf)); eapply valid_digit_measure; eassumption).
    change (allCuts D nu vl (digitContentsWith f pr ++
      contentsWith (nodeContentsWith f) m ++ digitContentsWith f sf) vr) in C.
    assert (Cp : allCuts D nu vl (digitContentsWith f pr)
      (GHC.Base.mappend (measure m) (GHC.Base.mappend (measure sf) vr))).
    { pose proof (allCuts_block D nu vl [] (digitContentsWith f pr)
        (contentsWith (nodeContentsWith f) m ++ digitContentsWith f sf) vr C) as Cp.
      cbn [listMeasure List.fold_right] in Cp.
      (* Preserve listMeasure blocks when normalizing the context. *)
      change (allCuts D nu (GHC.Base.mappend vl GHC.Base.mempty) (digitContentsWith f pr)
        (GHC.Base.mappend (listMeasure nu (contentsWith (nodeContentsWith f) m ++ digitContentsWith f sf)) vr)) in Cp.
      rewrite listMeasure_app, <- Em, <- Es in Cp by assumption; monoid; exact Cp. }
    assert (Cm : allCuts D nu (GHC.Base.mappend vl (measure pr))
      (contentsWith (nodeContentsWith f) m) (GHC.Base.mappend (measure sf) vr)).
    { rewrite Ep, Es; apply allCuts_block; exact C. }
    assert (Cs : allCuts D nu (GHC.Base.mappend (GHC.Base.mappend vl (measure pr)) (measure m))
      (digitContentsWith f sf) vr).
    { assert (Cs0 : allCuts D nu vl
        ((digitContentsWith f pr ++ contentsWith (nodeContentsWith f) m) ++ digitContentsWith f sf ++ []) vr).
      { rewrite !List.app_nil_r, <- List.app_assoc; exact C. }
      pose proof (allCuts_block D nu vl _ _ [] vr Cs0) as Cs.
      change (allCuts D nu (GHC.Base.mappend vl
        (listMeasure nu (digitContentsWith f pr ++ contentsWith (nodeContentsWith f) m)))
        (digitContentsWith f sf) (GHC.Base.mappend GHC.Base.mempty vr)) in Cs.
      rewrite listMeasure_app, <- Ep, <- Em in Cs by assumption; monoid; exact Cs. }
    cbn [searchCalls]; split.
    + pose proof (C (digitContentsWith f pr)
        (contentsWith (nodeContentsWith f) m ++ digitContentsWith f sf) eq_refl) as G.
      rewrite listMeasure_app, <- Ep, <- Em, <- Es in G by assumption; monoid; exact G.
    + destruct (p (GHC.Base.mappend vl (measure pr))
        (GHC.Base.mappend (measure m) (GHC.Base.mappend (measure sf) vr))) eqn:Gp.
      * rewrite digit_flatten in Cp; eapply allCuts_flatten; [exact Ef|apply digit_elements; exact Vp|exact Cp].
      * split.
        -- pose proof (C (digitContentsWith f pr ++ contentsWith (nodeContentsWith f) m)
             (digitContentsWith f sf) ltac:(rewrite <- List.app_assoc; reflexivity)) as G.
           rewrite listMeasure_app, <- Ep, <- Em, <- Es in G by assumption; monoid; exact G.
        -- destruct (p (GHC.Base.mappend (GHC.Base.mappend vl (measure pr)) (measure m))
             (GHC.Base.mappend (measure sf) vr)) eqn:Gm.
           ++ assert (Nm : m <> Empty).
              { intro E; subst m; change (p (GHC.Base.mappend vl (measure pr))
                  (GHC.Base.mappend GHC.Base.mempty (GHC.Base.mappend (measure sf) vr)) = false) in Gp.
                change (p (GHC.Base.mappend (GHC.Base.mappend vl (measure pr)) GHC.Base.mempty)
                  (GHC.Base.mappend (measure sf) vr) = true) in Gm; monoid; congruence. }
              split.
              ** eapply (IH Measured__Node__5 (nodeValidity (@measure v a _ _ M) P) b
                   (nodeContentsWith f) nu); [|exact Vm|exact Nm|exact Cm].
                 intros n Vn; eapply valid_node_measure; eassumption.
              ** intro Dn; pose proof (searchTree_contract _ m Measured__Node__5 Dn
                   (nodeValidity (@measure v a _ _ M) P) b (nodeContentsWith f) p
                   (GHC.Base.mappend vl (measure pr)) (GHC.Base.mappend (measure sf) vr) Vm Nm Gp Gm) as T.
                 destruct (@searchTree v (Node v a) _ _ Measured__Node__5 Dn p
                   (GHC.Base.mappend vl (measure pr)) m (GHC.Base.mappend (measure sf) vr)) as [ml n mr].
                 destruct T as [Vl [Vn [Vr [Et _]]]].
                 assert (Eml : measure ml = listMeasure nu (contentsWith (nodeContentsWith f) ml)).
                 { change (treeCacheWith nodeCache ml = listMeasure nu (contentsWith (nodeContentsWith f) ml)); eapply valid_tree_measure; [exact assoc|exact left_id| |exact Vl].
                   intros z Vz; eapply valid_node_measure; eassumption. }
                 assert (Emr : measure mr = listMeasure nu (contentsWith (nodeContentsWith f) mr)).
                 { change (treeCacheWith nodeCache mr = listMeasure nu (contentsWith (nodeContentsWith f) mr)); eapply valid_tree_measure; [exact assoc|exact left_id| |exact Vr].
                   intros z Vz; eapply valid_node_measure; eassumption. }
                 rewrite Et in Cm; pose proof (allCuts_block D nu _ _ _ _ _ Cm) as Cn.
                 rewrite <- Eml, <- Emr in Cn.
                 rewrite node_flatten in Cn; eapply allCuts_flatten;
                   [exact Ef|apply node_elements with (mu := measure); exact Vn|exact Cn].
           ++ rewrite digit_flatten in Cs; eapply allCuts_flatten; [exact Ef|apply digit_elements; exact Vs|exact Cs].
Qed.
Lemma allCuts_domain {a} (mu : a -> v) xs :
  allCuts (cutDomain mu xs) mu GHC.Base.mempty xs GHC.Base.mempty.
Proof.
  intros l r E; subst xs; exists (Datatypes.length l); split.
  - rewrite List.length_app; lia.
  - rewrite firstn_prefix.
    rewrite List.skipn_app, List.skipn_all, Nat.sub_diag; cbn.
    split; [apply left_id|apply right_id].
Qed.

Lemma search_calls_on_cuts {a} (M : Measured v a) p (t : FingerTree v a) :
  validity M t -> t <> Empty ->
  searchCalls M (cutDomain (@measure v a _ _ M) (contents t)) p GHC.Base.mempty t GHC.Base.mempty.
Proof.
  intros V NE; eapply searchCalls_domain; [|exact V|exact NE|apply allCuts_domain].
  intros; symmetry; apply listMeasure_singleton.
Qed.

Definition searchDigitTests {a} (M : Measured v a) (D : v -> v -> Prop) vl (d : Digit a) vr : Prop :=
  match d with
  | One _ => True
  | Two x y => D (GHC.Base.mappend vl (measure x)) (GHC.Base.mappend (measure y) vr)
  | Three x y z =>
      D (GHC.Base.mappend vl (measure x)) (GHC.Base.mappend (measure y) (GHC.Base.mappend (measure z) vr)) /\
      D (GHC.Base.mappend (GHC.Base.mappend vl (measure x)) (measure y)) (GHC.Base.mappend (measure z) vr)
  | Four x y z w =>
      D (GHC.Base.mappend vl (measure x))
        (GHC.Base.mappend (measure y) (GHC.Base.mappend (measure z) (GHC.Base.mappend (measure w) vr))) /\
      D (GHC.Base.mappend (GHC.Base.mappend vl (measure x)) (measure y))
        (GHC.Base.mappend (measure z) (GHC.Base.mappend (measure w) vr)) /\
      D (GHC.Base.mappend (GHC.Base.mappend (GHC.Base.mappend vl (measure x)) (measure y)) (measure z))
        (GHC.Base.mappend (measure w) vr)
  end.

Lemma searchDigitTests_cuts {a} (M : Measured v a) D vl (d : Digit a) vr :
  allCuts D (@measure v a _ _ M) vl (digitContentsWith (fun x => [x]) d) vr ->
  searchDigitTests M D vl d vr.
Proof.
  intro C; destruct d as [x|x y|x y z|x y z w]; [exact I|..];
    cbn [searchDigitTests]; repeat split.
  - pose proof (C [x] [y] eq_refl) as E;
      cbn [listMeasure List.fold_right] in E; monoid; exact E.
  - pose proof (C [x] [y;z] eq_refl) as E;
      cbn [listMeasure List.fold_right] in E; monoid; exact E.
  - pose proof (C [x;y] [z] eq_refl) as E;
      cbn [listMeasure List.fold_right] in E; monoid; exact E.
  - pose proof (C [x] [y;z;w] eq_refl) as E;
      cbn [listMeasure List.fold_right] in E; monoid; exact E.
  - pose proof (C [x;y] [z;w] eq_refl) as E;
      cbn [listMeasure List.fold_right] in E; monoid; exact E.
  - pose proof (C [x;y;z] [w] eq_refl) as E;
      cbn [listMeasure List.fold_right] in E; monoid; exact E.
Qed.

Lemma searchDigit_parametric {a} (M : Measured v a) p q vl d vr :
  allCuts (fun l r => p l r = q l r) (@measure v a _ _ M) vl (digitContentsWith (fun x => [x]) d) vr ->
  searchDigit p vl d vr = searchDigit q vl d vr.
Proof.
  intro C; apply searchDigitTests_cuts in C.
  destruct d; cbn [searchDigit searchDigitTests] in *; decompose [and] C;
    repeat match goal with E : ?p = ?q |- context [?p] => rewrite E end; reflexivity.
Qed.

Lemma digitContents_nonempty {a b} P (f : a -> list b) d :
  (forall x, P x -> f x <> []) -> digitValidity P d -> digitContentsWith f d <> [].
Proof.
  intros E V; destruct d as [x|x y|x y z|x y z w]; cbn [digitValidity digitContentsWith] in *;
    intro Hnil; repeat match type of Hnil with _ ++ _ = [] => apply List.app_eq_nil in Hnil; destruct Hnil as [Hnil _] end;
    exact (E x ltac:(tauto) Hnil).
Qed.

Lemma nodeContents_nonempty {a b} (mu : a -> v) P (f : a -> list b) n :
  (forall x, P x -> f x <> []) -> nodeValidity mu P n -> nodeContentsWith f n <> [].
Proof.
  intros E V; destruct n as [c x y|c x y z]; cbn [nodeValidity nodeContentsWith] in *;
    intro Hnil; apply List.app_eq_nil in Hnil; destruct Hnil as [Hnil _];
    exact (E x ltac:(tauto) Hnil).
Qed.

Fixpoint splitCalls {a} (M : Measured v a) (D : v -> Prop) (p : v -> bool) (i : v)
  (t : FingerTree v a) : Prop :=
  match t with
  | Empty => False
  | Single _ => True
  | Deep _ pr m sf =>
      let vpr := GHC.Base.mappend i (measure pr) in
      let vm := GHC.Base.mappend vpr (measure m) in
      D vpr /\ if p vpr then
        allPrefixes D (@measure v a _ _ M) i (digitContentsWith (fun x => [x]) pr)
      else D vm /\ if p vm then
        splitCalls Measured__Node__5 D p vpr m /\
        forall Dn : HsToRocq.Err.Default (Node v a),
        let '(MkSplit ml n mr) := @splitTree v (Node v a) _ _ Measured__Node__5 Dn p vpr m in
        allPrefixes D (@measure v a _ _ M) (GHC.Base.mappend vpr (measure ml))
          (nodeContentsWith (fun x => [x]) n)
      else allPrefixes D (@measure v a _ _ M) vm (digitContentsWith (fun x => [x]) sf)
  end.

Lemma splitCalls_domain : forall a (t : FingerTree v a) (M : Measured v a) P b
  (f : a -> list b) (nu : b -> v) D p i,
  (forall x, P x -> @measure v a _ _ M x = listMeasure nu (f x) /\ f x <> []) ->
  validityWith (@measure v a _ _ M) P t -> t <> Empty ->
  allPrefixes D nu i (contentsWith f t) -> splitCalls M D p i t.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a) P b
    (f : a -> list b) (nu : b -> v) D p i,
    (forall x, P x -> @measure v a _ _ M x = listMeasure nu (f x) /\ f x <> []) ->
    validityWith (@measure v a _ _ M) P t -> t <> Empty ->
    allPrefixes D nu i (contentsWith f t) -> splitCalls M D p i t) _ _ _).
  - intros; contradiction.
  - intros; exact I.
  - intros a c pr m IH sf M P b f nu D p i Ef [Vp [Vm [Vs Ec]]] NE C.
    assert (Efun : forall x, P x -> measure x = listMeasure nu (f x)) by (intros; apply Ef; assumption).
    assert (Ep : measure pr = listMeasure nu (digitContentsWith f pr)) by
      (change (digitMeasure (@measure v a _ _ M) pr = listMeasure nu (digitContentsWith f pr)); eapply valid_digit_measure; eassumption).
    assert (Em : measure m = listMeasure nu (contentsWith (nodeContentsWith f) m)).
    { change (treeCacheWith nodeCache m = listMeasure nu (contentsWith (nodeContentsWith f) m));
        eapply valid_tree_measure; [exact assoc|exact left_id| |exact Vm].
      intros n Vn; eapply valid_node_measure; eassumption. }
    assert (NEp : digitContentsWith f pr <> []) by
      (apply (digitContents_nonempty P f pr); [intros x Vx; exact (proj2 (Ef x Vx))|exact Vp]).
    change (allPrefixes D nu i (digitContentsWith f pr ++
      contentsWith (nodeContentsWith f) m ++ digitContentsWith f sf)) in C.
    assert (Cp : allPrefixes D nu i (digitContentsWith f pr)).
    { pose proof (allPrefixes_block D nu i [] (digitContentsWith f pr)
        (contentsWith (nodeContentsWith f) m ++ digitContentsWith f sf) C) as Cp.
      change (allPrefixes D nu (GHC.Base.mappend i GHC.Base.mempty) (digitContentsWith f pr)) in Cp.
      rewrite right_id in Cp; exact Cp. }
    assert (Cm : allPrefixes D nu (GHC.Base.mappend i (measure pr)) (contentsWith (nodeContentsWith f) m)).
    { rewrite Ep; apply allPrefixes_block with (r := digitContentsWith f sf); exact C. }
    assert (Cs : allPrefixes D nu (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure m))
      (digitContentsWith f sf)).
    { assert (Cs0 : allPrefixes D nu i
        ((digitContentsWith f pr ++ contentsWith (nodeContentsWith f) m) ++ digitContentsWith f sf ++ [])).
      { rewrite !List.app_nil_r, <- List.app_assoc; exact C. }
      pose proof (allPrefixes_block D nu i _ _ [] Cs0) as Cs.
      rewrite listMeasure_app, <- Ep, <- Em in Cs by assumption; monoid; exact Cs. }
    cbn [splitCalls]; split.
    + pose proof (C (digitContentsWith f pr)
        (contentsWith (nodeContentsWith f) m ++ digitContentsWith f sf) eq_refl NEp) as G.
      rewrite <- Ep in G; exact G.
    + destruct (p (GHC.Base.mappend i (measure pr))) eqn:Gp.
      * rewrite digit_flatten in Cp; eapply allPrefixes_flatten; [exact Ef|apply digit_elements; exact Vp|exact Cp].
      * split.
        -- pose proof (C (digitContentsWith f pr ++ contentsWith (nodeContentsWith f) m)
             (digitContentsWith f sf) ltac:(rewrite <- List.app_assoc; reflexivity)
             ltac:(intro E; apply List.app_eq_nil in E; tauto)) as G.
           rewrite listMeasure_app, <- Ep, <- Em in G by assumption; monoid; exact G.
        -- destruct (p (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure m))) eqn:Gm.
           ++ assert (Nm : m <> Empty) by (eapply split_middle_nonempty; eassumption).
              split.
              ** eapply (IH Measured__Node__5 (nodeValidity (@measure v a _ _ M) P) b
                   (nodeContentsWith f) nu); [|exact Vm|exact Nm|exact Cm].
                 intros n Vn; split.
                 --- eapply valid_node_measure; eassumption.
                 --- apply (nodeContents_nonempty (@measure v a _ _ M) P f n);
                       [intros x Vx; exact (proj2 (Ef x Vx))|exact Vn].
              ** intro Dn.
                 pose proof (splitTree_validityWith assoc left_id right_id _ m Measured__Node__5 Dn
                   (nodeValidity (@measure v a _ _ M) P) p (GHC.Base.mappend i (measure pr)) Nm Vm) as Vmid.
                 pose proof (splitTree_contentsWith right_id _ m Measured__Node__5 Dn b
                   (nodeContentsWith f) p (GHC.Base.mappend i (measure pr)) Nm) as Et.
                 destruct (@splitTree v (Node v a) _ _ Measured__Node__5 Dn p
                   (GHC.Base.mappend i (measure pr)) m) as [ml n mr].
                 destruct Vmid as [Vl [Vn Vr]].
                 assert (Eml : measure ml = listMeasure nu (contentsWith (nodeContentsWith f) ml)).
                 { change (treeCacheWith nodeCache ml = listMeasure nu (contentsWith (nodeContentsWith f) ml));
                     eapply valid_tree_measure; [exact assoc|exact left_id| |exact Vl].
                   intros z Vz; eapply valid_node_measure; eassumption. }
                 rewrite Et in Cm; pose proof (allPrefixes_block D nu _ _ _ _ Cm) as Cn.
                 rewrite <- Eml in Cn; rewrite node_flatten in Cn.
                 eapply allPrefixes_flatten; [exact Ef|apply node_elements with (mu := measure); exact Vn|exact Cn].
           ++ rewrite digit_flatten in Cs; eapply allPrefixes_flatten; [exact Ef|apply digit_elements; exact Vs|exact Cs].
Qed.
Lemma allPrefixes_domain {a} (mu : a -> v) xs :
  allPrefixes (nonemptyPrefixDomain mu xs) mu GHC.Base.mempty xs.
Proof.
  intros l r E NE; subst xs; exists (Datatypes.length l).
  split; [destruct l; cbn in *; [contradiction|lia]|].
  split; [rewrite List.length_app; lia|].
  rewrite firstn_prefix; apply left_id.
Qed.

Lemma split_calls_on_nonempty_prefixes {a} (M : Measured v a) p (t : FingerTree v a) :
  validity M t -> t <> Empty ->
  splitCalls M (nonemptyPrefixDomain (@measure v a _ _ M) (contents t)) p GHC.Base.mempty t.
Proof.
  intros V NE; eapply splitCalls_domain; [|exact V|exact NE|apply allPrefixes_domain].
  intros; split; [symmetry; apply listMeasure_singleton|discriminate].
Qed.

Lemma nonempty_total_domain {a} (M : Measured v a) (t : FingerTree v a) :
  validity M t -> t <> Empty ->
  nonemptyPrefixDomain (@measure v a _ _ M) (contents t) (measure t).
Proof.
  intros V NE; exists (Datatypes.length (contents t)); split.
  - assert (E : contents t <> []) by (rewrite contents_empty_iff; exact NE).
    destruct (contents t); cbn in *; [contradiction|lia].
  - split; [lia|rewrite List.firstn_all; apply measure_contents; assumption].
Qed.

Lemma search_endpoint_domains {a} (M : Measured v a) (t : FingerTree v a) :
  validity M t ->
  cutDomain (@measure v a _ _ M) (contents t) GHC.Base.mempty (measure t) /\
  cutDomain (@measure v a _ _ M) (contents t) (measure t) GHC.Base.mempty.
Proof.
  intro V; split.
  - exists 0; split; [lia|cbn [List.firstn List.skipn]; split; [reflexivity|apply measure_contents; assumption]].
  - exists (Datatypes.length (contents t)); split; [lia|].
    rewrite List.firstn_all, List.skipn_all; split; [apply measure_contents; assumption|reflexivity].
Qed.

Lemma search_domain_certificate {a} (M : Measured v a) p (t : FingerTree v a) :
  validity M t ->
  cutDomain (@measure v a _ _ M) (contents t) GHC.Base.mempty (measure t) /\
  cutDomain (@measure v a _ _ M) (contents t) (measure t) GHC.Base.mempty /\
  (t = Empty \/ searchCalls M (cutDomain (@measure v a _ _ M) (contents t))
    p GHC.Base.mempty t GHC.Base.mempty).
Proof.
  intro V; destruct (search_endpoint_domains M t V) as [E0 En]; split; [exact E0|]; split; [exact En|].
  destruct t; [left; reflexivity|right; apply search_calls_on_cuts; assumption || discriminate|right; apply search_calls_on_cuts; assumption || discriminate].
Qed.

Lemma split_domain_certificate {a} (M : Measured v a) p (t : FingerTree v a) :
  validity M t ->
  match t with
  | Empty => True
  | _ => nonemptyPrefixDomain (@measure v a _ _ M) (contents t) (measure t) /\
      splitCalls M (nonemptyPrefixDomain (@measure v a _ _ M) (contents t)) p GHC.Base.mempty t
  end.
Proof.
  intro V; destruct t; [exact I|..]; split;
    first [apply nonempty_total_domain|apply split_calls_on_nonempty_prefixes]; assumption || discriminate.
Qed.

Lemma searchCalls_nonempty {a} (M : Measured v a) D p vl (t : FingerTree v a) vr :
  searchCalls M D p vl t vr -> t <> Empty.
Proof. destruct t; cbn [searchCalls]; intuition discriminate. Qed.

Lemma splitCalls_nonempty {a} (M : Measured v a) D p i (t : FingerTree v a) :
  splitCalls M D p i t -> t <> Empty.
Proof. destruct t; cbn [splitCalls]; intuition discriminate. Qed.

Definition splitDigitTests {a} (M : Measured v a) (D : v -> Prop) i (d : Digit a) : Prop :=
  match d with
  | One _ => True
  | Two x _ => D (GHC.Base.mappend i (measure x))
  | Three x y _ => D (GHC.Base.mappend i (measure x)) /\
      D (GHC.Base.mappend (GHC.Base.mappend i (measure x)) (measure y))
  | Four x y z _ => D (GHC.Base.mappend i (measure x)) /\
      D (GHC.Base.mappend (GHC.Base.mappend i (measure x)) (measure y)) /\
      D (GHC.Base.mappend (GHC.Base.mappend (GHC.Base.mappend i (measure x)) (measure y)) (measure z))
  end.

Lemma splitDigitTests_prefixes {a} (M : Measured v a) D i (d : Digit a) :
  allPrefixes D (@measure v a _ _ M) i (digitContentsWith (fun x => [x]) d) ->
  splitDigitTests M D i d.
Proof.
  intro C; destruct d as [x|x y|x y z|x y z w]; [exact I|..];
    cbn [splitDigitTests]; repeat split.
  - pose proof (C [x] [y] eq_refl ltac:(discriminate)) as E;
      cbn [listMeasure List.fold_right] in E; monoid; exact E.
  - pose proof (C [x] [y;z] eq_refl ltac:(discriminate)) as E;
      cbn [listMeasure List.fold_right] in E; monoid; exact E.
  - pose proof (C [x;y] [z] eq_refl ltac:(discriminate)) as E;
      cbn [listMeasure List.fold_right] in E; monoid; exact E.
  - pose proof (C [x] [y;z;w] eq_refl ltac:(discriminate)) as E;
      cbn [listMeasure List.fold_right] in E; monoid; exact E.
  - pose proof (C [x;y] [z;w] eq_refl ltac:(discriminate)) as E;
      cbn [listMeasure List.fold_right] in E; monoid; exact E.
  - pose proof (C [x;y;z] [w] eq_refl ltac:(discriminate)) as E;
      cbn [listMeasure List.fold_right] in E; monoid; exact E.
Qed.

Lemma splitDigit_parametric {a} (M : Measured v a) p q i d :
  allPrefixes (fun w => p w = q w) (@measure v a _ _ M) i (digitContentsWith (fun x => [x]) d) ->
  splitDigit p i d = splitDigit q i d.
Proof.
  intro C; apply splitDigitTests_prefixes in C.
  destruct d; cbn [splitDigit splitDigitTests] in *; decompose [and] C;
    repeat match goal with E : ?p = ?q |- context [?p] => rewrite E end; reflexivity.
Qed.

Lemma searchNode_parametric {a} (M : Measured v a) p q vl n vr :
  allCuts (fun l r => p l r = q l r) (@measure v a _ _ M) vl (nodeContentsWith (fun x => [x]) n) vr ->
  searchNode p vl n vr = searchNode q vl n vr.
Proof.
  intro C; rewrite !searchNode_as_digit; apply searchDigit_parametric.
  rewrite nodeToDigit_contentsWith; exact C.
Qed.

Lemma splitNode_parametric {a} (M : Measured v a) p q i n :
  allPrefixes (fun w => p w = q w) (@measure v a _ _ M) i (nodeContentsWith (fun x => [x]) n) ->
  splitNode p i n = splitNode q i n.
Proof.
  intro C; rewrite !splitNode_as_digit; apply splitDigit_parametric.
  rewrite nodeToDigit_contentsWith; exact C.
Qed.
Lemma searchTree_parametric : forall a (t : FingerTree v a) (M : Measured v a)
  (Da Db : HsToRocq.Err.Default a) D p q vl vr,
  searchCalls M D p vl t vr -> (forall l r, D l r -> p l r = q l r) ->
  @searchTree v a _ _ M Da p vl t vr = @searchTree v a _ _ M Db q vl t vr.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    (Da Db : HsToRocq.Err.Default a) D p q vl vr,
    searchCalls M D p vl t vr -> (forall l r, D l r -> p l r = q l r) ->
    @searchTree v a _ _ M Da p vl t vr = @searchTree v a _ _ M Db q vl t vr) _ _ _).
  - intros; contradiction.
  - intros; reflexivity.
  - intros a c pr m IH sf M Da Db D p q vl vr C E.
    cbn [searchCalls] in C; destruct C as [Dpr C].
    cbn [searchTree]; rewrite <- (E _ _ Dpr).
    destruct (p (GHC.Base.mappend vl (measure pr))
      (GHC.Base.mappend (measure m) (GHC.Base.mappend (measure sf) vr))) eqn:Gpr.
    + rewrite (searchDigit_parametric M p q vl pr
        (GHC.Base.mappend (measure m) (GHC.Base.mappend (measure sf) vr))
        ltac:(intros l r El; apply E; apply C; exact El)); reflexivity.
    + destruct C as [Dm C]; rewrite <- (E _ _ Dm).
      destruct (p (GHC.Base.mappend (GHC.Base.mappend vl (measure pr)) (measure m))
        (GHC.Base.mappend (measure sf) vr)) eqn:Gm.
      * destruct C as [Cm Cn].
        pose proof (IH Measured__Node__5 (@DefaultNode v a _ _ Da) (@DefaultNode v a _ _ Db)
          D p q (GHC.Base.mappend vl (measure pr)) (GHC.Base.mappend (measure sf) vr) Cm E) as Em.
        rewrite <- Em; specialize (Cn (@DefaultNode v a _ _ Da)).
        destruct (@searchTree v (Node v a) _ _ Measured__Node__5 (@DefaultNode v a _ _ Da) p
          (GHC.Base.mappend vl (measure pr)) m (GHC.Base.mappend (measure sf) vr)) as [ml n mr].
        rewrite (searchNode_parametric M p q
          (GHC.Base.mappend (GHC.Base.mappend vl (measure pr)) (measure ml)) n
          (GHC.Base.mappend (measure mr) (GHC.Base.mappend (measure sf) vr))
          ltac:(intros l r El; apply E; apply Cn; exact El)); reflexivity.
      * rewrite (searchDigit_parametric M p q
          (GHC.Base.mappend (GHC.Base.mappend vl (measure pr)) (measure m)) sf vr
          ltac:(intros l r El; apply E; apply C; exact El)); reflexivity.
Qed.

Lemma splitTree_parametric : forall a (t : FingerTree v a) (M : Measured v a)
  (Da Db : HsToRocq.Err.Default a) D p q i,
  splitCalls M D p i t -> (forall w, D w -> p w = q w) ->
  @splitTree v a _ _ M Da p i t = @splitTree v a _ _ M Db q i t.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    (Da Db : HsToRocq.Err.Default a) D p q i,
    splitCalls M D p i t -> (forall w, D w -> p w = q w) ->
    @splitTree v a _ _ M Da p i t = @splitTree v a _ _ M Db q i t) _ _ _).
  - intros; contradiction.
  - intros; reflexivity.
  - intros a c pr m IH sf M Da Db D p q i C E.
    cbn [splitCalls] in C; destruct C as [Dpr C].
    cbn [splitTree]; rewrite <- (E _ Dpr).
    destruct (p (GHC.Base.mappend i (measure pr))) eqn:Gpr.
    + rewrite (splitDigit_parametric M p q i pr
        ltac:(intros l r El NE; apply E; apply C with (r := r); assumption)); reflexivity.
    + destruct C as [Dm C]; rewrite <- (E _ Dm).
      destruct (p (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure m))) eqn:Gm.
      * destruct C as [Cm Cn].
        pose proof (IH Measured__Node__5 (@DefaultNode v a _ _ Da) (@DefaultNode v a _ _ Db)
          D p q (GHC.Base.mappend i (measure pr)) Cm E) as Em.
        rewrite <- Em; specialize (Cn (@DefaultNode v a _ _ Da)).
        destruct (@splitTree v (Node v a) _ _ Measured__Node__5 (@DefaultNode v a _ _ Da) p
          (GHC.Base.mappend i (measure pr)) m) as [ml n mr].
        rewrite (splitNode_parametric M p q
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure ml)) n
          ltac:(intros l r El NE; apply E; apply Cn with (r := r); assumption)); reflexivity.
      * rewrite (splitDigit_parametric M p q
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure m)) sf
          ltac:(intros l r El NE; apply E; apply C with (r := r); assumption)); reflexivity.
Qed.
Lemma search_empty {a} (M : Measured v a) p :
  @search v a _ _ M p Empty = if p GHC.Base.mempty GHC.Base.mempty then OnLeft else OnRight.
Proof.
  pose proof (search_correct M p Empty I) as C.
  destruct (search p Empty); cbn [searchResultSpec contents contentsWith Datatypes.length] in C;
    rewrite !cutTest_zero in C;
    change (listMeasure (@measure v a _ _ M) []) with (@GHC.Base.mempty v _ _) in C;
    destruct (p GHC.Base.mempty GHC.Base.mempty); cbn in *; intuition discriminate.
Qed.

Lemma search_nonempty_unfold {a} (M : Measured v a) (Da : HsToRocq.Err.Default a) p (t : FingerTree v a) :
  validity M t -> t <> Empty ->
  search p t =
    if p GHC.Base.mempty (measure t) then
      if p (measure t) GHC.Base.mempty then OnLeft else Nowhere
    else if p (measure t) GHC.Base.mempty then
      let '(MkSplit l x r) := @searchTree v a _ _ M Da p GHC.Base.mempty t GHC.Base.mempty in Position l x r
    else OnRight.
Proof.
  intros V NE; unfold search.
  destruct (Bool.Sumbool.sumbool_of_bool
    (andb (p GHC.Base.mempty (measure t)) (p (measure t) GHC.Base.mempty))) as [EL|EL].
  - apply Bool.andb_true_iff in EL; destruct EL as [PL PR]; rewrite PL, PR; reflexivity.
  - destruct (Bool.Sumbool.sumbool_of_bool
      (andb (negb (p GHC.Base.mempty (measure t))) (p (measure t) GHC.Base.mempty))) as [EP|EP].
    + pose proof (proj1 (Bool.andb_true_iff _ _) EP) as [PL PR]; apply Bool.negb_true_iff in PL.
      match goal with |- ?lhs = _ =>
        match lhs with context [@searchTree v a _ _ M ?Dx p GHC.Base.mempty t GHC.Base.mempty] =>
          rewrite (searchTree_parametric a t M Dx Da _ p p GHC.Base.mempty GHC.Base.mempty
            (search_calls_on_cuts M p t V NE) ltac:(reflexivity))
        end
      end.
      rewrite PL, PR; destruct (@searchTree v a _ _ M Da p GHC.Base.mempty t GHC.Base.mempty); reflexivity.
    + destruct (Bool.Sumbool.sumbool_of_bool
        (andb (negb (p GHC.Base.mempty (measure t))) (negb (p (measure t) GHC.Base.mempty)))) as [ER|ER];
        destruct (p GHC.Base.mempty (measure t)), (p (measure t) GHC.Base.mempty);
        cbn in *; intuition discriminate.
Qed.

Lemma search_parametric_on_cuts {a} (M : Measured v a) p q (t : FingerTree v a) :
  validity M t ->
  (forall l r, cutDomain (@measure v a _ _ M) (contents t) l r -> p l r = q l r) ->
  search p t = search q t.
Proof.
  intros V E.
  assert (G : forall (tt : FingerTree v a) (Da : HsToRocq.Err.Default a),
    validity M tt ->
    (forall l r, cutDomain (@measure v a _ _ M) (contents tt) l r -> p l r = q l r) ->
    tt <> Empty -> search p tt = search q tt).
  { intros tt Da Vt Ee NE.
    rewrite (search_nonempty_unfold M Da p tt Vt NE), (search_nonempty_unfold M Da q tt Vt NE).
    destruct (search_endpoint_domains M tt Vt) as [D0 Dn].
    rewrite <- (Ee _ _ D0), <- (Ee _ _ Dn).
    rewrite (searchTree_parametric a tt M Da Da _ p q GHC.Base.mempty GHC.Base.mempty
      (search_calls_on_cuts M p tt Vt NE) Ee); reflexivity. }
  destruct t as [|x|c pr m sf] eqn:Et.
  - rewrite !search_empty.
    assert (Ee : p GHC.Base.mempty GHC.Base.mempty = q GHC.Base.mempty GHC.Base.mempty).
    { apply E; exists 0; split; [cbn; lia|split; reflexivity]. }
    rewrite Ee; reflexivity.
  - apply (G (Single x) (HsToRocq.Err.Build_Default a x)); assumption || discriminate.
  - apply (G (Deep c pr m sf) (HsToRocq.Err.Build_Default a (lheadDigit pr))); assumption || discriminate.
Qed.

Lemma split_parametric_on_nonempty_prefixes {a} (M : Measured v a) p q (t : FingerTree v a) :
  validity M t ->
  (forall w, nonemptyPrefixDomain (@measure v a _ _ M) (contents t) w -> p w = q w) ->
  split p t = split q t.
Proof.
  intros V E; unfold split; destruct t as [|x|c pr m sf]; [reflexivity|..];
    match goal with
    | |- context [@splitTree v a _ _ M ?Da p GHC.Base.mempty ?t] =>
      match goal with
      | |- context [@splitTree v a _ _ M ?Db q GHC.Base.mempty t] =>
        rewrite (splitTree_parametric a t M Da Db _ p q GHC.Base.mempty
          (split_calls_on_nonempty_prefixes M p t V ltac:(discriminate)) E);
        destruct (@splitTree v a _ _ M Db q GHC.Base.mempty t);
        rewrite (E _ (nonempty_total_domain M t V ltac:(discriminate))); reflexivity
      end
    end.
Qed.

Lemma split_empty {a} (M : Measured v a) p : @split v a _ _ M p Empty = (Empty, Empty).
Proof. reflexivity. Qed.

Lemma splitReference_empty {a} (mu : a -> v) p : splitReference mu p [] = ([], []).
Proof. reflexivity. Qed.

End Search.

(* Full types and global-dependency audit for every exported constant. *)
Check @cutTest. Print Assumptions cutTest.
Check @cutDomain. Print Assumptions cutDomain.
Check @nonemptyPrefixDomain. Print Assumptions nonemptyPrefixDomain.
Check @optionDigitMeasure. Print Assumptions optionDigitMeasure.
Check @optionDigitValidity. Print Assumptions optionDigitValidity.
Check @searchDigit_boundaries. Print Assumptions searchDigit_boundaries.
Check @searchDigit_validity. Print Assumptions searchDigit_validity.
Check @searchDigit_contentsWith. Print Assumptions searchDigit_contentsWith.
Check @searchNode_as_digit. Print Assumptions searchNode_as_digit.
Check @valid_measure_list. Print Assumptions valid_measure_list.
Check @deepL_measure. Print Assumptions deepL_measure.
Check @deepR_measure. Print Assumptions deepR_measure.
Check @maybeDigit_measure. Print Assumptions maybeDigit_measure.
Check @maybeDigit_validity. Print Assumptions maybeDigit_validity.
Check @maybeDigit_contentsWith. Print Assumptions maybeDigit_contentsWith.
Check @searchTree_contract. Print Assumptions searchTree_contract.
Check @cutTest_app. Print Assumptions cutTest_app.
Check @listMeasure_cons. Print Assumptions listMeasure_cons.
Check @listMeasure_singleton. Print Assumptions listMeasure_singleton.
Check @cutTest_zero. Print Assumptions cutTest_zero.
Check @cutTest_length. Print Assumptions cutTest_length.
Check @searchResultSpec. Print Assumptions searchResultSpec.
Check @search_correct. Print Assumptions search_correct.
Check @splitDigit_boundaries. Print Assumptions splitDigit_boundaries.
Check @splitNode_as_digit. Print Assumptions splitNode_as_digit.
Check @splitTree_boundaries. Print Assumptions splitTree_boundaries.
Check @splitListFrom. Print Assumptions splitListFrom.
Check @splitReference. Print Assumptions splitReference.
Check @prefixMonotone. Print Assumptions prefixMonotone.
Check @prefixesFalse. Print Assumptions prefixesFalse.
Check @splitListFrom_cut. Print Assumptions splitListFrom_cut.
Check @splitListFrom_none. Print Assumptions splitListFrom_none.
Check @firstn_prefix. Print Assumptions firstn_prefix.
Check @prefixMonotone_false_before. Print Assumptions prefixMonotone_false_before.
Check @split_true_contract. Print Assumptions split_true_contract.
Check @split_false_contract. Print Assumptions split_false_contract.
Check @split_correct. Print Assumptions split_correct.
Check @search_classification. Print Assumptions search_classification.
Check @cutMonotone. Print Assumptions cutMonotone.
Check @crossing_unique. Print Assumptions crossing_unique.
Check @takeUntil_correct. Print Assumptions takeUntil_correct.
Check @dropUntil_correct. Print Assumptions dropUntil_correct.
Check @split_trigger_contract. Print Assumptions split_trigger_contract.
Check @allCuts. Print Assumptions allCuts.
Check @allPrefixes. Print Assumptions allPrefixes.
Check @allCuts_block. Print Assumptions allCuts_block.
Check @allPrefixes_block. Print Assumptions allPrefixes_block.
Check @listMeasure_blocks. Print Assumptions listMeasure_blocks.
Check @allCuts_flatten. Print Assumptions allCuts_flatten.
Check @allPrefixes_flatten. Print Assumptions allPrefixes_flatten.
Check @digit_flatten. Print Assumptions digit_flatten.
Check @node_flatten. Print Assumptions node_flatten.
Check @digit_elements. Print Assumptions digit_elements.
Check @node_elements. Print Assumptions node_elements.
Check @searchCalls. Print Assumptions searchCalls.
Check @searchCalls_domain. Print Assumptions searchCalls_domain.
Check @allCuts_domain. Print Assumptions allCuts_domain.
Check @search_calls_on_cuts. Print Assumptions search_calls_on_cuts.
Check @searchDigitTests. Print Assumptions searchDigitTests.
Check @searchDigitTests_cuts. Print Assumptions searchDigitTests_cuts.
Check @searchDigit_parametric. Print Assumptions searchDigit_parametric.
Check @digitContents_nonempty. Print Assumptions digitContents_nonempty.
Check @nodeContents_nonempty. Print Assumptions nodeContents_nonempty.
Check @splitCalls. Print Assumptions splitCalls.
Check @splitCalls_domain. Print Assumptions splitCalls_domain.
Check @allPrefixes_domain. Print Assumptions allPrefixes_domain.
Check @split_calls_on_nonempty_prefixes. Print Assumptions split_calls_on_nonempty_prefixes.
Check @nonempty_total_domain. Print Assumptions nonempty_total_domain.
Check @search_endpoint_domains. Print Assumptions search_endpoint_domains.
Check @search_domain_certificate. Print Assumptions search_domain_certificate.
Check @split_domain_certificate. Print Assumptions split_domain_certificate.
Check @searchCalls_nonempty. Print Assumptions searchCalls_nonempty.
Check @splitCalls_nonempty. Print Assumptions splitCalls_nonempty.
Check @splitDigitTests. Print Assumptions splitDigitTests.
Check @splitDigitTests_prefixes. Print Assumptions splitDigitTests_prefixes.
Check @splitDigit_parametric. Print Assumptions splitDigit_parametric.
Check @searchNode_parametric. Print Assumptions searchNode_parametric.
Check @splitNode_parametric. Print Assumptions splitNode_parametric.
Check @searchTree_parametric. Print Assumptions searchTree_parametric.
Check @splitTree_parametric. Print Assumptions splitTree_parametric.
Check @search_empty. Print Assumptions search_empty.
Check @search_nonempty_unfold. Print Assumptions search_nonempty_unfold.
Check @search_parametric_on_cuts. Print Assumptions search_parametric_on_cuts.
Check @split_parametric_on_nonempty_prefixes. Print Assumptions split_parametric_on_nonempty_prefixes.
Check @split_empty. Print Assumptions split_empty.
Check @splitReference_empty. Print Assumptions splitReference_empty.
