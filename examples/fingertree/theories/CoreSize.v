From Stdlib Require Import Arith.PeanoNat micromega.Lia.
Require Import Data.FingerTree.

(* Independent leaf weights: cached measurements are deliberately ignored. *)
Definition digitSize {a} (f : a -> nat) (d : Digit a) : nat :=
  match d with
  | One x => f x
  | Two x y => f x + f y
  | Three x y z => f x + f y + f z
  | Four x y z w => f x + f y + f z + f w
  end.

Definition nodeSize {v a} (f : a -> nat) (n : Node v a) : nat :=
  match n with
  | Node2 _ x y => f x + f y
  | Node3 _ x y z => f x + f y + f z
  end.

Fixpoint sizeWith {v a} (f : a -> nat) (t : FingerTree v a) : nat :=
  match t with
  | Empty => 0
  | Single x => f x
  | Deep _ pr m sf => digitSize f pr + sizeWith (nodeSize f) m + digitSize f sf
  end.

Definition size {v a} (t : FingerTree v a) : nat := sizeWith (fun _ => 1) t.

Lemma digitSize_positive {a} (f : a -> nat) :
  (forall x, 0 < f x) -> forall d, 0 < digitSize f d.
Proof. intros H d; destruct d as [x|x y|x y z|x y z w]; cbn; pose proof (H x); lia. Qed.

Lemma nodeSize_positive {v a} (f : a -> nat) :
  (forall x, 0 < f x) -> forall n : Node v a, 0 < nodeSize f n.
Proof. intros H n; destruct n as [c x y|c x y z]; cbn; pose proof (H x); lia. Qed.

Lemma sizeWith_zero_iff {v} : forall a (t : FingerTree v a) (f : a -> nat),
  (forall x, 0 < f x) -> (sizeWith f t = 0 <-> t = Empty).
Proof.
  intros a t f Hf; destruct t as [|x|c pr m sf]; cbn.
  - tauto.
  - pose proof (Hf x); split; [lia|discriminate].
  - pose proof (digitSize_positive f Hf pr); split; [lia|discriminate].
Qed.

Lemma size_zero_iff {v a} (t : FingerTree v a) : size t = 0 <-> t = Empty.
Proof. apply sizeWith_zero_iff; intros; lia. Qed.

Lemma null_size_zero {v a} (t : FingerTree v a) : null t = true <-> size t = 0.
Proof.
  rewrite size_zero_iff; destruct t; cbn;
    split; intro E; try discriminate; reflexivity.
Qed.

Section Structural.
Context {v : Type} `{GHC.Base.Monoid v}.

Lemma digitToTree_sizeWith {a} (M : Measured v a) (f : a -> nat) d :
  sizeWith f (digitToTree d) = digitSize f d.
Proof. destruct d; cbn [digitToTree deep sizeWith digitSize]; lia. Qed.

Lemma nodeToDigit_size {a} (f : a -> nat) (n : Node v a) :
  digitSize f (nodeToDigit n) = nodeSize f n.
Proof. destruct n; reflexivity. Qed.

Lemma viewl_sizeWith : forall a (t : FingerTree v a) (M : Measured v a) (f : a -> nat),
  match @viewl v a _ _ M t with
  | EmptyL => sizeWith f t = 0
  | op_ZCzl__ x r => sizeWith f t = f x + sizeWith f r
  end.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a) (f : a -> nat),
    match @viewl v a _ _ M t with
    | EmptyL => sizeWith f t = 0
    | op_ZCzl__ x r => sizeWith f t = f x + sizeWith f r
    end) _ _ _).
  - intros; reflexivity.
  - intros; cbn; lia.
  - intros a c pr m IH sf M f.
    specialize (IH (Measured__Node__5) (nodeSize f)).
    destruct pr as [x|x y|x y z|x y z w];
      cbn [viewl lheadDigit ltailDigit deep sizeWith digitSize] in *;
      try lia.
    destruct (viewl m) as [|n r] eqn:E.
    + rewrite digitToTree_sizeWith; lia.
    + cbn [sizeWith]; rewrite nodeToDigit_size; lia.
Qed.

Lemma viewl_empty_iff {a} (M : Measured v a) (t : FingerTree v a) :
  viewl t = EmptyL <-> size t = 0.
Proof.
  rewrite size_zero_iff; destruct t as [|x|c pr m sf];
    [tauto|cbn; split; discriminate|].
  destruct pr; cbn; split; discriminate.
Qed.

Lemma viewl_size {a} (M : Measured v a) (t : FingerTree v a) x r :
  viewl t = op_ZCzl__ x r -> size t = S (size r).
Proof.
  intro E; pose proof (viewl_sizeWith a t M (fun _ => 1)) as Hsize.
  rewrite E in Hsize; exact Hsize.
Qed.

Lemma viewl_size_lt {a} (M : Measured v a) (t : FingerTree v a) x r :
  viewl t = op_ZCzl__ x r -> size r < size t.
Proof. intro E; pose proof (viewl_size M t x r E); lia. Qed.

Lemma consTree_sizeWith : forall a (t : FingerTree v a) (M : Measured v a)
  (f : a -> nat) x, sizeWith f (consTree x t) = f x + sizeWith f t.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    (f : a -> nat) x, sizeWith f (consTree x t) = f x + sizeWith f t) _ _ _).
  - intros; cbn; lia.
  - intros; cbn [consTree deep sizeWith digitSize]; lia.
  - intros a c pr m IH sf M f x.
    destruct pr; cbn [consTree deep sizeWith digitSize consDigit GHC.Prim.seq];
      try lia.
    rewrite IH; cbn [nodeSize node3]; lia.
Qed.

Lemma snocTree_sizeWith : forall a (t : FingerTree v a) (M : Measured v a)
  (f : a -> nat) x, sizeWith f (snocTree t x) = sizeWith f t + f x.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    (f : a -> nat) x, sizeWith f (snocTree t x) = sizeWith f t + f x) _ _ _).
  - intros; cbn; lia.
  - intros; cbn [snocTree deep sizeWith digitSize]; lia.
  - intros a c pr m IH sf M f x.
    destruct sf; cbn [snocTree deep sizeWith digitSize snocDigit GHC.Prim.seq];
      try lia.
    rewrite IH; cbn [nodeSize node3]; lia.
Qed.

Lemma appendTree2_deep {a} (M : Measured v a) c1 pr1 m1 sf1 x y c2 pr2 m2 sf2 :
  appendTree2 (Deep c1 pr1 m1 sf1) x y (Deep c2 pr2 m2 sf2) =
    deep pr1 (addDigits2 m1 sf1 x y pr2 m2) sf2.
Proof. reflexivity. Qed.

Lemma appendTree3_deep {a} (M : Measured v a) c1 pr1 m1 sf1 x y z c2 pr2 m2 sf2 :
  appendTree3 (Deep c1 pr1 m1 sf1) x y z (Deep c2 pr2 m2 sf2) =
    deep pr1 (addDigits3 m1 sf1 x y z pr2 m2) sf2.
Proof. reflexivity. Qed.

Lemma appendTree4_deep {a} (M : Measured v a) c1 pr1 m1 sf1 x y z w c2 pr2 m2 sf2 :
  appendTree4 (Deep c1 pr1 m1 sf1) x y z w (Deep c2 pr2 m2 sf2) =
    deep pr1 (addDigits4 m1 sf1 x y z w pr2 m2) sf2.
Proof. reflexivity. Qed.

Lemma appendTree234_sizeWith : forall a (t : FingerTree v a) (M : Measured v a)
  (f : a -> nat),
  (forall x y r, sizeWith f (appendTree2 t x y r) =
    sizeWith f t + f x + f y + sizeWith f r) /\
  (forall x y z r, sizeWith f (appendTree3 t x y z r) =
    sizeWith f t + f x + f y + f z + sizeWith f r) /\
  (forall x y z w r, sizeWith f (appendTree4 t x y z w r) =
    sizeWith f t + f x + f y + f z + f w + sizeWith f r).
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a) (f : a -> nat),
    (forall x y r, sizeWith f (appendTree2 t x y r) =
      sizeWith f t + f x + f y + sizeWith f r) /\
    (forall x y z r, sizeWith f (appendTree3 t x y z r) =
      sizeWith f t + f x + f y + f z + sizeWith f r) /\
    (forall x y z w r, sizeWith f (appendTree4 t x y z w r) =
      sizeWith f t + f x + f y + f z + f w + sizeWith f r)) _ _ _).
  - intros a M f; repeat split; intros;
      cbn [appendTree2 appendTree3 appendTree4 sizeWith];
      repeat rewrite consTree_sizeWith; lia.
  - intros a u M f; repeat split; intros;
      destruct r; cbn [appendTree2 appendTree3 appendTree4];
      repeat rewrite consTree_sizeWith; repeat rewrite snocTree_sizeWith;
      cbn [sizeWith]; lia.
  - intros a c pr m IH sf M f.
    destruct (IH Measured__Node__5 (nodeSize f)) as [I2 [I3 I4]].
    repeat split; intros.
    + destruct r as [|u|c2 pr2 m2 sf2].
      * cbn [appendTree2]; repeat rewrite snocTree_sizeWith; cbn [sizeWith]; lia.
      * cbn [appendTree2]; repeat rewrite snocTree_sizeWith; cbn [sizeWith]; lia.
      * rewrite appendTree2_deep; cbn [deep sizeWith].
        destruct sf; destruct pr2; cbn [addDigits2];
          rewrite ?I2, ?I3, ?I4; cbn [nodeSize node2 node3 digitSize]; lia.
    + destruct r as [|u|c2 pr2 m2 sf2].
      * cbn [appendTree3]; repeat rewrite snocTree_sizeWith; cbn [sizeWith]; lia.
      * cbn [appendTree3]; repeat rewrite snocTree_sizeWith; cbn [sizeWith]; lia.
      * rewrite appendTree3_deep; cbn [deep sizeWith].
        destruct sf; destruct pr2; cbn [addDigits3];
          rewrite ?I2, ?I3, ?I4; cbn [nodeSize node2 node3 digitSize]; lia.
    + destruct r as [|u|c2 pr2 m2 sf2].
      * cbn [appendTree4]; repeat rewrite snocTree_sizeWith; cbn [sizeWith]; lia.
      * cbn [appendTree4]; repeat rewrite snocTree_sizeWith; cbn [sizeWith]; lia.
      * rewrite appendTree4_deep; cbn [deep sizeWith].
        destruct sf; destruct pr2; cbn [addDigits4];
          rewrite ?I2, ?I3, ?I4; cbn [nodeSize node2 node3 digitSize]; lia.
Qed.

Lemma appendTree1_deep {a} (M : Measured v a) c1 pr1 m1 sf1 x c2 pr2 m2 sf2 :
  appendTree1 (Deep c1 pr1 m1 sf1) x (Deep c2 pr2 m2 sf2) =
    deep pr1 (addDigits1 m1 sf1 x pr2 m2) sf2.
Proof. reflexivity. Qed.

Lemma appendTree1_sizeWith : forall a (t : FingerTree v a) (M : Measured v a)
  (f : a -> nat) x r, sizeWith f (appendTree1 t x r) =
    sizeWith f t + f x + sizeWith f r.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    (f : a -> nat) x r, sizeWith f (appendTree1 t x r) =
      sizeWith f t + f x + sizeWith f r) _ _ _).
  - intros; cbn [appendTree1 sizeWith]; rewrite consTree_sizeWith; lia.
  - intros a u M f x r; destruct r;
      cbn [appendTree1]; repeat rewrite consTree_sizeWith;
      repeat rewrite snocTree_sizeWith; cbn [sizeWith]; lia.
  - intros a c pr m IH sf M f x r.
    pose proof (IH Measured__Node__5 (nodeSize f)) as I1.
    destruct (appendTree234_sizeWith _ m Measured__Node__5 (nodeSize f))
      as [I2 [I3 I4]].
    destruct r as [|u|c2 pr2 m2 sf2].
    + cbn [appendTree1]; repeat rewrite snocTree_sizeWith; cbn [sizeWith]; lia.
    + cbn [appendTree1]; repeat rewrite snocTree_sizeWith; cbn [sizeWith]; lia.
    + rewrite appendTree1_deep; cbn [deep sizeWith].
      destruct sf; destruct pr2; cbn [addDigits1];
        rewrite ?I1, ?I2, ?I3; cbn [nodeSize node2 node3 digitSize]; lia.
Qed.

Lemma append_sizeWith {a} (M : Measured v a) (f : a -> nat) l r :
  sizeWith f (op_zgzl__ l r) = sizeWith f l + sizeWith f r.
Proof.
  destruct l as [|x|c1 pr1 m1 sf1]; destruct r as [|y|c2 pr2 m2 sf2];
    cbn [op_zgzl__ appendTree0];
    rewrite ?consTree_sizeWith, ?snocTree_sizeWith; cbn [sizeWith]; try lia.
  pose proof (appendTree1_sizeWith _ m1 Measured__Node__5 (nodeSize f)) as I1.
  destruct (appendTree234_sizeWith _ m1 Measured__Node__5 (nodeSize f))
    as [I2 [I3 I4]].
  cbn [deep sizeWith]; destruct sf1; destruct pr2; cbn [addDigits0];
    rewrite ?I1, ?I2, ?I3; cbn [nodeSize node2 node3 digitSize]; lia.
Qed.

Lemma append_size {a} (M : Measured v a) (l r : FingerTree v a) :
  size (op_zgzl__ l r) = size l + size r.
Proof. apply append_sizeWith. Qed.

Lemma viewr_sizeWith : forall a (t : FingerTree v a) (M : Measured v a) (f : a -> nat),
  match @viewr v a _ _ M t with
  | EmptyR => sizeWith f t = 0
  | op_ZCzg__ l x => sizeWith f t = sizeWith f l + f x
  end.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a) (f : a -> nat),
    match @viewr v a _ _ M t with
    | EmptyR => sizeWith f t = 0
    | op_ZCzg__ l x => sizeWith f t = sizeWith f l + f x
    end) _ _ _).
  - intros; reflexivity.
  - intros; cbn; lia.
  - intros a c pr m IH sf M f.
    specialize (IH Measured__Node__5 (nodeSize f)).
    destruct sf as [x|x y|x y z|x y z w];
      cbn [viewr rheadDigit rtailDigit deep sizeWith digitSize] in *; try lia.
    destruct (viewr m) as [|r n] eqn:E.
    + rewrite digitToTree_sizeWith; lia.
    + cbn [sizeWith]; rewrite nodeToDigit_size; lia.
Qed.

Lemma rotL_sizeWith {a} (M : Measured v a) (f : a -> nat) m sf :
  sizeWith f (rotL m sf) = sizeWith (nodeSize f) m + digitSize f sf.
Proof.
  pose proof (viewl_sizeWith _ m Measured__Node__5 (nodeSize f)) as E.
  unfold rotL; destruct (viewl m) as [|n r];
    [rewrite digitToTree_sizeWith|cbn [sizeWith]; rewrite nodeToDigit_size]; lia.
Qed.

Lemma rotR_sizeWith {a} (M : Measured v a) (f : a -> nat) pr m :
  sizeWith f (rotR pr m) = digitSize f pr + sizeWith (nodeSize f) m.
Proof.
  pose proof (viewr_sizeWith _ m Measured__Node__5 (nodeSize f)) as E.
  unfold rotR; destruct (viewr m) as [|r n];
    [rewrite digitToTree_sizeWith|cbn [sizeWith]; rewrite nodeToDigit_size]; lia.
Qed.

Lemma deepL_sizeWith {a} (M : Measured v a) (f : a -> nat) pr m sf :
  sizeWith f (deepL pr m sf) =
    (match pr with None => 0 | Some d => digitSize f d end) +
      sizeWith (nodeSize f) m + digitSize f sf.
Proof. destruct pr; cbn [deepL deep sizeWith]; [reflexivity|apply rotL_sizeWith]. Qed.

Lemma deepR_sizeWith {a} (M : Measured v a) (f : a -> nat) pr m sf :
  sizeWith f (deepR pr m sf) = digitSize f pr + sizeWith (nodeSize f) m +
    (match sf with None => 0 | Some d => digitSize f d end).
Proof.
  destruct sf; cbn [deepR deep sizeWith]; [reflexivity|].
  rewrite rotR_sizeWith; lia.
Qed.

Lemma splitDigit_sizeWith {a} (M : Measured v a) (f : a -> nat) p i d :
  let '(MkSplit l x r) := splitDigit p i d in
  digitSize f d = (match l with None => 0 | Some d => digitSize f d end) +
    f x + (match r with None => 0 | Some d => digitSize f d end).
Proof.
  destruct d; cbn [splitDigit digitSize GHC.Prim.seq];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn [digitSize]; lia.
Qed.

Lemma splitNode_sizeWith {a} (M : Measured v a) (f : a -> nat) p i n :
  let '(MkSplit l x r) := splitNode p i n in
  nodeSize f n = (match l with None => 0 | Some d => digitSize f d end) +
    f x + (match r with None => 0 | Some d => digitSize f d end).
Proof.
  destruct n; cbn [splitNode nodeSize];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn [digitSize]; lia.
Qed.

Hypothesis mappend_right_identity : forall x : v,
  GHC.Base.mappend x GHC.Base.mempty = x.

Lemma split_middle_nonempty {a} (M : Measured v a) p i (t : FingerTree v a) :
  p i = false -> p (GHC.Base.mappend i (measure t)) = true -> t <> Empty.
Proof.
  intros E1 E2 ->.
  change (p (GHC.Base.mappend i GHC.Base.mempty) = true) in E2.
  rewrite mappend_right_identity in E2; congruence.
Qed.

Lemma splitTree_sizeWith : forall a (t : FingerTree v a) (M : Measured v a)
  (D : HsToRocq.Err.Default a) (f : a -> nat) p i, t <> Empty ->
  let '(MkSplit l x r) := @splitTree v a _ _ M D p i t in
  sizeWith f t = sizeWith f l + f x + sizeWith f r.
Proof.
  refine (FingerTree_rect v (fun a t => forall (M : Measured v a)
    (D : HsToRocq.Err.Default a) (f : a -> nat) p i, t <> Empty ->
    let '(MkSplit l x r) := @splitTree v a _ _ M D p i t in
    sizeWith f t = sizeWith f l + f x + sizeWith f r) _ _ _).
  - intros; contradiction.
  - intros; cbn; lia.
  - intros a c pr m IH sf M D f p i NE.
    cbn [splitTree].
    destruct (p (GHC.Base.mappend i (measure pr))) eqn:Epr.
    + pose proof (splitDigit_sizeWith M f p i pr) as Ed.
      destruct (splitDigit p i pr) as [l x r].
      rewrite deepL_sizeWith.
      destruct l; cbn [Data.Maybe.maybe sizeWith] in *;
        rewrite ?digitToTree_sizeWith; cbn [sizeWith]; lia.
    + destruct (p (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure m))) eqn:Em.
      * assert (Nm : m <> Empty).
        { eapply split_middle_nonempty; eassumption. }
        specialize (IH Measured__Node__5 (DefaultNode) (nodeSize f) p
          (GHC.Base.mappend i (measure pr)) Nm).
        destruct (splitTree p (GHC.Base.mappend i (measure pr)) m) as [ml n mr].
        pose proof (splitNode_sizeWith M f p
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure ml)) n) as En.
        destruct (splitNode p
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure ml)) n)
          as [l x r].
        rewrite deepL_sizeWith, deepR_sizeWith; cbn [sizeWith]; lia.
      * pose proof (splitDigit_sizeWith M f p
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure m)) sf) as Ed.
        destruct (splitDigit p
          (GHC.Base.mappend (GHC.Base.mappend i (measure pr)) (measure m)) sf)
          as [l x r].
        rewrite deepR_sizeWith.
        destruct r; cbn [Data.Maybe.maybe sizeWith] in *;
          rewrite ?digitToTree_sizeWith; cbn [sizeWith]; lia.
Qed.

Lemma split_sizeWith {a} (M : Measured v a) (f : a -> nat) p t :
  let '(l, r) := split p t in sizeWith f t = sizeWith f l + sizeWith f r.
Proof.
  unfold split; destruct t as [|u|c pr m sf];
    cbn -[splitTree consTree sizeWith]; try reflexivity;
    match goal with
    | |- context [@splitTree v a _ _ M ?D ?p ?i ?t] =>
        pose proof (splitTree_sizeWith a t M D f p i ltac:(discriminate)) as E;
        destruct (@splitTree v a _ _ M D p i t) as [l x r]
    end;
    destruct (Bool.Sumbool.sumbool_of_bool _);
    rewrite ?consTree_sizeWith; cbn [sizeWith] in *; lia.
Qed.

Lemma split_size {a} (M : Measured v a) p (t : FingerTree v a) l r :
  split p t = (l, r) -> size t = size l + size r.
Proof.
  intro E; pose proof (split_sizeWith M (fun _ => 1) p t) as Es.
  rewrite E in Es; exact Es.
Qed.

Lemma split_size_bounds {a} (M : Measured v a) p (t : FingerTree v a) l r :
  split p t = (l, r) -> size l <= size t /\ size r <= size t.
Proof. intro E; pose proof (split_size M p t l r E); lia. Qed.

(* The successful queue-removal branch: partition, remove a head, reappend. *)
Lemma split_viewl_append_size {a} (M : Measured v a) p
  (t l r : FingerTree v a) x r' :
  split p t = (l, r) -> viewl r = op_ZCzl__ x r' ->
  size t = S (size (op_zgzl__ l r')).
Proof.
  intros Es Ev.
  pose proof (split_size M p t l r Es).
  pose proof (viewl_size M r x r' Ev).
  rewrite append_size; lia.
Qed.

Lemma split_viewl_append_lt {a} (M : Measured v a) p
  (t l r : FingerTree v a) x r' :
  split p t = (l, r) -> viewl r = op_ZCzl__ x r' ->
  size (op_zgzl__ l r') < size t.
Proof.
  intros Es Ev; pose proof (split_viewl_append_size M p t l r x r' Es Ev); lia.
Qed.

Lemma takeUntil_size_le {a} (M : Measured v a) p (t : FingerTree v a) :
  size (takeUntil p t) <= size t.
Proof.
  unfold takeUntil, GHC.Base.op_z2218U__, Data.Tuple.fst.
  destruct (split p t) as [l r] eqn:E.
  exact (proj1 (split_size_bounds M p t l r E)).
Qed.

Lemma dropUntil_size_le {a} (M : Measured v a) p (t : FingerTree v a) :
  size (dropUntil p t) <= size t.
Proof.
  unfold dropUntil, GHC.Base.op_z2218U__, Data.Tuple.snd.
  destruct (split p t) as [l r] eqn:E.
  exact (proj2 (split_size_bounds M p t l r E)).
Qed.

End Structural.

(* Compile-time assumption audit for every definition and lemma in this file.
   Propositional identity is a theorem parameter, not a global axiom. *)
Print Assumptions digitSize.
Print Assumptions nodeSize.
Print Assumptions sizeWith.
Print Assumptions size.
Print Assumptions digitSize_positive.
Print Assumptions nodeSize_positive.
Print Assumptions sizeWith_zero_iff.
Print Assumptions size_zero_iff.
Print Assumptions null_size_zero.
Print Assumptions digitToTree_sizeWith.
Print Assumptions nodeToDigit_size.
Print Assumptions viewl_sizeWith.
Print Assumptions viewl_empty_iff.
Print Assumptions viewl_size.
Print Assumptions viewl_size_lt.
Print Assumptions consTree_sizeWith.
Print Assumptions snocTree_sizeWith.
Print Assumptions appendTree2_deep.
Print Assumptions appendTree3_deep.
Print Assumptions appendTree4_deep.
Print Assumptions appendTree234_sizeWith.
Print Assumptions appendTree1_deep.
Print Assumptions appendTree1_sizeWith.
Print Assumptions append_sizeWith.
Print Assumptions append_size.
Print Assumptions viewr_sizeWith.
Print Assumptions rotL_sizeWith.
Print Assumptions rotR_sizeWith.
Print Assumptions deepL_sizeWith.
Print Assumptions deepR_sizeWith.
Print Assumptions splitDigit_sizeWith.
Print Assumptions splitNode_sizeWith.
Print Assumptions split_middle_nonempty.
Print Assumptions splitTree_sizeWith.
Print Assumptions split_sizeWith.
Print Assumptions split_size.
Print Assumptions split_size_bounds.
Print Assumptions split_viewl_append_size.
Print Assumptions split_viewl_append_lt.
Print Assumptions takeUntil_size_le.
Print Assumptions dropUntil_size_le.
