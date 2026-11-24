(* Contents, left-to-right effect sequencing, and validity for all four
   translated core traversals, under arbitrary lawful applicatives.
   Safe traversals may change both element and measurement types. Unsafe
   traversal contents require no measure premise; its validity/cache theorem
   requires same-monoid per-element preservation inside F.

   Context accuracy uses original cache validity and explicit propositional
   monoid laws, never equality/decidable equality on measurements. The sharp
   public validity contracts quantify only over original list occurrences.
   Their proof labels the original leaves using CoreContext, then uses map/
   traversal fusion and a generalized contents-refinement invariant.
   The contents and positional proofs use functional extensionality, reported
   explicitly by the assumption inventory at the end. *)

From Stdlib Require Import Lists.List.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import GHC.Base.
Require Import Proofs.GHC.Base.
Require Import Data.FingerTree.
Require Import FingerTreeProofs.CoreModel.
Require Import FingerTreeProofs.CoreOperations.
Require Import FingerTreeProofs.CoreContext.
Require Import FingerTreeProofs.ApplicativeValidity.
Import ListNotations.
Set Warnings "-masking-absolute-name".
Set Bullet Behavior "Strict Subproofs".
Set Typeclasses Depth 3.

Definition append_pair {A : Type} (p : list A * list A) : list A :=
  match p with pair xs ys => xs ++ ys end.
Definition list_append {A : Type} (xs ys : list A) : list A := xs ++ ys.

Section GenericApplicative.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.

Lemma liftA2_pure_left {A B C : Type} (f : A -> B -> C) (x : A) (fb : F B) :
  GHC.Base.liftA2 f (GHC.Base.pure x) fb = GHC.Base.fmap (fun y => f x y) fb.
Proof.
  rewrite applicative_liftA2.
  rewrite applicative_fmap.
  rewrite applicative_homomorphism.
  rewrite <- applicative_fmap.
  reflexivity.
Qed.

Lemma liftA2_pure_right {A B C : Type} (f : A -> B -> C) (fa : F A) (y : B) :
  GHC.Base.liftA2 f fa (GHC.Base.pure y) = GHC.Base.fmap (fun x => f x y) fa.
Proof.
  rewrite applicative_liftA2.
  rewrite applicative_interchange.
  rewrite <- applicative_fmap.
  rewrite functor_composition.
  reflexivity.
Qed.

Lemma fmap_append_pair_liftA2_pair {A : Type} (x y : F (list A)) :
  GHC.Base.fmap (@append_pair A) (GHC.Base.liftA2 pair x y) =
  GHC.Base.liftA2 (@list_append A) x y.
Proof.
  replace (GHC.Base.liftA2 pair x y)
    with (GHC.Base.fmap pair x <*> y)
    by (rewrite applicative_liftA2; reflexivity).
  replace (GHC.Base.liftA2 (@list_append A) x y)
    with (GHC.Base.fmap (@list_append A) x <*> y)
    by (rewrite applicative_liftA2; reflexivity).
  rewrite fmap_ap.
  rewrite functor_composition.
  unfold list_append, append_pair.
  reflexivity.
Qed.

Lemma ap_fmap_right_comp {A B C : Type} (u : F (B -> C)) (k : A -> B) (v : F A) :
  GHC.Base.op_zlztzg__ u (GHC.Base.fmap k v)
  = GHC.Base.op_zlztzg__
      (GHC.Base.fmap (fun f => GHC.Base.op_z2218U__ f k) u) v.
Proof.
  rewrite applicative_fmap.
  rewrite <- applicative_composition.
  rewrite applicative_interchange.
  rewrite <- applicative_fmap.
  rewrite <- applicative_fmap.
  rewrite functor_composition.
  reflexivity.
Qed.

Lemma liftA2_app_assoc {A : Type} (fx fy fz : F (list A)) :
  GHC.Base.liftA2 (@list_append A) fx
    (GHC.Base.liftA2 (@list_append A) fy fz) =
  GHC.Base.liftA2 (@list_append A)
    (GHC.Base.liftA2 (@list_append A) fx fy) fz.
Proof.
  repeat rewrite applicative_liftA2.
  repeat rewrite <- applicative_composition.
  repeat rewrite <- applicative_fmap.
  repeat rewrite functor_composition.
  repeat rewrite ap_fmap_right_comp.
  repeat rewrite functor_composition.
  rewrite fmap_ap.
  rewrite functor_composition.
  unfold list_append.
  f_equal. f_equal. f_equal.
  apply functional_extensionality; intro a.
  apply functional_extensionality; intro b.
  apply functional_extensionality; intro c.
  unfold GHC.Base.op_z2218U__ in *. cbn in *.
  rewrite List.app_assoc. reflexivity.
Qed.

Fixpoint traverse_concat {A B : Type} (g : A -> F (list B)) (xs : list A) : F (list B) :=
  match xs with
  | nil => GHC.Base.pure nil
  | cons x xs => GHC.Base.liftA2 (@list_append B) (g x) (traverse_concat g xs)
  end.

Lemma traverse_concat_app {A B : Type} (g : A -> F (list B)) (xs ys : list A) :
  traverse_concat g (xs ++ ys) =
  GHC.Base.fmap (@append_pair B)
    (GHC.Base.liftA2 pair (traverse_concat g xs) (traverse_concat g ys)).
Proof.
  induction xs as [|x xs IH].
  - cbn [List.app traverse_concat].
    rewrite liftA2_pure_left.
    rewrite functor_composition.
    rewrite functor_identity.
    reflexivity.
  - cbn [List.app traverse_concat].
    rewrite IH.
    rewrite <- fmap_append_pair_liftA2_pair.
    repeat rewrite applicative_liftA2.
    repeat rewrite fmap_ap.
    repeat rewrite functor_composition.
    repeat rewrite ap_fmap_right_comp.
    repeat rewrite functor_composition.
    repeat rewrite <- applicative_composition.
    repeat rewrite <- applicative_fmap.
    repeat rewrite functor_composition.
    repeat rewrite ap_fmap_right_comp.
    repeat rewrite functor_composition.
    unfold list_append, append_pair.
    repeat rewrite List.app_assoc.
    repeat f_equal.
    apply functional_extensionality; intro a.
    apply functional_extensionality; intro b.
    apply functional_extensionality; intro c.
    unfold GHC.Base.op_z2218U__ in *. cbn in *.
    repeat rewrite List.app_assoc.
    reflexivity.
Qed.

Lemma traverse_concat_flat_map {A B C : Type}
  (g : A -> F (list C)) (h : B -> list A) (xs : list B) :
  traverse_concat g (List.flat_map h xs) =
  traverse_concat (fun y => traverse_concat g (h y)) xs.
Proof.
  induction xs as [|y ys IH].
  - reflexivity.
  - cbn [List.flat_map].
    rewrite traverse_concat_app.
    rewrite IH.
    rewrite fmap_append_pair_liftA2_pair.
    reflexivity.
Qed.

End GenericApplicative.

(* Digit validity, via the already-proved ApplicativeValidity lemma. *)
Section DigitValidity.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.

Lemma traverseDigit_validity {A B : Type} (P : A -> Prop) (Q : B -> Prop)
  (g : A -> F B) (d : Digit A) :
  (forall x, P x -> HoldsF Q (g x)) ->
  digitValidity P d -> HoldsF (digitValidity Q) (traverseDigit g d).
Proof.
  intros Hg Hd.
  rewrite <- (@functor_identity F _ _ (Digit B) (traverseDigit g d)).
  apply (@HoldsF_fmap F _ _ (Digit B) (Digit B) (DigitAll Q) (digitValidity Q) (@id (Digit B))).
  - intros x Hx. exact Hx.
  - apply (traverseDigit_holds Q P g d); assumption.
Qed.

End DigitValidity.

(* Node validity with rebuilt caches. *)
Section NodeValidity.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.

Lemma traverseNode_validity {v1 v2 A B : Type}
  `{GHC.Base.Semigroup v1} `{GHC.Base.Monoid v1}
  `{GHC.Base.Semigroup v2} `{GHC.Base.Monoid v2} `{Measured v2 B}
  (M1 : Measured v1 A) (P : A -> Prop) (Q : B -> Prop)
  (g : A -> F B) (n : Node v1 A) :
  (forall x, P x -> HoldsF Q (g x)) ->
  nodeValidity (@measure v1 A _ _ M1) P n ->
  HoldsF (nodeValidity (@measure v2 B _ _ _) Q) (traverseNode g n).
Proof.
  intros Hg Hn. destruct n as [c a b | c a b d]; cbn [nodeValidity] in *.
  - destruct Hn as [Ha [Hb Hc]].
    apply (HoldsF_app Q (nodeValidity measure Q)
      (GHC.Base.fmap (Data.FingerTree.node2 (v := v2) (a := B)) (g a)) (g b)).
    + apply (HoldsF_fmap Q
        (fun h => forall z, Q z -> nodeValidity measure Q (h z))
        (Data.FingerTree.node2 (v := v2) (a := B))).
      * intros y Hy z Hz. apply node2_validity; assumption.
      * apply Hg. exact Ha.
    + apply Hg. exact Hb.
  - destruct Hn as [Ha [Hb [Hc Hd]]].
    apply (HoldsF_app Q (nodeValidity measure Q)
      (GHC.Base.op_zlztzg__
        (GHC.Base.fmap (Data.FingerTree.node3 (v := v2) (a := B)) (g a)) (g b)) (g d)).
    + apply (HoldsF_app Q (fun h => forall z, Q z -> nodeValidity measure Q (h z))
        (GHC.Base.fmap (Data.FingerTree.node3 (v := v2) (a := B)) (g a)) (g b)).
      * apply (HoldsF_fmap Q
          (fun h => forall y, Q y -> forall z, Q z -> nodeValidity measure Q (h y z))
          (Data.FingerTree.node3 (v := v2) (a := B))).
        { intros y Hy z Hz w Hw. apply node3_validity; assumption. }
        { apply Hg. exact Ha. }
      * apply Hg. exact Hb.
    + apply Hg. exact Hc.
Qed.

End NodeValidity.

(* Measurement-preserving digit traversal, used by unsafeTraverse. *)
Section DigitMeasure.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.
Context {v : Type}.
Context `{GHC.Base.Semigroup v}.
Context `{GHC.Base.Monoid v}.

Lemma traverseDigit_measure {A B : Type}
  (mu : A -> v) (nu : B -> v) (P : A -> Prop) (Q : B -> Prop)
  (g : A -> F B) (d : Digit A) :
  (forall x, P x -> HoldsF (fun y => Q y /\ nu y = mu x) (g x)) ->
  digitValidity P d ->
  HoldsF (fun d' => digitValidity Q d' /\ digitMeasure nu d' = digitMeasure mu d)
    (traverseDigit g d).
Proof.
  intros Hg Hd. destruct d as [a | a b | a b c | a b c d]; cbn in *.
  - apply (HoldsF_fmap (fun y => Q y /\ nu y = mu a)
      (fun d' => digitValidity Q d' /\ digitMeasure nu d' = digitMeasure mu (One a))
      (@One B)).
    + intros y [Qy Ey]. split; [exact Qy | cbn; rewrite Ey; reflexivity].
    + apply Hg; exact Hd.
  - destruct Hd as [Ha Hb].
    apply (HoldsF_app (fun y => Q y /\ nu y = mu b)
      (fun d' => digitValidity Q d' /\ digitMeasure nu d' = digitMeasure mu (Two a b))
      (GHC.Base.fmap (@Two B) (g a)) (g b)).
    + apply (HoldsF_fmap (fun y => Q y /\ nu y = mu a)
        (fun h => forall z, Q z /\ nu z = mu b ->
          digitValidity Q (h z) /\ digitMeasure nu (h z) = digitMeasure mu (Two a b))
        (@Two B)).
      * intros y [Qy Ey] z [Qz Ez]. split; [cbn; split; assumption | cbn; rewrite Ey, Ez; reflexivity].
      * apply Hg; exact Ha.
    + apply Hg; exact Hb.
  - destruct Hd as [Ha [Hb Hc]].
    apply (HoldsF_app (fun y => Q y /\ nu y = mu c)
      (fun d' => digitValidity Q d' /\ digitMeasure nu d' = digitMeasure mu (Three a b c))
      (GHC.Base.op_zlztzg__
        (GHC.Base.fmap (@Three B) (g a)) (g b)) (g c)).
    + apply (HoldsF_app (fun z => Q z /\ nu z = mu b)
        (fun h => forall z, Q z /\ nu z = mu c ->
          digitValidity Q (h z) /\ digitMeasure nu (h z) = digitMeasure mu (Three a b c))
        (GHC.Base.fmap (@Three B) (g a)) (g b)).
      * apply (HoldsF_fmap (fun y => Q y /\ nu y = mu a)
          (fun h => forall y, Q y /\ nu y = mu b ->
            forall z, Q z /\ nu z = mu c ->
            digitValidity Q (h y z) /\ digitMeasure nu (h y z) = digitMeasure mu (Three a b c))
          (@Three B)).
        { intros y [Qy Ey] y' [Qy' Ey'] z [Qz Ez].
          split; [cbn; repeat split; assumption | cbn; rewrite Ey, Ey', Ez; reflexivity]. }
        { apply Hg; exact Ha. }
      * apply Hg; exact Hb.
    + apply Hg; exact Hc.
  - destruct Hd as [Ha [Hb [Hc Hd]]].
    apply (HoldsF_app (fun w => Q w /\ nu w = mu d)
      (fun d' => digitValidity Q d' /\ digitMeasure nu d' = digitMeasure mu (Four a b c d))
      (GHC.Base.op_zlztzg__
        (GHC.Base.op_zlztzg__
          (GHC.Base.fmap (@Four B) (g a)) (g b)) (g c)) (g d)).
    + apply (HoldsF_app (fun z => Q z /\ nu z = mu c)
        (fun h => forall w, Q w /\ nu w = mu d ->
          digitValidity Q (h w) /\ digitMeasure nu (h w) = digitMeasure mu (Four a b c d))
        (GHC.Base.op_zlztzg__
          (GHC.Base.fmap (@Four B) (g a)) (g b)) (g c)).
      * apply (HoldsF_app (fun y => Q y /\ nu y = mu b)
          (fun h => forall z, Q z /\ nu z = mu c ->
            forall w, Q w /\ nu w = mu d ->
            digitValidity Q (h z w) /\ digitMeasure nu (h z w) = digitMeasure mu (Four a b c d))
          (GHC.Base.fmap (@Four B) (g a)) (g b)).
        { apply (HoldsF_fmap (fun y => Q y /\ nu y = mu a)
            (fun h => forall y, Q y /\ nu y = mu b ->
              forall z, Q z /\ nu z = mu c ->
              forall w, Q w /\ nu w = mu d ->
              digitValidity Q (h y z w) /\ digitMeasure nu (h y z w) = digitMeasure mu (Four a b c d))
            (@Four B)).
          - intros y [Qy Ey] y' [Qy' Ey'] z [Qz Ez] w [Qw Ew].
            split; [cbn; repeat split; assumption | cbn; rewrite Ey, Ey', Ez, Ew; reflexivity].
          - apply Hg; exact Ha. }
        { apply Hg; exact Hb. }
      * apply Hg; exact Hc.
    + apply Hg; exact Hd.
Qed.

End DigitMeasure.

(* Unsafe node traversal: validity plus cache preservation. *)
Section UnsafeNode.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.
Context {v : Type}.
Context `{GHC.Base.Semigroup v}.
Context `{GHC.Base.Monoid v}.

Lemma unsafeTraverseNode_measure {A B : Type}
  (mu : A -> v) (nu : B -> v) (P : A -> Prop) (Q : B -> Prop)
  (g : A -> F B) (n : Node v A) :
  (forall x, P x -> HoldsF (fun y => Q y /\ nu y = mu x) (g x)) ->
  nodeValidity mu P n ->
  HoldsF (fun n' => nodeValidity nu Q n' /\ nodeCache n' = nodeCache n)
    (unsafeTraverseNode g n).
Proof.
  intros Hg Hn. destruct n as [c a b | c a b d]; cbn [nodeValidity nodeCache] in *.
  - destruct Hn as [Ha [Hb Hc]].
    apply (HoldsF_app (fun y => Q y /\ nu y = mu b)
      (fun n' => nodeValidity nu Q n' /\ nodeCache n' = c)
      (GHC.Base.fmap (fun y => Node2 c y) (g a)) (g b)).
    + apply (HoldsF_fmap (fun y => Q y /\ nu y = mu a)
        (fun h => forall z, Q z /\ nu z = mu b ->
          nodeValidity nu Q (h z) /\ nodeCache (h z) = c)
        (fun y => Node2 c y)).
      * intros y [Qy Ey] z [Qz Ez]. split.
        { cbn; repeat split; try assumption. rewrite Ey, Ez. exact Hc. }
        { reflexivity. }
      * apply Hg; exact Ha.
    + apply Hg; exact Hb.
  - destruct Hn as [Ha [Hb [Hc Hd]]].
    apply (HoldsF_app (fun y => Q y /\ nu y = mu d)
      (fun n' => nodeValidity nu Q n' /\ nodeCache n' = c)
      (GHC.Base.op_zlztzg__
        (GHC.Base.fmap (fun y => Node3 c y) (g a)) (g b)) (g d)).
    + apply (HoldsF_app (fun z => Q z /\ nu z = mu b)
        (fun h => forall z, Q z /\ nu z = mu d ->
          nodeValidity nu Q (h z) /\ nodeCache (h z) = c)
        (GHC.Base.fmap (fun y => Node3 c y) (g a)) (g b)).
      * apply (HoldsF_fmap (fun y => Q y /\ nu y = mu a)
          (fun h => forall y, Q y /\ nu y = mu b ->
            forall z, Q z /\ nu z = mu d ->
            nodeValidity nu Q (h y z) /\ nodeCache (h y z) = c)
          (fun y => Node3 c y)).
        { intros y [Qy Ey] y' [Qy' Ey'] z [Qz Ez]. split.
          - cbn; repeat split; try assumption. rewrite Ey, Ey', Ez. exact Hd.
          - reflexivity. }
        { apply Hg; exact Ha. }
      * apply Hg; exact Hb.
    + apply Hg; exact Hc.
Qed.

End UnsafeNode.


Lemma HoldsF_app3 {F : Type -> Type} `{Proofs.GHC.Base.ApplicativeLaws F}
  {A B C D : Type}
  (P : A -> Prop) (Q : B -> Prop) (R : C -> Prop) (S : D -> Prop)
  (g : A -> B -> C -> D) (fa : F A) (fb : F B) (fc : F C) :
  (forall a b c, P a -> Q b -> R c -> S (g a b c)) ->
  HoldsF P fa -> HoldsF Q fb -> HoldsF R fc ->
  HoldsF S ((GHC.Base.fmap g fa <*> fb) <*> fc).
Proof.
  intros Hpt Ha Hb Hc.
  eapply HoldsF_app.
  - eapply HoldsF_app.
    + eapply HoldsF_fmap.
      * intros a Pa b Qb c Rc. exact (Hpt a b c Pa Qb Rc).
      * exact Ha.
    + exact Hb.
  - exact Hc.
Qed.

(* Safe ordinary traversal: validity inside F, with rebuilt caches. *)
Section TraverseTreeValidity.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.

Lemma traverseTree_validityWith {v1 v2 A B : Type}
  `{GHC.Base.Semigroup v1} `{GHC.Base.Monoid v1}
  `{GHC.Base.Semigroup v2} `{GHC.Base.Monoid v2}
  (M1 : Measured v1 A) (M2 : Measured v2 B)
  (P : A -> Prop) (Q : B -> Prop) :
  forall (g : A -> F B) (t : FingerTree v1 A),
  (forall x, P x -> HoldsF Q (g x)) ->
  validityWith (@measure v1 A _ _ M1) P t ->
  HoldsF (validityWith (@measure v2 B _ _ M2) Q) (traverseTree g t).
Proof.
  intros g t Hg V.
  revert g Hg V.
  refine ((FingerTree_rect v1 (fun A0 t =>
    forall (M3 : Measured v1 A0) (P0 : A0 -> Prop)
           (B0 : Type) (M4 : Measured v2 B0) (Q0 : B0 -> Prop)
           (g0 : A0 -> F B0),
    (forall x, P0 x -> HoldsF Q0 (g0 x)) ->
    validityWith (@measure v1 A0 _ _ M3) P0 t ->
    HoldsF (validityWith (@measure v2 B0 _ _ M4) Q0) (traverseTree g0 t)) _ _ _)
    A t M1 P B M2 Q).
  - intros A0 M3 P0 B0 M4 Q0 g0 Hg0 V0. cbn [traverseTree].
    apply HoldsF_pure. exact I.
  - intros A0 x M3 P0 B0 M4 Q0 g0 Hg0 Hx. cbn [traverseTree validityWith].
    apply (HoldsF_fmap Q0 (fun t => validityWith (@measure v2 B0 _ _ M4) Q0 t)
      (@Single v2 B0)).
    + intros y Hy. cbn [validityWith]. exact Hy.
    + apply Hg0. exact Hx.
  - intros A0 c pr m IH sf M3 P0 B0 M4 Q0 g0 Hg0 [Vp [Vm [Vs Ec]]].
    cbn [traverseTree].
    set (dpr := traverseDigit g0 pr).
    set (dmid := traverseTree (traverseNode g0) m).
    set (dsf := traverseDigit g0 sf).
    assert (Dp : HoldsF (digitValidity Q0) dpr).
    { apply (traverseDigit_validity P0 Q0 g0 pr); assumption. }
    assert (Dm : HoldsF (validityWith nodeCache (nodeValidity (@measure v2 B0 _ _ M4) Q0)) dmid).
    { apply (IH Measured__Node__5 (nodeValidity (@measure v1 A0 _ _ M3) P0)
        (Node v2 B0) Measured__Node__5 (nodeValidity (@measure v2 B0 _ _ M4) Q0)
        (traverseNode (v2 := v2) (a2 := B0) g0)).
      - intros n Vn. apply (traverseNode_validity (A := A0) (B := B0) M3 P0 Q0 g0 n); assumption.
      - exact Vm. }
    assert (Ds : HoldsF (digitValidity Q0) dsf).
    { apply (traverseDigit_validity P0 Q0 g0 sf); assumption. }
    subst dpr dmid dsf.
    change (HoldsF (validityWith (@measure v2 B0 _ _ M4) Q0)
      ((GHC.Base.fmap (@deep v2 B0 _ _ _) (traverseDigit g0 pr) <*>
        traverseTree (traverseNode (v2 := v2) (a2 := B0) g0) m) <*>
       traverseDigit g0 sf)).
    refine (@HoldsF_app3 F Functor0 Applicative0 FunctorLaws0 H
      (Digit B0) (FingerTree v2 (Node v2 B0)) (Digit B0) (FingerTree v2 B0)
      (digitValidity Q0)
      (validityWith nodeCache (nodeValidity (@measure v2 B0 _ _ M4) Q0))
      (digitValidity Q0)
      (validityWith (@measure v2 B0 _ _ M4) Q0)
      (@deep v2 B0 _ _ _) (traverseDigit g0 pr)
      (traverseTree (traverseNode (v2 := v2) (a2 := B0) g0) m)
      (traverseDigit g0 sf) _ Dp Dm Ds).
    intros d m0 s' Vd Vm0 Vs'. apply deep_validityWith; assumption.
Qed.

End TraverseTreeValidity.

(* Unsafe traversal: same monoid, per-element measurement preserved. *)
Section UnsafeTraverse.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.
Context {v : Type}.
Context `{GHC.Base.Semigroup v}.
Context `{GHC.Base.Monoid v}.

Lemma unsafeTraverse_measure {A B : Type}
  (mu : A -> v) (nu : B -> v) (P : A -> Prop) (Q : B -> Prop) :
  forall (g : A -> F B) (t : FingerTree v A),
  (forall x, P x -> HoldsF (fun y => Q y /\ nu y = mu x) (g x)) ->
  validityWith mu P t ->
  HoldsF (fun t' => validityWith nu Q t' /\
    treeCacheWith nu t' = treeCacheWith mu t) (unsafeTraverse g t).
Proof.
  intros g t Hg V.
  revert g Hg V.
  refine ((FingerTree_rect v (fun A0 t =>
    forall (mu0 : A0 -> v) (P0 : A0 -> Prop)
           (B0 : Type) (nu0 : B0 -> v) (Q0 : B0 -> Prop)
           (g0 : A0 -> F B0),
    (forall x, P0 x -> HoldsF (fun y => Q0 y /\ nu0 y = mu0 x) (g0 x)) ->
    validityWith mu0 P0 t ->
    HoldsF (fun t' => validityWith nu0 Q0 t' /\
      treeCacheWith nu0 t' = treeCacheWith mu0 t) (unsafeTraverse g0 t)) _ _ _)
    A t mu P B nu Q).
  - intros A0 mu0 P0 B0 nu0 Q0 g0 Hg0 V0. cbn [unsafeTraverse].
    apply HoldsF_pure. split; [exact I|reflexivity].
  - intros A0 x mu0 P0 B0 nu0 Q0 g0 Hg0 Hx. cbn [unsafeTraverse].
    apply (HoldsF_fmap (fun y => Q0 y /\ nu0 y = mu0 x)
      (fun t' => validityWith nu0 Q0 t' /\
        treeCacheWith nu0 t' = treeCacheWith mu0 (Single x))
      (@Single v B0)).
    + intros y [Qy Ey]. split; [cbn [validityWith]; exact Qy | cbn [treeCacheWith]; exact Ey].
    + apply Hg0. exact Hx.
  - intros A0 c pr m IH sf mu0 P0 B0 nu0 Q0 g0 Hg0 [Vp [Vm [Vs Ec]]].
    cbn [unsafeTraverse].
    set (dpr := traverseDigit g0 pr).
    set (dmid := unsafeTraverse (unsafeTraverseNode g0) m).
    set (dsf := traverseDigit g0 sf).
    assert (Dp : HoldsF (fun d' => digitValidity Q0 d' /\
        digitMeasure nu0 d' = digitMeasure mu0 pr) dpr).
    { apply (traverseDigit_measure mu0 nu0 P0 Q0 g0 pr); assumption. }
    assert (Dm : HoldsF (fun m' => validityWith nodeCache (nodeValidity nu0 Q0) m' /\
        treeCacheWith nodeCache m' = treeCacheWith nodeCache m) dmid).
    { apply (IH nodeCache (nodeValidity mu0 P0) (Node v B0) nodeCache
        (nodeValidity nu0 Q0) (unsafeTraverseNode g0)).
      - intros n Vn. apply (unsafeTraverseNode_measure mu0 nu0 P0 Q0 g0 n); assumption.
      - exact Vm. }
    assert (Ds : HoldsF (fun d' => digitValidity Q0 d' /\
        digitMeasure nu0 d' = digitMeasure mu0 sf) dsf).
    { apply (traverseDigit_measure mu0 nu0 P0 Q0 g0 sf); assumption. }
    subst dpr dmid dsf.
    change (HoldsF (fun t' => validityWith nu0 Q0 t' /\
        treeCacheWith nu0 t' = treeCacheWith mu0 (Deep c pr m sf))
      ((GHC.Base.fmap (@Deep v B0 c) (traverseDigit g0 pr) <*>
        unsafeTraverse (unsafeTraverseNode g0) m) <*>
       traverseDigit g0 sf)).
    refine (@HoldsF_app3 F Functor0 Applicative0 FunctorLaws0 H
      (Digit B0) (FingerTree v (Node v B0)) (Digit B0) (FingerTree v B0)
      (fun d' => digitValidity Q0 d' /\ digitMeasure nu0 d' = digitMeasure mu0 pr)
      (fun m' => validityWith nodeCache (nodeValidity nu0 Q0) m' /\
        treeCacheWith nodeCache m' = treeCacheWith nodeCache m)
      (fun d' => digitValidity Q0 d' /\ digitMeasure nu0 d' = digitMeasure mu0 sf)
      (fun t' => validityWith nu0 Q0 t' /\
        treeCacheWith nu0 t' = treeCacheWith mu0 (Deep c pr m sf))
      (@Deep v B0 c) (traverseDigit g0 pr)
      (unsafeTraverse (unsafeTraverseNode g0) m) (traverseDigit g0 sf)
      _ Dp Dm Ds).
    intros d m0 s' [Vd Ed] [Vm0 Em] [Vs' Es].
    split.
    + cbn [validityWith]. repeat split; try assumption.
      rewrite Ec, Ed, Em, Es. reflexivity.
    + reflexivity.
Qed.

End UnsafeTraverse.



(* Positional traversal: validity with a prefix-parametric mapping premise. *)
Section WPDigitValidity.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.

Lemma traverseWPDigit_validity {v1 A B : Type}
  `{GHC.Base.Semigroup v1} `{GHC.Base.Monoid v1}
  (M1 : Measured v1 A) (P : A -> Prop) (Q : B -> Prop)
  (g : v1 -> A -> F B) (vl : v1) (d : Digit A) :
  (forall vl x, P x -> HoldsF Q (g vl x)) ->
  digitValidity P d -> HoldsF (digitValidity Q) (traverseWPDigit g vl d).
Proof.
  intros Hg Hd. destruct d as [a | a b | a b c | a b c d]; cbn in *.
  - apply (HoldsF_fmap Q (digitValidity Q) (@One B)).
    + intros y Hy. exact Hy.
    + apply Hg. exact Hd.
  - destruct Hd as [Ha Hb].
    apply (HoldsF_app Q (digitValidity Q)
      (GHC.Base.fmap (@Two B) (g vl a)) (g (GHC.Base.mappend vl (measure a)) b)).
    + apply (HoldsF_fmap Q (fun h => forall z, Q z -> digitValidity Q (h z))
        (@Two B)).
      * intros y Hy z Hz. cbn. split; assumption.
      * apply Hg. exact Ha.
    + apply Hg. exact Hb.
  - destruct Hd as [Ha [Hb Hc]].
    set (va := GHC.Base.mappend vl (measure a)).
    set (vab := GHC.Base.mappend va (measure b)).
    apply (HoldsF_app Q (digitValidity Q)
      (GHC.Base.op_zlztzg__
        (GHC.Base.fmap (@Three B) (g vl a)) (g va b)) (g vab c)).
    + apply (HoldsF_app Q (fun h => forall z, Q z -> digitValidity Q (h z))
        (GHC.Base.fmap (@Three B) (g vl a)) (g va b)).
      * apply (HoldsF_fmap Q
          (fun h => forall y, Q y -> forall z, Q z -> digitValidity Q (h y z))
          (@Three B)).
        { intros y Hy z Hz w Hw. cbn. repeat split; assumption. }
        { apply Hg. exact Ha. }
      * apply Hg. exact Hb.
    + apply Hg. exact Hc.
  - destruct Hd as [Ha [Hb [Hc Hd]]].
    set (va := GHC.Base.mappend vl (measure a)).
    set (vab := GHC.Base.mappend va (measure b)).
    set (vabc := GHC.Base.mappend vab (measure c)).
    apply (HoldsF_app Q (digitValidity Q)
      (GHC.Base.op_zlztzg__
        (GHC.Base.op_zlztzg__
          (GHC.Base.fmap (@Four B) (g vl a)) (g va b)) (g vab c)) (g vabc d)).
    + apply (HoldsF_app Q (fun h => forall z, Q z -> digitValidity Q (h z))
        (GHC.Base.op_zlztzg__
          (GHC.Base.fmap (@Four B) (g vl a)) (g va b)) (g vab c)).
      * apply (HoldsF_app Q
          (fun h => forall z, Q z -> forall w, Q w -> digitValidity Q (h z w))
          (GHC.Base.fmap (@Four B) (g vl a)) (g va b)).
        { apply (HoldsF_fmap Q
            (fun h => forall y, Q y -> forall z, Q z -> forall w, Q w ->
              digitValidity Q (h y z w))
            (@Four B)).
          - intros y Hy z Hz w Hw u Hu. cbn. repeat split; assumption.
          - apply Hg. exact Ha. }
        { apply Hg. exact Hb. }
      * apply Hg. exact Hc.
    + apply Hg. exact Hd.
Qed.

End WPDigitValidity.

(* Positional node traversal: rebuilt caches. *)
Section WPNodeValidity.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.

Lemma traverseWPNode_validity {v1 v2 A B : Type}
  `{GHC.Base.Semigroup v1} `{GHC.Base.Monoid v1}
  `{GHC.Base.Semigroup v2} `{GHC.Base.Monoid v2}
  (M1 : Measured v1 A) (M2 : Measured v2 B)
  (P : A -> Prop) (Q : B -> Prop) (g : v1 -> A -> F B)
  (vl : v1) (n : Node v1 A) :
  (forall vl x, P x -> HoldsF Q (g vl x)) ->
  nodeValidity (@measure v1 A _ _ M1) P n ->
  HoldsF (nodeValidity (@measure v2 B _ _ M2) Q) (traverseWPNode g vl n).
Proof.
  intros Hg Hn. destruct n as [c a b | c a b d]; cbn [nodeValidity] in *.
  - destruct Hn as [Ha [Hb Hc]].
    apply (HoldsF_app Q (nodeValidity measure Q)
      (GHC.Base.fmap (Data.FingerTree.node2 (v := v2) (a := B)) (g vl a))
      (g (GHC.Base.mappend vl (measure a)) b)).
    + apply (HoldsF_fmap Q
        (fun h => forall z, Q z -> nodeValidity measure Q (h z))
        (Data.FingerTree.node2 (v := v2) (a := B))).
      * intros y Hy z Hz. apply node2_validity; assumption.
      * apply Hg. exact Ha.
    + apply Hg. exact Hb.
  - destruct Hn as [Ha [Hb [Hc Hd]]].
    set (va := GHC.Base.mappend vl (measure a)).
    set (vab := GHC.Base.mappend va (measure b)).
    apply (HoldsF_app Q (nodeValidity measure Q)
      (GHC.Base.op_zlztzg__
        (GHC.Base.fmap (Data.FingerTree.node3 (v := v2) (a := B)) (g vl a))
        (g va b)) (g vab d)).
    + apply (HoldsF_app Q (fun h => forall z, Q z -> nodeValidity measure Q (h z))
        (GHC.Base.fmap (Data.FingerTree.node3 (v := v2) (a := B)) (g vl a))
        (g va b)).
      * apply (HoldsF_fmap Q
          (fun h => forall y, Q y -> forall z, Q z -> nodeValidity measure Q (h y z))
          (Data.FingerTree.node3 (v := v2) (a := B))).
        { intros y Hy z Hz w Hw. apply node3_validity; assumption. }
        { apply Hg. exact Ha. }
      * apply Hg. exact Hb.
    + apply Hg. exact Hc.
Qed.

End WPNodeValidity.

(* Positional traversal of the whole tree. *)
Section WPTreeValidity.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.
Context {v1 v2 A B : Type}
  `{GHC.Base.Semigroup v1} `{GHC.Base.Monoid v1}
  `{GHC.Base.Semigroup v2} `{GHC.Base.Monoid v2}
  (M1 : Measured v1 A) (M2 : Measured v2 B)
  (P : A -> Prop) (Q : B -> Prop).

Lemma traverseWPTree_validityWith :
  forall (g : v1 -> A -> F B) (vl : v1) (t : FingerTree v1 A),
  (forall vl x, P x -> HoldsF Q (g vl x)) ->
  validityWith (@measure v1 A _ _ M1) P t ->
  HoldsF (validityWith (@measure v2 B _ _ M2) Q) (traverseWPTree g vl t).
Proof.
  intros g vl t Hg V.
  revert g vl Hg V.
  refine ((FingerTree_rect v1 (fun A0 t =>
    forall (M3 : Measured v1 A0) (P0 : A0 -> Prop)
           (B0 : Type) (M4 : Measured v2 B0) (Q0 : B0 -> Prop)
           (g0 : v1 -> A0 -> F B0) (vl0 : v1),
    (forall vl x, P0 x -> HoldsF Q0 (g0 vl x)) ->
    validityWith (@measure v1 A0 _ _ M3) P0 t ->
    HoldsF (validityWith (@measure v2 B0 _ _ M4) Q0) (traverseWPTree g0 vl0 t)) _ _ _)
    A t M1 P B M2 Q).
  - intros A0 M3 P0 B0 M4 Q0 g0 vl0 Hg0 V0. cbn [traverseWPTree].
    apply HoldsF_pure. exact I.
  - intros A0 x M3 P0 B0 M4 Q0 g0 vl0 Hg0 Hx. cbn [traverseWPTree validityWith].
    apply (HoldsF_fmap Q0 (fun t' => validityWith (@measure v2 B0 _ _ M4) Q0 t')
      (@Single v2 B0)).
    + intros y Hy. cbn [validityWith]. exact Hy.
    + apply Hg0. exact Hx.
  - intros A0 c pr m IH sf M3 P0 B0 M4 Q0 g0 vl0 Hg0 [Vp [Vm [Vs Ec]]].
    cbn [traverseWPTree].
    set (dpr := traverseWPDigit g0 vl0 pr).
    set (vpr := GHC.Base.mappend vl0 (measure pr)).
    set (dmid := traverseWPTree (traverseWPNode g0) vpr m).
    set (vm := GHC.Base.mappend vpr (measure m)).
    set (dsf := traverseWPDigit g0 vm sf).
    assert (Dp : HoldsF (digitValidity Q0) dpr).
    { apply (traverseWPDigit_validity M3 P0 Q0 g0 vl0 pr); assumption. }
    assert (Dm : HoldsF (validityWith nodeCache (nodeValidity (@measure v2 B0 _ _ M4) Q0)) dmid).
    { apply (IH Measured__Node__5 (nodeValidity (@measure v1 A0 _ _ M3) P0)
        (Node v2 B0) Measured__Node__5 (nodeValidity (@measure v2 B0 _ _ M4) Q0)
        (traverseWPNode g0) vpr).
      - intros vl n Vn. apply (traverseWPNode_validity M3 M4 P0 Q0 g0 vl n); assumption.
      - exact Vm. }
    assert (Ds : HoldsF (digitValidity Q0) dsf).
    { apply (traverseWPDigit_validity M3 P0 Q0 g0 vm sf); assumption. }
    subst dpr vpr dmid vm dsf.
    change (HoldsF (validityWith (@measure v2 B0 _ _ M4) Q0)
      ((GHC.Base.fmap (@deep v2 B0 _ _ _) (traverseWPDigit g0 vl0 pr) <*>
        traverseWPTree (traverseWPNode g0) (GHC.Base.mappend vl0 (measure pr)) m) <*>
       traverseWPDigit g0 (GHC.Base.mappend (GHC.Base.mappend vl0 (measure pr)) (measure m)) sf)).
    refine (@HoldsF_app3 F Functor0 Applicative0 FunctorLaws0 H
      (Digit B0) (FingerTree v2 (Node v2 B0)) (Digit B0) (FingerTree v2 B0)
      (digitValidity Q0)
      (validityWith nodeCache (nodeValidity (@measure v2 B0 _ _ M4) Q0))
      (digitValidity Q0)
      (validityWith (@measure v2 B0 _ _ M4) Q0)
      (@deep v2 B0 _ _ _)
      (traverseWPDigit g0 vl0 pr)
      (traverseWPTree (traverseWPNode g0) (GHC.Base.mappend vl0 (measure pr)) m)
      (traverseWPDigit g0 (GHC.Base.mappend (GHC.Base.mappend vl0 (measure pr)) (measure m)) sf)
      _ Dp Dm Ds).
    intros d m0 s' Vd Vm0 Vs'. apply deep_validityWith; assumption.
Qed.

Lemma traverseWithPos_validityWith (g : v1 -> A -> F B) (t : FingerTree v1 A) :
  (forall vl x, P x -> HoldsF Q (g vl x)) ->
  validityWith (@measure v1 A _ _ M1) P t ->
  HoldsF (validityWith (@measure v2 B _ _ M2) Q) (traverseWithPos g t).
Proof.
  intros Hg V. apply (traverseWPTree_validityWith g GHC.Base.mempty t); assumption.
Qed.

End WPTreeValidity.

(* Contextual traversal: validity with prefix/suffix-parametric mapping. *)
Section WCDigitValidity.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.

Lemma traverseWCDigit_validity {v1 A B : Type}
  `{GHC.Base.Semigroup v1} `{GHC.Base.Monoid v1}
  (M1 : Measured v1 A) (P : A -> Prop) (Q : B -> Prop)
  (g : v1 -> A -> v1 -> F B) (vl : v1) (d : Digit A) (vr : v1) :
  (forall vl x vr, P x -> HoldsF Q (g vl x vr)) ->
  digitValidity P d -> HoldsF (digitValidity Q) (traverseWCDigit g vl d vr).
Proof.
  intros Hg Hd. destruct d as [a | a b | a b c | a b c d]; cbn in *.
  - apply (HoldsF_fmap Q (digitValidity Q) (@One B)).
    + intros y Hy. exact Hy.
    + apply Hg. exact Hd.
  - destruct Hd as [Ha Hb].
    set (vbr := GHC.Base.mappend (measure b) vr).
    set (vla := GHC.Base.mappend vl (measure a)).
    apply (HoldsF_app Q (digitValidity Q)
      (GHC.Base.fmap (@Two B) (g vl a vbr)) (g vla b vr)).
    + apply (HoldsF_fmap Q (fun h => forall z, Q z -> digitValidity Q (h z))
        (@Two B)).
      * intros y Hy z Hz. cbn. split; assumption.
      * apply Hg. exact Ha.
    + apply Hg. exact Hb.
  - destruct Hd as [Ha [Hb Hc]].
    set (vcr := GHC.Base.mappend (measure c) vr).
    set (vbcr := GHC.Base.mappend (measure b) vcr).
    set (vla := GHC.Base.mappend vl (measure a)).
    set (vlab := GHC.Base.mappend vla (measure b)).
    apply (HoldsF_app Q (digitValidity Q)
      (GHC.Base.op_zlztzg__
        (GHC.Base.fmap (@Three B) (g vl a vbcr)) (g vla b vcr))
      (g vlab c vr)).
    + apply (HoldsF_app Q (fun h => forall z, Q z -> digitValidity Q (h z))
        (GHC.Base.fmap (@Three B) (g vl a vbcr)) (g vla b vcr)).
      * apply (HoldsF_fmap Q
          (fun h => forall y, Q y -> forall z, Q z -> digitValidity Q (h y z))
          (@Three B)).
        { intros y Hy z Hz w Hw. cbn. repeat split; assumption. }
        { apply Hg. exact Ha. }
      * apply Hg. exact Hb.
    + apply Hg. exact Hc.
  - destruct Hd as [Ha [Hb [Hc Hd]]].
    set (vdr := GHC.Base.mappend (measure d) vr).
    set (vcdr := GHC.Base.mappend (measure c) vdr).
    set (vbcdr := GHC.Base.mappend (measure b) vcdr).
    set (vla := GHC.Base.mappend vl (measure a)).
    set (vlab := GHC.Base.mappend vla (measure b)).
    set (vlabc := GHC.Base.mappend vlab (measure c)).
    apply (HoldsF_app Q (digitValidity Q)
      (GHC.Base.op_zlztzg__
        (GHC.Base.op_zlztzg__
          (GHC.Base.fmap (@Four B) (g vl a vbcdr)) (g vla b vcdr))
        (g vlab c vdr)) (g vlabc d vr)).
    + apply (HoldsF_app Q (fun h => forall z, Q z -> digitValidity Q (h z))
        (GHC.Base.op_zlztzg__
          (GHC.Base.fmap (@Four B) (g vl a vbcdr)) (g vla b vcdr))
        (g vlab c vdr)).
      * apply (HoldsF_app Q
          (fun h => forall z, Q z -> forall w, Q w -> digitValidity Q (h z w))
          (GHC.Base.fmap (@Four B) (g vl a vbcdr)) (g vla b vcdr)).
        { apply (HoldsF_fmap Q
            (fun h => forall y, Q y -> forall z, Q z -> forall w, Q w ->
              digitValidity Q (h y z w))
            (@Four B)).
          - intros y Hy z Hz w Hw u Hu. cbn. repeat split; assumption.
          - apply Hg. exact Ha. }
        { apply Hg. exact Hb. }
      * apply Hg. exact Hc.
    + apply Hg. exact Hd.
Qed.

End WCDigitValidity.

Section WCNodeValidity.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.

Lemma traverseWCNode_validity {v1 v2 A B : Type}
  `{GHC.Base.Semigroup v1} `{GHC.Base.Monoid v1}
  `{GHC.Base.Semigroup v2} `{GHC.Base.Monoid v2}
  (M1 : Measured v1 A) (M2 : Measured v2 B)
  (P : A -> Prop) (Q : B -> Prop) (g : v1 -> A -> v1 -> F B)
  (vl : v1) (n : Node v1 A) (vr : v1) :
  (forall vl x vr, P x -> HoldsF Q (g vl x vr)) ->
  nodeValidity (@measure v1 A _ _ M1) P n ->
  HoldsF (nodeValidity (@measure v2 B _ _ M2) Q) (traverseWCNode g vl n vr).
Proof.
  intros Hg Hn. destruct n as [c a b | c a b d]; cbn [nodeValidity] in *.
  - destruct Hn as [Ha [Hb Hc]].
    set (vbr := GHC.Base.mappend (measure b) vr).
    set (vla := GHC.Base.mappend vl (measure a)).
    apply (HoldsF_app Q (nodeValidity measure Q)
      (GHC.Base.fmap (Data.FingerTree.node2 (v := v2) (a := B)) (g vl a vbr))
      (g vla b vr)).
    + apply (HoldsF_fmap Q
        (fun h => forall z, Q z -> nodeValidity measure Q (h z))
        (Data.FingerTree.node2 (v := v2) (a := B))).
      * intros y Hy z Hz. apply node2_validity; assumption.
      * apply Hg. exact Ha.
    + apply Hg. exact Hb.
  - destruct Hn as [Ha [Hb [Hc Hd]]].
    set (vcr := GHC.Base.mappend (measure d) vr).
    set (vbcr := GHC.Base.mappend (measure b) vcr).
    set (vla := GHC.Base.mappend vl (measure a)).
    set (vlab := GHC.Base.mappend vla (measure b)).
    apply (HoldsF_app Q (nodeValidity measure Q)
      (GHC.Base.op_zlztzg__
        (GHC.Base.fmap (Data.FingerTree.node3 (v := v2) (a := B)) (g vl a vbcr))
        (g vla b vcr)) (g vlab d vr)).
    + apply (HoldsF_app Q (fun h => forall z, Q z -> nodeValidity measure Q (h z))
        (GHC.Base.fmap (Data.FingerTree.node3 (v := v2) (a := B)) (g vl a vbcr))
        (g vla b vcr)).
      * apply (HoldsF_fmap Q
          (fun h => forall y, Q y -> forall z, Q z -> nodeValidity measure Q (h y z))
          (Data.FingerTree.node3 (v := v2) (a := B))).
        { intros y Hy z Hz w Hw. apply node3_validity; assumption. }
        { apply Hg. exact Ha. }
      * apply Hg. exact Hb.
    + apply Hg. exact Hc.
Qed.

End WCNodeValidity.

(* Contextual traversal of the whole tree. *)
Section WCTreeValidity.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.
Context {v1 v2 A B : Type}
  `{GHC.Base.Semigroup v1} `{GHC.Base.Monoid v1}
  `{GHC.Base.Semigroup v2} `{GHC.Base.Monoid v2}
  (M1 : Measured v1 A) (M2 : Measured v2 B)
  (P : A -> Prop) (Q : B -> Prop).

Lemma traverseWCTree_validityWith :
  forall (g : v1 -> A -> v1 -> F B) (vl : v1) (t : FingerTree v1 A) (vr : v1),
  (forall vl x vr, P x -> HoldsF Q (g vl x vr)) ->
  validityWith (@measure v1 A _ _ M1) P t ->
  HoldsF (validityWith (@measure v2 B _ _ M2) Q) (traverseWCTree g vl t vr).
Proof.
  intros g vl t vr Hg V.
  revert g vl vr Hg V.
  refine ((FingerTree_rect v1 (fun A0 t =>
    forall (M3 : Measured v1 A0) (P0 : A0 -> Prop)
           (B0 : Type) (M4 : Measured v2 B0) (Q0 : B0 -> Prop)
           (g0 : v1 -> A0 -> v1 -> F B0) (vl0 vr0 : v1),
    (forall vl x vr, P0 x -> HoldsF Q0 (g0 vl x vr)) ->
    validityWith (@measure v1 A0 _ _ M3) P0 t ->
    HoldsF (validityWith (@measure v2 B0 _ _ M4) Q0)
      (traverseWCTree g0 vl0 t vr0)) _ _ _)
    A t M1 P B M2 Q).
  - intros A0 M3 P0 B0 M4 Q0 g0 vl0 vr0 Hg0 V0. cbn [traverseWCTree].
    apply HoldsF_pure. exact I.
  - intros A0 x M3 P0 B0 M4 Q0 g0 vl0 vr0 Hg0 Hx.
    cbn [traverseWCTree validityWith].
    apply (HoldsF_fmap Q0 (fun t' => validityWith (@measure v2 B0 _ _ M4) Q0 t')
      (@Single v2 B0)).
    + intros y Hy. cbn [validityWith]. exact Hy.
    + apply Hg0. exact Hx.
  - intros A0 c pr m IH sf M3 P0 B0 M4 Q0 g0 vl0 vr0 Hg0 [Vp [Vm [Vs Ec]]].
    cbn [traverseWCTree].
    set (vm := measure m).
    set (vsr := GHC.Base.mappend (measure sf) vr0).
    set (vmsr := GHC.Base.mappend vm vsr).
    set (vlp := GHC.Base.mappend vl0 (measure pr)).
    set (vlpm := GHC.Base.mappend vlp vm).
    set (dpr := traverseWCDigit g0 vl0 pr vmsr).
    set (dmid := traverseWCTree (traverseWCNode g0) vlp m vsr).
    set (dsf := traverseWCDigit g0 vlpm sf vr0).
    assert (Dp : HoldsF (digitValidity Q0) dpr).
    { apply (traverseWCDigit_validity M3 P0 Q0 g0 vl0 pr vmsr); assumption. }
    assert (Dm : HoldsF (validityWith nodeCache (nodeValidity (@measure v2 B0 _ _ M4) Q0)) dmid).
    { apply (IH Measured__Node__5 (nodeValidity (@measure v1 A0 _ _ M3) P0)
        (Node v2 B0) Measured__Node__5 (nodeValidity (@measure v2 B0 _ _ M4) Q0)
        (traverseWCNode g0) vlp vsr).
      - intros vl n vr Vn. apply (traverseWCNode_validity M3 M4 P0 Q0 g0 vl n vr); assumption.
      - exact Vm. }
    assert (Ds : HoldsF (digitValidity Q0) dsf).
    { apply (traverseWCDigit_validity M3 P0 Q0 g0 vlpm sf vr0); assumption. }
    subst vm vsr vmsr vlp vlpm dpr dmid dsf.
    change (HoldsF (validityWith (@measure v2 B0 _ _ M4) Q0)
      ((GHC.Base.fmap (@deep v2 B0 _ _ _)
          (traverseWCDigit g0 vl0 pr (GHC.Base.mappend (measure m)
            (GHC.Base.mappend (measure sf) vr0))) <*>
        traverseWCTree (traverseWCNode g0) (GHC.Base.mappend vl0 (measure pr)) m
          (GHC.Base.mappend (measure sf) vr0)) <*>
       traverseWCDigit g0
         (GHC.Base.mappend (GHC.Base.mappend vl0 (measure pr)) (measure m)) sf vr0)).
    refine (@HoldsF_app3 F Functor0 Applicative0 FunctorLaws0 H
      (Digit B0) (FingerTree v2 (Node v2 B0)) (Digit B0) (FingerTree v2 B0)
      (digitValidity Q0)
      (validityWith nodeCache (nodeValidity (@measure v2 B0 _ _ M4) Q0))
      (digitValidity Q0)
      (validityWith (@measure v2 B0 _ _ M4) Q0)
      (@deep v2 B0 _ _ _)
      (traverseWCDigit g0 vl0 pr (GHC.Base.mappend (measure m)
        (GHC.Base.mappend (measure sf) vr0)))
      (traverseWCTree (traverseWCNode g0) (GHC.Base.mappend vl0 (measure pr)) m
        (GHC.Base.mappend (measure sf) vr0))
      (traverseWCDigit g0
        (GHC.Base.mappend (GHC.Base.mappend vl0 (measure pr)) (measure m)) sf vr0)
      _ Dp Dm Ds).
    intros d m0 s' Vd Vm0 Vs'. apply deep_validityWith; assumption.
Qed.

Lemma traverseWithContext_validityWith (g : v1 -> A -> v1 -> F B) (t : FingerTree v1 A) :
  (forall vl x vr, P x -> HoldsF Q (g vl x vr)) ->
  validityWith (@measure v1 A _ _ M1) P t ->
  HoldsF (validityWith (@measure v2 B _ _ M2) Q) (traverseWithContext g t).
Proof.
  intros Hg V. apply (traverseWCTree_validityWith g GHC.Base.mempty t GHC.Base.mempty); assumption.
Qed.

End WCTreeValidity.

(* Public corollary: [traverse'] is the generated tree traversal. *)
Section PublicTraverse.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.
Context {v1 v2 A B : Type}
  `{GHC.Base.Semigroup v1} `{GHC.Base.Monoid v1}
  `{GHC.Base.Semigroup v2} `{GHC.Base.Monoid v2}
  (M1 : Measured v1 A) (M2 : Measured v2 B)
  (P : A -> Prop) (Q : B -> Prop).

Lemma traverse'_validityWith (g : A -> F B) (t : FingerTree v1 A) :
  (forall x, P x -> HoldsF Q (g x)) ->
  validityWith (@measure v1 A _ _ M1) P t ->
  HoldsF (validityWith (@measure v2 B _ _ M2) Q) (traverse' g t).
Proof.
  intros Hg V. unfold traverse'. apply (traverseTree_validityWith M1 M2 P Q g t); assumption.
Qed.

End PublicTraverse.

Check @HoldsF_app3.
Check @traverseDigit_validity.
Check @traverseNode_validity.
Check @traverseDigit_measure.
Check @unsafeTraverseNode_measure.
Check @traverseTree_validityWith.
Check @unsafeTraverse_measure.
Check @traverseWPDigit_validity.
Check @traverseWPNode_validity.
Check @traverseWPTree_validityWith.
Check @traverseWithPos_validityWith.
Check @traverseWCDigit_validity.
Check @traverseWCNode_validity.
Check @traverseWCTree_validityWith.
Check @traverseWithContext_validityWith.
Check @traverse'_validityWith.

Print Assumptions traverseDigit_validity.
Print Assumptions traverseNode_validity.
Print Assumptions traverseDigit_measure.
Print Assumptions unsafeTraverseNode_measure.
Print Assumptions traverseTree_validityWith.
Print Assumptions unsafeTraverse_measure.
Print Assumptions traverseWPDigit_validity.
Print Assumptions traverseWPNode_validity.
Print Assumptions traverseWPTree_validityWith.
Print Assumptions traverseWithPos_validityWith.
Print Assumptions traverseWCDigit_validity.
Print Assumptions traverseWCNode_validity.
Print Assumptions traverseWCTree_validityWith.
Print Assumptions traverseWithContext_validityWith.
Print Assumptions traverse'_validityWith.

(* List-composition infrastructure used by the contents theorems.
   These lemmas use functional extensionality; the validity API above does
   not. *)
Check @append_pair.
Check @list_append.
Check @liftA2_pure_left.
Check @liftA2_pure_right.
Check @fmap_append_pair_liftA2_pair.
Check @ap_fmap_right_comp.
Check @liftA2_app_assoc.
Check @traverse_concat.
Check @traverse_concat_app.
Check @traverse_concat_flat_map.
Print Assumptions liftA2_app_assoc.
Print Assumptions traverse_concat_app.
Print Assumptions traverse_concat_flat_map.
Print Assumptions append_pair.
Print Assumptions list_append.
Print Assumptions liftA2_pure_left.
Print Assumptions liftA2_pure_right.
Print Assumptions fmap_append_pair_liftA2_pair.
Print Assumptions ap_fmap_right_comp.
Print Assumptions traverse_concat.
Print Assumptions HoldsF_app3.

Section ContentsSequencing.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.

(* Normalize finite applicative expressions without changing their effect order. *)
Local Ltac normalize_effects :=
  unfold Data.Functor.op_zlzdzg__;
  repeat rewrite applicative_liftA2;
  repeat first [rewrite fmap_ap | rewrite ap_fmap_right_comp |
    rewrite functor_composition].

Lemma traverseDigit_contentsWith {A B X Y : Type}
  (i : A -> list X) (o : B -> list Y) (k : X -> F (list Y))
  (g : A -> F B) (d : Digit A) :
  (forall x, GHC.Base.fmap o (g x) = traverse_concat k (i x)) ->
  GHC.Base.fmap (digitContentsWith o) (traverseDigit g d) =
    traverse_concat k (digitContentsWith i d).
Proof.
  intro E; destruct d; cbn [traverseDigit digitContentsWith];
    repeat rewrite traverse_concat_app;
    repeat rewrite fmap_append_pair_liftA2_pair;
    repeat rewrite liftA2_app_assoc;
    repeat rewrite <- E;
    normalize_effects; try reflexivity;
    repeat f_equal; repeat (apply functional_extensionality; intro);
    unfold GHC.Base.op_z2218U__, list_append; cbn [digitContentsWith];
    repeat rewrite List.app_assoc; reflexivity.
Qed.

Lemma traverseNode_contentsWith {v1 v2 A B X Y : Type}
  `{GHC.Base.Semigroup v2} `{GHC.Base.Monoid v2} (M : Measured v2 B)
  (i : A -> list X) (o : B -> list Y) (k : X -> F (list Y))
  (g : A -> F B) (n : Node v1 A) :
  (forall x, GHC.Base.fmap o (g x) = traverse_concat k (i x)) ->
  GHC.Base.fmap (nodeContentsWith o) (traverseNode g n) =
    traverse_concat k (nodeContentsWith i n).
Proof.
  intro E; destruct n; cbn [traverseNode nodeContentsWith];
    repeat rewrite traverse_concat_app;
    repeat rewrite fmap_append_pair_liftA2_pair;
    repeat rewrite liftA2_app_assoc;
    repeat rewrite <- E;
    normalize_effects; try reflexivity;
    repeat f_equal; repeat (apply functional_extensionality; intro);
    unfold GHC.Base.op_z2218U__, list_append; cbn [nodeContentsWith Data.FingerTree.node2 Data.FingerTree.node3];
    repeat rewrite List.app_assoc; reflexivity.
Qed.

Lemma traverseTree_contentsWith {v1 v2 : Type}
  `{GHC.Base.Semigroup v2} `{GHC.Base.Monoid v2} :
  forall A (t : FingerTree v1 A) B (M : Measured v2 B) X Y
    (i : A -> list X) (o : B -> list Y) (k : X -> F (list Y)) (g : A -> F B),
  (forall x, GHC.Base.fmap o (g x) = traverse_concat k (i x)) ->
  GHC.Base.fmap (contentsWith o) (traverseTree g t) =
    traverse_concat k (contentsWith i t).
Proof.
  refine (FingerTree_rect v1 (fun A t => forall B (M : Measured v2 B) X Y
    (i : A -> list X) (o : B -> list Y) (k : X -> F (list Y)) (g : A -> F B),
    (forall x, GHC.Base.fmap o (g x) = traverse_concat k (i x)) ->
    GHC.Base.fmap (contentsWith o) (traverseTree g t) =
      traverse_concat k (contentsWith i t)) _ _ _).
  - intros. cbn [traverseTree contentsWith traverse_concat].
    rewrite fmap_pure. reflexivity.
  - intros A x B M X Y i o k g E.
    cbn [traverseTree contentsWith]. normalize_effects. apply E.
  - intros A c pr m IH sf B M X Y i o k g E.
    cbn [traverseTree contentsWith].
    repeat rewrite traverse_concat_app.
    repeat rewrite fmap_append_pair_liftA2_pair.
    rewrite <- (traverseDigit_contentsWith i o k g pr E).
    rewrite <- (traverseDigit_contentsWith i o k g sf E).
    rewrite <- (IH (Node v2 B) Measured__Node__5 X Y
      (nodeContentsWith i) (nodeContentsWith o) k (traverseNode g)).
    2: { intro n. apply traverseNode_contentsWith. exact E. }
    rewrite liftA2_app_assoc.
    normalize_effects.
    repeat f_equal; repeat (apply functional_extensionality; intro).
    unfold GHC.Base.op_z2218U__, list_append;
      cbn [contentsWith deep].
    rewrite List.app_assoc. reflexivity.
Qed.

Lemma unsafeTraverseNode_contentsWith {v A B X Y : Type}
  (i : A -> list X) (o : B -> list Y) (k : X -> F (list Y))
  (g : A -> F B) (n : Node v A) :
  (forall x, GHC.Base.fmap o (g x) = traverse_concat k (i x)) ->
  GHC.Base.fmap (nodeContentsWith o) (unsafeTraverseNode g n) =
    traverse_concat k (nodeContentsWith i n).
Proof.
  intro E; destruct n; cbn [unsafeTraverseNode nodeContentsWith];
    repeat rewrite traverse_concat_app;
    repeat rewrite fmap_append_pair_liftA2_pair;
    repeat rewrite liftA2_app_assoc;
    repeat rewrite <- E;
    normalize_effects; try reflexivity;
    repeat f_equal; repeat (apply functional_extensionality; intro);
    unfold GHC.Base.op_z2218U__, list_append; cbn [nodeContentsWith];
    repeat rewrite List.app_assoc; reflexivity.
Qed.

Lemma unsafeTraverse_contentsWith {v : Type} :
  forall A (t : FingerTree v A) B X Y
    (i : A -> list X) (o : B -> list Y) (k : X -> F (list Y)) (g : A -> F B),
  (forall x, GHC.Base.fmap o (g x) = traverse_concat k (i x)) ->
  GHC.Base.fmap (contentsWith o) (unsafeTraverse g t) =
    traverse_concat k (contentsWith i t).
Proof.
  refine (FingerTree_rect v (fun A t => forall B X Y
    (i : A -> list X) (o : B -> list Y) (k : X -> F (list Y)) (g : A -> F B),
    (forall x, GHC.Base.fmap o (g x) = traverse_concat k (i x)) ->
    GHC.Base.fmap (contentsWith o) (unsafeTraverse g t) =
      traverse_concat k (contentsWith i t)) _ _ _).
  - intros. cbn [unsafeTraverse contentsWith traverse_concat].
    rewrite fmap_pure. reflexivity.
  - intros A x B X Y i o k g E.
    cbn [unsafeTraverse contentsWith]. normalize_effects. apply E.
  - intros A c pr m IH sf B X Y i o k g E.
    cbn [unsafeTraverse contentsWith].
    repeat rewrite traverse_concat_app.
    repeat rewrite fmap_append_pair_liftA2_pair.
    rewrite <- (traverseDigit_contentsWith i o k g pr E).
    rewrite <- (traverseDigit_contentsWith i o k g sf E).
    rewrite <- (IH (Node v B) X Y
      (nodeContentsWith i) (nodeContentsWith o) k (unsafeTraverseNode g)).
    2: { intro n. apply unsafeTraverseNode_contentsWith. exact E. }
    rewrite liftA2_app_assoc.
    normalize_effects.
    repeat f_equal; repeat (apply functional_extensionality; intro).
    unfold GHC.Base.op_z2218U__, list_append; cbn [contentsWith].
    rewrite List.app_assoc. reflexivity.
Qed.

Lemma traverse_concat_list {A B : Type} (g : A -> F B) xs :
  traverse_concat (fun x => GHC.Base.fmap (fun y => [y]) (g x)) xs =
    ApplicativeValidity.traverse_list g xs.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  cbn [traverse_concat ApplicativeValidity.traverse_list].
  rewrite IH. normalize_effects. reflexivity.
Qed.

Lemma traverse_concat_singleton {A B : Type} (g : A -> F B) x :
  traverse_concat (fun x => GHC.Base.fmap (fun y => [y]) (g x)) [x] =
  GHC.Base.fmap (fun y => [y]) (g x).
Proof.
  cbn [traverse_concat]. rewrite liftA2_pure_right, functor_composition.
  reflexivity.
Qed.

Lemma traverse'_contents {v1 v2 A B : Type}
  `{GHC.Base.Semigroup v1} `{GHC.Base.Monoid v1} (M1 : Measured v1 A)
  `{GHC.Base.Semigroup v2} `{GHC.Base.Monoid v2} (M : Measured v2 B)
  (g : A -> F B) (t : FingerTree v1 A) :
  GHC.Base.fmap contents (traverse' g t) = traverse_list g (contents t).
Proof.
  rewrite <- traverse_concat_list. unfold traverse', contents.
  apply traverseTree_contentsWith. intro x.
  symmetry; apply traverse_concat_singleton.
Qed.

Lemma unsafeTraverse_contents {v A B : Type}
  (g : A -> F B) (t : FingerTree v A) :
  GHC.Base.fmap contents (unsafeTraverse g t) = traverse_list g (contents t).
Proof.
  rewrite <- traverse_concat_list. unfold contents.
  apply unsafeTraverse_contentsWith. intro x.
  symmetry; apply traverse_concat_singleton.
Qed.

End ContentsSequencing.

Section ContextListSequencing.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.
Context {v : Type} {S : GHC.Base.Semigroup v} {M : GHC.Base.Monoid v}.
Hypothesis assoc : forall x y z : v, GHC.Base.mappend (GHC.Base.mappend x y) z =
  GHC.Base.mappend x (GHC.Base.mappend y z).
Hypothesis left_id : forall x : v, GHC.Base.mappend GHC.Base.mempty x = x.
Hypothesis right_id : forall x : v, GHC.Base.mappend x GHC.Base.mempty = x.

Fixpoint traverse_context_concat {A B : Type} (mu : A -> v)
  (g : v -> A -> v -> F (list B)) (vl : v) (xs : list A) (vr : v) : F (list B) :=
  match xs with
  | [] => GHC.Base.pure []
  | x :: tail => GHC.Base.liftA2 list_append
      (g vl x (GHC.Base.mappend (listMeasure mu tail) vr))
      (traverse_context_concat mu g (GHC.Base.mappend vl (mu x)) tail vr)
  end.

Lemma traverse_context_concat_app {A B : Type} (mu : A -> v)
  (g : v -> A -> v -> F (list B)) xs ys vl vr :
  traverse_context_concat mu g vl (xs ++ ys) vr =
  GHC.Base.liftA2 list_append
    (traverse_context_concat mu g vl xs (GHC.Base.mappend (listMeasure mu ys) vr))
    (traverse_context_concat mu g (GHC.Base.mappend vl (listMeasure mu xs)) ys vr).
Proof.
  revert vl; induction xs as [|x xs IH]; intro vl.
  - cbn [List.app traverse_context_concat listMeasure List.fold_right].
    rewrite right_id, liftA2_pure_left.
    apply eq_sym. apply functor_identity.
  - cbn [List.app traverse_context_concat].
    rewrite (listMeasure_app assoc left_id), assoc, IH.
    cbn [listMeasure List.fold_right].
    rewrite assoc, liftA2_app_assoc. reflexivity.
Qed.

End ContextListSequencing.

Section ContextContents.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.
Context {v1 v2 : Type} {S1 : GHC.Base.Semigroup v1} {M1 : GHC.Base.Monoid v1}
  {S2 : GHC.Base.Semigroup v2} {M2 : GHC.Base.Monoid v2}.
Hypothesis assoc : forall x y z : v1, GHC.Base.mappend (GHC.Base.mappend x y) z =
  GHC.Base.mappend x (GHC.Base.mappend y z).
Hypothesis left_id : forall x : v1, GHC.Base.mappend GHC.Base.mempty x = x.
Hypothesis right_id : forall x : v1, GHC.Base.mappend x GHC.Base.mempty = x.

Local Ltac normalize_context_effects :=
  unfold Data.Functor.op_zlzdzg__;
  repeat rewrite applicative_liftA2;
  repeat first [rewrite fmap_ap | rewrite ap_fmap_right_comp |
    rewrite functor_composition].

Lemma traverseWCDigit_contentsWith {A B X Y : Type} (MA : Measured v1 A)
  (P : A -> Prop) (mu : X -> v1) (i : A -> list X) (o : B -> list Y)
  (k : v1 -> X -> v1 -> F (list Y)) (g : v1 -> A -> v1 -> F B) d vl vr :
  (forall x, P x -> @measure v1 A _ _ MA x = listMeasure mu (i x)) ->
  (forall l x r, P x -> GHC.Base.fmap o (g l x r) =
    traverse_context_concat mu k l (i x) r) ->
  digitValidity P d ->
  GHC.Base.fmap (digitContentsWith o) (traverseWCDigit g vl d vr) =
    traverse_context_concat mu k vl (digitContentsWith i d) vr.
Proof.
  intros Em E V; destruct d; cbn [digitValidity] in V;
    repeat match goal with V : _ /\ _ |- _ => destruct V end;
    cbn [traverseWCDigit digitContentsWith];
    repeat rewrite (traverse_context_concat_app assoc left_id right_id);
    repeat rewrite (listMeasure_app assoc left_id);
    repeat rewrite <- Em by assumption;
    repeat rewrite assoc;
    repeat rewrite <- E by assumption;
    repeat rewrite liftA2_app_assoc;
    normalize_context_effects; try reflexivity;
    repeat f_equal; repeat (apply functional_extensionality; intro);
    unfold GHC.Base.op_z2218U__, list_append; cbn [digitContentsWith];
    repeat rewrite List.app_assoc; reflexivity.
Qed.

Lemma traverseWCNode_contentsWith {A B X Y : Type}
  (MA : Measured v1 A) (MB : Measured v2 B)
  (P : A -> Prop) (mu : X -> v1) (i : A -> list X) (o : B -> list Y)
  (k : v1 -> X -> v1 -> F (list Y)) (g : v1 -> A -> v1 -> F B) n vl vr :
  (forall x, P x -> @measure v1 A _ _ MA x = listMeasure mu (i x)) ->
  (forall l x r, P x -> GHC.Base.fmap o (g l x r) =
    traverse_context_concat mu k l (i x) r) ->
  nodeValidity (@measure v1 A _ _ MA) P n ->
  GHC.Base.fmap (nodeContentsWith o) (traverseWCNode g vl n vr) =
    traverse_context_concat mu k vl (nodeContentsWith i n) vr.
Proof.
  intros Em E V; destruct n; cbn [nodeValidity] in V;
    repeat match goal with V : _ /\ _ |- _ => destruct V end;
    cbn [traverseWCNode nodeContentsWith];
    repeat rewrite (traverse_context_concat_app assoc left_id right_id);
    repeat rewrite (listMeasure_app assoc left_id);
    repeat rewrite <- Em by assumption;
    repeat rewrite assoc;
    repeat rewrite <- E by assumption;
    repeat rewrite liftA2_app_assoc;
    normalize_context_effects; try reflexivity;
    repeat f_equal; repeat (apply functional_extensionality; intro);
    unfold GHC.Base.op_z2218U__, list_append;
    cbn [nodeContentsWith node2 node3];
    repeat rewrite List.app_assoc; reflexivity.
Qed.

Lemma traverseWCTree_contentsWith :
  forall A (t : FingerTree v1 A) B (MA : Measured v1 A) (MB : Measured v2 B)
    X Y (P : A -> Prop) (mu : X -> v1) (i : A -> list X) (o : B -> list Y)
    (k : v1 -> X -> v1 -> F (list Y)) (g : v1 -> A -> v1 -> F B) vl vr,
  (forall x, P x -> @measure v1 A _ _ MA x = listMeasure mu (i x)) ->
  (forall l x r, P x -> GHC.Base.fmap o (g l x r) =
    traverse_context_concat mu k l (i x) r) ->
  validityWith (@measure v1 A _ _ MA) P t ->
  GHC.Base.fmap (contentsWith o) (traverseWCTree g vl t vr) =
    traverse_context_concat mu k vl (contentsWith i t) vr.
Proof.
  refine (FingerTree_rect v1 (fun A t =>
    forall B (MA : Measured v1 A) (MB : Measured v2 B)
      X Y (P : A -> Prop) (mu : X -> v1) (i : A -> list X) (o : B -> list Y)
      (k : v1 -> X -> v1 -> F (list Y)) (g : v1 -> A -> v1 -> F B) vl vr,
    (forall x, P x -> @measure v1 A _ _ MA x = listMeasure mu (i x)) ->
    (forall l x r, P x -> GHC.Base.fmap o (g l x r) =
      traverse_context_concat mu k l (i x) r) ->
    validityWith (@measure v1 A _ _ MA) P t ->
    GHC.Base.fmap (contentsWith o) (traverseWCTree g vl t vr) =
      traverse_context_concat mu k vl (contentsWith i t) vr) _ _ _).
  - intros. cbn [traverseWCTree contentsWith traverse_context_concat].
    rewrite fmap_pure. reflexivity.
  - intros A x B MA MB X Y P mu i o k g vl vr Em E V.
    cbn [traverseWCTree contentsWith]. normalize_context_effects.
    apply E. exact V.
  - intros A c pr m IH sf B MA MB X Y P mu i o k g vl vr Em E
      [Vp [Vm [Vs Ec]]].
    assert (Ep : measure pr = listMeasure mu (digitContentsWith i pr)).
    { change (digitMeasure (@measure v1 A _ _ MA) pr = listMeasure mu (digitContentsWith i pr)).
      exact (valid_digit_measure assoc left_id (@measure v1 A _ _ MA) P i mu pr Em Vp). }
    assert (Es : measure sf = listMeasure mu (digitContentsWith i sf)).
    { change (digitMeasure (@measure v1 A _ _ MA) sf = listMeasure mu (digitContentsWith i sf)).
      exact (valid_digit_measure assoc left_id (@measure v1 A _ _ MA) P i mu sf Em Vs). }
    assert (En : forall n, nodeValidity (@measure v1 A _ _ MA) P n ->
      @measure v1 (Node v1 A) _ _ Measured__Node__5 n =
      listMeasure mu (nodeContentsWith i n)).
    { intros n Vn. eapply valid_node_measure; eassumption. }
    assert (Et : measure m = listMeasure mu (contentsWith (nodeContentsWith i) m)).
    { change (treeCacheWith nodeCache m = listMeasure mu (contentsWith (nodeContentsWith i) m)).
      eapply valid_tree_measure; eassumption. }
    cbn [traverseWCTree contentsWith].
    repeat rewrite (traverse_context_concat_app assoc left_id right_id).
    repeat rewrite (listMeasure_app assoc left_id).
    rewrite <- Ep, <- Es, <- Et.
    rewrite (assoc (measure m) (measure sf) vr).
    rewrite <- (traverseWCDigit_contentsWith MA P mu i o k g pr vl
      (GHC.Base.mappend (measure m) (GHC.Base.mappend (measure sf) vr)) Em E Vp).
    rewrite <- (traverseWCDigit_contentsWith MA P mu i o k g sf
      (GHC.Base.mappend (GHC.Base.mappend vl (measure pr)) (measure m)) vr Em E Vs).
    rewrite <- (IH (Node v2 B) Measured__Node__5 Measured__Node__5 X Y
      (nodeValidity (@measure v1 A _ _ MA) P) mu (nodeContentsWith i)
      (nodeContentsWith o) k (traverseWCNode g)
      (GHC.Base.mappend vl (measure pr)) (GHC.Base.mappend (measure sf) vr) En).
    2: { intros l n r Vn. apply (traverseWCNode_contentsWith MA MB P); assumption. }
    2: exact Vm.
    rewrite liftA2_app_assoc. normalize_context_effects.
    repeat f_equal; repeat (apply functional_extensionality; intro).
    unfold GHC.Base.op_z2218U__, list_append; cbn [contentsWith deep].
    rewrite List.app_assoc. reflexivity.
Qed.

End ContextContents.

Section PublicContextContents.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.
Context {v1 v2 : Type} {S1 : GHC.Base.Semigroup v1} {M1 : GHC.Base.Monoid v1}
  {S2 : GHC.Base.Semigroup v2} {M2 : GHC.Base.Monoid v2}.
Hypothesis assoc : forall x y z : v1, GHC.Base.mappend (GHC.Base.mappend x y) z =
  GHC.Base.mappend x (GHC.Base.mappend y z).
Hypothesis left_id : forall x : v1, GHC.Base.mappend GHC.Base.mempty x = x.
Hypothesis right_id : forall x : v1, GHC.Base.mappend x GHC.Base.mempty = x.

Definition traverse_context_list {A B : Type} (mu : A -> v1)
  (g : v1 -> A -> v1 -> F B) (xs : list A) : F (list B) :=
  traverse_context_concat mu (fun l x r => GHC.Base.fmap (fun y => [y]) (g l x r))
    GHC.Base.mempty xs GHC.Base.mempty.

Lemma traverseWithContext_contents {A B : Type}
  (MA : Measured v1 A) (MB : Measured v2 B)
  (P : A -> Prop) (g : v1 -> A -> v1 -> F B) (t : FingerTree v1 A) :
  validityWith (@measure v1 A _ _ MA) P t ->
  GHC.Base.fmap contents (traverseWithContext g t) =
    traverse_context_list (@measure v1 A _ _ MA) g (contents t).
Proof.
  intro V. unfold traverseWithContext, contents, traverse_context_list.
  eapply (traverseWCTree_contentsWith assoc left_id right_id A t B MA MB _ _ P).
  - intros x Px. cbn [listMeasure List.fold_right]. symmetry; apply right_id.
  - intros l x r Px. cbn [traverse_context_concat listMeasure List.fold_right].
    rewrite left_id, liftA2_pure_right, functor_composition. reflexivity.
  - exact V.
Qed.

Lemma traverseWPNode_as_WC {A B : Type}
  (MA : Measured v1 A) (MB : Measured v2 B)
  (g : v1 -> A -> F B) l (n : Node v1 A) r :
  traverseWPNode g l n = traverseWCNode (fun l x _ => g l x) l n r.
Proof. destruct n; reflexivity. Qed.

Lemma traverseWPDigit_as_WC {A B : Type} (MA : Measured v1 A)
  (g : v1 -> A -> F B) l (d : Digit A) r :
  traverseWPDigit g l d = traverseWCDigit (fun l x _ => g l x) l d r.
Proof. destruct d; reflexivity. Qed.

Lemma traverseWPTree_as_WC : forall A (t : FingerTree v1 A) B
  (MA : Measured v1 A) (MB : Measured v2 B) (g : v1 -> A -> F B) l r,
  traverseWPTree g l t = traverseWCTree (fun l x _ => g l x) l t r.
Proof.
  refine (FingerTree_rect v1 (fun A t => forall B
    (MA : Measured v1 A) (MB : Measured v2 B) (g : v1 -> A -> F B) l r,
    traverseWPTree g l t = traverseWCTree (fun l x _ => g l x) l t r) _ _ _).
  - reflexivity.
  - reflexivity.
  - intros A c pr m IH sf B MA MB g l r.
    cbn [traverseWPTree traverseWCTree].
    rewrite (traverseWPDigit_as_WC MA g l pr
      (GHC.Base.mappend (measure m) (GHC.Base.mappend (measure sf) r))).
    rewrite (traverseWPDigit_as_WC MA g
      (GHC.Base.mappend (GHC.Base.mappend l (measure pr)) (measure m)) sf r).
    rewrite (IH (Node v2 B) Measured__Node__5 Measured__Node__5
      (traverseWPNode g) (GHC.Base.mappend l (measure pr))
      (GHC.Base.mappend (measure sf) r)).
    assert (E : (fun l n r => traverseWPNode g l n) =
      (traverseWCNode (fun l x _ => g l x))).
    { apply functional_extensionality; intro l0.
      apply functional_extensionality; intro n.
      apply functional_extensionality; intro r0.
      apply traverseWPNode_as_WC. }
    rewrite E. reflexivity.
Qed.

Definition traverse_pos_list {A B : Type} (mu : A -> v1)
  (g : v1 -> A -> F B) (xs : list A) : F (list B) :=
  traverse_context_list mu (fun l x _ => g l x) xs.

Lemma traverseWithPos_contents {A B : Type}
  (MA : Measured v1 A) (MB : Measured v2 B)
  (P : A -> Prop) (g : v1 -> A -> F B) (t : FingerTree v1 A) :
  validityWith (@measure v1 A _ _ MA) P t ->
  GHC.Base.fmap contents (traverseWithPos g t) =
    traverse_pos_list (@measure v1 A _ _ MA) g (contents t).
Proof.
  intro V. unfold traverseWithPos.
  rewrite (traverseWPTree_as_WC A t B MA MB g GHC.Base.mempty GHC.Base.mempty).
  exact (traverseWithContext_contents MA MB P (fun l x _ => g l x) t V).
Qed.

End PublicContextContents.

Section ContextFusion.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.
Context {v w : Type} {S : GHC.Base.Semigroup v} {M : GHC.Base.Monoid v}
  {T : GHC.Base.Semigroup w} {N : GHC.Base.Monoid w}.

Lemma traverseDigit_mapWC {A B C : Type} (MA : Measured v A)
  (f : v -> A -> v -> B) (h : B -> F C) (g : v -> A -> v -> F C) d l r :
  (forall l x r, h (f l x r) = g l x r) ->
  traverseDigit h (mapWCDigit f l d r) = traverseWCDigit g l d r.
Proof.
  intro E; destruct d; cbn [mapWCDigit traverseDigit traverseWCDigit];
    repeat rewrite E; reflexivity.
Qed.

Lemma traverseNode_mapWC {A B C : Type}
  (MA : Measured v A) (MB : Measured v B) (MC : Measured w C)
  (f : v -> A -> v -> B) (h : B -> F C) (g : v -> A -> v -> F C) n l r :
  (forall l x r, h (f l x r) = g l x r) ->
  traverseNode h (mapWCNode f l n r) = traverseWCNode g l n r.
Proof.
  intro E; destruct n; cbn [mapWCNode node2 node3 traverseNode traverseWCNode];
    repeat rewrite E; reflexivity.
Qed.

Lemma traverseTree_mapWC : forall A (t : FingerTree v A) B C
  (MA : Measured v A) (MB : Measured v B) (MC : Measured w C)
  (f : v -> A -> v -> B) (h : B -> F C) (g : v -> A -> v -> F C) l r,
  (forall l x r, h (f l x r) = g l x r) ->
  traverseTree h (mapWCTree f l t r) = traverseWCTree g l t r.
Proof.
  refine (FingerTree_rect v (fun A t => forall B C
    (MA : Measured v A) (MB : Measured v B) (MC : Measured w C)
    (f : v -> A -> v -> B) (h : B -> F C) (g : v -> A -> v -> F C) l r,
    (forall l x r, h (f l x r) = g l x r) ->
    traverseTree h (mapWCTree f l t r) = traverseWCTree g l t r) _ _ _).
  - reflexivity.
  - intros. cbn [mapWCTree traverseTree traverseWCTree].
    rewrite H0. reflexivity.
  - intros A c pr m IH sf B C MA MB MC f h g l r E.
    cbn [mapWCTree deep traverseTree traverseWCTree].
    rewrite (traverseDigit_mapWC MA f h g pr _ _ E).
    rewrite (traverseDigit_mapWC MA f h g sf _ _ E).
    rewrite (IH (Node v B) (Node w C) Measured__Node__5 Measured__Node__5
      Measured__Node__5 (mapWCNode f) (traverseNode h) (traverseWCNode g)
      _ _).
    + reflexivity.
    + intros. apply (traverseNode_mapWC MA MB MC f h g). exact E.
Qed.

End ContextFusion.

Section OccurrenceValidity.
Context {v : Type} {S : GHC.Base.Semigroup v} {M : GHC.Base.Monoid v}.

Lemma validityWith_refine_contents : forall A (t : FingerTree v A)
  (mu : A -> v) (P Q : A -> Prop) X (f : A -> list X) (R : X -> Prop),
  (forall x, P x -> List.Forall R (f x) -> Q x) ->
  validityWith mu P t -> List.Forall R (contentsWith f t) -> validityWith mu Q t.
Proof.
  refine (FingerTree_rect v (fun A t => forall (mu : A -> v) (P Q : A -> Prop)
    X (f : A -> list X) (R : X -> Prop),
    (forall x, P x -> List.Forall R (f x) -> Q x) ->
    validityWith mu P t -> List.Forall R (contentsWith f t) -> validityWith mu Q t) _ _ _).
  - intros. exact I.
  - intros A x mu P Q X f R E V All. exact (E x V All).
  - intros A c pr m IH sf mu P Q X f R E [Vp [Vm [Vs Ec]]] All.
    cbn [contentsWith] in All. apply List.Forall_app in All.
    destruct All as [Ap Rest]. apply List.Forall_app in Rest.
    destruct Rest as [Am As]. cbn [validityWith].
    assert (D : forall d, digitValidity P d ->
      List.Forall R (digitContentsWith f d) -> digitValidity Q d).
    { intros d V Ad; destruct d; cbn [digitValidity digitContentsWith] in *;
        repeat match goal with J : List.Forall _ (_ ++ _) |- _ =>
          apply List.Forall_app in J; destruct J end;
        intuition eauto. }
    split; [exact (D pr Vp Ap)|]. split.
    + eapply (IH nodeCache (nodeValidity mu P) (nodeValidity mu Q)
        X (nodeContentsWith f) R); [|exact Vm|exact Am].
      intros n Vn An. destruct n; cbn [nodeValidity nodeContentsWith] in *;
        repeat match goal with J : List.Forall _ (_ ++ _) |- _ =>
          apply List.Forall_app in J; destruct J end;
        intuition eauto.
    + split; [exact (D sf Vs As)|exact Ec].
Qed.

Hypothesis assoc : forall x y z : v, GHC.Base.mappend (GHC.Base.mappend x y) z =
  GHC.Base.mappend x (GHC.Base.mappend y z).
Hypothesis left_id : forall x : v, GHC.Base.mappend GHC.Base.mempty x = x.
Hypothesis right_id : forall x : v, GHC.Base.mappend x GHC.Base.mempty = x.

Lemma contextMap_occurrences {A B : Type} (mu : A -> v)
  (f : v -> A -> v -> B) (Q : B -> Prop) xs :
  (forall pre x post, xs = pre ++ x :: post ->
    Q (f (listMeasure mu pre) x (listMeasure mu post))) ->
  List.Forall Q (contextMap mu f GHC.Base.mempty xs GHC.Base.mempty).
Proof.
  intro E. apply Forall_forall. intros y Hy.
  apply In_nth_error in Hy. destruct Hy as [n Hy].
  assert (L : (n < Corelib.Init.Datatypes.length xs)%nat).
  { rewrite <- (contextMap_length mu f xs GHC.Base.mempty GHC.Base.mempty).
    apply (proj1 (nth_error_Some _ _)). rewrite Hy. discriminate. }
  destruct (List.nth_error xs n) as [x|] eqn:Hx.
  - apply nth_error_split in Hx. destruct Hx as [pre [post [Ex En]]].
    subst xs n.
    rewrite (contextMap_original_at assoc left_id right_id mu f pre x post) in Hy.
    inversion Hy; subst y. apply E. reflexivity.
  - apply (proj2 (nth_error_Some xs n)) in L. contradiction.
Qed.

End OccurrenceValidity.

Section SharpPublicValidity.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.
Context {v w : Type} {S : GHC.Base.Semigroup v} {M : GHC.Base.Monoid v}
  {T : GHC.Base.Semigroup w} {N : GHC.Base.Monoid w}.
Hypothesis assoc : forall x y z : v, GHC.Base.mappend (GHC.Base.mappend x y) z =
  GHC.Base.mappend x (GHC.Base.mappend y z).
Hypothesis left_id : forall x : v, GHC.Base.mappend GHC.Base.mempty x = x.
Hypothesis right_id : forall x : v, GHC.Base.mappend x GHC.Base.mempty = x.

Lemma traverseWithContext_validity_occurrences {A B : Type}
  (MA : Measured v A) (MB : Measured w B) (Q : B -> Prop)
  (g : v -> A -> v -> F B) (t : FingerTree v A) :
  validity MA t ->
  (forall pre x post, contents t = pre ++ x :: post ->
    HoldsF Q (g (listMeasure (@measure v A _ _ MA) pre) x
      (listMeasure (@measure v A _ _ MA) post))) ->
  HoldsF (validityWith (@measure w B _ _ MB) Q) (traverseWithContext g t).
Proof.
  intros V E.
  set (tag := fun (l : v) (x : A) (r : v) => (l,x,r)).
  set (h := fun p : v * A * v => g (fst (fst p)) (snd (fst p)) (snd p)).
  set (R := fun p : v * A * v => HoldsF Q (h p)).
  set (tagged := @fmapWithContext v A v (v * A * v) S M MA S M
    (contextTagMeasured MA) tag t).
  assert (Va : validityWith (@measure v (v * A * v) S M (contextTagMeasured MA))
      (fun _ => True) tagged).
  { unfold tagged, fmapWithContext. apply mapWCTree_validityWith. intros; exact I. }
  assert (All : List.Forall R (contents tagged)).
  { unfold tagged. rewrite (fmapWithContext_contents assoc left_id right_id MA S M
      (contextTagMeasured MA) tag t V).
    apply (contextMap_occurrences assoc left_id right_id).
    intros pre x post Ex. exact (E pre x post Ex). }
  assert (Vr : validityWith (@measure v (v * A * v) S M (contextTagMeasured MA)) R tagged).
  { eapply validityWith_refine_contents; [|exact Va|exact All].
    intros x _ Ax. inversion Ax; assumption. }
  unfold traverseWithContext.
  rewrite <- (traverseTree_mapWC A t (v * A * v) B MA (contextTagMeasured MA)
    MB tag h g GHC.Base.mempty GHC.Base.mempty ltac:(reflexivity)).
  change (HoldsF (validityWith (@measure w B _ _ MB) Q) (traverseTree h tagged)).
  apply (traverseTree_validityWith (contextTagMeasured MA) MB R Q h tagged).
  - intros x Rx. exact Rx.
  - exact Vr.
Qed.

Lemma traverseWithPos_validity_occurrences {A B : Type}
  (MA : Measured v A) (MB : Measured w B) (Q : B -> Prop)
  (g : v -> A -> F B) (t : FingerTree v A) :
  validity MA t ->
  (forall pre x post, contents t = pre ++ x :: post ->
    HoldsF Q (g (listMeasure (@measure v A _ _ MA) pre) x)) ->
  HoldsF (validityWith (@measure w B _ _ MB) Q) (traverseWithPos g t).
Proof.
  intros V E. unfold traverseWithPos.
  rewrite (traverseWPTree_as_WC A t B MA MB g GHC.Base.mempty GHC.Base.mempty).
  apply (traverseWithContext_validity_occurrences MA MB Q (fun l x _ => g l x) t V).
  exact E.
Qed.

End SharpPublicValidity.

(* The independent accumulator traversal is exactly ordinary list traversal
   over CoreContext's occurrence labels. contextMap_original_at fixes each
   label to the original prefix/suffix excluding the current element. *)
Section ReferenceOccurrenceSequencing.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.
Context {v : Type} {S : GHC.Base.Semigroup v} {M : GHC.Base.Monoid v}.

Lemma traverse_context_concat_labels {A B : Type} (mu : A -> v)
  (g : v -> A -> v -> F (list B)) xs l r :
  traverse_context_concat mu g l xs r =
  traverse_concat (fun p : v * A * v => g (fst (fst p)) (snd (fst p)) (snd p))
    (contextMap mu (fun l x r => (l,x,r)) l xs r).
Proof.
  revert l. induction xs as [|x xs IH]; intro l.
  - reflexivity.
  - cbn [traverse_context_concat contextMap contextFlatMap traverse_concat].
    rewrite IH. reflexivity.
Qed.

Lemma traverse_context_list_labels {A B : Type} (mu : A -> v)
  (g : v -> A -> v -> F B) xs :
  traverse_context_list mu g xs =
  traverse_list (fun p : v * A * v => g (fst (fst p)) (snd (fst p)) (snd p))
    (contextMap mu (fun l x r => (l,x,r)) GHC.Base.mempty xs GHC.Base.mempty).
Proof.
  rewrite <- traverse_concat_list. unfold traverse_context_list.
  exact (traverse_context_concat_labels mu
    (fun l x r => GHC.Base.fmap (fun y => [y]) (g l x r)) xs
    GHC.Base.mempty GHC.Base.mempty).
Qed.

Lemma traverse_pos_concat_labels {A B : Type} (mu : A -> v)
  (g : v -> A -> F (list B)) xs l r :
  traverse_context_concat mu (fun l x _ => g l x) l xs r =
  traverse_concat (fun p : v * A => g (fst p) (snd p))
    (positionMap mu pair l xs).
Proof.
  revert l. induction xs as [|x xs IH]; intro l.
  - reflexivity.
  - cbn [traverse_context_concat positionMap positionFlatMap traverse_concat].
    rewrite IH. reflexivity.
Qed.

Lemma traverse_pos_list_labels {A B : Type} (mu : A -> v)
  (g : v -> A -> F B) xs :
  traverse_pos_list mu g xs =
  ApplicativeValidity.traverse_list (fun p : v * A => g (fst p) (snd p))
    (positionMap mu pair GHC.Base.mempty xs).
Proof.
  rewrite <- traverse_concat_list. unfold traverse_pos_list, traverse_context_list.
  exact (traverse_pos_concat_labels mu
    (fun l x => GHC.Base.fmap (fun y => [y]) (g l x)) xs
    GHC.Base.mempty GHC.Base.mempty).
Qed.

End ReferenceOccurrenceSequencing.

Check @traverseDigit_contentsWith. Print Assumptions traverseDigit_contentsWith.
Check @traverseNode_contentsWith. Print Assumptions traverseNode_contentsWith.
Check @traverseTree_contentsWith. Print Assumptions traverseTree_contentsWith.
Check @unsafeTraverseNode_contentsWith. Print Assumptions unsafeTraverseNode_contentsWith.
Check @unsafeTraverse_contentsWith. Print Assumptions unsafeTraverse_contentsWith.
Check @traverse_concat_list. Print Assumptions traverse_concat_list.
Check @traverse_concat_singleton. Print Assumptions traverse_concat_singleton.
Check @traverse'_contents. Print Assumptions traverse'_contents.
Check @unsafeTraverse_contents. Print Assumptions unsafeTraverse_contents.
Check @traverse_context_concat. Print Assumptions traverse_context_concat.
Check @traverse_context_concat_app. Print Assumptions traverse_context_concat_app.
Check @traverseWCDigit_contentsWith. Print Assumptions traverseWCDigit_contentsWith.
Check @traverseWCNode_contentsWith. Print Assumptions traverseWCNode_contentsWith.
Check @traverseWCTree_contentsWith. Print Assumptions traverseWCTree_contentsWith.
Check @traverse_context_list. Print Assumptions traverse_context_list.
Check @traverseWithContext_contents. Print Assumptions traverseWithContext_contents.
Check @traverseWPNode_as_WC. Print Assumptions traverseWPNode_as_WC.
Check @traverseWPDigit_as_WC. Print Assumptions traverseWPDigit_as_WC.
Check @traverseWPTree_as_WC. Print Assumptions traverseWPTree_as_WC.
Check @traverse_pos_list. Print Assumptions traverse_pos_list.
Check @traverseWithPos_contents. Print Assumptions traverseWithPos_contents.
Check @traverseDigit_mapWC. Print Assumptions traverseDigit_mapWC.
Check @traverseNode_mapWC. Print Assumptions traverseNode_mapWC.
Check @traverseTree_mapWC. Print Assumptions traverseTree_mapWC.
Check @validityWith_refine_contents. Print Assumptions validityWith_refine_contents.
Check @contextMap_occurrences. Print Assumptions contextMap_occurrences.
Check @traverseWithContext_validity_occurrences. Print Assumptions traverseWithContext_validity_occurrences.
Check @traverseWithPos_validity_occurrences. Print Assumptions traverseWithPos_validity_occurrences.
Check @traverse_context_concat_labels. Print Assumptions traverse_context_concat_labels.
Check @traverse_context_list_labels. Print Assumptions traverse_context_list_labels.
Check @traverse_pos_concat_labels. Print Assumptions traverse_pos_concat_labels.
Check @traverse_pos_list_labels. Print Assumptions traverse_pos_list_labels.

(* Exact global-assumption inventory (58 exported declarations):
   18 have the singleton set {functional_extensionality_dep}:
     liftA2_app_assoc, traverse_concat_app, traverse_concat_flat_map,
     traverseDigit_contentsWith, traverseNode_contentsWith,
     traverseTree_contentsWith, unsafeTraverseNode_contentsWith,
     unsafeTraverse_contentsWith, traverse'_contents, unsafeTraverse_contents,
     traverse_context_concat_app, traverseWCDigit_contentsWith,
     traverseWCNode_contentsWith, traverseWCTree_contentsWith,
     traverseWithContext_contents, traverseWPTree_as_WC,
     traverseWithPos_contents, traverseWithPos_validity_occurrences.
   The other 40 have the empty global-assumption set, including
   traverseWithContext_validity_occurrences and all original validity/cache
   contracts. Dictionaries, laws, input validity and mapping-function premises
   are explicit theorem parameters, not global assumptions. *)
