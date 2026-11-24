(* Generic applicative validity for the translated finger-tree traversals.

   This file implements the constructive [HoldsF] specification from the
   agreed finger-tree specification (generic applicative traversals):

     HoldsF P fa  :=  exists z : F {a : A | P a},
                        fmap proj1_sig z = fa

   The operations and dictionaries are the translated ones in the isolated
   Rocq 9.2 [GHC.Base], and the law hypotheses are the translated
   [Proofs.GHC.Base.FunctorLaws] and [Proofs.GHC.Base.ApplicativeLaws].
   No effect is assumed to disappear: [None], for example, satisfies the
   specification vacuously. *)

(* The base-thy proof module deliberately reuses the logical module name
   [GHC.Base].  Loading it therefore masks the root [GHC.Base] name; both
   modules still resolve, as the checks at the end of this file show. *)
Set Warnings "-masking-absolute-name".

Require Import GHC.Base.
Require Import Proofs.GHC.Base.
Require Import Data.Traversable.
Require Import Data.FingerTree.
Require Import Stdlib.Lists.List.

Set Bullet Behavior "Strict Subproofs".
Set Typeclasses Depth 3.

(* ------------------------------------------------------------------ *)
(* Constructive validity inside an arbitrary functor.                  *)
(* ------------------------------------------------------------------ *)

Definition HoldsF {F : Type -> Type} `{GHC.Base.Functor F} {A : Type}
    (P : A -> Prop) (fa : F A) : Prop :=
  exists z : F {a : A | P a}, GHC.Base.fmap (@proj1_sig A P) z = fa.

(* ------------------------------------------------------------------ *)
(* Functor-law closure.                                               *)
(* ------------------------------------------------------------------ *)

Section HoldsFFunctor.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.FunctorLaws F}.

Lemma HoldsF_fmap {A B : Type} (P : A -> Prop) (Q : B -> Prop)
    (f : A -> B) :
  (forall x, P x -> Q (f x)) ->
  forall fa, HoldsF P fa -> HoldsF Q (GHC.Base.fmap f fa).
Proof.
  intros Hpt fa [z Hz]. subst fa.
  exists (GHC.Base.fmap
    (fun a : {x : A | P x} =>
       exist Q (f (proj1_sig a)) (Hpt (proj1_sig a) (proj2_sig a))) z).
  rewrite functor_composition.
  rewrite functor_composition.
  reflexivity.
Qed.

End HoldsFFunctor.

(* ------------------------------------------------------------------ *)
(* Lawful-applicative coherence and closure.                          *)
(* ------------------------------------------------------------------ *)

Section HoldsFApplicative.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.

(* These are the derived coherence facts needed to push [fmap proj1_sig]
   through [<*>].  They use only [ApplicativeLaws], not an extra law. *)
Lemma fmap_pure {A B : Type} (f : A -> B) (x : A) :
  GHC.Base.fmap f (GHC.Base.pure x) = GHC.Base.pure (f x).
Proof.
  rewrite applicative_fmap.
  rewrite applicative_homomorphism.
  reflexivity.
Qed.

Lemma fmap_ap {A B C : Type} (h : B -> C)
    (u : F (A -> B)) (v : F A) :
  GHC.Base.fmap h (GHC.Base.op_zlztzg__ u v)
  = GHC.Base.op_zlztzg__ (GHC.Base.fmap (GHC.Base.op_z2218U__ h) u) v.
Proof.
  rewrite applicative_fmap.
  rewrite <- applicative_composition.
  rewrite applicative_homomorphism.
  rewrite <- applicative_fmap.
  reflexivity.
Qed.

Lemma ap_fmap_right {A B C : Type} (u : F (B -> C)) (k : A -> B) (v : F A) :
  GHC.Base.op_zlztzg__ u (GHC.Base.fmap k v)
  = GHC.Base.op_zlztzg__ (GHC.Base.fmap (fun f x => f (k x)) u) v.
Proof.
  rewrite applicative_fmap.
  rewrite <- applicative_composition.
  rewrite applicative_interchange.
  rewrite <- applicative_fmap.
  rewrite <- applicative_fmap.
  rewrite functor_composition.
  reflexivity.
Qed.

Lemma HoldsF_pure {A : Type} (P : A -> Prop) (x : A) :
  P x -> HoldsF P (GHC.Base.pure x).
Proof.
  intro HP. exists (GHC.Base.pure (exist P x HP)).
  apply fmap_pure.
Qed.

(* The exact forall preserving premise required by the specification. *)
Lemma HoldsF_app {A B : Type} (P : A -> Prop) (Q : B -> Prop)
    (ff : F (A -> B)) (fa : F A) :
  HoldsF (fun f => forall x, P x -> Q (f x)) ff ->
  HoldsF P fa -> HoldsF Q (GHC.Base.op_zlztzg__ ff fa).
Proof.
  intros [zf Hf] [za Ha]. subst ff fa.
  exists (GHC.Base.op_zlztzg__
    (GHC.Base.fmap
      (fun f : {f : A -> B | forall x, P x -> Q (f x)} =>
         fun a : {x : A | P x} =>
           exist Q (proj1_sig f (proj1_sig a))
             (proj2_sig f (proj1_sig a) (proj2_sig a))) zf) za).
  rewrite fmap_ap.
  rewrite functor_composition.
  rewrite ap_fmap_right.
  rewrite functor_composition.
  reflexivity.
Qed.

Lemma HoldsF_liftA2 {A B C : Type} (P : A -> Prop) (Q : B -> Prop)
    (R : C -> Prop) (f : A -> B -> C) (fa : F A) (fb : F B) :
  (forall x y, P x -> Q y -> R (f x y)) ->
  HoldsF P fa -> HoldsF Q fb -> HoldsF R (GHC.Base.liftA2 f fa fb).
Proof.
  intros Hpt Ha Hb.
  rewrite applicative_liftA2.
  eapply HoldsF_app.
  - eapply HoldsF_fmap.
    + intros x Hx y Hy. exact (Hpt x y Hx Hy).
    + exact Ha.
  - exact Hb.
Qed.

End HoldsFApplicative.

(* ------------------------------------------------------------------ *)
(* Left-to-right list traversal.                                      *)
(* ------------------------------------------------------------------ *)

(* [traverse_list] is the reference left-to-right traversal: the head
   effect is the first argument to [liftA2] and the tail is the second.
   It has exactly the generated list instance's [foldr] shape. *)
Section ListTraversals.
Context {F : Type -> Type}.
Context `{GHC.Base.Applicative F}.

Fixpoint traverse_list {A B : Type} (g : A -> F B) (xs : list A) : F (list B) :=
  match xs with
  | nil => GHC.Base.pure nil
  | cons x xs => GHC.Base.liftA2 cons (g x) (traverse_list g xs)
  end.

Definition sequenceA_list {A : Type} (xs : list (F A)) : F (list A) :=
  traverse_list (fun x => x) xs.

Lemma traverse_list_eq_foldr {A B : Type} (g : A -> F B) (xs : list A) :
  traverse_list g xs =
  GHC.Base.foldr (fun x ys => GHC.Base.liftA2 cons (g x) ys) (GHC.Base.pure nil) xs.
Proof.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* The generated list instance is exactly the reference traversal. *)
Lemma Traversable_list_traverse_eq {A B : Type} (g : A -> F B) (xs : list A) :
  Data.Traversable.Traversable__list_traverse g xs = traverse_list g xs.
Proof.
  rewrite traverse_list_eq_foldr.
  reflexivity.
Qed.

Lemma Traversable_list_sequenceA_eq {A : Type} (xs : list (F A)) :
  Data.Traversable.Traversable__list_sequenceA xs = sequenceA_list xs.
Proof.
  unfold Data.Traversable.Traversable__list_sequenceA.
  unfold sequenceA_list.
  apply Traversable_list_traverse_eq.
Qed.

(* The public class method agrees with the generated list instance body. *)
Lemma Traversable_list_traverse_class_eq {A B : Type} (g : A -> F B) (xs : list A) :
  Data.Traversable.traverse (f := F) (a := A) (b := B) g xs = traverse_list g xs.
Proof.
  unfold Data.Traversable.traverse.
  unfold Data.Traversable.Traversable__list.
  apply Traversable_list_traverse_eq.
Qed.

Lemma Traversable_list_sequenceA_class_eq {A : Type} (xs : list (F A)) :
  Data.Traversable.sequenceA (f := F) (a := A) xs = sequenceA_list xs.
Proof.
  unfold Data.Traversable.sequenceA.
  unfold Data.Traversable.Traversable__list.
  unfold Data.Traversable.Traversable__list_sequenceA.
  apply Traversable_list_traverse_eq.
Qed.

End ListTraversals.

(* ------------------------------------------------------------------ *)
(* Validity of list sequencing and traversal.                         *)
(* ------------------------------------------------------------------ *)

Section ListValidity.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.

Lemma HoldsF_traverse_list {A B : Type} (P : B -> Prop) (Q : A -> Prop)
    (g : A -> F B) (xs : list A) :
  (forall x, Q x -> HoldsF P (g x)) ->
  Forall Q xs -> HoldsF (Forall P) (traverse_list g xs).
Proof.
  intros Hg Hxs. induction xs as [|x xs IH].
  - simpl. apply HoldsF_pure. constructor.
  - simpl. inversion Hxs as [|x' xs' Hx Hxs']; subst.
    apply (HoldsF_liftA2 P (Forall P) (Forall P) (@cons B) (g x) (traverse_list g xs)).
    + intros y ys Hy Hys. constructor; assumption.
    + apply Hg. assumption.
    + apply IH. assumption.
Qed.

Lemma HoldsF_sequenceA_list {A : Type} (P : A -> Prop) (xs : list (F A)) :
  Forall (HoldsF P) xs -> HoldsF (Forall P) (sequenceA_list xs).
Proof.
  unfold sequenceA_list.
  apply (HoldsF_traverse_list P (HoldsF P) (fun x => x)).
  - intros x Hx. exact Hx.
Qed.

Lemma HoldsF_Traversable_list_traverse {A B : Type} (P : B -> Prop)
    (Q : A -> Prop) (g : A -> F B) (xs : list A) :
  (forall x, Q x -> HoldsF P (g x)) ->
  Forall Q xs ->
  HoldsF (Forall P) (Data.Traversable.Traversable__list_traverse g xs).
Proof.
  intros Hg Hxs. rewrite Traversable_list_traverse_eq.
  apply (HoldsF_traverse_list P Q g xs); assumption.
Qed.

Lemma HoldsF_Traversable_list_sequenceA {A : Type} (P : A -> Prop)
    (xs : list (F A)) :
  Forall (HoldsF P) xs ->
  HoldsF (Forall P) (Data.Traversable.Traversable__list_sequenceA xs).
Proof.
  intros Hxs.
  unfold Data.Traversable.Traversable__list_sequenceA.
  apply HoldsF_Traversable_list_traverse with (Q := HoldsF P).
  - intros x Hx. exact Hx.
  - exact Hxs.
Qed.

Lemma HoldsF_Traversable_list_traverse_class {A B : Type} (P : B -> Prop)
    (Q : A -> Prop) (g : A -> F B) (xs : list A) :
  (forall x, Q x -> HoldsF P (g x)) ->
  Forall Q xs ->
  HoldsF (Forall P) (Data.Traversable.traverse (f := F) (a := A) (b := B) g xs).
Proof.
  intros Hg Hxs. rewrite Traversable_list_traverse_class_eq.
  apply (HoldsF_traverse_list P Q g xs); assumption.
Qed.

Lemma HoldsF_Traversable_list_sequenceA_class {A : Type} (P : A -> Prop)
    (xs : list (F A)) :
  Forall (HoldsF P) xs ->
  HoldsF (Forall P) (Data.Traversable.sequenceA (f := F) (a := A) xs).
Proof.
  intros Hxs. rewrite Traversable_list_sequenceA_class_eq.
  apply HoldsF_sequenceA_list. exact Hxs.
Qed.

End ListValidity.

(* ------------------------------------------------------------------ *)
(* Actual small generated core traversals: [Digit] and [Node].         *)
(* ------------------------------------------------------------------ *)

Definition DigitAll {A : Type} (P : A -> Prop) (d : Digit A) : Prop :=
  match d with
  | One a => P a
  | Two a b => P a /\ P b
  | Three a b c => P a /\ P b /\ P c
  | Four a b c d => P a /\ P b /\ P c /\ P d
  end.

Definition NodeAll {v A : Type} (P : A -> Prop) (n : Node v A) : Prop :=
  match n with
  | Node2 _ a b => P a /\ P b
  | Node3 _ a b c => P a /\ P b /\ P c
  end.

Section NodeAllConstructors.
Context {v A : Type}.
Context {Hsemi : GHC.Base.Semigroup v}.
Context {Hmono : GHC.Base.Monoid v}.
Context {Hmeas : Measured v A}.

Lemma NodeAll_node2 (P : A -> Prop) (x y : A) :
  NodeAll P (@Data.FingerTree.node2 v A _ _ _ x y) <-> P x /\ P y.
Proof. simpl. reflexivity. Qed.

Lemma NodeAll_node3 (P : A -> Prop) (x y z : A) :
  NodeAll P (@Data.FingerTree.node3 v A _ _ _ x y z) <-> P x /\ P y /\ P z.
Proof. simpl. reflexivity. Qed.

End NodeAllConstructors.

Section CoreSmallTraversals.
Context {F : Type -> Type}.
Context `{Proofs.GHC.Base.ApplicativeLaws F}.

Lemma traverseDigit_holds {A B : Type} (P : B -> Prop) (Q : A -> Prop)
    (g : A -> F B) (d : Digit A) :
  (forall x, Q x -> HoldsF P (g x)) ->
  DigitAll Q d -> HoldsF (DigitAll P) (@Data.FingerTree.traverseDigit F A B _ _ g d).
Proof.
  intros Hg Hd. destruct d as [a | a b | a b c | a b c d]; simpl in *.
  - apply (HoldsF_fmap P (DigitAll P) (@Data.FingerTree.One B)).
    + intros y Hy. exact Hy.
    + apply Hg. exact Hd.
  - destruct Hd as [Ha Hb].
    apply (HoldsF_app P (DigitAll P)
      (GHC.Base.fmap (@Data.FingerTree.Two B) (g a)) (g b)).
    + apply (HoldsF_fmap P
        (fun h => forall z, P z -> DigitAll P (h z))
        (@Data.FingerTree.Two B)).
      * intros y Hy z Hz. simpl. split; assumption.
      * apply Hg. exact Ha.
    + apply Hg. exact Hb.
  - destruct Hd as [Ha [Hb Hc]].
    apply (HoldsF_app P (DigitAll P)
      (GHC.Base.op_zlztzg__
        (GHC.Base.fmap (@Data.FingerTree.Three B) (g a)) (g b)) (g c)).
    + apply (HoldsF_app P (fun h => forall z, P z -> DigitAll P (h z))
        (GHC.Base.fmap (@Data.FingerTree.Three B) (g a)) (g b)).
      * apply (HoldsF_fmap P
          (fun h => forall y, P y -> forall z, P z -> DigitAll P (h y z))
          (@Data.FingerTree.Three B)).
        { intros y Hy z Hz w Hw. simpl. repeat split; assumption. }
        { apply Hg. exact Ha. }
      * apply Hg. exact Hb.
    + apply Hg. exact Hc.
  - destruct Hd as [Ha [Hb [Hc Hd]]].
    apply (HoldsF_app P (DigitAll P)
      (GHC.Base.op_zlztzg__
        (GHC.Base.op_zlztzg__
          (GHC.Base.fmap (@Data.FingerTree.Four B) (g a)) (g b)) (g c)) (g d)).
    + apply (HoldsF_app P (fun h => forall z, P z -> DigitAll P (h z))
        (GHC.Base.op_zlztzg__
          (GHC.Base.fmap (@Data.FingerTree.Four B) (g a)) (g b)) (g c)).
      * apply (HoldsF_app P (fun h => forall z, P z -> forall w, P w -> DigitAll P (h z w))
          (GHC.Base.fmap (@Data.FingerTree.Four B) (g a)) (g b)).
        { apply (HoldsF_fmap P
            (fun h => forall y, P y -> forall z, P z -> forall w, P w -> DigitAll P (h y z w))
            (@Data.FingerTree.Four B)).
          - intros y Hy z Hz w Hw u Hu. simpl. repeat split; assumption.
          - apply Hg. exact Ha. }
        { apply Hg. exact Hb. }
      * apply Hg. exact Hc.
    + apply Hg. exact Hd.
Qed.

Section TraverseNodeAux.
Context {v1 v2 A B : Type}.
Context {Hsemi : GHC.Base.Semigroup v2}.
Context {Hmono : GHC.Base.Monoid v2}.
Context {Hmeas : Measured v2 B}.

Lemma traverseNode_holds
    (P : B -> Prop) (Q : A -> Prop) (g : A -> F B) (n : Node v1 A) :
  (forall x, Q x -> HoldsF P (g x)) ->
  NodeAll Q n ->
  HoldsF (NodeAll P)
    (Data.FingerTree.traverseNode (v2 := v2) (a2 := B) (f := F)
       (a1 := A) (v1 := v1) g n).
Proof.
  intros Hg Hn. destruct n as [v a b | v a b c]; simpl in *.
  - destruct Hn as [Ha Hb].
    apply (HoldsF_app P (NodeAll P)
      (GHC.Base.fmap (Data.FingerTree.node2 (v := v2) (a := B)) (g a)) (g b)).
    + apply (HoldsF_fmap P
        (fun h => forall z, P z -> NodeAll P (h z))
        (Data.FingerTree.node2 (v := v2) (a := B))).
      * intros y Hy z Hz. simpl. split; assumption.
      * apply Hg. exact Ha.
    + apply Hg. exact Hb.
  - destruct Hn as [Ha [Hb Hc]].
    apply (HoldsF_app P (NodeAll P)
      (GHC.Base.op_zlztzg__
        (GHC.Base.fmap (Data.FingerTree.node3 (v := v2) (a := B)) (g a)) (g b)) (g c)).
    + apply (HoldsF_app P (fun h => forall z, P z -> NodeAll P (h z))
        (GHC.Base.fmap (Data.FingerTree.node3 (v := v2) (a := B)) (g a)) (g b)).
      * apply (HoldsF_fmap P
          (fun h => forall y, P y -> forall z, P z -> NodeAll P (h y z))
          (Data.FingerTree.node3 (v := v2) (a := B))).
        { intros y Hy z Hz w Hw. simpl. repeat split; assumption. }
        { apply Hg. exact Ha. }
      * apply Hg. exact Hb.
    + apply Hg. exact Hc.
Qed.

End TraverseNodeAux.

End CoreSmallTraversals.

(* ------------------------------------------------------------------ *)
(* Concrete vacuity check: validity does not force effects to vanish. *)
(* ------------------------------------------------------------------ *)

Section OptionSanity.
Lemma HoldsF_None {A : Type} (P : A -> Prop) :
  @HoldsF option GHC.Base.Functor__option A P None.
Proof. exists None. reflexivity. Qed.

Lemma HoldsF_Some_iff {A : Type} (P : A -> Prop) (x : A) :
  @HoldsF option GHC.Base.Functor__option A P (Some x) <-> P x.
Proof.
  split.
  - intros [[a |] H]; [| discriminate H].
    destruct a as [a Ha]. simpl in H. inversion H. subst. exact Ha.
  - intro HP. exists (Some (exist P x HP)). reflexivity.
Qed.
End OptionSanity.

(* ------------------------------------------------------------------ *)
(* Auditable interface.                                               *)
(* ------------------------------------------------------------------ *)

Check @HoldsF.
Check @HoldsF_fmap.
Check @fmap_pure.
Check @fmap_ap.
Check @ap_fmap_right.
Check @HoldsF_pure.
Check @HoldsF_app.
Check @HoldsF_liftA2.
Check @traverse_list.
Check @sequenceA_list.
Check @HoldsF_traverse_list.
Check @HoldsF_sequenceA_list.
Check @HoldsF_Traversable_list_traverse.
Check @HoldsF_Traversable_list_sequenceA.
Check @HoldsF_Traversable_list_traverse_class.
Check @HoldsF_Traversable_list_sequenceA_class.
Check @DigitAll.
Check @NodeAll.
Check @traverseDigit_holds.
Check @traverseNode_holds.
Check @NodeAll_node2.
Check @NodeAll_node3.
Check @HoldsF_None.
Check @HoldsF_Some_iff.

Print Assumptions HoldsF.
Print Assumptions HoldsF_fmap.
Print Assumptions fmap_pure.
Print Assumptions fmap_ap.
Print Assumptions ap_fmap_right.
Print Assumptions HoldsF_pure.
Print Assumptions HoldsF_app.
Print Assumptions HoldsF_liftA2.
Print Assumptions traverse_list.
Print Assumptions sequenceA_list.
Print Assumptions traverse_list_eq_foldr.
Print Assumptions Traversable_list_traverse_eq.
Print Assumptions Traversable_list_sequenceA_eq.
Print Assumptions Traversable_list_traverse_class_eq.
Print Assumptions Traversable_list_sequenceA_class_eq.
Print Assumptions HoldsF_traverse_list.
Print Assumptions HoldsF_sequenceA_list.
Print Assumptions HoldsF_Traversable_list_traverse.
Print Assumptions HoldsF_Traversable_list_sequenceA.
Print Assumptions HoldsF_Traversable_list_traverse_class.
Print Assumptions HoldsF_Traversable_list_sequenceA_class.
Print Assumptions DigitAll.
Print Assumptions NodeAll.
Print Assumptions NodeAll_node2.
Print Assumptions NodeAll_node3.
Print Assumptions traverseDigit_holds.
Print Assumptions traverseNode_holds.
Print Assumptions HoldsF_None.
Print Assumptions HoldsF_Some_iff.