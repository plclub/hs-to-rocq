From Stdlib Require Import Lists.List ZArith.ZArith Bool.Bool Classes.RelationClasses micromega.Lia.
Require Import Data.FingerTree Data.Foldable GHC.Num Data.SemigroupInternal.
Require Import FingerTreeProofs.CoreModel FingerTreeProofs.CoreOperations.
Require Import Proofs.GHC.Base.
Import ListNotations.

Definition digitContents {a} (d : Digit a) := digitContentsWith (fun x => [x]) d.
Definition nodeContents {v a} (n : Node v a) := nodeContentsWith (fun x => [x]) n.

(* A behavioral contract for all twelve actual Foldable methods. Strict folds
   use their source left/right association; no numeric laws are assumed. *)
Definition FoldableBehavior (F : Type -> Type) (FL : Data.Foldable.Foldable F)
  (C : forall a, F a -> list a) : Prop :=
  (forall m (S : GHC.Base.Semigroup m) (N : GHC.Base.Monoid m),
    (forall x y z : m, GHC.Base.mappend (GHC.Base.mappend x y) z = GHC.Base.mappend x (GHC.Base.mappend y z)) ->
    (forall x : m, GHC.Base.mappend GHC.Base.mempty x = x) ->
    (forall x : m, GHC.Base.mappend x GHC.Base.mempty = x) ->
    forall a (f : a -> m) t, @Data.Foldable.foldMap F FL m a S N f t = listMeasure f (C a t)) /\
  (forall m (S : GHC.Base.Semigroup m) (N : GHC.Base.Monoid m),
    (forall x y z : m, GHC.Base.mappend (GHC.Base.mappend x y) z = GHC.Base.mappend x (GHC.Base.mappend y z)) ->
    (forall x : m, GHC.Base.mappend GHC.Base.mempty x = x) ->
    (forall x : m, GHC.Base.mappend x GHC.Base.mempty = x) ->
    forall t, @Data.Foldable.fold F FL m S N t = listMeasure (fun x => x) (C m t)) /\
  (forall m a (S : GHC.Base.Semigroup m) (N : GHC.Base.Monoid m) (f : a -> m) t,
    @Data.Foldable.foldMap' F FL m a S N f t =
      List.fold_left (fun acc x => GHC.Base.op_zlzlzgzg__ acc (f x)) (C a t) GHC.Base.mempty) /\
  (forall a b (f : a -> b -> b) z t, @Data.Foldable.foldr F FL a b f z t = List.fold_right f z (C a t)) /\
  (forall b a (f : b -> a -> b) z t, @Data.Foldable.foldl F FL b a f z t = List.fold_left f (C a t) z) /\
  (forall b a (f : b -> a -> b) z t, @Data.Foldable.foldl' F FL b a f z t = List.fold_left f (C a t) z) /\
  (forall a b (f : a -> b -> b) z t, @Data.Foldable.foldr' F FL a b f z t = List.fold_right f z (C a t)) /\
  (forall a t, @Data.Foldable.null F FL a t = match C a t with [] => true | _ => false end) /\
  (forall a t, @Data.Foldable.length F FL a t = Z.of_nat (Datatypes.length (C a t))) /\
  (forall a (N : GHC.Num.Num a) t, @Data.Foldable.product F FL a N t =
    List.fold_left GHC.Num.op_zt__ (C a t) (GHC.Num.fromInteger 1%Z)) /\
  (forall a (N : GHC.Num.Num a) t, @Data.Foldable.sum F FL a N t =
    List.fold_left GHC.Num.op_zp__ (C a t) (GHC.Num.fromInteger 0%Z)) /\
  (forall a t, @Data.Foldable.toList F FL a t = C a t).

Lemma digit_foldable_behavior : FoldableBehavior Digit Foldable__Digit (fun a => @digitContents a).
Proof.
  unfold FoldableBehavior; repeat apply conj.
  - intros m S N A L R a f t; rewrite foldMap_digit; apply digitMeasure_contents; assumption.
  - intros m S N A L R t; change (Data.Foldable.foldMap (fun x => x) t = listMeasure (fun x => x) (digitContents t)).
    rewrite foldMap_digit; apply digitMeasure_contents; assumption.
  - intros; destruct t; reflexivity.
  - intros; destruct t; reflexivity.
  - intros; destruct t; reflexivity.
  - intros; destruct t; reflexivity.
  - intros; destruct t; reflexivity.
  - intros; destruct t; reflexivity.
  - intros; destruct t; reflexivity.
  - intros; destruct t; reflexivity.
  - intros; destruct t; reflexivity.
  - intros; destruct t; reflexivity.
Qed.

Definition viewLModel {s a} (x : ViewL s a) : option (a * s a) :=
  match x with EmptyL => None | op_ZCzl__ x xs => Some (x, xs) end.
Definition viewRModel {s a} (x : ViewR s a) : option (s a * a) :=
  match x with EmptyR => None | op_ZCzg__ xs x => Some (xs, x) end.
Definition searchEqModel {v a} (x : SearchResult v a)
  : option (option (option (list a * (a * list a)))) :=
  match x with
  | Position l x r => Some (Some (Some (contents l, (x, contents r))))
  | OnLeft => Some (Some None)
  | OnRight => Some None
  | Nowhere => None
  end.

Lemma viewL_eq_model {s a} `{GHC.Base.Eq_ a} `{GHC.Base.Eq_ (s a)} (x y : ViewL s a) :
  GHC.Base.op_zeze__ x y = GHC.Base.op_zeze__ (viewLModel x) (viewLModel y).
Proof. destruct x, y; reflexivity. Qed.
Lemma viewR_eq_model {s a} `{GHC.Base.Eq_ a} `{GHC.Base.Eq_ (s a)} (x y : ViewR s a) :
  GHC.Base.op_zeze__ x y = GHC.Base.op_zeze__ (viewRModel x) (viewRModel y).
Proof. destruct x, y; reflexivity. Qed.
Lemma search_eq_model {v a} `{GHC.Base.Eq_ a} (x y : SearchResult v a) :
  GHC.Base.op_zeze__ x y = GHC.Base.op_zeze__ (searchEqModel x) (searchEqModel y).
Proof.
  destruct x, y; try reflexivity.
  change (andb (GHC.Base.op_zeze__ f f1)
      (andb (GHC.Base.op_zeze__ a0 a1) (GHC.Base.op_zeze__ f0 f2)) =
    andb (GHC.Base.op_zeze__ (contents f) (contents f1))
      (andb (GHC.Base.op_zeze__ a0 a1) (GHC.Base.op_zeze__ (contents f0) (contents f2)))).
  rewrite !eq_contents; reflexivity.
Qed.

Lemma tree_neq_default {v a} `{GHC.Base.Eq_ a} (x y : FingerTree v a) :
  GHC.Base.op_zsze__ x y = negb (GHC.Base.op_zeze__ x y).
Proof. reflexivity. Qed.
Lemma viewL_neq_default {s a} `{GHC.Base.Eq_ a} `{GHC.Base.Eq_ (s a)} (x y : ViewL s a) :
  GHC.Base.op_zsze__ x y = negb (GHC.Base.op_zeze__ x y).
Proof. reflexivity. Qed.
Lemma viewR_neq_default {s a} `{GHC.Base.Eq_ a} `{GHC.Base.Eq_ (s a)} (x y : ViewR s a) :
  GHC.Base.op_zsze__ x y = negb (GHC.Base.op_zeze__ x y).
Proof. reflexivity. Qed.
Lemma search_neq_default {v a} `{GHC.Base.Eq_ a} (x y : SearchResult v a) :
  GHC.Base.op_zsze__ x y = negb (GHC.Base.op_zeze__ x y).
Proof. reflexivity. Qed.

Lemma EqLaws_pullback {a b} `{GHC.Base.Eq_ a} `{EqLaws b} (f : a -> b) :
  (forall x y, GHC.Base.op_zeze__ x y = GHC.Base.op_zeze__ (f x) (f y)) ->
  (forall x y : a, GHC.Base.op_zsze__ x y = negb (GHC.Base.op_zeze__ x y)) -> EqLaws a.
Proof.
  intros E N; constructor.
  - intro x; rewrite E; apply Eq_refl.
  - intros x y; rewrite !E; apply Eq_sym.
  - intros x y z Ex Ey; rewrite E in Ex, Ey; rewrite E; eapply Eq_trans; eassumption.
  - intros x y; change (GHC.Base.op_zeze__ x y = negb (GHC.Base.op_zsze__ x y)).
    rewrite N, Bool.negb_involutive; reflexivity.
Qed.

Lemma tree_EqLaws {v a} `{EqLaws a} : EqLaws (FingerTree v a).
Proof. apply (EqLaws_pullback (@contents v a)); [apply eq_contents|apply tree_neq_default]. Qed.
Lemma viewL_EqLaws {s a} `{EqLaws a} `{EqLaws (s a)} : EqLaws (ViewL s a).
Proof. apply (EqLaws_pullback (@viewLModel s a)); [apply viewL_eq_model|apply viewL_neq_default]. Qed.
Lemma viewR_EqLaws {s a} `{EqLaws a} `{EqLaws (s a)} : EqLaws (ViewR s a).
Proof. apply (EqLaws_pullback (@viewRModel s a)); [apply viewR_eq_model|apply viewR_neq_default]. Qed.
Lemma search_EqLaws {v a} `{EqLaws a} : EqLaws (SearchResult v a).
Proof. apply (EqLaws_pullback (@searchEqModel v a)); [apply search_eq_model|apply search_neq_default]. Qed.

Section TreeAlgebra.
Context {v a} `{Measured v a}.
Definition contentsEquiv (l r : FingerTree v a) : Prop := contents l = contents r.

Lemma semigroup_contents (l r : FingerTree v a) :
  contents (GHC.Base.op_zlzlzgzg__ l r) = contents l ++ contents r.
Proof. apply append_contents. Qed.
Lemma mappend_contents (l r : FingerTree v a) :
  contents (GHC.Base.mappend l r) = contents l ++ contents r.
Proof. apply append_contents. Qed.
Lemma mempty_contents : contents (@GHC.Base.mempty (FingerTree v a) _ _) = [].
Proof. reflexivity. Qed.
Lemma mconcat_contents (ts : list (FingerTree v a)) :
  contents (GHC.Base.mconcat ts) = List.concat (List.map contents ts).
Proof.
  induction ts as [|t ts IH]; [reflexivity|].
  change (contents (GHC.Base.mappend t (GHC.Base.mconcat ts)) = contents t ++ List.concat (List.map contents ts)).
  rewrite mappend_contents, IH; reflexivity.
Qed.
Lemma contentsEquiv_equivalence : Equivalence contentsEquiv.
Proof. unfold contentsEquiv; constructor; congruence. Qed.
Lemma append_congruent l l' r r' : contentsEquiv l l' -> contentsEquiv r r' ->
  contentsEquiv (GHC.Base.mappend l r) (GHC.Base.mappend l' r').
Proof. unfold contentsEquiv; rewrite !mappend_contents; congruence. Qed.
Lemma append_associative x y z : contentsEquiv
  (GHC.Base.mappend (GHC.Base.mappend x y) z) (GHC.Base.mappend x (GHC.Base.mappend y z)).
Proof. unfold contentsEquiv; rewrite !mappend_contents, List.app_assoc; reflexivity. Qed.
Lemma append_identities x : contentsEquiv (GHC.Base.mappend GHC.Base.mempty x) x /\
  contentsEquiv (GHC.Base.mappend x GHC.Base.mempty) x.
Proof. unfold contentsEquiv; rewrite !mappend_contents, mempty_contents, List.app_nil_r; split; reflexivity. Qed.

Context `{EqLaws a}.
#[local] Existing Instance tree_EqLaws.
Lemma tree_SemigroupLaws : SemigroupLaws (FingerTree v a).
Proof.
  constructor; intros; rewrite eq_contents, !semigroup_contents, List.app_assoc; apply Eq_refl.
Qed.
#[local] Existing Instance tree_SemigroupLaws.
Lemma tree_MonoidLaws : MonoidLaws (FingerTree v a).
Proof.
  constructor.
  - intro x; rewrite eq_contents, mappend_contents, mempty_contents.
    exact (@Eq_refl (list a) _ _ (contents x)).
  - intro x; rewrite eq_contents, mappend_contents, mempty_contents, List.app_nil_r; apply Eq_refl.
  - intros; apply Eq_refl.
  - intros; apply Eq_refl.
Qed.
End TreeAlgebra.

Lemma viewL_fmap_behavior {s} `{GHC.Base.Functor s} {a b} (f : a -> b) (x : ViewL s a) :
  GHC.Base.fmap f x = match x with EmptyL => EmptyL | op_ZCzl__ y ys => op_ZCzl__ (f y) (GHC.Base.fmap f ys) end.
Proof. destruct x; reflexivity. Qed.
Lemma viewR_fmap_behavior {s} `{GHC.Base.Functor s} {a b} (f : a -> b) (x : ViewR s a) :
  GHC.Base.fmap f x = match x with EmptyR => EmptyR | op_ZCzg__ ys y => op_ZCzg__ (GHC.Base.fmap f ys) (f y) end.
Proof. destruct x; reflexivity. Qed.
Lemma viewL_replace_default {s} `{GHC.Base.Functor s} {a b} (y : b) (x : ViewL s a) :
  GHC.Base.op_zlzd__ y x = GHC.Base.fmap (fun _ => y) x.
Proof. reflexivity. Qed.
Lemma viewR_replace_default {s} `{GHC.Base.Functor s} {a b} (y : b) (x : ViewR s a) :
  GHC.Base.op_zlzd__ y x = GHC.Base.fmap (fun _ => y) x.
Proof. reflexivity. Qed.
Lemma viewL_FunctorLaws {s} `{FunctorLaws s} : FunctorLaws (ViewL s).
Proof.
  constructor.
  - intros a x; destruct x as [|y ys]; [reflexivity|].
    change (op_ZCzl__ y (GHC.Base.fmap GHC.Base.id ys) = op_ZCzl__ y ys).
    rewrite functor_identity; reflexivity.
  - intros a b c f g x; destruct x as [|y ys]; [reflexivity|].
    change (op_ZCzl__ (g (f y)) (GHC.Base.fmap g (GHC.Base.fmap f ys)) =
      op_ZCzl__ (g (f y)) (GHC.Base.fmap (GHC.Base.op_z2218U__ g f) ys)).
    rewrite functor_composition; reflexivity.
Qed.
Lemma viewR_FunctorLaws {s} `{FunctorLaws s} : FunctorLaws (ViewR s).
Proof.
  constructor.
  - intros a x; destruct x as [|ys y]; [reflexivity|].
    change (op_ZCzg__ (GHC.Base.fmap GHC.Base.id ys) y = op_ZCzg__ ys y).
    rewrite functor_identity; reflexivity.
  - intros a b c f g x; destruct x as [|ys y]; [reflexivity|].
    change (op_ZCzg__ (GHC.Base.fmap g (GHC.Base.fmap f ys)) (g (f y)) =
      op_ZCzg__ (GHC.Base.fmap (GHC.Base.op_z2218U__ g f) ys) (g (f y))).
    rewrite functor_composition; reflexivity.
Qed.

Lemma node_foldable_behavior {v} :
  FoldableBehavior (Node v) Foldable__Node (fun a => @nodeContents v a).
Proof.
  unfold FoldableBehavior; repeat apply conj.
  - intros m S N A L R a f t; destruct t;
      cbn [nodeContents nodeContentsWith List.app listMeasure List.fold_right
        Data.Foldable.foldMap Foldable__Node Data.Foldable.foldMap__ Data.FingerTree.Foldable__Node_foldMap];
      rewrite R; repeat rewrite A; reflexivity.
  - intros m S N A L R t; destruct t;
      cbn [nodeContents nodeContentsWith List.app listMeasure List.fold_right
        Data.Foldable.fold Foldable__Node Data.Foldable.fold__ Data.FingerTree.Foldable__Node_fold
        Data.FingerTree.Foldable__Node_foldMap GHC.Base.id];
      rewrite R; repeat rewrite A; reflexivity.
  - intros; destruct t; reflexivity.
  - intros; destruct t; reflexivity.
  - intros; destruct t; reflexivity.
  - intros; destruct t; reflexivity.
  - intros; destruct t; reflexivity.
  - intros; destruct t; reflexivity.
  - intros; destruct t; reflexivity.
  - intros; destruct t; reflexivity.
  - intros; destruct t; reflexivity.
  - intros; destruct t; reflexivity.
Qed.

Lemma count_fold {a} (xs : list a) z :
  List.fold_left (fun n _ => Z.add n 1) xs z = Z.add z (Z.of_nat (Datatypes.length xs)).
Proof.
  revert z; induction xs; intro z; [cbn; lia|].
  change (List.fold_left (fun n (_ : a) => Z.add n 1) xs (Z.add z 1) =
    Z.add z (Z.of_nat (S (Datatypes.length xs)))).
  rewrite IHxs, Nat2Z.inj_succ; lia.
Qed.

Lemma product_fold {a} `{GHC.Num.Num a} (xs : list a) z :
  Data.SemigroupInternal.getProduct
    (List.fold_left (fun acc x => GHC.Base.op_zlzlzgzg__ acc (Data.SemigroupInternal.Mk_Product x)) xs
      (Data.SemigroupInternal.Mk_Product z)) = List.fold_left GHC.Num.op_zt__ xs z.
Proof. revert z; induction xs; cbn; intros; [reflexivity|apply IHxs]. Qed.

Lemma sum_fold {a} `{GHC.Num.Num a} (xs : list a) z :
  Data.SemigroupInternal.getSum
    (List.fold_left (fun acc x => GHC.Base.op_zlzlzgzg__ acc (Data.SemigroupInternal.Mk_Sum x)) xs
      (Data.SemigroupInternal.Mk_Sum z)) = List.fold_left GHC.Num.op_zp__ xs z.
Proof. revert z; induction xs; cbn; intros; [reflexivity|apply IHxs]. Qed.

Lemma tree_foldable_behavior {v} :
  FoldableBehavior (FingerTree v) Foldable__FingerTree (fun a => @contents v a).
Proof.
  unfold FoldableBehavior; repeat apply conj.
  - intros; apply foldMap_contents; assumption.
  - intros m S N A L R t; change (Data.Foldable.foldMap (fun x => x) t = listMeasure (fun x => x) (contents t)).
    apply foldMap_contents; assumption.
  - intros m a S N f t.
    change (Data.Foldable.foldl' (fun acc x => GHC.Base.op_zlzlzgzg__ acc (f x)) GHC.Base.mempty t =
      List.fold_left (fun acc x => GHC.Base.op_zlzlzgzg__ acc (f x)) (contents t) GHC.Base.mempty).
    apply foldl'_contents.
  - intros; apply foldr_contents.
  - intros; apply foldl_contents.
  - intros; apply foldl'_contents.
  - intros; apply foldr'_contents.
  - intros a t; destruct t as [|x|c pr m sf]; [reflexivity|reflexivity|].
    destruct pr; reflexivity.
  - intros a t.
    change (Data.Foldable.foldl' (fun n _ => Z.add n 1) 0%Z t = Z.of_nat (Datatypes.length (contents t))).
    rewrite foldl'_contents, count_fold; reflexivity.
  - intros a N t.
    change (Data.SemigroupInternal.getProduct
      (Data.Foldable.foldl' (fun acc x => GHC.Base.op_zlzlzgzg__ acc (Data.SemigroupInternal.Mk_Product x))
        GHC.Base.mempty t) = List.fold_left GHC.Num.op_zt__ (contents t) (GHC.Num.fromInteger 1%Z)).
    rewrite foldl'_contents; apply product_fold.
  - intros a N t.
    change (Data.SemigroupInternal.getSum
      (Data.Foldable.foldl' (fun acc x => GHC.Base.op_zlzlzgzg__ acc (Data.SemigroupInternal.Mk_Sum x))
        GHC.Base.mempty t) = List.fold_left GHC.Num.op_zp__ (contents t) (GHC.Num.fromInteger 0%Z)).
    rewrite foldl'_contents; apply sum_fold.
  - intros; apply toList_contents.
Qed.

Section Measurement.
Context {v} `{GHC.Base.Monoid v}.
Hypothesis A : forall x y z : v, GHC.Base.mappend (GHC.Base.mappend x y) z = GHC.Base.mappend x (GHC.Base.mappend y z).
Hypothesis L : forall x : v, GHC.Base.mappend GHC.Base.mempty x = x.
Hypothesis R : forall x : v, GHC.Base.mappend x GHC.Base.mempty = x.

Lemma digit_measured_behavior {a} (M : Measured v a) d :
  measure d = listMeasure (@measure v a _ _ M) (digitContents d).
Proof. rewrite measure_digit_model; apply digitMeasure_contents; assumption. Qed.
Lemma node_measured_behavior {a} (M : Measured v a) P n :
  nodeValidity (@measure v a _ _ M) P n ->
  @measure v (Node v a) _ _ Measured__Node__5 n = listMeasure (@measure v a _ _ M) (nodeContents n).
Proof.
  intro V; change (nodeCache n = listMeasure (@measure v a _ _ M) (nodeContents n)).
  eapply valid_node_measure; [exact A|exact L| |exact V].
  intros; symmetry; cbn [listMeasure List.fold_right]; apply R.
Qed.
Lemma tree_measured_behavior {a} (M : Measured v a) t :
  validity M t -> measure t = listMeasure (@measure v a _ _ M) (contents t).
Proof. apply measure_contents; assumption. Qed.

Lemma fold_left_measure {a} (f : a -> v) xs z :
  List.fold_left (fun acc x => GHC.Base.mappend acc (f x)) xs z = GHC.Base.mappend z (listMeasure f xs).
Proof.
  revert z; induction xs; intro z; [cbn [List.fold_left listMeasure List.fold_right]; symmetry; apply R|].
  cbn [List.fold_left]; rewrite IHxs; change (GHC.Base.mappend (GHC.Base.mappend z (f a0)) (listMeasure f xs) =
    GHC.Base.mappend z (GHC.Base.mappend (f a0) (listMeasure f xs))); apply A.
Qed.

Lemma foldMap_strict_coherence (F : Type -> Type) (FL : Data.Foldable.Foldable F)
  C (B : FoldableBehavior F FL C) {a} (f : a -> v) t :
  (forall x y : v, GHC.Base.op_zlzlzgzg__ x y = GHC.Base.mappend x y) ->
  @Data.Foldable.foldMap' F FL v a _ _ f t = @Data.Foldable.foldMap F FL v a _ _ f t.
Proof.
  intro E; destruct B as [FM [_ [FSM _]]].
  rewrite FSM, (FM v _ _ A L R a f t).
  transitivity (List.fold_left (fun acc x => GHC.Base.mappend acc (f x)) (C a t) GHC.Base.mempty).
  - generalize (@GHC.Base.mempty v _ _); induction (C a t); cbn; intro z;
      [reflexivity|rewrite E; apply IHl].
  - rewrite fold_left_measure, L; reflexivity.
Qed.
End Measurement.

(* Comparator laws are stated over comparison ties, not propositional equality.
   They admit lawful nontrivial Boolean equivalences. No EqExact is required. *)
Definition compareOpp (c : comparison) := match c with Eq => Eq | Lt => Gt | Gt => Lt end.
Definition isLT (c : comparison) := match c with Lt => true | _ => false end.
Definition isLE (c : comparison) := match c with Gt => false | _ => true end.
Definition isEQ (c : comparison) := match c with Eq => true | _ => false end.
Definition lexCompare (c d : comparison) := match c with Eq => d | Lt => Lt | Gt => Gt end.

Definition ComparisonLaws {a} (cmp : a -> a -> comparison) : Prop :=
  (forall x, cmp x x = Eq) /\
  (forall x y, cmp y x = compareOpp (cmp x y)) /\
  (forall x y z, cmp x y = Lt -> cmp y z = Lt -> cmp x z = Lt) /\
  (forall x x' y y', cmp x x' = Eq -> cmp y y' = Eq -> cmp x y = cmp x' y').

Definition EqCompare {a} (eqb : a -> a -> bool) (cmp : a -> a -> comparison) : Prop :=
  forall x y, eqb x y = isEQ (cmp x y).

Lemma compare_eq_left {a} cmp (C : @ComparisonLaws a cmp) x y z :
  cmp x y = Eq -> cmp x z = cmp y z.
Proof. destruct C as [R [_ [_ E]]]; intro H; apply E; [exact H|apply R]. Qed.
Lemma compare_eq_right {a} cmp (C : @ComparisonLaws a cmp) x y z :
  cmp y z = Eq -> cmp x y = cmp x z.
Proof. destruct C as [R [_ [_ E]]]; intro H; apply E; [apply R|exact H]. Qed.
Lemma lex_eq_inv c d : lexCompare c d = Eq -> c = Eq /\ d = Eq.
Proof. destruct c, d; cbn; intuition discriminate. Qed.
Lemma lex_swap c d : lexCompare (compareOpp c) (compareOpp d) = compareOpp (lexCompare c d).
Proof. destruct c; reflexivity. Qed.

Lemma lex_trans_at {a b} ca cb (C : @ComparisonLaws a ca) x y z (u w k : b) :
  (cb u w = Lt -> cb w k = Lt -> cb u k = Lt) ->
  lexCompare (ca x y) (cb u w) = Lt -> lexCompare (ca y z) (cb w k) = Lt ->
  lexCompare (ca x z) (cb u k) = Lt.
Proof.
  intros T E1 E2; destruct (ca x y) eqn:Exy, (ca y z) eqn:Eyz;
    cbn [lexCompare] in E1, E2; try discriminate.
  - rewrite (compare_eq_left ca C x y z Exy), Eyz; cbn [lexCompare]; apply T; assumption.
  - rewrite (compare_eq_left ca C x y z Exy), Eyz; reflexivity.
  - rewrite <- (compare_eq_right ca C x y z Eyz), Exy; reflexivity.
  - destruct C as [_ [_ [CT _]]]; rewrite (CT x y z Exy Eyz); reflexivity.
Qed.

Definition pairCompare {a b} (ca : a -> a -> comparison) (cb : b -> b -> comparison)
  (x y : a * b) := lexCompare (ca (fst x) (fst y)) (cb (snd x) (snd y)).

Lemma pairComparisonLaws {a b} ca cb :
  @ComparisonLaws a ca -> @ComparisonLaws b cb -> ComparisonLaws (pairCompare ca cb).
Proof.
  intros CA CB; destruct CA as [RA [SA [TA EA]]], CB as [RB [SB [TB EB]]].
  repeat apply conj.
  - intros [x u]; unfold pairCompare; cbn; rewrite RA, RB; reflexivity.
  - intros [x u] [y w]; unfold pairCompare; cbn; rewrite SA, SB; apply lex_swap.
  - intros [x u] [y w] [z k]; apply lex_trans_at; [repeat split; assumption|apply TB].
  - intros [x u] [x' u'] [y w] [y' w']; unfold pairCompare; cbn; intros Ex Ey.
    apply lex_eq_inv in Ex, Ey; destruct Ex as [Ex Eu], Ey as [Ey Ew].
    rewrite (EA x x' y y' Ex Ey), (EB u u' w w' Eu Ew); reflexivity.
Qed.

Definition optionCompare {a} (c : a -> a -> comparison) (x y : option a) :=
  match x, y with None, None => Eq | None, Some _ => Lt | Some _, None => Gt | Some x, Some y => c x y end.

Lemma optionComparisonLaws {a} c : @ComparisonLaws a c -> ComparisonLaws (optionCompare c).
Proof.
  intro C; destruct C as [R [S [T E]]]; repeat apply conj.
  - intros [x|]; cbn [optionCompare]; auto.
  - intros [x|] [y|]; cbn [optionCompare compareOpp]; auto.
  - intros [x|] [y|] [z|]; cbn [optionCompare]; intros; try discriminate; auto; eapply T; eassumption.
  - intros [x|] [x'|] [y|] [y'|]; cbn [optionCompare]; intros; try discriminate; auto; eapply E; eassumption.
Qed.

Fixpoint listCompare {a} (c : a -> a -> comparison) (xs ys : list a) :=
  match xs, ys with
  | [], [] => Eq | [], _ :: _ => Lt | _ :: _, [] => Gt
  | x :: xs, y :: ys => lexCompare (c x y) (listCompare c xs ys)
  end.

Lemma listCompare_refl {a} c : @ComparisonLaws a c -> forall xs, listCompare c xs xs = Eq.
Proof. intros [R _] xs; induction xs; cbn [listCompare]; [reflexivity|rewrite R, IHxs; reflexivity]. Qed.
Lemma listCompare_transport {a} c : @ComparisonLaws a c ->
  forall xs xs' ys ys', listCompare c xs xs' = Eq -> listCompare c ys ys' = Eq ->
  listCompare c xs ys = listCompare c xs' ys'.
Proof.
  intros [_ [_ [_ E]]] xs; induction xs as [|x xs IH];
    intros [|x' xs'] [|y ys] [|y' ys']; cbn [listCompare]; intros Ex Ey;
    try discriminate; try reflexivity.
  apply lex_eq_inv in Ex, Ey; destruct Ex as [Ex Et], Ey as [Ey Eu].
  rewrite (E x x' y y' Ex Ey), (IH xs' ys ys' Et Eu); reflexivity.
Qed.

Lemma listComparisonLaws {a} c : @ComparisonLaws a c -> ComparisonLaws (listCompare c).
Proof.
  intro C; repeat apply conj.
  - apply listCompare_refl; exact C.
  - induction x as [|x xs IH]; intro y; destruct y as [|y ys]; cbn [listCompare compareOpp]; try reflexivity.
    destruct C as [_ [S _]]; rewrite S, IH; apply lex_swap.
  - induction x as [|x xs IH]; intros y z; destruct y as [|y ys], z as [|z zs];
      cbn [listCompare]; intros E1 E2; try discriminate; try reflexivity.
    eapply lex_trans_at; [exact C|apply IH|exact E1|exact E2].
  - apply listCompare_transport; exact C.
Qed.

Lemma pairEqCompare {a b} `{GHC.Base.Eq_ a} `{GHC.Base.Eq_ b} ca cb :
  EqCompare (@GHC.Base.op_zeze__ a _) ca -> EqCompare (@GHC.Base.op_zeze__ b _) cb ->
  EqCompare (@GHC.Base.op_zeze__ (a * b) _) (pairCompare ca cb).
Proof.
  intros EA EB [x u] [y w]; change (andb (GHC.Base.op_zeze__ x y) (GHC.Base.op_zeze__ u w) =
    isEQ (lexCompare (ca x y) (cb u w))).
  rewrite EA, EB; destruct (ca x y), (cb u w); reflexivity.
Qed.

Definition optionCompareLast {a} (c : a -> a -> comparison) (x y : option a) :=
  match x, y with None, None => Eq | None, Some _ => Gt | Some _, None => Lt | Some x, Some y => c x y end.

Lemma optionLastComparisonLaws {a} c : @ComparisonLaws a c -> ComparisonLaws (optionCompareLast c).
Proof.
  intros [R [S [T E]]]; repeat apply conj.
  - intros [x|]; cbn [optionCompareLast]; auto.
  - intros [x|] [y|]; cbn [optionCompareLast compareOpp]; auto.
  - intros [x|] [y|] [z|]; cbn [optionCompareLast]; intros; try discriminate; auto; eapply T; eassumption.
  - intros [x|] [x'|] [y|] [y'|]; cbn [optionCompareLast]; intros; try discriminate; auto; eapply E; eassumption.
Qed.

Lemma optionEqCompare {a} `{GHC.Base.Eq_ a} c : EqCompare (@GHC.Base.op_zeze__ a _) c ->
  EqCompare (@GHC.Base.op_zeze__ (option a) _) (optionCompare c).
Proof. intros E [x|] [y|]; cbn [optionCompare]; try reflexivity; apply E. Qed.
Lemma optionLastEqCompare {a} `{GHC.Base.Eq_ a} c : EqCompare (@GHC.Base.op_zeze__ a _) c ->
  EqCompare (@GHC.Base.op_zeze__ (option a) _) (optionCompareLast c).
Proof. intros E [x|] [y|]; cbn [optionCompareLast]; try reflexivity; apply E. Qed.
Lemma listEqCompare {a} `{GHC.Base.Eq_ a} c : EqCompare (@GHC.Base.op_zeze__ a _) c ->
  EqCompare (@GHC.Base.op_zeze__ (list a) _) (listCompare c).
Proof.
  intros E xs; induction xs as [|x xs IH]; intros [|y ys]; try reflexivity.
  change (andb (GHC.Base.op_zeze__ x y) (GHC.Base.op_zeze__ xs ys) =
    isEQ (lexCompare (c x y) (listCompare c xs ys))).
  rewrite E, IH; destruct (c x y), (listCompare c xs ys); reflexivity.
Qed.

Lemma comparison_pullback {a b} ca cb (f : a -> b) :
  (forall x y, ca x y = cb (f x) (f y)) -> ComparisonLaws cb -> ComparisonLaws ca.
Proof.
  intros E [R [S [T Q]]]; repeat apply conj.
  - intro x; rewrite E; apply R.
  - intros x y; rewrite !E; apply S.
  - intros x y z Ex Ey; rewrite E in Ex, Ey; rewrite E; eapply T; eassumption.
  - intros x x' y y' Ex Ey; rewrite E in Ex, Ey; rewrite !E; apply Q; assumption.
Qed.

Lemma source_list_compare {a} `{GHC.Base.Ord a} (xs ys : list a) :
  GHC.Base.compare xs ys = listCompare (@GHC.Base.compare a _ _) xs ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys]; try reflexivity.
  change (match GHC.Base.compare x y with Eq => GHC.Base.compare xs ys | Lt => Lt | Gt => Gt end =
    lexCompare (GHC.Base.compare x y) (listCompare (@GHC.Base.compare a _ _) xs ys)).
  rewrite IH; destruct (GHC.Base.compare x y); reflexivity.
Qed.

Lemma viewL_compare_model {s a} `{GHC.Base.Ord a} `{GHC.Base.Ord (s a)} (x y : ViewL s a) :
  GHC.Base.compare x y = optionCompare (pairCompare (@GHC.Base.compare a _ _) (@GHC.Base.compare (s a) _ _))
    (viewLModel x) (viewLModel y).
Proof. destruct x, y; reflexivity. Qed.
Lemma viewR_compare_model {s a} `{GHC.Base.Ord a} `{GHC.Base.Ord (s a)} (x y : ViewR s a) :
  GHC.Base.compare x y = optionCompare (pairCompare (@GHC.Base.compare (s a) _ _) (@GHC.Base.compare a _ _))
    (viewRModel x) (viewRModel y).
Proof. destruct x, y; reflexivity. Qed.
Lemma search_compare_model {v a} `{GHC.Base.Ord a} (x y : SearchResult v a) :
  GHC.Base.compare x y = optionCompareLast (optionCompareLast (optionCompareLast
    (pairCompare (listCompare (@GHC.Base.compare a _ _))
      (pairCompare (@GHC.Base.compare a _ _) (listCompare (@GHC.Base.compare a _ _))))))
    (searchEqModel x) (searchEqModel y).
Proof.
  destruct x, y; try reflexivity.
  change (lexCompare (GHC.Base.compare f f1) (lexCompare (GHC.Base.compare a0 a1) (GHC.Base.compare f0 f2)) =
    lexCompare (listCompare (@GHC.Base.compare a _ _) (contents f) (contents f1))
      (lexCompare (GHC.Base.compare a0 a1) (listCompare (@GHC.Base.compare a _ _) (contents f0) (contents f2)))).
  rewrite !compare_contents, !source_list_compare; reflexivity.
Qed.

Definition OrdMethods (a : Type) `{GHC.Base.Ord a} : Prop :=
  (forall x y : a, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)) /\
  (forall x y : a, GHC.Base.op_zlze__ x y = isLE (GHC.Base.compare x y)) /\
  (forall x y : a, GHC.Base.op_zg__ x y = isLT (compareOpp (GHC.Base.compare x y))) /\
  (forall x y : a, GHC.Base.op_zgze__ x y = isLE (compareOpp (GHC.Base.compare x y))) /\
  (forall x y : a, GHC.Base.min x y = if isLE (GHC.Base.compare x y) then x else y) /\
  (forall x y : a, GHC.Base.max x y = if isLE (GHC.Base.compare x y) then y else x).

Definition OrdBehavior (a : Type) `{GHC.Base.Ord a} : Prop :=
  ComparisonLaws (@GHC.Base.compare a _ _) /\
  EqCompare (@GHC.Base.op_zeze__ a _) (@GHC.Base.compare a _ _) /\ OrdMethods a.

Ltac direct_ord_methods :=
  unfold OrdMethods; repeat apply conj; intros x y;
  match goal with |- _ = ?rhs =>
    first [change (GHC.Base.op_zeze__ (GHC.Base.compare x y) Lt = rhs)
          |change (GHC.Base.op_zsze__ (GHC.Base.compare x y) Gt = rhs)
          |change (GHC.Base.op_zeze__ (GHC.Base.compare x y) Gt = rhs)
          |change (GHC.Base.op_zsze__ (GHC.Base.compare x y) Lt = rhs)
          |change ((if GHC.Base.op_zsze__ (GHC.Base.compare x y) Gt then x else y) = rhs)
          |change ((if GHC.Base.op_zsze__ (GHC.Base.compare x y) Gt then y else x) = rhs)]
  end; destruct (GHC.Base.compare x y); reflexivity.

Lemma tree_ord_methods {v a} `{GHC.Base.Ord a} : OrdMethods (FingerTree v a).
Proof. direct_ord_methods. Qed.
Lemma search_ord_methods {v a} `{GHC.Base.Ord a} : OrdMethods (SearchResult v a).
Proof. direct_ord_methods. Qed.

Lemma tree_ord_behavior {v a} `{GHC.Base.Ord a} :
  ComparisonLaws (@GHC.Base.compare a _ _) -> EqCompare (@GHC.Base.op_zeze__ a _) (@GHC.Base.compare a _ _) ->
  OrdBehavior (FingerTree v a).
Proof.
  intros C E; split.
  - eapply (comparison_pullback _ _ (@contents v a)).
    + intros; rewrite compare_contents, source_list_compare; reflexivity.
    + apply listComparisonLaws; exact C.
  - split; [|apply tree_ord_methods].
    intros x y; rewrite eq_contents, compare_contents, source_list_compare; apply listEqCompare; exact E.
Qed.

Lemma search_ord_behavior {v a} `{GHC.Base.Ord a} :
  ComparisonLaws (@GHC.Base.compare a _ _) -> EqCompare (@GHC.Base.op_zeze__ a _) (@GHC.Base.compare a _ _) ->
  OrdBehavior (SearchResult v a).
Proof.
  intros C E; split.
  - eapply (comparison_pullback _ _ (@searchEqModel v a)); [apply search_compare_model|].
    repeat apply optionLastComparisonLaws; apply pairComparisonLaws.
    + apply listComparisonLaws; exact C.
    + apply pairComparisonLaws; [exact C|apply listComparisonLaws; exact C].
  - split; [|apply search_ord_methods].
    intros x y; rewrite search_eq_model, search_compare_model.
    repeat apply optionLastEqCompare; apply pairEqCompare.
    + apply listEqCompare; exact E.
    + apply pairEqCompare; [exact E|apply listEqCompare; exact E].
Qed.

Lemma viewL_lt_compare {s a} `{GHC.Base.Ord a} `{GHC.Base.Ord (s a)} :
  (forall x y : s a, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)) ->
  forall x y : ViewL s a, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y).
Proof.
  intros E [|x xs] [|y ys]; try reflexivity.
  change (match GHC.Base.compare x y with Eq => GHC.Base.op_zl__ xs ys | Lt => true | Gt => false end =
    isLT (lexCompare (GHC.Base.compare x y) (GHC.Base.compare xs ys))).
  rewrite E; destruct (GHC.Base.compare x y); reflexivity.
Qed.
Lemma viewR_lt_compare {s a} `{GHC.Base.Ord a} `{GHC.Base.Ord (s a)} :
  (forall x y : a, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)) ->
  forall x y : ViewR s a, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y).
Proof.
  intros E [|xs x] [|ys y]; try reflexivity.
  change (match GHC.Base.compare xs ys with Eq => GHC.Base.op_zl__ x y | Lt => true | Gt => false end =
    isLT (lexCompare (GHC.Base.compare xs ys) (GHC.Base.compare x y))).
  rewrite E; destruct (GHC.Base.compare xs ys); reflexivity.
Qed.

Local Ltac view_ord_methods LT SW :=
  unfold OrdMethods; repeat apply conj; intros x y;
  first [apply LT | match goal with |- _ = ?rhs =>
    first [change (negb (GHC.Base.op_zl__ y x) = rhs)
          |change (GHC.Base.op_zl__ y x = rhs)
          |change (negb (GHC.Base.op_zl__ x y) = rhs)
          |change ((if negb (GHC.Base.op_zl__ y x) then x else y) = rhs)
          |change ((if negb (GHC.Base.op_zl__ y x) then y else x) = rhs)]
    end; rewrite !LT; rewrite ?(SW x y); destruct (GHC.Base.compare x y); reflexivity].

Lemma viewL_ord_methods {s a} `{GHC.Base.Ord a} `{GHC.Base.Ord (s a)} :
  ComparisonLaws (@GHC.Base.compare (ViewL s a) _ _) ->
  (forall x y : s a, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)) -> OrdMethods (ViewL s a).
Proof.
  intros [_ [SW _]] E; pose proof (viewL_lt_compare E) as LT; view_ord_methods LT SW.
Qed.
Lemma viewR_ord_methods {s a} `{GHC.Base.Ord a} `{GHC.Base.Ord (s a)} :
  ComparisonLaws (@GHC.Base.compare (ViewR s a) _ _) ->
  (forall x y : a, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)) -> OrdMethods (ViewR s a).
Proof.
  intros [_ [SW _]] E; pose proof (viewR_lt_compare E) as LT; view_ord_methods LT SW.
Qed.

Lemma viewL_ord_behavior {s a} `{GHC.Base.Ord a} `{GHC.Base.Ord (s a)} :
  ComparisonLaws (@GHC.Base.compare a _ _) -> ComparisonLaws (@GHC.Base.compare (s a) _ _) ->
  EqCompare (@GHC.Base.op_zeze__ a _) (@GHC.Base.compare a _ _) ->
  EqCompare (@GHC.Base.op_zeze__ (s a) _) (@GHC.Base.compare (s a) _ _) ->
  (forall x y : s a, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)) -> OrdBehavior (ViewL s a).
Proof.
  intros CA CS EA ES LT.
  assert (C : ComparisonLaws (@GHC.Base.compare (ViewL s a) _ _)).
  { eapply (comparison_pullback _ _ (@viewLModel s a)); [apply viewL_compare_model|].
    apply optionComparisonLaws; apply pairComparisonLaws; assumption. }
  split; [exact C|]; split.
  - intros x y; rewrite viewL_eq_model, viewL_compare_model.
    apply optionEqCompare; apply pairEqCompare; assumption.
  - apply viewL_ord_methods; assumption.
Qed.
Lemma viewR_ord_behavior {s a} `{GHC.Base.Ord a} `{GHC.Base.Ord (s a)} :
  ComparisonLaws (@GHC.Base.compare a _ _) -> ComparisonLaws (@GHC.Base.compare (s a) _ _) ->
  EqCompare (@GHC.Base.op_zeze__ a _) (@GHC.Base.compare a _ _) ->
  EqCompare (@GHC.Base.op_zeze__ (s a) _) (@GHC.Base.compare (s a) _ _) ->
  (forall x y : a, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)) -> OrdBehavior (ViewR s a).
Proof.
  intros CA CS EA ES LT.
  assert (C : ComparisonLaws (@GHC.Base.compare (ViewR s a) _ _)).
  { eapply (comparison_pullback _ _ (@viewRModel s a)); [apply viewR_compare_model|].
    apply optionComparisonLaws; apply pairComparisonLaws; assumption. }
  split; [exact C|]; split.
  - intros x y; rewrite viewR_eq_model, viewR_compare_model.
    apply optionEqCompare; apply pairEqCompare; assumption.
  - apply viewR_ord_methods; assumption.
Qed.

Lemma comparison_le_trans {a} c (C : @ComparisonLaws a c) x y z :
  isLE (c x y) = true -> isLE (c y z) = true -> isLE (c x z) = true.
Proof.
  intros E1 E2; destruct (c x y) eqn:Ex, (c y z) eqn:Ey; try discriminate.
  - rewrite (compare_eq_left c C x y z Ex), Ey; reflexivity.
  - rewrite (compare_eq_left c C x y z Ex), Ey; reflexivity.
  - rewrite <- (compare_eq_right c C x y z Ey), Ex; reflexivity.
  - destruct C as [_ [_ [T _]]]; rewrite (T x y z Ex Ey); reflexivity.
Qed.

Definition OrderLaws (a : Type) `{GHC.Base.Ord a} : Prop :=
  (forall x : a, GHC.Base.op_zlze__ x x = true) /\
  (forall x y z : a, GHC.Base.op_zlze__ x y = true -> GHC.Base.op_zlze__ y z = true -> GHC.Base.op_zlze__ x z = true) /\
  (forall x y : a, orb (GHC.Base.op_zlze__ x y) (GHC.Base.op_zlze__ y x) = true) /\
  (forall x y : a, (GHC.Base.op_zlze__ x y = true /\ GHC.Base.op_zlze__ y x = true) <-> GHC.Base.op_zeze__ x y = true) /\
  (forall x y z : a, GHC.Base.op_zl__ x y = true -> GHC.Base.op_zl__ y z = true -> GHC.Base.op_zl__ x z = true) /\
  (forall x y : a, GHC.Base.op_zl__ x y = andb (GHC.Base.op_zlze__ x y) (negb (GHC.Base.op_zeze__ x y))) /\
  (forall x y : a, GHC.Base.op_zlze__ (GHC.Base.min x y) x = true /\ GHC.Base.op_zlze__ (GHC.Base.min x y) y = true) /\
  (forall x y : a, GHC.Base.op_zlze__ x (GHC.Base.max x y) = true /\ GHC.Base.op_zlze__ y (GHC.Base.max x y) = true) /\
  (forall x y z : a, (GHC.Base.op_zlze__ z x = true /\ GHC.Base.op_zlze__ z y = true) <-> GHC.Base.op_zlze__ z (GHC.Base.min x y) = true) /\
  (forall x y z : a, (GHC.Base.op_zlze__ x z = true /\ GHC.Base.op_zlze__ y z = true) <-> GHC.Base.op_zlze__ (GHC.Base.max x y) z = true).

Lemma ord_behavior_laws {a} `{GHC.Base.Ord a} : OrdBehavior a -> OrderLaws a.
Proof.
  intros [C [E [LT [LE [GT [GE [MN MX]]]]]]].
  destruct C as [R [SW [T Q]]].
  assert (C : ComparisonLaws (@GHC.Base.compare a _ _)) by (repeat split; assumption).
  unfold OrderLaws; repeat apply conj.
  - intro x; rewrite LE, R; reflexivity.
  - intros x y z E1 E2; rewrite LE in E1, E2; rewrite LE; eapply comparison_le_trans; eassumption.
  - intros x y; rewrite !LE, (SW x y); destruct (GHC.Base.compare x y); reflexivity.
  - intros x y; rewrite !LE, E, (SW x y); destruct (GHC.Base.compare x y); cbn; intuition discriminate.
  - intros x y z E1 E2; rewrite LT in E1, E2; rewrite LT.
    destruct (GHC.Base.compare x y) eqn:Ex, (GHC.Base.compare y z) eqn:Ey; try discriminate.
    rewrite (T x y z Ex Ey); reflexivity.
  - intros x y; rewrite LT, LE, E; destruct (GHC.Base.compare x y); reflexivity.
  - intros x y; rewrite MN, !LE.
    destruct (GHC.Base.compare x y) eqn:Ex; cbn [isLE compareOpp]; rewrite ?R, ?(SW x y), ?Ex; split; reflexivity.
  - intros x y; rewrite MX, !LE.
    destruct (GHC.Base.compare x y) eqn:Ex; cbn [isLE compareOpp]; rewrite ?R, ?(SW x y), ?Ex; split; reflexivity.
  - intros x y z; rewrite MN, !LE.
    destruct (GHC.Base.compare x y) eqn:Ex; cbn [isLE].
    + rewrite (compare_eq_right _ C z x y Ex); tauto.
    + split; [tauto|intro Ez; split; [exact Ez|]].
      eapply comparison_le_trans; [exact C|exact Ez|rewrite Ex; reflexivity].
    + split; [tauto|intro Ez; split; [|exact Ez]].
      eapply comparison_le_trans; [exact C|exact Ez|rewrite (SW x y), Ex; reflexivity].
  - intros x y z; rewrite MX, !LE.
    destruct (GHC.Base.compare x y) eqn:Ex; cbn [isLE].
    + rewrite (compare_eq_left _ C x y z Ex); tauto.
    + split; [tauto|intro Ez; split; [|exact Ez]].
      eapply comparison_le_trans; [exact C|rewrite Ex; reflexivity|exact Ez].
    + split; [tauto|intro Ez; split; [exact Ez|]].
      eapply comparison_le_trans; [exact C|rewrite (SW x y), Ex; reflexivity|exact Ez].
Qed.

Lemma tree_OrderLaws {v a} `{GHC.Base.Ord a} :
  ComparisonLaws (@GHC.Base.compare a _ _) -> EqCompare (@GHC.Base.op_zeze__ a _) (@GHC.Base.compare a _ _) ->
  OrderLaws (FingerTree v a).
Proof. intros; apply ord_behavior_laws; apply tree_ord_behavior; assumption. Qed.
Lemma search_OrderLaws {v a} `{GHC.Base.Ord a} :
  ComparisonLaws (@GHC.Base.compare a _ _) -> EqCompare (@GHC.Base.op_zeze__ a _) (@GHC.Base.compare a _ _) ->
  OrderLaws (SearchResult v a).
Proof. intros; apply ord_behavior_laws; apply search_ord_behavior; assumption. Qed.
Lemma viewL_OrderLaws {s a} `{GHC.Base.Ord a} `{GHC.Base.Ord (s a)} :
  ComparisonLaws (@GHC.Base.compare a _ _) -> ComparisonLaws (@GHC.Base.compare (s a) _ _) ->
  EqCompare (@GHC.Base.op_zeze__ a _) (@GHC.Base.compare a _ _) ->
  EqCompare (@GHC.Base.op_zeze__ (s a) _) (@GHC.Base.compare (s a) _ _) ->
  (forall x y : s a, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)) -> OrderLaws (ViewL s a).
Proof. intros; apply ord_behavior_laws; apply viewL_ord_behavior; assumption. Qed.
Lemma viewR_OrderLaws {s a} `{GHC.Base.Ord a} `{GHC.Base.Ord (s a)} :
  ComparisonLaws (@GHC.Base.compare a _ _) -> ComparisonLaws (@GHC.Base.compare (s a) _ _) ->
  EqCompare (@GHC.Base.op_zeze__ a _) (@GHC.Base.compare a _ _) ->
  EqCompare (@GHC.Base.op_zeze__ (s a) _) (@GHC.Base.compare (s a) _ _) ->
  (forall x y : a, GHC.Base.op_zl__ x y = isLT (GHC.Base.compare x y)) -> OrderLaws (ViewR s a).
Proof. intros; apply ord_behavior_laws; apply viewR_ord_behavior; assumption. Qed.

Definition MinMaxLaws (a : Type) `{GHC.Base.Ord a} : Prop :=
  (forall x : a, GHC.Base.op_zeze__ (GHC.Base.min x x) x = true) /\
  (forall x : a, GHC.Base.op_zeze__ (GHC.Base.max x x) x = true) /\
  (forall x y : a, GHC.Base.op_zeze__ (GHC.Base.min x y) (GHC.Base.min y x) = true) /\
  (forall x y : a, GHC.Base.op_zeze__ (GHC.Base.max x y) (GHC.Base.max y x) = true) /\
  (forall x y z : a, GHC.Base.op_zeze__ (GHC.Base.min (GHC.Base.min x y) z) (GHC.Base.min x (GHC.Base.min y z)) = true) /\
  (forall x y z : a, GHC.Base.op_zeze__ (GHC.Base.max (GHC.Base.max x y) z) (GHC.Base.max x (GHC.Base.max y z)) = true) /\
  (forall x y : a, GHC.Base.op_zeze__ (GHC.Base.min x (GHC.Base.max x y)) x = true) /\
  (forall x y : a, GHC.Base.op_zeze__ (GHC.Base.max x (GHC.Base.min x y)) x = true).

Lemma order_minmax_laws {a} `{GHC.Base.Ord a} : OrderLaws a -> MinMaxLaws a.
Proof.
  intros [R [T [_ [AS [_ [_ [MB [XB [GLB LUB]]]]]]]]].
  pose (M1 := fun x y => proj1 (MB x y)); pose (M2 := fun x y => proj2 (MB x y)).
  pose (X1 := fun x y => proj1 (XB x y)); pose (X2 := fun x y => proj2 (XB x y)).
  unfold MinMaxLaws; repeat apply conj.
  - intro x; apply (proj1 (AS _ _)); split; [apply M1|apply GLB; split; apply R].
  - intro x; apply (proj1 (AS _ _)); split; [apply LUB; split; apply R|apply X1].
  - intros x y; apply (proj1 (AS _ _)); split; apply GLB; split; [apply M2|apply M1|apply M2|apply M1].
  - intros x y; apply (proj1 (AS _ _)); split; apply LUB; split; [apply X2|apply X1|apply X2|apply X1].
  - intros x y z; apply (proj1 (AS _ _)); split.
    + apply GLB; split.
      * exact (T _ _ _ (M1 (GHC.Base.min x y) z) (M1 x y)).
      * apply GLB; split; [exact (T _ _ _ (M1 (GHC.Base.min x y) z) (M2 x y))|apply M2].
    + apply GLB; split.
      * apply GLB; split; [apply M1|exact (T _ _ _ (M2 x (GHC.Base.min y z)) (M1 y z))].
      * exact (T _ _ _ (M2 x (GHC.Base.min y z)) (M2 y z)).
  - intros x y z; apply (proj1 (AS _ _)); split.
    + apply LUB; split.
      * apply LUB; split; [apply X1|exact (T _ _ _ (X1 y z) (X2 x (GHC.Base.max y z)))].
      * exact (T _ _ _ (X2 y z) (X2 x (GHC.Base.max y z))).
    + apply LUB; split.
      * exact (T _ _ _ (X1 x y) (X1 (GHC.Base.max x y) z)).
      * apply LUB; split; [exact (T _ _ _ (X2 x y) (X1 (GHC.Base.max x y) z))|apply X2].
  - intros x y; apply (proj1 (AS _ _)); split; [apply M1|apply GLB; split; [apply R|apply X1]].
  - intros x y; apply (proj1 (AS _ _)); split; [apply LUB; split; [apply R|apply M1]|apply X1].
Qed.

Lemma eqlist_append {a} `{GHC.Base.Eq_ a} : forall (xs xs' ys ys' : list a),
  GHC.Base.op_zeze__ xs xs' = true -> GHC.Base.op_zeze__ ys ys' = true ->
  GHC.Base.op_zeze__ (xs ++ ys) (xs' ++ ys') = true.
Proof.
  induction xs as [|x xs IH]; intros [|x' xs'] ys ys' Ex Ey;
    try (change (false = true) in Ex; discriminate); [exact Ey|].
  rewrite simpl_list_cons_eq in Ex; apply Bool.andb_true_iff in Ex; destruct Ex as [Ex Et].
  cbn [List.app]; rewrite simpl_list_cons_eq, Ex; cbn; apply IH; assumption.
Qed.

Lemma append_boolean_congruent {v a} `{Measured v a} `{GHC.Base.Eq_ a}
  (l l' r r' : FingerTree v a) :
  GHC.Base.op_zeze__ l l' = true -> GHC.Base.op_zeze__ r r' = true ->
  GHC.Base.op_zeze__ (GHC.Base.mappend l r) (GHC.Base.mappend l' r') = true.
Proof.
  intros El Er; rewrite eq_contents in El, Er; rewrite eq_contents, !mappend_contents.
  apply eqlist_append; assumption.
Qed.

Lemma mconcat_validity {v a} `{GHC.Base.Monoid v} (M : Measured v a)
  (A : forall x y z : v, GHC.Base.mappend (GHC.Base.mappend x y) z = GHC.Base.mappend x (GHC.Base.mappend y z))
  (L : forall x : v, GHC.Base.mappend GHC.Base.mempty x = x)
  (R : forall x : v, GHC.Base.mappend x GHC.Base.mempty = x) ts :
  List.Forall (validity M) ts -> validity M (GHC.Base.mconcat ts).
Proof.
  intro V; induction V as [|t ts Vt Vts IH]; [exact I|].
  change (validity M (op_zgzl__ t (GHC.Base.mconcat ts))).
  apply append_validity; assumption.
Qed.

Lemma foldable_null_length F FL C (B : FoldableBehavior F FL C) a (t : F a) :
  @Data.Foldable.null F FL a t = Z.eqb (@Data.Foldable.length F FL a t) 0.
Proof.
  destruct B as [_ [_ [_ [_ [_ [_ [_ [N [Len _]]]]]]]]].
  rewrite N, Len; destruct (C a t); [reflexivity|].
  symmetry; apply Z.eqb_neq; change (Z.of_nat (S (Datatypes.length l)) <> 0%Z); lia.
Qed.

(* Every exported constant has a typed interface and transitive audit. *)
Check @digitContents. Print Assumptions digitContents.
Check @nodeContents. Print Assumptions nodeContents.
Check @FoldableBehavior. Print Assumptions FoldableBehavior.
Check @digit_foldable_behavior. Print Assumptions digit_foldable_behavior.
Check @viewLModel. Print Assumptions viewLModel.
Check @viewRModel. Print Assumptions viewRModel.
Check @searchEqModel. Print Assumptions searchEqModel.
Check @viewL_eq_model. Print Assumptions viewL_eq_model.
Check @viewR_eq_model. Print Assumptions viewR_eq_model.
Check @search_eq_model. Print Assumptions search_eq_model.
Check @tree_neq_default. Print Assumptions tree_neq_default.
Check @viewL_neq_default. Print Assumptions viewL_neq_default.
Check @viewR_neq_default. Print Assumptions viewR_neq_default.
Check @search_neq_default. Print Assumptions search_neq_default.
Check @EqLaws_pullback. Print Assumptions EqLaws_pullback.
Check @tree_EqLaws. Print Assumptions tree_EqLaws.
Check @viewL_EqLaws. Print Assumptions viewL_EqLaws.
Check @viewR_EqLaws. Print Assumptions viewR_EqLaws.
Check @search_EqLaws. Print Assumptions search_EqLaws.
Check @contentsEquiv. Print Assumptions contentsEquiv.
Check @semigroup_contents. Print Assumptions semigroup_contents.
Check @mappend_contents. Print Assumptions mappend_contents.
Check @mempty_contents. Print Assumptions mempty_contents.
Check @mconcat_contents. Print Assumptions mconcat_contents.
Check @contentsEquiv_equivalence. Print Assumptions contentsEquiv_equivalence.
Check @append_congruent. Print Assumptions append_congruent.
Check @append_associative. Print Assumptions append_associative.
Check @append_identities. Print Assumptions append_identities.
Check @tree_SemigroupLaws. Print Assumptions tree_SemigroupLaws.
Check @tree_MonoidLaws. Print Assumptions tree_MonoidLaws.
Check @viewL_fmap_behavior. Print Assumptions viewL_fmap_behavior.
Check @viewR_fmap_behavior. Print Assumptions viewR_fmap_behavior.
Check @viewL_replace_default. Print Assumptions viewL_replace_default.
Check @viewR_replace_default. Print Assumptions viewR_replace_default.
Check @viewL_FunctorLaws. Print Assumptions viewL_FunctorLaws.
Check @viewR_FunctorLaws. Print Assumptions viewR_FunctorLaws.
Check @node_foldable_behavior. Print Assumptions node_foldable_behavior.
Check @count_fold. Print Assumptions count_fold.
Check @product_fold. Print Assumptions product_fold.
Check @sum_fold. Print Assumptions sum_fold.
Check @tree_foldable_behavior. Print Assumptions tree_foldable_behavior.
Check @digit_measured_behavior. Print Assumptions digit_measured_behavior.
Check @node_measured_behavior. Print Assumptions node_measured_behavior.
Check @tree_measured_behavior. Print Assumptions tree_measured_behavior.
Check @fold_left_measure. Print Assumptions fold_left_measure.
Check @foldMap_strict_coherence. Print Assumptions foldMap_strict_coherence.
Check @compareOpp. Print Assumptions compareOpp.
Check @isLT. Print Assumptions isLT.
Check @isLE. Print Assumptions isLE.
Check @isEQ. Print Assumptions isEQ.
Check @lexCompare. Print Assumptions lexCompare.
Check @ComparisonLaws. Print Assumptions ComparisonLaws.
Check @EqCompare. Print Assumptions EqCompare.
Check @compare_eq_left. Print Assumptions compare_eq_left.
Check @compare_eq_right. Print Assumptions compare_eq_right.
Check @lex_eq_inv. Print Assumptions lex_eq_inv.
Check @lex_swap. Print Assumptions lex_swap.
Check @lex_trans_at. Print Assumptions lex_trans_at.
Check @pairCompare. Print Assumptions pairCompare.
Check @pairComparisonLaws. Print Assumptions pairComparisonLaws.
Check @optionCompare. Print Assumptions optionCompare.
Check @optionComparisonLaws. Print Assumptions optionComparisonLaws.
Check @listCompare. Print Assumptions listCompare.
Check @listCompare_refl. Print Assumptions listCompare_refl.
Check @listCompare_transport. Print Assumptions listCompare_transport.
Check @listComparisonLaws. Print Assumptions listComparisonLaws.
Check @pairEqCompare. Print Assumptions pairEqCompare.
Check @optionCompareLast. Print Assumptions optionCompareLast.
Check @optionLastComparisonLaws. Print Assumptions optionLastComparisonLaws.
Check @optionEqCompare. Print Assumptions optionEqCompare.
Check @optionLastEqCompare. Print Assumptions optionLastEqCompare.
Check @listEqCompare. Print Assumptions listEqCompare.
Check @comparison_pullback. Print Assumptions comparison_pullback.
Check @source_list_compare. Print Assumptions source_list_compare.
Check @viewL_compare_model. Print Assumptions viewL_compare_model.
Check @viewR_compare_model. Print Assumptions viewR_compare_model.
Check @search_compare_model. Print Assumptions search_compare_model.
Check @OrdMethods. Print Assumptions OrdMethods.
Check @OrdBehavior. Print Assumptions OrdBehavior.
Check @tree_ord_methods. Print Assumptions tree_ord_methods.
Check @search_ord_methods. Print Assumptions search_ord_methods.
Check @tree_ord_behavior. Print Assumptions tree_ord_behavior.
Check @search_ord_behavior. Print Assumptions search_ord_behavior.
Check @viewL_lt_compare. Print Assumptions viewL_lt_compare.
Check @viewR_lt_compare. Print Assumptions viewR_lt_compare.
Check @viewL_ord_methods. Print Assumptions viewL_ord_methods.
Check @viewR_ord_methods. Print Assumptions viewR_ord_methods.
Check @viewL_ord_behavior. Print Assumptions viewL_ord_behavior.
Check @viewR_ord_behavior. Print Assumptions viewR_ord_behavior.
Check @comparison_le_trans. Print Assumptions comparison_le_trans.
Check @OrderLaws. Print Assumptions OrderLaws.
Check @ord_behavior_laws. Print Assumptions ord_behavior_laws.
Check @tree_OrderLaws. Print Assumptions tree_OrderLaws.
Check @search_OrderLaws. Print Assumptions search_OrderLaws.
Check @viewL_OrderLaws. Print Assumptions viewL_OrderLaws.
Check @viewR_OrderLaws. Print Assumptions viewR_OrderLaws.
Check @MinMaxLaws. Print Assumptions MinMaxLaws.
Check @order_minmax_laws. Print Assumptions order_minmax_laws.
Check @eqlist_append. Print Assumptions eqlist_append.
Check @append_boolean_congruent. Print Assumptions append_boolean_congruent.
Check @mconcat_validity. Print Assumptions mconcat_validity.
Check @foldable_null_length. Print Assumptions foldable_null_length.
