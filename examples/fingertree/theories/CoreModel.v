From Stdlib Require Import Lists.List.
Require Import Data.FingerTree.
Import ListNotations.

(* These interpretations inspect constructors, never source folds or caches. *)
Definition digitContentsWith {a b} (f : a -> list b) (d : Digit a) : list b :=
  match d with
  | One x => f x
  | Two x y => f x ++ f y
  | Three x y z => f x ++ f y ++ f z
  | Four x y z w => f x ++ f y ++ f z ++ f w
  end.
Definition nodeContentsWith {v a b} (f : a -> list b) (n : Node v a) : list b :=
  match n with
  | Node2 _ x y => f x ++ f y
  | Node3 _ x y z => f x ++ f y ++ f z
  end.
Fixpoint contentsWith {v a b} (f : a -> list b) (t : FingerTree v a) : list b :=
  match t with
  | Empty => []
  | Single x => f x
  | Deep _ pr m sf => digitContentsWith f pr ++
      contentsWith (nodeContentsWith f) m ++ digitContentsWith f sf
  end.
Definition contents {v a} (t : FingerTree v a) : list a :=
  contentsWith (fun x => [x]) t.
Definition digitValidity {a} (P : a -> Prop) (d : Digit a) : Prop :=
  match d with
  | One x => P x
  | Two x y => P x /\ P y
  | Three x y z => P x /\ P y /\ P z
  | Four x y z w => P x /\ P y /\ P z /\ P w
  end.

Section Measures.
Context {v : Type} `{GHC.Base.Monoid v}.
Definition listMeasure {a} (mu : a -> v) (xs : list a) : v :=
  List.fold_right (fun x acc => GHC.Base.mappend (mu x) acc) GHC.Base.mempty xs.
Definition digitMeasure {a} (mu : a -> v) (d : Digit a) : v :=
  match d with
  | One x => mu x
  | Two x y => GHC.Base.mappend (mu x) (mu y)
  | Three x y z => GHC.Base.mappend (GHC.Base.mappend (mu x) (mu y)) (mu z)
  | Four x y z w => GHC.Base.mappend
      (GHC.Base.mappend (GHC.Base.mappend (mu x) (mu y)) (mu z)) (mu w)
  end.
Definition nodeCache {a} (n : Node v a) : v :=
  match n with Node2 c _ _ => c | Node3 c _ _ _ => c end.
Definition treeCacheWith {a} (mu : a -> v) (t : FingerTree v a) : v :=
  match t with Empty => GHC.Base.mempty | Single x => mu x | Deep c _ _ _ => c end.
Definition nodeValidity {a} (mu : a -> v) (P : a -> Prop) (n : Node v a) : Prop :=
  match n with
  | Node2 c x y => P x /\ P y /\ c = GHC.Base.mappend (mu x) (mu y)
  | Node3 c x y z => P x /\ P y /\ P z /\
      c = GHC.Base.mappend (GHC.Base.mappend (mu x) (mu y)) (mu z)
  end.
(* The middle predicate lifts both element validity and cache validity at every
   node level. Digit/node arities and balanced depth are enforced by the type. *)
Fixpoint validityWith {a} (mu : a -> v) (P : a -> Prop) (t : FingerTree v a) : Prop :=
  match t with
  | Empty => True
  | Single x => P x
  | Deep c pr m sf => digitValidity P pr /\
      validityWith nodeCache (nodeValidity mu P) m /\ digitValidity P sf /\
      c = GHC.Base.mappend
        (GHC.Base.mappend (digitMeasure mu pr) (treeCacheWith nodeCache m))
        (digitMeasure mu sf)
  end.
Definition validity {a} (M : Measured v a) (t : FingerTree v a) : Prop :=
  validityWith (@measure v a _ _ M) (fun _ => True) t.

Hypothesis assoc : forall x y z : v, GHC.Base.mappend (GHC.Base.mappend x y) z =
  GHC.Base.mappend x (GHC.Base.mappend y z).
Hypothesis left_id : forall x : v, GHC.Base.mappend GHC.Base.mempty x = x.
Hypothesis right_id : forall x : v, GHC.Base.mappend x GHC.Base.mempty = x.

Lemma listMeasure_app {a} (mu : a -> v) xs ys :
  listMeasure mu (xs ++ ys) = GHC.Base.mappend (listMeasure mu xs) (listMeasure mu ys).
Proof. unfold listMeasure; induction xs; cbn; [symmetry; apply left_id|].
  rewrite IHxs, assoc; reflexivity. Qed.

Lemma digitMeasure_contents {a} (mu : a -> v) d :
  digitMeasure mu d = listMeasure mu (digitContentsWith (fun x => [x]) d).
Proof. destruct d; cbn [digitMeasure digitContentsWith listMeasure List.fold_right List.app];
  rewrite right_id; repeat rewrite assoc; reflexivity. Qed.

Lemma digitMeasure_flatten {a b} (mu : b -> v) (f : a -> list b) d :
  digitMeasure (fun x => listMeasure mu (f x)) d = listMeasure mu (digitContentsWith f d).
Proof. destruct d; cbn [digitMeasure digitContentsWith];
  repeat rewrite listMeasure_app; repeat rewrite assoc; reflexivity. Qed.

Lemma valid_node_measure {a b} (mu : a -> v) (P : a -> Prop)
  (f : a -> list b) (nu : b -> v) n :
  (forall x, P x -> mu x = listMeasure nu (f x)) ->
  nodeValidity mu P n -> nodeCache n = listMeasure nu (nodeContentsWith f n).
Proof.
  intros E V; destruct n; cbn [nodeValidity nodeCache nodeContentsWith] in *;
    decompose [and] V; subst; repeat rewrite listMeasure_app;
    repeat rewrite <- assoc; f_equal; auto; f_equal; auto.
Qed.

Lemma valid_digit_measure {a b} (mu : a -> v) (P : a -> Prop)
  (f : a -> list b) (nu : b -> v) d :
  (forall x, P x -> mu x = listMeasure nu (f x)) ->
  digitValidity P d -> digitMeasure mu d = listMeasure nu (digitContentsWith f d).
Proof.
  intros E V; rewrite <- digitMeasure_flatten; destruct d;
    cbn [digitValidity digitMeasure] in *; decompose [and] V;
    repeat match goal with Hx : P ?x |- _ => rewrite (E x Hx) end; reflexivity.
Qed.

Lemma valid_tree_measure : forall a (t : FingerTree v a) (mu : a -> v) P
  b (f : a -> list b) (nu : b -> v),
  (forall x, P x -> mu x = listMeasure nu (f x)) ->
  validityWith mu P t -> treeCacheWith mu t = listMeasure nu (contentsWith f t).
Proof.
  refine (FingerTree_rect v (fun a t => forall (mu : a -> v) P
    b (f : a -> list b) (nu : b -> v),
    (forall x, P x -> mu x = listMeasure nu (f x)) ->
    validityWith mu P t -> treeCacheWith mu t = listMeasure nu (contentsWith f t)) _ _ _).
  - intros; reflexivity.
  - intros; cbn in *; auto.
  - intros a c pr m IH sf mu P b f nu E [Vp [Vm [Vs Ec]]].
    cbn [treeCacheWith contentsWith]; rewrite Ec.
    rewrite (IH nodeCache (nodeValidity mu P) b (nodeContentsWith f) nu).
    + rewrite (valid_digit_measure mu P f nu pr E Vp),
        (valid_digit_measure mu P f nu sf E Vs).
      repeat rewrite listMeasure_app; apply assoc.
    + intros n Vn; eapply valid_node_measure; eassumption.
    + exact Vm.
Qed.

Lemma measure_contents {a} (M : Measured v a) (t : FingerTree v a) :
  validity M t -> measure t = listMeasure (@measure v a _ _ M) (contents t).
Proof.
  intro V; change (treeCacheWith (@measure v a _ _ M) t =
    listMeasure (@measure v a _ _ M) (contentsWith (fun x => [x]) t)).
  eapply valid_tree_measure; [|exact V].
  intros; cbn [listMeasure List.fold_right]; symmetry; apply right_id.
Qed.

Lemma foldMap_digit {a} (g : a -> v) (d : Digit a) :
  Data.Foldable.foldMap g d = digitMeasure g d.
Proof. destruct d; reflexivity. Qed.

Lemma foldMap_node_flatten {c a b} (g : a -> v) (f : a -> list b) (nu : b -> v)
  (n : Node c a) :
  (forall x, g x = listMeasure nu (f x)) ->
  Data.Foldable.foldMap g n = listMeasure nu (nodeContentsWith f n).
Proof.
  intro E; destruct n; cbn [nodeContentsWith Data.Foldable.foldMap
    Foldable__Node Data.Foldable.foldMap__ Data.FingerTree.Foldable__Node_foldMap]; repeat rewrite listMeasure_app;
    repeat rewrite <- assoc; f_equal; auto; f_equal; auto.
Qed.

Lemma foldMap_contentsWith {c} : forall a (t : FingerTree c a) b
  (g : a -> v) (f : a -> list b) (nu : b -> v),
  (forall x, g x = listMeasure nu (f x)) ->
  Data.Foldable.foldMap g t = listMeasure nu (contentsWith f t).
Proof.
  refine (FingerTree_rect c (fun a t => forall b (g : a -> v)
    (f : a -> list b) (nu : b -> v),
    (forall x, g x = listMeasure nu (f x)) ->
    Data.Foldable.foldMap g t = listMeasure nu (contentsWith f t)) _ _ _).
  - intros; reflexivity.
  - intros; apply H1.
  - intros a cache pr m IH sf b g f nu E.
    change (GHC.Base.mappend
      (GHC.Base.mappend (Data.Foldable.foldMap g pr)
        (Data.Foldable.foldMap (fun n : Node c a => Data.Foldable.foldMap g n) m))
      (Data.Foldable.foldMap g sf) =
      listMeasure nu (digitContentsWith f pr ++ contentsWith (nodeContentsWith f) m ++ digitContentsWith f sf)).
    rewrite (IH b _ (nodeContentsWith f) nu).
    + rewrite !foldMap_digit.
      rewrite (valid_digit_measure g (fun _ => True) f nu pr),
        (valid_digit_measure g (fun _ => True) f nu sf).
      * repeat rewrite listMeasure_app; apply assoc.
      * auto.
      * destruct sf; cbn; auto.
      * auto.
      * destruct pr; cbn; auto.
    + intros; apply foldMap_node_flatten; exact E.
Qed.

Lemma foldMap_contents {c a} (g : a -> v) (t : FingerTree c a) :
  Data.Foldable.foldMap g t = listMeasure g (contents t).
Proof.
  apply foldMap_contentsWith; intro x.
  cbn [listMeasure List.fold_right]; symmetry; apply right_id.
Qed.

Lemma validityWith_Forall : forall a (t : FingerTree v a) (mu : a -> v) P
  b (f : a -> list b) (R : b -> Prop),
  (forall x, P x -> List.Forall R (f x)) -> validityWith mu P t ->
  List.Forall R (contentsWith f t).
Proof.
  refine (FingerTree_rect v (fun a t => forall (mu : a -> v) P
    b (f : a -> list b) (R : b -> Prop),
    (forall x, P x -> List.Forall R (f x)) -> validityWith mu P t ->
    List.Forall R (contentsWith f t)) _ _ _).
  - intros; constructor.
  - intros; apply H1; assumption.
  - intros a c pr m IH sf mu P b f R E [Vp [Vm [Vs Ec]]].
    cbn [contentsWith]; rewrite !List.Forall_app; repeat split.
    + destruct pr; cbn [digitValidity digitContentsWith] in *;
        rewrite ?List.Forall_app; repeat split; apply E; tauto.
    + eapply IH; [|exact Vm].
      intros n Vn; destruct n; cbn [nodeValidity nodeContentsWith] in *;
        rewrite ?List.Forall_app; repeat split; apply E; tauto.
    + destruct sf; cbn [digitValidity digitContentsWith] in *;
        rewrite ?List.Forall_app; repeat split; apply E; tauto.
Qed.

Lemma validityWith_elements {a} (mu : a -> v) P (t : FingerTree v a) :
  validityWith mu P t -> List.Forall P (contents t).
Proof.
  intro V; eapply validityWith_Forall; [|exact V].
  intros; constructor; [assumption|constructor].
Qed.
End Measures.

Lemma foldr_contents {v a b} (f : a -> b -> b) z (t : FingerTree v a) :
  Data.Foldable.foldr f z t = List.fold_right f z (contents t).
Proof.
  change (Data.SemigroupInternal.appEndo
    (Data.Foldable.foldMap (fun x => Data.SemigroupInternal.Mk_Endo (f x)) t) z =
    List.fold_right f z (contents t)).
  rewrite (@foldMap_contents (Data.SemigroupInternal.Endo b) _ _
    ltac:(intros [u] [w] [r]; reflexivity)
    ltac:(intros [u]; reflexivity) ltac:(intros [u]; reflexivity)
    v a (fun x => Data.SemigroupInternal.Mk_Endo (f x)) t).
  unfold listMeasure; induction (contents t) as [|x xs IH]; cbn in *;
    [reflexivity|rewrite IH; reflexivity].
Qed.

Lemma foldl_contents {v a b} (f : b -> a -> b) z (t : FingerTree v a) :
  Data.Foldable.foldl f z t = List.fold_left f (contents t) z.
Proof.
  change (Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
    (Data.Foldable.foldMap (fun x => Data.SemigroupInternal.Mk_Dual
      (Data.SemigroupInternal.Mk_Endo (fun z => f z x))) t)) z =
    List.fold_left f (contents t) z).
  rewrite (@foldMap_contents (Data.SemigroupInternal.Dual (Data.SemigroupInternal.Endo b)) _ _
    ltac:(intros [[u]] [[w]] [[r]]; reflexivity)
    ltac:(intros [[u]]; reflexivity) ltac:(intros [[u]]; reflexivity)
    v a (fun x => Data.SemigroupInternal.Mk_Dual
      (Data.SemigroupInternal.Mk_Endo (fun z => f z x))) t).
  unfold listMeasure; revert z; induction (contents t) as [|x xs IH]; intro z.
  - reflexivity.
  - cbn [List.fold_right List.fold_left].
    destruct (List.fold_right (fun x acc => GHC.Base.mappend
      (Data.SemigroupInternal.Mk_Dual (Data.SemigroupInternal.Mk_Endo (fun z => f z x))) acc)
      GHC.Base.mempty xs) as [[k]] eqn:E.
    exact (IH (f z x)).
Qed.

Lemma toList_contents {v a} (t : FingerTree v a) : Data.Foldable.toList t = contents t.
Proof.
  change (Data.Foldable.foldr (@cons a) [] t = contents t).
  rewrite foldr_contents; induction (contents t); cbn; congruence.
Qed.

Lemma foldl'_contents {v a b} (f : b -> a -> b) z (t : FingerTree v a) :
  Data.Foldable.foldl' f z t = List.fold_left f (contents t) z.
Proof.
  change (Data.Foldable.foldr (fun x k z => k (f z x)) (fun z => z) t z =
    List.fold_left f (contents t) z).
  rewrite foldr_contents.
  revert z; induction (contents t); cbn; intros; [reflexivity|apply IHl].
Qed.

Lemma foldr'_contents {v a b} (f : a -> b -> b) z (t : FingerTree v a) :
  Data.Foldable.foldr' f z t = List.fold_right f z (contents t).
Proof.
  change (Data.Foldable.foldl (fun k x z => k (f x z)) (fun z => z) t z =
    List.fold_right f z (contents t)).
  rewrite foldl_contents.
  assert (G : forall xs (k : b -> b) z,
    List.fold_left (fun k x z => k (f x z)) xs k z = k (List.fold_right f z xs)).
  { induction xs; cbn; intros; [reflexivity|rewrite IHxs; reflexivity]. }
  apply G.
Qed.

Check @digitContentsWith. Print Assumptions digitContentsWith.
Check @nodeContentsWith. Print Assumptions nodeContentsWith.
Check @contentsWith. Print Assumptions contentsWith.
Check @contents. Print Assumptions contents.
Check @digitValidity. Print Assumptions digitValidity.
Check @listMeasure. Print Assumptions listMeasure.
Check @digitMeasure. Print Assumptions digitMeasure.
Check @nodeCache. Print Assumptions nodeCache.
Check @treeCacheWith. Print Assumptions treeCacheWith.
Check @nodeValidity. Print Assumptions nodeValidity.
Check @validityWith. Print Assumptions validityWith.
Check @validity. Print Assumptions validity.
Check @listMeasure_app. Print Assumptions listMeasure_app.
Check @digitMeasure_contents. Print Assumptions digitMeasure_contents.
Check @digitMeasure_flatten. Print Assumptions digitMeasure_flatten.
Check @valid_node_measure. Print Assumptions valid_node_measure.
Check @valid_digit_measure. Print Assumptions valid_digit_measure.
Check @valid_tree_measure. Print Assumptions valid_tree_measure.
Check @measure_contents. Print Assumptions measure_contents.
Check @foldMap_digit. Print Assumptions foldMap_digit.
Check @foldMap_node_flatten. Print Assumptions foldMap_node_flatten.
Check @foldMap_contentsWith. Print Assumptions foldMap_contentsWith.
Check @foldMap_contents. Print Assumptions foldMap_contents.
Check @foldr_contents. Print Assumptions foldr_contents.
Check @foldl_contents. Print Assumptions foldl_contents.
Check @toList_contents. Print Assumptions toList_contents.
Check @validityWith_Forall. Print Assumptions validityWith_Forall.
Check @validityWith_elements. Print Assumptions validityWith_elements.
Check @foldl'_contents. Print Assumptions foldl'_contents.
Check @foldr'_contents. Print Assumptions foldr'_contents.
