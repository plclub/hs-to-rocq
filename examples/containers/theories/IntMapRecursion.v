(* Guarded unfolding for the translated IntMap algorithms. The measure counts
   raw branch nodes, so no map validity assumption is needed. *)
From Coq Require Import Lia Arith.Wf_nat.
Require Import HsToRocq.DeferredFix.
Require Import Data.IntSet.Internal Data.IntMap.Internal.
Import HsToRocq.DeferredFix.

Definition map_pair_size {a b} (p : IntMap a * IntMap b) : nat :=
  (size_nat (fst p) + size_nat (snd p))%nat.

Definition map_set_size {a} (p : IntMap a * IntSet) : nat :=
  (size_nat (fst p) + Data.IntSet.Internal.size_nat (snd p))%nat.

(* These are the actual generated functionals, not replacement algorithms. *)
Definition mergeWithKey'_f {c a b}
  (bin' : Prefix -> Mask -> IntMap c -> IntMap c -> IntMap c)
  (f : IntMap a -> IntMap b -> IntMap c)
  (g1 : IntMap a -> IntMap c) (g2 : IntMap b -> IntMap c) :
  (IntMap a -> IntMap b -> IntMap c) -> IntMap a -> IntMap b -> IntMap c.
Proof.
  let rhs := eval unfold mergeWithKey' in (@mergeWithKey' c a b bin' f g1 g2) in
  match rhs with context [deferredFix2 ?body] => exact body end.
Defined.

Definition disjoint_f {a b} :
  (IntMap a -> IntMap b -> bool) -> IntMap a -> IntMap b -> bool.
Proof.
  let rhs := eval unfold disjoint in (@disjoint a b) in
  match rhs with context [deferredFix2 ?body] => exact body end.
Defined.

Definition restrictKeys_f {a} :
  (IntMap a -> IntSet -> IntMap a) -> IntMap a -> IntSet -> IntMap a.
Proof.
  let rhs := eval unfold restrictKeys in (@restrictKeys a) in
  match rhs with context [deferredFix2 ?body] => exact body end.
Defined.

Definition withoutKeys_f {a} :
  (IntMap a -> IntSet -> IntMap a) -> IntMap a -> IntSet -> IntMap a.
Proof.
  let rhs := eval unfold withoutKeys in (@withoutKeys a) in
  match rhs with context [deferredFix2 ?body] => exact body end.
Defined.

(* Split only the branch tests of the functional, leaving the recursive calls
   opaque. Each resulting call is on a strict structural subproblem. *)
Local Ltac split_tests :=
  repeat match goal with
  | |- context [if ?test then _ else _] => destruct test
  end.

Lemma mergeWithKey'_recurses {c a b} bin' f g1 g2 :
  recurses_on (fun _ => True) (ltof _ (@map_pair_size a b))
    (fun g => uncurry (@mergeWithKey'_f c a b bin' f g1 g2 (curry g))).
Proof.
  intros g h [x y] _ IH.
  destruct x; destruct y; cbn [uncurry mergeWithKey'_f curry];
    try reflexivity.
  split_tests; unfold curry;
    repeat match goal with
    | |- context [g (?x, ?y)] =>
      rewrite (IH (x, y) I ltac:(unfold ltof, map_pair_size; cbn; lia))
    end; reflexivity.
Qed.

Lemma mergeWithKey'_eq {c a b}
  (bin' : Prefix -> Mask -> IntMap c -> IntMap c -> IntMap c)
  (f : IntMap a -> IntMap b -> IntMap c)
  (g1 : IntMap a -> IntMap c) (g2 : IntMap b -> IntMap c)
  (x : IntMap a) (y : IntMap b) :
  mergeWithKey' bin' f g1 g2 x y =
  mergeWithKey'_f bin' f g1 g2 (mergeWithKey' bin' f g1 g2) x y.
Proof.
  change (deferredFix (fun g => uncurry (mergeWithKey'_f bin' f g1 g2 (curry g))) (x,y) =
    uncurry (mergeWithKey'_f bin' f g1 g2 (mergeWithKey' bin' f g1 g2)) (x,y)).
  apply (deferredFix_eq_on
    (fun g => uncurry (mergeWithKey'_f bin' f g1 g2 (curry g)))
    (fun _ => True) (ltof _ (@map_pair_size a b))).
  - apply well_founded_ltof.
  - apply mergeWithKey'_recurses.
  - exact I.
Qed.

Lemma disjoint_recurses {a b} :
  recurses_on (fun _ => True) (ltof _ (@map_pair_size a b))
    (fun g => uncurry (@disjoint_f a b (curry g))).
Proof.
  intros g h [x y] _ IH.
  destruct x; destruct y; cbn [uncurry disjoint_f curry];
    try reflexivity.
  split_tests; unfold curry;
    repeat match goal with
    | |- context [g (?x, ?y)] =>
      rewrite (IH (x, y) I ltac:(unfold ltof, map_pair_size; cbn; lia))
    end; reflexivity.
Qed.

Lemma disjoint_eq {a b} (x : IntMap a) (y : IntMap b) :
  disjoint x y = disjoint_f disjoint x y.
Proof.
  change (deferredFix (fun g => uncurry (disjoint_f (curry g))) (x,y) =
    uncurry (disjoint_f disjoint) (x,y)).
  apply (deferredFix_eq_on (fun g => uncurry (disjoint_f (curry g)))
    (fun _ => True) (ltof _ (@map_pair_size a b))).
  - apply well_founded_ltof.
  - apply disjoint_recurses.
  - exact I.
Qed.

Lemma restrictKeys_recurses {a} :
  recurses_on (fun _ => True) (ltof _ (@map_set_size a))
    (fun g => uncurry (@restrictKeys_f a (curry g))).
Proof.
  intros g h [x y] _ IH.
  destruct x; destruct y; cbn [uncurry restrictKeys_f curry];
    try reflexivity.
  split_tests; unfold curry;
    repeat match goal with
    | |- context [g (?x, ?y)] =>
      rewrite (IH (x, y) I ltac:(unfold ltof, map_set_size; cbn; lia))
    end; reflexivity.
Qed.

Lemma restrictKeys_eq {a} (x : IntMap a) (y : IntSet) :
  restrictKeys x y = restrictKeys_f restrictKeys x y.
Proof.
  change (deferredFix (fun g => uncurry (restrictKeys_f (curry g))) (x,y) =
    uncurry (restrictKeys_f restrictKeys) (x,y)).
  apply (deferredFix_eq_on (fun g => uncurry (restrictKeys_f (curry g)))
    (fun _ => True) (ltof _ (@map_set_size a))).
  - apply well_founded_ltof.
  - apply restrictKeys_recurses.
  - exact I.
Qed.

Lemma withoutKeys_recurses {a} :
  recurses_on (fun _ => True) (ltof _ (@map_set_size a))
    (fun g => uncurry (@withoutKeys_f a (curry g))).
Proof.
  intros g h [x y] _ IH.
  destruct x; destruct y; cbn [uncurry withoutKeys_f curry];
    try reflexivity.
  split_tests; unfold curry;
    repeat match goal with
    | |- context [g (?x, ?y)] =>
      rewrite (IH (x, y) I ltac:(unfold ltof, map_set_size; cbn; lia))
    end; reflexivity.
Qed.

Lemma withoutKeys_eq {a} (x : IntMap a) (y : IntSet) :
  withoutKeys x y = withoutKeys_f withoutKeys x y.
Proof.
  change (deferredFix (fun g => uncurry (withoutKeys_f (curry g))) (x,y) =
    uncurry (withoutKeys_f withoutKeys) (x,y)).
  apply (deferredFix_eq_on (fun g => uncurry (withoutKeys_f (curry g)))
    (fun _ => True) (ltof _ (@map_set_size a))).
  - apply well_founded_ltof.
  - apply withoutKeys_recurses.
  - exact I.
Qed.

Print Assumptions mergeWithKey'_eq.
Print Assumptions disjoint_eq.
Print Assumptions restrictKeys_eq.
Print Assumptions withoutKeys_eq.
