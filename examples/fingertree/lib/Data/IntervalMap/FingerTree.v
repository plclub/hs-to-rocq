(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Stdlib.Program.Tactics.
Require Stdlib.Program.Wf.
Require Import Stdlib.Program.WfExtensionality.

(* Converted imports: *)

Require Corelib.Init.Peano.
Require Corelib.Program.Basics.
Require Data.FingerTree.
Require Data.Foldable.
Require Data.Functor.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require GHC.Prim.
Require HsToRocq.Wf.
Import Data.FingerTree.Notations.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Interval v : Type := | MkInterval : v -> v -> Interval v.

Inductive Node v a : Type := | MkNode : (Interval v) -> a -> Node v a.

Inductive IntInterval v : Type :=
  | NoInterval : IntInterval v
  | MkIntInterval : (Interval v) -> v -> IntInterval v.

Inductive IntervalMap v a : Type :=
  | MkIntervalMap
   : (Data.FingerTree.FingerTree (IntInterval v) (Node v a)) -> IntervalMap v a.

Arguments MkInterval {_} _ _.

Arguments MkNode {_} {_} _ _.

Arguments NoInterval {_}.

Arguments MkIntInterval {_} _ _.

Arguments MkIntervalMap {_} {_} _.

(* Midamble *)

From Stdlib Require Import micromega.Lia.
Require Import FingerTreeProofs.CoreSize.

Local Obligation Tactic := idtac.

Definition interval_measure {v : Type} {a : Type}
  (as_ bs : Data.FingerTree.FingerTree (IntInterval v) (Node v a)) : nat :=
  size as_ + size bs.

Ltac interval_identity_do tac :=
  match goal with
  | Hord : GHC.Base.Ord ?vv |- _ =>
      let Hid := open_constr:(fun x : IntInterval vv =>
        match x as x0 return
          @GHC.Base.mappend (IntInterval vv)
            ltac:(typeclasses eauto) ltac:(typeclasses eauto) x0
            (@GHC.Base.mempty (IntInterval vv)
              ltac:(typeclasses eauto) ltac:(typeclasses eauto)) = x0 with
        | NoInterval => eq_refl
        | MkIntInterval i h => eq_refl
        end) in
      pose proof Hid as Hid_proof;
      tac Hid_proof
  end.

Ltac interval_union_decrease_with Hid_proof :=
  unfold interval_measure in *;
  match goal with
  | Hv0 : (Data.FingerTree.op_ZCzl__ ?x0 ?r0) = ?fv0,
    Hs0 : (?l0, ?r0') = ?fv1,
    Hv2 : (Data.FingerTree.op_ZCzl__ ?x2 ?r2) = ?fv2,
    Hs : (?l, ?r) = ?fv3 |- _ =>
      unfold fv0 in Hv0; symmetry in Hv0;
      pose proof (viewl_size_lt _ _ x0 r0 Hv0) as Hview_as;
      unfold fv1 in Hs0; symmetry in Hs0;
      pose proof (split_size_bounds Hid_proof _ _ _ l0 r0' Hs0)
        as Hsplit_bs;
      unfold fv2 in Hv2; symmetry in Hv2;
      pose proof (viewl_size_lt _ _ x2 r2 Hv2) as Hview_r0;
      unfold fv3 in Hs; symmetry in Hs;
      pose proof (split_size_bounds Hid_proof _ _ _ l r Hs)
        as Hsplit_as;
      lia
  end.

Ltac interval_union_decrease :=
  interval_identity_do interval_union_decrease_with.

Ltac interval_union_termination :=
  intros;
  match goal with
  | |- well_founded _ => apply PeanoNat.Nat.lt_wf_0
  | _ => interval_union_decrease
  end.

Ltac interval_inRange_decrease_with Hid_proof :=
  unfold interval_measure in *;
  match goal with
  | Hv : (Data.FingerTree.op_ZCzl__ ?x ?r) = ?fv |- _ =>
      unfold fv in Hv;
      pose proof (viewl_size_lt _ _ x r (eq_sym Hv)) as Hview;
      match type of Hv with
      | _ = Data.FingerTree.viewl (Data.FingerTree.dropUntil ?p ?t) =>
          pose proof (dropUntil_size_le Hid_proof _ p t) as Hdrop
      end;
      lia
  end.

Ltac interval_inRange_decrease :=
  interval_identity_do interval_inRange_decrease_with.

Ltac interval_inRange_termination :=
  intros;
  match goal with
  | |- well_founded _ => apply PeanoNat.Nat.lt_wf_0
  | _ => interval_inRange_decrease
  end.

(* Converted value declarations: *)

#[local] Definition Eq___Interval_op_zeze__ {inst_v : Type} `{GHC.Base.Eq_
  inst_v}
   : Interval inst_v -> Interval inst_v -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkInterval a1 a2, MkInterval b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    end.

#[local] Definition Eq___Interval_op_zsze__ {inst_v : Type} `{GHC.Base.Eq_
  inst_v}
   : Interval inst_v -> Interval inst_v -> bool :=
  fun x y => negb (Eq___Interval_op_zeze__ x y).

#[global]
Program Instance Eq___Interval {v : Type} `{GHC.Base.Eq_ v}
   : GHC.Base.Eq_ (Interval v) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Interval_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Interval_op_zsze__ |}.

#[local] Definition Eq___Node_op_zeze__ {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Eq_ inst_v} `{GHC.Base.Eq_ inst_a}
   : Node inst_v inst_a -> Node inst_v inst_a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkNode a1 a2, MkNode b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    end.

#[local] Definition Eq___Node_op_zsze__ {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Eq_ inst_v} `{GHC.Base.Eq_ inst_a}
   : Node inst_v inst_a -> Node inst_v inst_a -> bool :=
  fun x y => negb (Eq___Node_op_zeze__ x y).

#[global]
Program Instance Eq___Node {v : Type} {a : Type} `{GHC.Base.Eq_ v}
  `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Node v a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Node_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Node_op_zsze__ |}.

#[local] Definition Ord__Interval_compare {inst_v : Type} `{GHC.Base.Ord inst_v}
   : Interval inst_v -> Interval inst_v -> comparison :=
  fun a b =>
    let 'MkInterval a1 a2 := a in
    let 'MkInterval b1 b2 := b in
    match (GHC.Base.compare a1 b1) with
    | Lt => Lt
    | Eq => (GHC.Base.compare a2 b2)
    | Gt => Gt
    end.

#[local] Definition Ord__Interval_op_zl__ {inst_v : Type} `{GHC.Base.Ord inst_v}
   : Interval inst_v -> Interval inst_v -> bool :=
  fun a b =>
    let 'MkInterval a1 a2 := a in
    let 'MkInterval b1 b2 := b in
    match (GHC.Base.compare a1 b1) with
    | Lt => true
    | Eq => (a2 GHC.Base.< b2)
    | Gt => false
    end.

#[local] Definition Ord__Interval_op_zlze__ {inst_v : Type} `{GHC.Base.Ord
  inst_v}
   : Interval inst_v -> Interval inst_v -> bool :=
  fun a b => negb (Ord__Interval_op_zl__ b a).

#[local] Definition Ord__Interval_max {inst_v : Type} `{GHC.Base.Ord inst_v}
   : Interval inst_v -> Interval inst_v -> Interval inst_v :=
  fun x y => if Ord__Interval_op_zlze__ x y : bool then y else x.

#[local] Definition Ord__Interval_min {inst_v : Type} `{GHC.Base.Ord inst_v}
   : Interval inst_v -> Interval inst_v -> Interval inst_v :=
  fun x y => if Ord__Interval_op_zlze__ x y : bool then x else y.

#[local] Definition Ord__Interval_op_zg__ {inst_v : Type} `{GHC.Base.Ord inst_v}
   : Interval inst_v -> Interval inst_v -> bool :=
  fun a b => Ord__Interval_op_zl__ b a.

#[local] Definition Ord__Interval_op_zgze__ {inst_v : Type} `{GHC.Base.Ord
  inst_v}
   : Interval inst_v -> Interval inst_v -> bool :=
  fun a b => negb (Ord__Interval_op_zl__ a b).

#[global]
Program Instance Ord__Interval {v : Type} `{GHC.Base.Ord v}
   : GHC.Base.Ord (Interval v) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Interval_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Interval_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Interval_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Interval_op_zgze__ ;
           GHC.Base.compare__ := Ord__Interval_compare ;
           GHC.Base.max__ := Ord__Interval_max ;
           GHC.Base.min__ := Ord__Interval_min |}.

#[local] Definition Ord__Node_op_zl__ {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_v} `{GHC.Base.Ord inst_a}
   : Node inst_v inst_a -> Node inst_v inst_a -> bool :=
  fun a b =>
    let 'MkNode a1 a2 := a in
    let 'MkNode b1 b2 := b in
    match (GHC.Base.compare a1 b1) with
    | Lt => true
    | Eq => (a2 GHC.Base.< b2)
    | Gt => false
    end.

#[local] Definition Ord__Node_op_zlze__ {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_v} `{GHC.Base.Ord inst_a}
   : Node inst_v inst_a -> Node inst_v inst_a -> bool :=
  fun a b => negb (Ord__Node_op_zl__ b a).

#[local] Definition Ord__Node_op_zg__ {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_v} `{GHC.Base.Ord inst_a}
   : Node inst_v inst_a -> Node inst_v inst_a -> bool :=
  fun a b => Ord__Node_op_zl__ b a.

#[local] Definition Ord__Node_op_zgze__ {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_v} `{GHC.Base.Ord inst_a}
   : Node inst_v inst_a -> Node inst_v inst_a -> bool :=
  fun a b => negb (Ord__Node_op_zl__ a b).

#[local] Definition Ord__Node_compare {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_v} `{GHC.Base.Ord inst_a}
   : Node inst_v inst_a -> Node inst_v inst_a -> comparison :=
  fun a b =>
    let 'MkNode a1 a2 := a in
    let 'MkNode b1 b2 := b in
    match (GHC.Base.compare a1 b1) with
    | Lt => Lt
    | Eq => (GHC.Base.compare a2 b2)
    | Gt => Gt
    end.

#[local] Definition Ord__Node_max {inst_v : Type} {inst_a : Type} `{GHC.Base.Ord
  inst_v} `{GHC.Base.Ord inst_a}
   : Node inst_v inst_a -> Node inst_v inst_a -> Node inst_v inst_a :=
  fun x y => if Ord__Node_op_zlze__ x y : bool then y else x.

#[local] Definition Ord__Node_min {inst_v : Type} {inst_a : Type} `{GHC.Base.Ord
  inst_v} `{GHC.Base.Ord inst_a}
   : Node inst_v inst_a -> Node inst_v inst_a -> Node inst_v inst_a :=
  fun x y => if Ord__Node_op_zlze__ x y : bool then x else y.

#[global]
Program Instance Ord__Node {v : Type} {a : Type} `{GHC.Base.Ord v}
  `{GHC.Base.Ord a}
   : GHC.Base.Ord (Node v a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Node_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Node_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Node_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Node_op_zgze__ ;
           GHC.Base.compare__ := Ord__Node_compare ;
           GHC.Base.max__ := Ord__Node_max ;
           GHC.Base.min__ := Ord__Node_min |}.

#[local] Definition Functor__Node_fmap {inst_v : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> Node inst_v a -> Node inst_v b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, MkNode i x => MkNode i (f x)
      end.

#[local] Definition Functor__Node_op_zlzd__ {inst_v : Type}
   : forall {a : Type}, forall {b : Type}, a -> Node inst_v b -> Node inst_v a :=
  fun {a : Type} {b : Type} => Functor__Node_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__Node {v : Type} : GHC.Base.Functor (Node v) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Node_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) => Functor__Node_op_zlzd__ |}.

#[local] Definition Foldable__Node_foldMap {inst_v : Type}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Node inst_v a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, MkNode _ x => f x end.

#[local] Definition Foldable__Node_fold {inst_v : Type}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Node inst_v m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Node_foldMap GHC.Base.id.

#[local] Definition Foldable__Node_foldr {inst_v : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Node inst_v a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Node_foldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__Node_foldl' {inst_v : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Node inst_v a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__Node_foldr (fun arg_0__ arg_1__ =>
                                match arg_0__, arg_1__ with
                                | x, k => (fun '(z) => GHC.Prim.seq z (k (f z x)))
                                end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__Node_foldMap' {inst_v : Type}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Node inst_v a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Node_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Node_foldl {inst_v : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Node inst_v a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Node_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                               (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__Node_foldr' {inst_v : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Node inst_v a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__Node_foldl (fun arg_0__ arg_1__ =>
                                match arg_0__, arg_1__ with
                                | k, x => (fun '(z) => GHC.Prim.seq z (k (f x z)))
                                end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__Node_length {inst_v : Type}
   : forall {a : Type}, Node inst_v a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__Node_foldl' (fun arg_0__ arg_1__ =>
                             match arg_0__, arg_1__ with
                             | c, _ => c GHC.Num.+ #1
                             end) #0.

#[local] Definition Foldable__Node_null {inst_v : Type}
   : forall {a : Type}, Node inst_v a -> bool :=
  fun {a : Type} => Foldable__Node_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__Node_product {inst_v : Type}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Node inst_v a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getProduct
                                   (Foldable__Node_foldMap' Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__Node_sum {inst_v : Type}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Node inst_v a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getSum
                                   (Foldable__Node_foldMap' Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__Node_toList {inst_v : Type}
   : forall {a : Type}, Node inst_v a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Node_foldr c n t)).

#[global]
Program Instance Foldable__Node {v : Type} : Data.Foldable.Foldable (Node v) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Foldable__Node_fold ;
           Data.Foldable.foldMap__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Node_foldMap ;
           Data.Foldable.foldMap'__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Node_foldMap' ;
           Data.Foldable.foldl__ := fun (b : Type) (a : Type) => Foldable__Node_foldl ;
           Data.Foldable.foldl'__ := fun (b : Type) (a : Type) => Foldable__Node_foldl' ;
           Data.Foldable.foldr__ := fun (a : Type) (b : Type) => Foldable__Node_foldr ;
           Data.Foldable.foldr'__ := fun (a : Type) (b : Type) => Foldable__Node_foldr' ;
           Data.Foldable.length__ := fun (a : Type) => Foldable__Node_length ;
           Data.Foldable.null__ := fun (a : Type) => Foldable__Node_null ;
           Data.Foldable.product__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__Node_product ;
           Data.Foldable.sum__ := fun (a : Type) `(GHC.Num.Num a) => Foldable__Node_sum ;
           Data.Foldable.toList__ := fun (a : Type) => Foldable__Node_toList |}.

#[local] Definition Traversable__Node_traverse {inst_v : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> Node inst_v a -> f (Node inst_v b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, MkNode i x => Data.Functor.op_zlzdzg__ (MkNode i) (f x)
      end.

#[local] Definition Traversable__Node_mapM {inst_v : Type}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m}, (a -> m b) -> Node inst_v a -> m (Node inst_v b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Node_traverse.

#[local] Definition Traversable__Node_sequenceA {inst_v : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f}, Node inst_v (f a) -> f (Node inst_v a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Node_traverse GHC.Base.id.

#[local] Definition Traversable__Node_sequence {inst_v : Type}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m}, Node inst_v (m a) -> m (Node inst_v a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Node_sequenceA.

#[global]
Program Instance Traversable__Node {v : Type}
   : Data.Traversable.Traversable (Node v) :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun (m : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Monad m) =>
             Traversable__Node_mapM ;
           Data.Traversable.sequence__ := fun (m : Type -> Type)
           (a : Type)
           `(GHC.Base.Monad m) =>
             Traversable__Node_sequence ;
           Data.Traversable.sequenceA__ := fun (f : Type -> Type)
           (a : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__Node_sequenceA ;
           Data.Traversable.traverse__ := fun (f : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__Node_traverse |}.

#[global] Definition intervalUnion {v} `{GHC.Base.Ord v}
   : IntInterval v -> IntInterval v -> IntInterval v :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoInterval, i => i
    | i, NoInterval => i
    | MkIntInterval _ hi1, MkIntInterval int2 hi2 =>
        MkIntInterval int2 (GHC.Base.max hi1 hi2)
    end.

#[local] Definition Semigroup__IntInterval_op_zlzlzgzg__ {inst_v : Type}
  `{GHC.Base.Ord inst_v}
   : IntInterval inst_v -> IntInterval inst_v -> IntInterval inst_v :=
  intervalUnion.

#[global]
Program Instance Semigroup__IntInterval {v : Type} `{GHC.Base.Ord v}
   : GHC.Base.Semigroup (IntInterval v) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__IntInterval_op_zlzlzgzg__ |}.

#[local] Definition Monoid__IntInterval_mappend {inst_v : Type} `{GHC.Base.Ord
  inst_v}
   : IntInterval inst_v -> IntInterval inst_v -> IntInterval inst_v :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__IntInterval_mempty {inst_v : Type} `{GHC.Base.Ord
  inst_v}
   : IntInterval inst_v :=
  NoInterval.

#[local] Definition Monoid__IntInterval_mconcat {inst_v : Type} `{GHC.Base.Ord
  inst_v}
   : list (IntInterval inst_v) -> IntInterval inst_v :=
  GHC.Base.foldr Monoid__IntInterval_mappend Monoid__IntInterval_mempty.

#[global]
Program Instance Monoid__IntInterval {v : Type} `{GHC.Base.Ord v}
   : GHC.Base.Monoid (IntInterval v) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__IntInterval_mappend ;
           GHC.Base.mconcat__ := Monoid__IntInterval_mconcat ;
           GHC.Base.mempty__ := Monoid__IntInterval_mempty |}.

#[global] Definition high {v : Type} : Interval v -> v :=
  fun '(MkInterval _ hi) => hi.

#[local] Definition Measured__IntInterval__Node_measure {inst_v : Type} {inst_a
   : Type} `{(GHC.Base.Ord inst_v)}
   : Node inst_v inst_a -> IntInterval inst_v :=
  fun '(MkNode i _) => MkIntInterval i (high i).

#[global]
Program Instance Measured__IntInterval__Node {v : Type} {a : Type}
  `{(GHC.Base.Ord v)}
   : Data.FingerTree.Measured (IntInterval v) (Node v a) :=
  fun _ k__ =>
    k__ {| Data.FingerTree.measure__ := Measured__IntInterval__Node_measure |}.

#[local] Definition Functor__IntervalMap_fmap {inst_v : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> IntervalMap inst_v a -> IntervalMap inst_v b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, MkIntervalMap t =>
          MkIntervalMap (Data.FingerTree.unsafeFmap (GHC.Base.fmap f) t)
      end.

#[local] Definition Functor__IntervalMap_op_zlzd__ {inst_v : Type}
   : forall {a : Type},
     forall {b : Type}, a -> IntervalMap inst_v b -> IntervalMap inst_v a :=
  fun {a : Type} {b : Type} =>
    Functor__IntervalMap_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__IntervalMap {v : Type}
   : GHC.Base.Functor (IntervalMap v) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) =>
             Functor__IntervalMap_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__IntervalMap_op_zlzd__ |}.

#[local] Definition Foldable__IntervalMap_foldMap {inst_v : Type}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> IntervalMap inst_v a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, MkIntervalMap t =>
          Data.Foldable.foldMap (fun (x : Node inst_v a) => Data.Foldable.foldMap f x) t
      end.

#[local] Definition Foldable__IntervalMap_fold {inst_v : Type}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, IntervalMap inst_v m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} =>
    Foldable__IntervalMap_foldMap GHC.Base.id.

#[local] Definition Foldable__IntervalMap_foldr {inst_v : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> IntervalMap inst_v a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__IntervalMap_foldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__IntervalMap_foldl' {inst_v : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> IntervalMap inst_v a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__IntervalMap_foldr (fun arg_0__ arg_1__ =>
                                       match arg_0__, arg_1__ with
                                       | x, k => (fun '(z) => GHC.Prim.seq z (k (f z x)))
                                       end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__IntervalMap_foldMap' {inst_v : Type}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> IntervalMap inst_v a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__IntervalMap_foldl' (fun acc a => acc GHC.Base.<<>> f a)
      GHC.Base.mempty.

#[local] Definition Foldable__IntervalMap_foldl {inst_v : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> IntervalMap inst_v a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__IntervalMap_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                      (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                       GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__IntervalMap_foldr' {inst_v : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> IntervalMap inst_v a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__IntervalMap_foldl (fun arg_0__ arg_1__ =>
                                       match arg_0__, arg_1__ with
                                       | k, x => (fun '(z) => GHC.Prim.seq z (k (f x z)))
                                       end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__IntervalMap_length {inst_v : Type}
   : forall {a : Type}, IntervalMap inst_v a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__IntervalMap_foldl' (fun arg_0__ arg_1__ =>
                                    match arg_0__, arg_1__ with
                                    | c, _ => c GHC.Num.+ #1
                                    end) #0.

#[local] Definition Foldable__IntervalMap_null {inst_v : Type}
   : forall {a : Type}, IntervalMap inst_v a -> bool :=
  fun {a : Type} => fun '(MkIntervalMap t) => Data.FingerTree.null t.

#[local] Definition Foldable__IntervalMap_product {inst_v : Type}
   : forall {a : Type}, forall `{GHC.Num.Num a}, IntervalMap inst_v a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getProduct
                                   (Foldable__IntervalMap_foldMap' Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__IntervalMap_sum {inst_v : Type}
   : forall {a : Type}, forall `{GHC.Num.Num a}, IntervalMap inst_v a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getSum
                                   (Foldable__IntervalMap_foldMap' Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__IntervalMap_toList {inst_v : Type}
   : forall {a : Type}, IntervalMap inst_v a -> list a :=
  fun {a : Type} =>
    fun t =>
      GHC.Base.build' (fun _ => (fun c n => Foldable__IntervalMap_foldr c n t)).

#[global]
Program Instance Foldable__IntervalMap {v : Type}
   : Data.Foldable.Foldable (IntervalMap v) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Foldable__IntervalMap_fold ;
           Data.Foldable.foldMap__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__IntervalMap_foldMap ;
           Data.Foldable.foldMap'__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__IntervalMap_foldMap' ;
           Data.Foldable.foldl__ := fun (b : Type) (a : Type) =>
             Foldable__IntervalMap_foldl ;
           Data.Foldable.foldl'__ := fun (b : Type) (a : Type) =>
             Foldable__IntervalMap_foldl' ;
           Data.Foldable.foldr__ := fun (a : Type) (b : Type) =>
             Foldable__IntervalMap_foldr ;
           Data.Foldable.foldr'__ := fun (a : Type) (b : Type) =>
             Foldable__IntervalMap_foldr' ;
           Data.Foldable.length__ := fun (a : Type) => Foldable__IntervalMap_length ;
           Data.Foldable.null__ := fun (a : Type) => Foldable__IntervalMap_null ;
           Data.Foldable.product__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__IntervalMap_product ;
           Data.Foldable.sum__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__IntervalMap_sum ;
           Data.Foldable.toList__ := fun (a : Type) => Foldable__IntervalMap_toList |}.

#[local] Definition Traversable__IntervalMap_traverse {inst_v : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> IntervalMap inst_v a -> f (IntervalMap inst_v b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, MkIntervalMap t =>
          Data.Functor.op_zlzdzg__ MkIntervalMap (Data.FingerTree.unsafeTraverse
                                    (Data.Traversable.traverse f) t)
      end.

#[local] Definition Traversable__IntervalMap_mapM {inst_v : Type}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> IntervalMap inst_v a -> m (IntervalMap inst_v b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__IntervalMap_traverse.

#[local] Definition Traversable__IntervalMap_sequenceA {inst_v : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     IntervalMap inst_v (f a) -> f (IntervalMap inst_v a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__IntervalMap_traverse GHC.Base.id.

#[local] Definition Traversable__IntervalMap_sequence {inst_v : Type}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     IntervalMap inst_v (m a) -> m (IntervalMap inst_v a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__IntervalMap_sequenceA.

#[global]
Program Instance Traversable__IntervalMap {v : Type}
   : Data.Traversable.Traversable (IntervalMap v) :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun (m : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Monad m) =>
             Traversable__IntervalMap_mapM ;
           Data.Traversable.sequence__ := fun (m : Type -> Type)
           (a : Type)
           `(GHC.Base.Monad m) =>
             Traversable__IntervalMap_sequence ;
           Data.Traversable.sequenceA__ := fun (f : Type -> Type)
           (a : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__IntervalMap_sequenceA ;
           Data.Traversable.traverse__ := fun (f : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__IntervalMap_traverse |}.

#[local] Definition Eq___IntervalMap_op_zeze__ {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Eq_ inst_v} `{GHC.Base.Eq_ inst_a}
   : IntervalMap inst_v inst_a -> IntervalMap inst_v inst_a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkIntervalMap xs, MkIntervalMap ys =>
        Data.Foldable.toList xs GHC.Base.== Data.Foldable.toList ys
    end.

#[local] Definition Eq___IntervalMap_op_zsze__ {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Eq_ inst_v} `{GHC.Base.Eq_ inst_a}
   : IntervalMap inst_v inst_a -> IntervalMap inst_v inst_a -> bool :=
  fun x y => negb (Eq___IntervalMap_op_zeze__ x y).

#[global]
Program Instance Eq___IntervalMap {v : Type} {a : Type} `{GHC.Base.Eq_ v}
  `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (IntervalMap v a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___IntervalMap_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___IntervalMap_op_zsze__ |}.

#[local] Definition Ord__IntervalMap_compare {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_v} `{GHC.Base.Ord inst_a}
   : IntervalMap inst_v inst_a -> IntervalMap inst_v inst_a -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkIntervalMap xs, MkIntervalMap ys =>
        GHC.Base.compare (Data.Foldable.toList xs) (Data.Foldable.toList ys)
    end.

#[local] Definition Ord__IntervalMap_op_zl__ {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_v} `{GHC.Base.Ord inst_a}
   : IntervalMap inst_v inst_a -> IntervalMap inst_v inst_a -> bool :=
  fun x y => Ord__IntervalMap_compare x y GHC.Base.== Lt.

#[local] Definition Ord__IntervalMap_op_zlze__ {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_v} `{GHC.Base.Ord inst_a}
   : IntervalMap inst_v inst_a -> IntervalMap inst_v inst_a -> bool :=
  fun x y => Ord__IntervalMap_compare x y GHC.Base./= Gt.

#[local] Definition Ord__IntervalMap_op_zg__ {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_v} `{GHC.Base.Ord inst_a}
   : IntervalMap inst_v inst_a -> IntervalMap inst_v inst_a -> bool :=
  fun x y => Ord__IntervalMap_compare x y GHC.Base.== Gt.

#[local] Definition Ord__IntervalMap_op_zgze__ {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_v} `{GHC.Base.Ord inst_a}
   : IntervalMap inst_v inst_a -> IntervalMap inst_v inst_a -> bool :=
  fun x y => Ord__IntervalMap_compare x y GHC.Base./= Lt.

#[local] Definition Ord__IntervalMap_max {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_v} `{GHC.Base.Ord inst_a}
   : IntervalMap inst_v inst_a ->
     IntervalMap inst_v inst_a -> IntervalMap inst_v inst_a :=
  fun x y => if Ord__IntervalMap_op_zlze__ x y : bool then y else x.

#[local] Definition Ord__IntervalMap_min {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_v} `{GHC.Base.Ord inst_a}
   : IntervalMap inst_v inst_a ->
     IntervalMap inst_v inst_a -> IntervalMap inst_v inst_a :=
  fun x y => if Ord__IntervalMap_op_zlze__ x y : bool then x else y.

#[global]
Program Instance Ord__IntervalMap {v : Type} {a : Type} `{GHC.Base.Ord v}
  `{GHC.Base.Ord a}
   : GHC.Base.Ord (IntervalMap v a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__IntervalMap_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__IntervalMap_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__IntervalMap_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__IntervalMap_op_zgze__ ;
           GHC.Base.compare__ := Ord__IntervalMap_compare ;
           GHC.Base.max__ := Ord__IntervalMap_max ;
           GHC.Base.min__ := Ord__IntervalMap_min |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.IntervalMap.FingerTree.Show__IntervalMap' *)

#[global] Program Definition union {v : Type} {a : Type} `{GHC.Base.Ord v}
   : IntervalMap v a -> IntervalMap v a -> IntervalMap v a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkIntervalMap xs, MkIntervalMap ys =>
        let merge1 :=
          HsToRocq.Wf.wfFix2 Corelib.Init.Peano.lt (fun as_ bs => interval_measure as_ bs)
                             _ (fun as_ bs merge1 =>
                                match Data.FingerTree.viewl as_ with
                                | Data.FingerTree.EmptyL => bs
                                | Data.FingerTree.op_ZCzl__ (MkNode inlined_13__ _ as inlined_11__)
                                inlined_12__ =>
                                    let inlined_16__ :=
                                      fun inlined_14__ =>
                                        match inlined_14__ with
                                        | MkIntInterval inlined_15__ _ => inlined_15__ GHC.Base.>= inlined_13__
                                        | NoInterval => GHC.Err.error (GHC.Base.hs_string__ "larger NoInterval")
                                        end in
                                    let 'pair inlined_17__ inlined_18__ := Data.FingerTree.split inlined_16__ bs in
                                    inlined_17__ Data.FingerTree.><
                                    Data.FingerTree.consTree inlined_11__ ((match Data.FingerTree.viewl
                                                                                    (inlined_18__ : Data.FingerTree.FingerTree
                                                                                     (IntInterval v) (Node v a)) with
                                                               | Data.FingerTree.EmptyL =>
                                                                   inlined_12__ : (@Data.FingerTree.FingerTree
                                                                    (IntInterval v) (Node v a))
                                                               | Data.FingerTree.op_ZCzl__ (MkNode inlined_23__
                                                                _ as inlined_21__) inlined_22__ =>
                                                                   let inlined_26__ :=
                                                                     fun inlined_24__ =>
                                                                       match inlined_24__ with
                                                                       | MkIntInterval inlined_25__ _ =>
                                                                           inlined_25__ GHC.Base.> inlined_23__
                                                                       | NoInterval =>
                                                                           GHC.Err.error (GHC.Base.hs_string__
                                                                                          "larger NoInterval")
                                                                       end in
                                                                   let 'pair inlined_27__ inlined_28__ :=
                                                                     Data.FingerTree.split inlined_26__
                                                                       (inlined_12__ : (@Data.FingerTree.FingerTree
                                                                         (IntInterval v) (Node v a))) in
                                                                   inlined_27__ Data.FingerTree.><
                                                                   Data.FingerTree.consTree inlined_21__ (merge1
                                                                                             inlined_28__ inlined_22__)
                                                               end) : Data.FingerTree.FingerTree (IntInterval v) (Node v
                                                                                                                       a))
                                end) in
        let merge2
         : (@Data.FingerTree.FingerTree (IntInterval v) (Node v a)) ->
           Data.FingerTree.FingerTree (IntInterval v) (Node v a) ->
           Data.FingerTree.FingerTree (IntInterval v) (Node v a) :=
          fun as_ bs =>
            match Data.FingerTree.viewl bs with
            | Data.FingerTree.EmptyL => as_
            | Data.FingerTree.op_ZCzl__ (MkNode i _ as b) bs' =>
                let larger :=
                  fun arg_12__ =>
                    match arg_12__ with
                    | MkIntInterval k _ => k GHC.Base.> i
                    | NoInterval => GHC.Err.error (GHC.Base.hs_string__ "larger NoInterval")
                    end in
                let 'pair l r := Data.FingerTree.split larger as_ in
                l Data.FingerTree.>< Data.FingerTree.consTree b (merge1 r bs')
            end in
        MkIntervalMap (merge1 xs ys)
    end.
Solve Obligations with (interval_union_termination).

#[local] Definition Semigroup__IntervalMap_op_zlzlzgzg__ {inst_v : Type} {inst_a
   : Type} `{(GHC.Base.Ord inst_v)}
   : IntervalMap inst_v inst_a ->
     IntervalMap inst_v inst_a -> IntervalMap inst_v inst_a :=
  union.

#[global]
Program Instance Semigroup__IntervalMap {v : Type} {a : Type} `{(GHC.Base.Ord
   v)}
   : GHC.Base.Semigroup (IntervalMap v a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__IntervalMap_op_zlzlzgzg__ |}.

#[local] Definition Monoid__IntervalMap_mappend {inst_v : Type} {inst_a : Type}
  `{(GHC.Base.Ord inst_v)}
   : IntervalMap inst_v inst_a ->
     IntervalMap inst_v inst_a -> IntervalMap inst_v inst_a :=
  _GHC.Base.<<>>_.

#[global] Definition empty {v : Type} {a : Type} `{GHC.Base.Ord v}
   : IntervalMap v a :=
  MkIntervalMap Data.FingerTree.empty.

#[local] Definition Monoid__IntervalMap_mempty {inst_v : Type} {inst_a : Type}
  `{(GHC.Base.Ord inst_v)}
   : IntervalMap inst_v inst_a :=
  empty.

#[local] Definition Monoid__IntervalMap_mconcat {inst_v : Type} {inst_a : Type}
  `{(GHC.Base.Ord inst_v)}
   : list (IntervalMap inst_v inst_a) -> IntervalMap inst_v inst_a :=
  GHC.Base.foldr Monoid__IntervalMap_mappend Monoid__IntervalMap_mempty.

#[global]
Program Instance Monoid__IntervalMap {v : Type} {a : Type} `{(GHC.Base.Ord v)}
   : GHC.Base.Monoid (IntervalMap v a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__IntervalMap_mappend ;
           GHC.Base.mconcat__ := Monoid__IntervalMap_mconcat ;
           GHC.Base.mempty__ := Monoid__IntervalMap_mempty |}.

#[global] Definition low {v : Type} : Interval v -> v :=
  fun '(MkInterval lo _) => lo.

#[global] Definition point {v : Type} : v -> Interval v :=
  fun v => MkInterval v v.

#[global] Definition singleton {v : Type} {a : Type} `{GHC.Base.Ord v}
   : Interval v -> a -> IntervalMap v a :=
  fun i x => MkIntervalMap (Data.FingerTree.singleton (MkNode i x)).

#[global] Definition insert {v : Type} {a : Type} `{GHC.Base.Ord v}
   : Interval v -> a -> IntervalMap v a -> IntervalMap v a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | MkInterval lo hi, _, m =>
        if lo GHC.Base.> hi : bool then m else
        match arg_0__, arg_1__, arg_2__ with
        | i, x, MkIntervalMap t =>
            let larger :=
              fun arg_3__ =>
                match arg_3__ with
                | MkIntInterval k _ => k GHC.Base.>= i
                | NoInterval => GHC.Err.error (GHC.Base.hs_string__ "larger NoInterval")
                end in
            let 'pair l r := Data.FingerTree.split larger t in
            MkIntervalMap (l Data.FingerTree.>< Data.FingerTree.consTree (MkNode i x) r)
        end
    end.

#[global] Definition atleast {v} `{(GHC.Base.Ord v)}
   : v -> IntInterval v -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | k, MkIntInterval _ hi => k GHC.Base.<= hi
    | _, NoInterval => GHC.Err.error (GHC.Base.hs_string__ "atleast NoInterval")
    end.

#[global] Definition greater {v} `{(GHC.Base.Ord v)}
   : v -> IntInterval v -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | k, MkIntInterval i _ => low i GHC.Base.> k
    | _, NoInterval => GHC.Err.error (GHC.Base.hs_string__ "greater NoInterval")
    end.

#[global] Program Definition inRange {v} {a} `{(GHC.Base.Ord v)}
   : v -> v -> IntervalMap v a -> list (Interval v * a)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | lo, hi, MkIntervalMap t =>
        let matches
         : Data.FingerTree.FingerTree (IntInterval v) (Node v a) ->
           list (prod (Interval v) a) :=
          HsToRocq.Wf.wfFix1 Corelib.Init.Peano.lt (fun (xs
                                : Data.FingerTree.FingerTree (IntInterval v) (Node v a)) =>
                                size xs) _ (fun (xs : Data.FingerTree.FingerTree (IntInterval v) (Node v a))
                              matches =>
                                match Data.FingerTree.viewl (Data.FingerTree.dropUntil (atleast lo) xs) with
                                | Data.FingerTree.EmptyL => nil
                                | Data.FingerTree.op_ZCzl__ (MkNode i x) xs' => cons (pair i x) (matches xs')
                                end) in
        matches (Data.FingerTree.takeUntil (greater hi) t)
    end.
Solve Obligations with (interval_inRange_termination).

#[global] Definition intersections {v : Type} {a : Type} `{GHC.Base.Ord v}
   : Interval v -> IntervalMap v a -> list (Interval v * a)%type :=
  fun i => inRange (low i) (high i).

#[global] Definition dominators {v : Type} {a : Type} `{GHC.Base.Ord v}
   : Interval v -> IntervalMap v a -> list (Interval v * a)%type :=
  fun i => inRange (high i) (low i).

#[global] Definition search {v : Type} {a : Type} `{GHC.Base.Ord v}
   : v -> IntervalMap v a -> list (Interval v * a)%type :=
  fun p => inRange p p.

#[global] Definition bounds {v : Type} {a : Type} `{GHC.Base.Ord v}
   : IntervalMap v a -> option (Interval v) :=
  fun '(MkIntervalMap t) =>
    match Data.FingerTree.measure t with
    | NoInterval => None
    | MkIntInterval _ hi =>
        match Data.FingerTree.viewl t with
        | Data.FingerTree.EmptyL => None
        | Data.FingerTree.op_ZCzl__ (MkNode (MkInterval lo _) _) _ =>
            Some (MkInterval lo hi)
        end
    end.

#[global] Definition leastView {v : Type} {a : Type} `{GHC.Base.Ord v}
   : IntervalMap v a -> option ((Interval v * a)%type * IntervalMap v a)%type :=
  fun '(MkIntervalMap t) =>
    match Data.FingerTree.viewl t with
    | Data.FingerTree.EmptyL => None
    | Data.FingerTree.op_ZCzl__ (MkNode i a) t' =>
        Some (pair (pair i a) (MkIntervalMap t'))
    end.

#[global] Definition splitAfter {v : Type} {a : Type} `{GHC.Base.Ord v}
   : v -> IntervalMap v a -> (IntervalMap v a * IntervalMap v a)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | k, MkIntervalMap t =>
        let 'pair before after := Data.FingerTree.split (greater k) t in
        pair (MkIntervalMap before) (MkIntervalMap after)
    end.

(* External variables:
     Eq Gt Lt None Some Type andb bool comparison cons false interval_measure list
     negb nil op_zt__ option pair prod size true Corelib.Init.Peano.lt
     Corelib.Program.Basics.compose Data.FingerTree.EmptyL Data.FingerTree.FingerTree
     Data.FingerTree.Measured Data.FingerTree.consTree Data.FingerTree.dropUntil
     Data.FingerTree.empty Data.FingerTree.measure Data.FingerTree.measure__
     Data.FingerTree.null Data.FingerTree.op_ZCzl__ Data.FingerTree.op_zgzl__
     Data.FingerTree.singleton Data.FingerTree.split Data.FingerTree.takeUntil
     Data.FingerTree.unsafeFmap Data.FingerTree.unsafeTraverse Data.FingerTree.viewl
     Data.Foldable.Foldable Data.Foldable.foldMap Data.Foldable.foldMap'__
     Data.Foldable.foldMap__ Data.Foldable.fold__ Data.Foldable.foldl'__
     Data.Foldable.foldl__ Data.Foldable.foldr'__ Data.Foldable.foldr__
     Data.Foldable.length__ Data.Foldable.null__ Data.Foldable.product__
     Data.Foldable.sum__ Data.Foldable.toList Data.Foldable.toList__
     Data.Functor.op_zlzdzg__ Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Endo Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.appEndo
     Data.SemigroupInternal.getDual Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum Data.Traversable.Traversable
     Data.Traversable.mapM__ Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.Semigroup GHC.Base.build' GHC.Base.compare GHC.Base.compare__
     GHC.Base.const GHC.Base.flip GHC.Base.fmap GHC.Base.fmap__ GHC.Base.foldr
     GHC.Base.id GHC.Base.mappend__ GHC.Base.max GHC.Base.max__ GHC.Base.mconcat__
     GHC.Base.mempty GHC.Base.mempty__ GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg__ GHC.Base.op_zg____
     GHC.Base.op_zgze__ GHC.Base.op_zgze____ GHC.Base.op_zl__ GHC.Base.op_zl____
     GHC.Base.op_zlzd____ GHC.Base.op_zlze__ GHC.Base.op_zlze____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Base.op_zsze__
     GHC.Base.op_zsze____ GHC.Err.error GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger
     GHC.Num.op_zp__ GHC.Prim.seq HsToRocq.Wf.wfFix1 HsToRocq.Wf.wfFix2
*)
