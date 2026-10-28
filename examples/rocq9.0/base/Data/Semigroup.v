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

Require Corelib.Program.Basics.
Require Data.Bifoldable.
Require Data.Bifunctor.
Require Data.Bitraversable.
Require Data.Foldable.
Require Data.Functor.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require HsToRocq.Unpeel.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive WrappedMonoid m : Type :=
  | WrapMonoid (unwrapMonoid : m) : WrappedMonoid m.

Inductive Min a : Type := | Mk_Min (getMin : a) : Min a.

Inductive Max a : Type := | Mk_Max (getMax : a) : Max a.

Inductive Last a : Type := | Mk_Last (getLast : a) : Last a.

Inductive First a : Type := | Mk_First (getFirst : a) : First a.

Inductive Arg a b : Type := | Mk_Arg : a -> b -> Arg a b.

#[global] Definition ArgMax a b :=
  (Max (Arg a b))%type.

#[global] Definition ArgMin a b :=
  (Min (Arg a b))%type.

Arguments WrapMonoid {_} _.

Arguments Mk_Min {_} _.

Arguments Mk_Max {_} _.

Arguments Mk_Last {_} _.

Arguments Mk_First {_} _.

Arguments Mk_Arg {_} {_} _ _.

#[global] Definition unwrapMonoid {m} (arg_0__ : WrappedMonoid m) :=
  let 'WrapMonoid unwrapMonoid := arg_0__ in
  unwrapMonoid.

#[global] Definition getMin {a} (arg_0__ : Min a) :=
  let 'Mk_Min getMin := arg_0__ in
  getMin.

#[global] Definition getMax {a} (arg_0__ : Max a) :=
  let 'Mk_Max getMax := arg_0__ in
  getMax.

#[global] Definition getLast {a} (arg_0__ : Last a) :=
  let 'Mk_Last getLast := arg_0__ in
  getLast.

#[global] Definition getFirst {a} (arg_0__ : First a) :=
  let 'Mk_First getFirst := arg_0__ in
  getFirst.

(* Midamble *)

Require Data.List.NonEmpty.

Definition sconcat {a} `{GHC.Base.Semigroup a} : GHC.Base.NonEmpty a -> a :=
  Data.List.NonEmpty.NonEmpty_foldr1 (@GHC.Base.op_zlzlzgzg__ a _).

(* ------------------------- *)

(* These two instances are here because we don't mangle the instance names
   enough. This file creates instances for Monoid.First and Semigroup.First
   (which are different types.) But we produce the same names for them.
*)

Local Definition Semigroup__SFirst_op_zlzlzgzg__ {inst_a} : (First inst_a) -> (First
                                                       inst_a) -> (First inst_a) :=
  fun arg_0__ arg_1__ => match arg_0__ , arg_1__ with | a , _ => a end.

Local Definition Semigroup__SFirst_sconcat {inst_a} : GHC.Base.NonEmpty
                                                     (First inst_a) -> (First inst_a) :=
  fun arg_0__ =>
    match arg_0__ with
      | GHC.Base.NEcons a as_ => let fix go arg_1__ arg_2__
                                                     := match arg_1__ , arg_2__ with
                                                          | b , cons c cs => Semigroup__SFirst_op_zlzlzgzg__ b (go c cs)
                                                          | b , nil => b
                                                        end in
                                           go a as_
    end.



Program Instance Semigroup__SFirst {a} : GHC.Base.Semigroup (First a) := fun _ k =>
    k {| GHC.Base.op_zlzlzgzg____ := Semigroup__SFirst_op_zlzlzgzg__ |}.

Local Definition Semigroup__SLast_op_zlzlzgzg__ {inst_a} : (Last inst_a) -> (Last
                                                      inst_a) -> (Last inst_a) :=
  fun arg_0__ arg_1__ => match arg_0__ , arg_1__ with | _ , b => b end.

Local Definition Semigroup__SLast_sconcat {inst_a} : GHC.Base.NonEmpty
                                                    (Last inst_a) -> (Last inst_a) :=
  fun arg_0__ =>
    match arg_0__ with
      | GHC.Base.NEcons a as_ => let fix go arg_1__ arg_2__
                                                     := match arg_1__ , arg_2__ with
                                                          | b , cons c cs => Semigroup__SLast_op_zlzlzgzg__ b (go c cs)
                                                          | b , nil => b
                                                        end in
                                           go a as_
    end.


Program Instance Semigroup__SLast {a} : GHC.Base.Semigroup (Last a) := fun _ k =>
    k {| GHC.Base.op_zlzlzgzg____ := Semigroup__SLast_op_zlzlzgzg__ |}.

(* ------------------------- *)

(* Converted value declarations: *)

(* Skipping all instances of class `GHC.Enum.Enum', including
   `Data.Semigroup.Enum__Min' *)

#[local] Definition Semigroup__Min_op_zlzlzgzg__ {inst_a : Type} `{GHC.Base.Ord
  inst_a}
   : Min inst_a -> Min inst_a -> Min inst_a :=
  fun arg_0__ arg_1__ => Mk_Min (GHC.Base.min (getMin arg_0__) (getMin arg_1__)).

#[global]
Program Instance Semigroup__Min {a : Type} `{GHC.Base.Ord a}
   : GHC.Base.Semigroup (Min a) :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Min_op_zlzlzgzg__ |}.

(* Skipping instance `Data.Semigroup.Monoid__Min' of class `GHC.Base.Monoid' *)

#[local] Definition Functor__Min_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Min a -> Min b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Min x => Mk_Min (f x)
      end.

#[local] Definition Functor__Min_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> Min b -> Min a :=
  fun {a : Type} {b : Type} => Functor__Min_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__Min : GHC.Base.Functor Min :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Min_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) => Functor__Min_op_zlzd__ |}.

#[local] Definition Foldable__Min_foldMap
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> Min a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, Mk_Min a => f a end.

#[local] Definition Foldable__Min_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Min m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Min_foldMap GHC.Base.id.

#[local] Definition Foldable__Min_foldr
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> Min a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Min_foldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__Min_foldl'
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> Min a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__Min_foldr (fun arg_0__ arg_1__ =>
                               match arg_0__, arg_1__ with
                               | x, k => (fun '(z) => GHC.Prim.seq z (k (f z x)))
                               end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__Min_foldMap'
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> Min a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Min_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Min_foldl
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> Min a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Min_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                              (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                               GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__Min_foldr'
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> Min a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__Min_foldl (fun arg_0__ arg_1__ =>
                               match arg_0__, arg_1__ with
                               | k, x => (fun '(z) => GHC.Prim.seq z (k (f x z)))
                               end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__Min_length
   : forall {a : Type}, Min a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__Min_foldl' (fun arg_0__ arg_1__ =>
                            match arg_0__, arg_1__ with
                            | c, _ => c GHC.Num.+ #1
                            end) #0.

#[local] Definition Foldable__Min_null : forall {a : Type}, Min a -> bool :=
  fun {a : Type} => Foldable__Min_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__Min_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, Min a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getProduct
                                   (Foldable__Min_foldMap' Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__Min_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, Min a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getSum
                                   (Foldable__Min_foldMap' Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__Min_toList : forall {a : Type}, Min a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Min_foldr c n t)).

#[global]
Program Instance Foldable__Min : Data.Foldable.Foldable Min :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Foldable__Min_fold ;
           Data.Foldable.foldMap__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Min_foldMap ;
           Data.Foldable.foldMap'__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Min_foldMap' ;
           Data.Foldable.foldl__ := fun (b : Type) (a : Type) => Foldable__Min_foldl ;
           Data.Foldable.foldl'__ := fun (b : Type) (a : Type) => Foldable__Min_foldl' ;
           Data.Foldable.foldr__ := fun (a : Type) (b : Type) => Foldable__Min_foldr ;
           Data.Foldable.foldr'__ := fun (a : Type) (b : Type) => Foldable__Min_foldr' ;
           Data.Foldable.length__ := fun (a : Type) => Foldable__Min_length ;
           Data.Foldable.null__ := fun (a : Type) => Foldable__Min_null ;
           Data.Foldable.product__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__Min_product ;
           Data.Foldable.sum__ := fun (a : Type) `(GHC.Num.Num a) => Foldable__Min_sum ;
           Data.Foldable.toList__ := fun (a : Type) => Foldable__Min_toList |}.

#[local] Definition Traversable__Min_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> Min a -> f (Min b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Min a => GHC.Base.fmap Mk_Min (f a)
      end.

#[local] Definition Traversable__Min_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m}, (a -> m b) -> Min a -> m (Min b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Min_traverse.

#[local] Definition Traversable__Min_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Applicative f}, Min (f a) -> f (Min a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Min_traverse GHC.Base.id.

#[local] Definition Traversable__Min_sequence
   : forall {m : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Monad m}, Min (m a) -> m (Min a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Min_sequenceA.

#[global]
Program Instance Traversable__Min : Data.Traversable.Traversable Min :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun (m : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Monad m) =>
             Traversable__Min_mapM ;
           Data.Traversable.sequence__ := fun (m : Type -> Type)
           (a : Type)
           `(GHC.Base.Monad m) =>
             Traversable__Min_sequence ;
           Data.Traversable.sequenceA__ := fun (f : Type -> Type)
           (a : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__Min_sequenceA ;
           Data.Traversable.traverse__ := fun (f : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__Min_traverse |}.

#[local] Definition Applicative__Min_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Min a -> Min b -> Min c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      Mk_Min (arg_0__ (getMin arg_1__) (getMin arg_2__)).

#[local] Definition Applicative__Min_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, Min (a -> b) -> Min a -> Min b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Min (getMin arg_0__ (getMin arg_1__)).

#[local] Definition Applicative__Min_op_ztzg__
   : forall {a : Type}, forall {b : Type}, Min a -> Min b -> Min b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, a => a end.

#[local] Definition Applicative__Min_pure : forall {a : Type}, a -> Min a :=
  fun {a : Type} => Mk_Min.

#[global]
Program Instance Applicative__Min : GHC.Base.Applicative Min :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__Min_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Min_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Min_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__Min_pure |}.

#[local] Definition Monad__Min_op_zgzg__
   : forall {a : Type}, forall {b : Type}, Min a -> Min b -> Min b :=
  fun {a : Type} {b : Type} => _GHC.Base.*>_.

#[local] Definition Monad__Min_op_zgzgze__
   : forall {a : Type}, forall {b : Type}, Min a -> (a -> Min b) -> Min b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | Mk_Min a, f => f a end.

#[local] Definition Monad__Min_return_ : forall {a : Type}, a -> Min a :=
  fun {a : Type} => GHC.Base.pure.

#[global]
Program Instance Monad__Min : GHC.Base.Monad Min :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__Min_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) => Monad__Min_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__Min_return_ |}.

(* Skipping all instances of class `GHC.Internal.Control.Monad.Fix.MonadFix',
   including `Data.Semigroup.MonadFix__Min' *)

(* Skipping all instances of class `GHC.Num.Num', including
   `Data.Semigroup.Num__Min' *)

(* Skipping all instances of class `GHC.Enum.Enum', including
   `Data.Semigroup.Enum__Max' *)

#[local] Definition Semigroup__Max_op_zlzlzgzg__ {inst_a : Type} `{GHC.Base.Ord
  inst_a}
   : Max inst_a -> Max inst_a -> Max inst_a :=
  fun arg_0__ arg_1__ => Mk_Max (GHC.Base.max (getMax arg_0__) (getMax arg_1__)).

#[global]
Program Instance Semigroup__Max {a : Type} `{GHC.Base.Ord a}
   : GHC.Base.Semigroup (Max a) :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Max_op_zlzlzgzg__ |}.

(* Skipping instance `Data.Semigroup.Monoid__Max' of class `GHC.Base.Monoid' *)

#[local] Definition Functor__Max_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Max a -> Max b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Max x => Mk_Max (f x)
      end.

#[local] Definition Functor__Max_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> Max b -> Max a :=
  fun {a : Type} {b : Type} => Functor__Max_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__Max : GHC.Base.Functor Max :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Max_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) => Functor__Max_op_zlzd__ |}.

#[local] Definition Foldable__Max_foldMap
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> Max a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, Mk_Max a => f a end.

#[local] Definition Foldable__Max_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Max m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Max_foldMap GHC.Base.id.

#[local] Definition Foldable__Max_foldr
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> Max a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Max_foldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__Max_foldl'
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> Max a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__Max_foldr (fun arg_0__ arg_1__ =>
                               match arg_0__, arg_1__ with
                               | x, k => (fun '(z) => GHC.Prim.seq z (k (f z x)))
                               end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__Max_foldMap'
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> Max a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Max_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Max_foldl
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> Max a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Max_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                              (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                               GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__Max_foldr'
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> Max a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__Max_foldl (fun arg_0__ arg_1__ =>
                               match arg_0__, arg_1__ with
                               | k, x => (fun '(z) => GHC.Prim.seq z (k (f x z)))
                               end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__Max_length
   : forall {a : Type}, Max a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__Max_foldl' (fun arg_0__ arg_1__ =>
                            match arg_0__, arg_1__ with
                            | c, _ => c GHC.Num.+ #1
                            end) #0.

#[local] Definition Foldable__Max_null : forall {a : Type}, Max a -> bool :=
  fun {a : Type} => Foldable__Max_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__Max_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, Max a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getProduct
                                   (Foldable__Max_foldMap' Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__Max_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, Max a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getSum
                                   (Foldable__Max_foldMap' Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__Max_toList : forall {a : Type}, Max a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Max_foldr c n t)).

#[global]
Program Instance Foldable__Max : Data.Foldable.Foldable Max :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Foldable__Max_fold ;
           Data.Foldable.foldMap__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Max_foldMap ;
           Data.Foldable.foldMap'__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Max_foldMap' ;
           Data.Foldable.foldl__ := fun (b : Type) (a : Type) => Foldable__Max_foldl ;
           Data.Foldable.foldl'__ := fun (b : Type) (a : Type) => Foldable__Max_foldl' ;
           Data.Foldable.foldr__ := fun (a : Type) (b : Type) => Foldable__Max_foldr ;
           Data.Foldable.foldr'__ := fun (a : Type) (b : Type) => Foldable__Max_foldr' ;
           Data.Foldable.length__ := fun (a : Type) => Foldable__Max_length ;
           Data.Foldable.null__ := fun (a : Type) => Foldable__Max_null ;
           Data.Foldable.product__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__Max_product ;
           Data.Foldable.sum__ := fun (a : Type) `(GHC.Num.Num a) => Foldable__Max_sum ;
           Data.Foldable.toList__ := fun (a : Type) => Foldable__Max_toList |}.

#[local] Definition Traversable__Max_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> Max a -> f (Max b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Max a => GHC.Base.fmap Mk_Max (f a)
      end.

#[local] Definition Traversable__Max_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m}, (a -> m b) -> Max a -> m (Max b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Max_traverse.

#[local] Definition Traversable__Max_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Applicative f}, Max (f a) -> f (Max a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Max_traverse GHC.Base.id.

#[local] Definition Traversable__Max_sequence
   : forall {m : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Monad m}, Max (m a) -> m (Max a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Max_sequenceA.

#[global]
Program Instance Traversable__Max : Data.Traversable.Traversable Max :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun (m : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Monad m) =>
             Traversable__Max_mapM ;
           Data.Traversable.sequence__ := fun (m : Type -> Type)
           (a : Type)
           `(GHC.Base.Monad m) =>
             Traversable__Max_sequence ;
           Data.Traversable.sequenceA__ := fun (f : Type -> Type)
           (a : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__Max_sequenceA ;
           Data.Traversable.traverse__ := fun (f : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__Max_traverse |}.

#[local] Definition Applicative__Max_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Max a -> Max b -> Max c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      Mk_Max (arg_0__ (getMax arg_1__) (getMax arg_2__)).

#[local] Definition Applicative__Max_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, Max (a -> b) -> Max a -> Max b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Max (getMax arg_0__ (getMax arg_1__)).

#[local] Definition Applicative__Max_op_ztzg__
   : forall {a : Type}, forall {b : Type}, Max a -> Max b -> Max b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, a => a end.

#[local] Definition Applicative__Max_pure : forall {a : Type}, a -> Max a :=
  fun {a : Type} => Mk_Max.

#[global]
Program Instance Applicative__Max : GHC.Base.Applicative Max :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__Max_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Max_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Max_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__Max_pure |}.

#[local] Definition Monad__Max_op_zgzg__
   : forall {a : Type}, forall {b : Type}, Max a -> Max b -> Max b :=
  fun {a : Type} {b : Type} => _GHC.Base.*>_.

#[local] Definition Monad__Max_op_zgzgze__
   : forall {a : Type}, forall {b : Type}, Max a -> (a -> Max b) -> Max b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | Mk_Max a, f => f a end.

#[local] Definition Monad__Max_return_ : forall {a : Type}, a -> Max a :=
  fun {a : Type} => GHC.Base.pure.

#[global]
Program Instance Monad__Max : GHC.Base.Monad Max :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__Max_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) => Monad__Max_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__Max_return_ |}.

(* Skipping all instances of class `GHC.Internal.Control.Monad.Fix.MonadFix',
   including `Data.Semigroup.MonadFix__Max' *)

(* Skipping all instances of class `GHC.Num.Num', including
   `Data.Semigroup.Num__Max' *)

#[local] Definition Functor__Arg_fmap {inst_a : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> Arg inst_a a -> Arg inst_a b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Arg x a => Mk_Arg x (f a)
      end.

#[local] Definition Functor__Arg_op_zlzd__ {inst_a : Type}
   : forall {a : Type}, forall {b : Type}, a -> Arg inst_a b -> Arg inst_a a :=
  fun {a : Type} {b : Type} => Functor__Arg_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__Arg {a : Type} : GHC.Base.Functor (Arg a) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Arg_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) => Functor__Arg_op_zlzd__ |}.

#[local] Definition Foldable__Arg_foldMap {inst_a : Type}
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> Arg inst_a a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, Mk_Arg _ a => f a end.

#[local] Definition Foldable__Arg_fold {inst_a : Type}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Arg inst_a m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Arg_foldMap GHC.Base.id.

#[local] Definition Foldable__Arg_foldr {inst_a : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Arg inst_a a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Arg_foldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__Arg_foldl' {inst_a : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Arg inst_a a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__Arg_foldr (fun arg_0__ arg_1__ =>
                               match arg_0__, arg_1__ with
                               | x, k => (fun '(z) => GHC.Prim.seq z (k (f z x)))
                               end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__Arg_foldMap' {inst_a : Type}
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> Arg inst_a a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Arg_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Arg_foldl {inst_a : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Arg inst_a a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Arg_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                              (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                               GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__Arg_foldr' {inst_a : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Arg inst_a a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__Arg_foldl (fun arg_0__ arg_1__ =>
                               match arg_0__, arg_1__ with
                               | k, x => (fun '(z) => GHC.Prim.seq z (k (f x z)))
                               end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__Arg_length {inst_a : Type}
   : forall {a : Type}, Arg inst_a a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__Arg_foldl' (fun arg_0__ arg_1__ =>
                            match arg_0__, arg_1__ with
                            | c, _ => c GHC.Num.+ #1
                            end) #0.

#[local] Definition Foldable__Arg_null {inst_a : Type}
   : forall {a : Type}, Arg inst_a a -> bool :=
  fun {a : Type} => Foldable__Arg_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__Arg_product {inst_a : Type}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Arg inst_a a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getProduct
                                   (Foldable__Arg_foldMap' Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__Arg_sum {inst_a : Type}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Arg inst_a a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getSum
                                   (Foldable__Arg_foldMap' Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__Arg_toList {inst_a : Type}
   : forall {a : Type}, Arg inst_a a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Arg_foldr c n t)).

#[global]
Program Instance Foldable__Arg {a : Type} : Data.Foldable.Foldable (Arg a) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Foldable__Arg_fold ;
           Data.Foldable.foldMap__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Arg_foldMap ;
           Data.Foldable.foldMap'__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Arg_foldMap' ;
           Data.Foldable.foldl__ := fun (b : Type) (a : Type) => Foldable__Arg_foldl ;
           Data.Foldable.foldl'__ := fun (b : Type) (a : Type) => Foldable__Arg_foldl' ;
           Data.Foldable.foldr__ := fun (a : Type) (b : Type) => Foldable__Arg_foldr ;
           Data.Foldable.foldr'__ := fun (a : Type) (b : Type) => Foldable__Arg_foldr' ;
           Data.Foldable.length__ := fun (a : Type) => Foldable__Arg_length ;
           Data.Foldable.null__ := fun (a : Type) => Foldable__Arg_null ;
           Data.Foldable.product__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__Arg_product ;
           Data.Foldable.sum__ := fun (a : Type) `(GHC.Num.Num a) => Foldable__Arg_sum ;
           Data.Foldable.toList__ := fun (a : Type) => Foldable__Arg_toList |}.

#[local] Definition Traversable__Arg_traverse {inst_a : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> Arg inst_a a -> f (Arg inst_a b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Arg x a => GHC.Base.fmap (Mk_Arg x) (f a)
      end.

#[local] Definition Traversable__Arg_mapM {inst_a : Type}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m}, (a -> m b) -> Arg inst_a a -> m (Arg inst_a b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Arg_traverse.

#[local] Definition Traversable__Arg_sequenceA {inst_a : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f}, Arg inst_a (f a) -> f (Arg inst_a a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Arg_traverse GHC.Base.id.

#[local] Definition Traversable__Arg_sequence {inst_a : Type}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m}, Arg inst_a (m a) -> m (Arg inst_a a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Arg_sequenceA.

#[global]
Program Instance Traversable__Arg {a : Type}
   : Data.Traversable.Traversable (Arg a) :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun (m : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Monad m) =>
             Traversable__Arg_mapM ;
           Data.Traversable.sequence__ := fun (m : Type -> Type)
           (a : Type)
           `(GHC.Base.Monad m) =>
             Traversable__Arg_sequence ;
           Data.Traversable.sequenceA__ := fun (f : Type -> Type)
           (a : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__Arg_sequenceA ;
           Data.Traversable.traverse__ := fun (f : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__Arg_traverse |}.

#[local] Definition Eq___Arg_op_zeze__ {inst_a : Type} {inst_b : Type}
  `{GHC.Base.Eq_ inst_a}
   : Arg inst_a inst_b -> Arg inst_a inst_b -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Arg a _, Mk_Arg b _ => a GHC.Base.== b
    end.

#[local] Definition Eq___Arg_op_zsze__ {inst_a : Type} {inst_b : Type}
  `{GHC.Base.Eq_ inst_a}
   : Arg inst_a inst_b -> Arg inst_a inst_b -> bool :=
  fun x y => negb (Eq___Arg_op_zeze__ x y).

#[global]
Program Instance Eq___Arg {a : Type} {b : Type} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Arg a b) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Arg_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Arg_op_zsze__ |}.

(* Skipping instance `Data.Semigroup.Ord__Arg' of class `GHC.Base.Ord' *)

#[local] Definition Bifunctor__Arg_bimap
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     forall {d : Type}, (a -> b) -> (c -> d) -> Arg a c -> Arg b d :=
  fun {a : Type} {b : Type} {c : Type} {d : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, Mk_Arg a b => Mk_Arg (f a) (g b)
      end.

#[local] Definition Bifunctor__Arg_first
   : forall {a : Type},
     forall {b : Type}, forall {c : Type}, (a -> b) -> Arg a c -> Arg b c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f => Bifunctor__Arg_bimap f GHC.Base.id.

#[local] Definition Bifunctor__Arg_second
   : forall {b : Type},
     forall {c : Type}, forall {a : Type}, (b -> c) -> Arg a b -> Arg a c :=
  fun {b : Type} {c : Type} {a : Type} => Bifunctor__Arg_bimap GHC.Base.id.

#[global]
Program Instance Bifunctor__Arg : Data.Bifunctor.Bifunctor Arg :=
  fun _ k__ =>
    k__ {| Data.Bifunctor.bimap__ := fun (a : Type)
           (b : Type)
           (c : Type)
           (d : Type) =>
             Bifunctor__Arg_bimap ;
           Data.Bifunctor.first__ := fun (a : Type) (b : Type) (c : Type) =>
             Bifunctor__Arg_first ;
           Data.Bifunctor.second__ := fun (b : Type) (c : Type) (a : Type) =>
             Bifunctor__Arg_second |}.

#[local] Definition Bitraversable__Arg_bitraverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {c : Type},
     forall {b : Type},
     forall {d : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f c) -> (b -> f d) -> Arg a b -> f (Arg c d) :=
  fun {f : Type -> Type}
  {a : Type}
  {c : Type}
  {b : Type}
  {d : Type}
  `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, Mk_Arg a b => Data.Functor.op_zlzdzg__ Mk_Arg (f a) GHC.Base.<*> g b
      end.

#[local] Definition Bifoldable__Arg_bifoldMap
   : forall {m : Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (b -> m) -> Arg a b -> m :=
  fun {m : Type} {a : Type} {b : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, Mk_Arg a b => f a GHC.Base.<<>> g b
      end.

#[local] Definition Bifoldable__Arg_bifold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Arg m m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} =>
    Bifoldable__Arg_bifoldMap GHC.Base.id GHC.Base.id.

#[local] Definition Bifoldable__Arg_bifoldl
   : forall {c : Type},
     forall {a : Type},
     forall {b : Type}, (c -> a -> c) -> (c -> b -> c) -> c -> Arg a b -> c :=
  fun {c : Type} {a : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__Arg_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                  (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                   GHC.Base.flip f)) (Data.SemigroupInternal.Mk_Dual
                                                                                      GHC.Base.∘
                                                                                      (Data.SemigroupInternal.Mk_Endo
                                                                                       GHC.Base.∘
                                                                                       GHC.Base.flip g)) t)) z.

#[local] Definition Bifoldable__Arg_bifoldr
   : forall {a : Type},
     forall {c : Type},
     forall {b : Type}, (a -> c -> c) -> (b -> c -> c) -> c -> Arg a b -> c :=
  fun {a : Type} {c : Type} {b : Type} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__Arg_bifoldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

#[global]
Program Instance Bifoldable__Arg : Data.Bifoldable.Bifoldable Arg :=
  fun _ k__ =>
    k__ {| Data.Bifoldable.bifold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Bifoldable__Arg_bifold ;
           Data.Bifoldable.bifoldMap__ := fun (m : Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Monoid m) =>
             Bifoldable__Arg_bifoldMap ;
           Data.Bifoldable.bifoldl__ := fun (c : Type) (a : Type) (b : Type) =>
             Bifoldable__Arg_bifoldl ;
           Data.Bifoldable.bifoldr__ := fun (a : Type) (c : Type) (b : Type) =>
             Bifoldable__Arg_bifoldr |}.

#[global]
Program Instance Bitraversable__Arg : Data.Bitraversable.Bitraversable Arg :=
  fun _ k__ =>
    k__ {| Data.Bitraversable.bitraverse__ := fun (f : Type -> Type)
           (a : Type)
           (c : Type)
           (b : Type)
           (d : Type)
           `(GHC.Base.Applicative f) =>
             Bitraversable__Arg_bitraverse |}.

(* Skipping all instances of class `GHC.Enum.Enum', including
   `Data.Semigroup.Enum__First' *)

#[local] Definition Semigroup__First_op_zlzlzgzg__ {inst_a : Type}
   : First inst_a -> First inst_a -> First inst_a :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | a, _ => a end.

#[global]
Program Instance Semigroup__First {a : Type} : GHC.Base.Semigroup (First a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__First_op_zlzlzgzg__ |}.

#[local] Definition Functor__First_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> First a -> First b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_First x => Mk_First (f x)
      end.

#[local] Definition Functor__First_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> First b -> First a :=
  fun {a : Type} {b : Type} => Functor__First_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__First : GHC.Base.Functor First :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__First_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__First_op_zlzd__ |}.

#[local] Definition Foldable__First_foldMap
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> First a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, Mk_First a => f a end.

#[local] Definition Foldable__First_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, First m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__First_foldMap GHC.Base.id.

#[local] Definition Foldable__First_foldr
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> First a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__First_foldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__First_foldl'
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> First a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__First_foldr (fun arg_0__ arg_1__ =>
                                 match arg_0__, arg_1__ with
                                 | x, k => (fun '(z) => GHC.Prim.seq z (k (f z x)))
                                 end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__First_foldMap'
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> First a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__First_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__First_foldl
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> First a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__First_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                 GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__First_foldr'
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> First a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__First_foldl (fun arg_0__ arg_1__ =>
                                 match arg_0__, arg_1__ with
                                 | k, x => (fun '(z) => GHC.Prim.seq z (k (f x z)))
                                 end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__First_length
   : forall {a : Type}, First a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__First_foldl' (fun arg_0__ arg_1__ =>
                              match arg_0__, arg_1__ with
                              | c, _ => c GHC.Num.+ #1
                              end) #0.

#[local] Definition Foldable__First_null : forall {a : Type}, First a -> bool :=
  fun {a : Type} => Foldable__First_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__First_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, First a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getProduct
                                   (Foldable__First_foldMap' Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__First_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, First a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getSum
                                   (Foldable__First_foldMap' Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__First_toList
   : forall {a : Type}, First a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__First_foldr c n t)).

#[global]
Program Instance Foldable__First : Data.Foldable.Foldable First :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Foldable__First_fold ;
           Data.Foldable.foldMap__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__First_foldMap ;
           Data.Foldable.foldMap'__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__First_foldMap' ;
           Data.Foldable.foldl__ := fun (b : Type) (a : Type) => Foldable__First_foldl ;
           Data.Foldable.foldl'__ := fun (b : Type) (a : Type) => Foldable__First_foldl' ;
           Data.Foldable.foldr__ := fun (a : Type) (b : Type) => Foldable__First_foldr ;
           Data.Foldable.foldr'__ := fun (a : Type) (b : Type) => Foldable__First_foldr' ;
           Data.Foldable.length__ := fun (a : Type) => Foldable__First_length ;
           Data.Foldable.null__ := fun (a : Type) => Foldable__First_null ;
           Data.Foldable.product__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__First_product ;
           Data.Foldable.sum__ := fun (a : Type) `(GHC.Num.Num a) => Foldable__First_sum ;
           Data.Foldable.toList__ := fun (a : Type) => Foldable__First_toList |}.

#[local] Definition Traversable__First_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> First a -> f (First b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_First a => GHC.Base.fmap Mk_First (f a)
      end.

#[local] Definition Traversable__First_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m}, (a -> m b) -> First a -> m (First b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__First_traverse.

#[local] Definition Traversable__First_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f}, First (f a) -> f (First a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__First_traverse GHC.Base.id.

#[local] Definition Traversable__First_sequence
   : forall {m : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Monad m}, First (m a) -> m (First a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__First_sequenceA.

#[global]
Program Instance Traversable__First : Data.Traversable.Traversable First :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun (m : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Monad m) =>
             Traversable__First_mapM ;
           Data.Traversable.sequence__ := fun (m : Type -> Type)
           (a : Type)
           `(GHC.Base.Monad m) =>
             Traversable__First_sequence ;
           Data.Traversable.sequenceA__ := fun (f : Type -> Type)
           (a : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__First_sequenceA ;
           Data.Traversable.traverse__ := fun (f : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__First_traverse |}.

#[local] Definition Applicative__First_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> First a -> First b -> First c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      Mk_First (arg_0__ (getFirst arg_1__) (getFirst arg_2__)).

#[local] Definition Applicative__First_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, First (a -> b) -> First a -> First b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_First (getFirst arg_0__ (getFirst arg_1__)).

#[local] Definition Applicative__First_op_ztzg__
   : forall {a : Type}, forall {b : Type}, First a -> First b -> First b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, a => a end.

#[local] Definition Applicative__First_pure : forall {a : Type}, a -> First a :=
  fun {a : Type} => fun x => Mk_First x.

#[global]
Program Instance Applicative__First : GHC.Base.Applicative First :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__First_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__First_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__First_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__First_pure |}.

#[local] Definition Monad__First_op_zgzg__
   : forall {a : Type}, forall {b : Type}, First a -> First b -> First b :=
  fun {a : Type} {b : Type} => _GHC.Base.*>_.

#[local] Definition Monad__First_op_zgzgze__
   : forall {a : Type}, forall {b : Type}, First a -> (a -> First b) -> First b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | Mk_First a, f => f a end.

#[local] Definition Monad__First_return_ : forall {a : Type}, a -> First a :=
  fun {a : Type} => GHC.Base.pure.

#[global]
Program Instance Monad__First : GHC.Base.Monad First :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__First_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) =>
             Monad__First_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__First_return_ |}.

(* Skipping all instances of class `GHC.Internal.Control.Monad.Fix.MonadFix',
   including `Data.Semigroup.MonadFix__First' *)

(* Skipping all instances of class `GHC.Enum.Enum', including
   `Data.Semigroup.Enum__Last' *)

#[local] Definition Semigroup__Last_op_zlzlzgzg__ {inst_a : Type}
   : Last inst_a -> Last inst_a -> Last inst_a :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, b => b end.

#[global]
Program Instance Semigroup__Last {a : Type} : GHC.Base.Semigroup (Last a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Last_op_zlzlzgzg__ |}.

#[local] Definition Functor__Last_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Last a -> Last b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Last x => Mk_Last (f x)
      end.

#[local] Definition Functor__Last_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> Last b -> Last a :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | a, _ => Mk_Last a end.

#[global]
Program Instance Functor__Last : GHC.Base.Functor Last :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Last_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) => Functor__Last_op_zlzd__ |}.

#[local] Definition Foldable__Last_foldMap
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> Last a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, Mk_Last a => f a end.

#[local] Definition Foldable__Last_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Last m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Last_foldMap GHC.Base.id.

#[local] Definition Foldable__Last_foldr
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> Last a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Last_foldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__Last_foldl'
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> Last a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__Last_foldr (fun arg_0__ arg_1__ =>
                                match arg_0__, arg_1__ with
                                | x, k => (fun '(z) => GHC.Prim.seq z (k (f z x)))
                                end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__Last_foldMap'
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> Last a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Last_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Last_foldl
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> Last a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Last_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                               (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__Last_foldr'
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> Last a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__Last_foldl (fun arg_0__ arg_1__ =>
                                match arg_0__, arg_1__ with
                                | k, x => (fun '(z) => GHC.Prim.seq z (k (f x z)))
                                end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__Last_length
   : forall {a : Type}, Last a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__Last_foldl' (fun arg_0__ arg_1__ =>
                             match arg_0__, arg_1__ with
                             | c, _ => c GHC.Num.+ #1
                             end) #0.

#[local] Definition Foldable__Last_null : forall {a : Type}, Last a -> bool :=
  fun {a : Type} => Foldable__Last_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__Last_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, Last a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getProduct
                                   (Foldable__Last_foldMap' Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__Last_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, Last a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getSum
                                   (Foldable__Last_foldMap' Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__Last_toList
   : forall {a : Type}, Last a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Last_foldr c n t)).

#[global]
Program Instance Foldable__Last : Data.Foldable.Foldable Last :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Foldable__Last_fold ;
           Data.Foldable.foldMap__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Last_foldMap ;
           Data.Foldable.foldMap'__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Last_foldMap' ;
           Data.Foldable.foldl__ := fun (b : Type) (a : Type) => Foldable__Last_foldl ;
           Data.Foldable.foldl'__ := fun (b : Type) (a : Type) => Foldable__Last_foldl' ;
           Data.Foldable.foldr__ := fun (a : Type) (b : Type) => Foldable__Last_foldr ;
           Data.Foldable.foldr'__ := fun (a : Type) (b : Type) => Foldable__Last_foldr' ;
           Data.Foldable.length__ := fun (a : Type) => Foldable__Last_length ;
           Data.Foldable.null__ := fun (a : Type) => Foldable__Last_null ;
           Data.Foldable.product__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__Last_product ;
           Data.Foldable.sum__ := fun (a : Type) `(GHC.Num.Num a) => Foldable__Last_sum ;
           Data.Foldable.toList__ := fun (a : Type) => Foldable__Last_toList |}.

#[local] Definition Traversable__Last_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> Last a -> f (Last b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Last a => GHC.Base.fmap Mk_Last (f a)
      end.

#[local] Definition Traversable__Last_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m}, (a -> m b) -> Last a -> m (Last b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Last_traverse.

#[local] Definition Traversable__Last_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Applicative f}, Last (f a) -> f (Last a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Last_traverse GHC.Base.id.

#[local] Definition Traversable__Last_sequence
   : forall {m : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Monad m}, Last (m a) -> m (Last a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Last_sequenceA.

#[global]
Program Instance Traversable__Last : Data.Traversable.Traversable Last :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun (m : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Monad m) =>
             Traversable__Last_mapM ;
           Data.Traversable.sequence__ := fun (m : Type -> Type)
           (a : Type)
           `(GHC.Base.Monad m) =>
             Traversable__Last_sequence ;
           Data.Traversable.sequenceA__ := fun (f : Type -> Type)
           (a : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__Last_sequenceA ;
           Data.Traversable.traverse__ := fun (f : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__Last_traverse |}.

#[local] Definition Applicative__Last_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Last a -> Last b -> Last c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      Mk_Last (arg_0__ (getLast arg_1__) (getLast arg_2__)).

#[local] Definition Applicative__Last_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, Last (a -> b) -> Last a -> Last b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Last (getLast arg_0__ (getLast arg_1__)).

#[local] Definition Applicative__Last_op_ztzg__
   : forall {a : Type}, forall {b : Type}, Last a -> Last b -> Last b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, a => a end.

#[local] Definition Applicative__Last_pure : forall {a : Type}, a -> Last a :=
  fun {a : Type} => Mk_Last.

#[global]
Program Instance Applicative__Last : GHC.Base.Applicative Last :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__Last_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Last_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Last_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__Last_pure |}.

#[local] Definition Monad__Last_op_zgzg__
   : forall {a : Type}, forall {b : Type}, Last a -> Last b -> Last b :=
  fun {a : Type} {b : Type} => _GHC.Base.*>_.

#[local] Definition Monad__Last_op_zgzgze__
   : forall {a : Type}, forall {b : Type}, Last a -> (a -> Last b) -> Last b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | Mk_Last a, f => f a end.

#[local] Definition Monad__Last_return_ : forall {a : Type}, a -> Last a :=
  fun {a : Type} => GHC.Base.pure.

#[global]
Program Instance Monad__Last : GHC.Base.Monad Last :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__Last_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) => Monad__Last_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__Last_return_ |}.

(* Skipping all instances of class `GHC.Internal.Control.Monad.Fix.MonadFix',
   including `Data.Semigroup.MonadFix__Last' *)

#[local] Definition Semigroup__WrappedMonoid_op_zlzlzgzg__ {inst_m : Type}
  `{GHC.Base.Monoid inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> WrappedMonoid inst_m :=
  fun arg_0__ arg_1__ =>
    WrapMonoid (GHC.Base.mappend (unwrapMonoid arg_0__) (unwrapMonoid arg_1__)).

#[global]
Program Instance Semigroup__WrappedMonoid {m : Type} `{GHC.Base.Monoid m}
   : GHC.Base.Semigroup (WrappedMonoid m) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__WrappedMonoid_op_zlzlzgzg__ |}.

#[local] Definition Monoid__WrappedMonoid_mappend {inst_m : Type}
  `{GHC.Base.Monoid inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> WrappedMonoid inst_m :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__WrappedMonoid_mconcat {inst_m : Type}
  `{GHC.Base.Monoid inst_m}
   : list (WrappedMonoid inst_m) -> WrappedMonoid inst_m :=
  fun arg_0__ =>
    WrapMonoid (GHC.Base.mconcat (GHC.Base.map unwrapMonoid arg_0__)).

#[local] Definition Monoid__WrappedMonoid_mempty {inst_m : Type}
  `{GHC.Base.Monoid inst_m}
   : WrappedMonoid inst_m :=
  WrapMonoid GHC.Base.mempty.

#[global]
Program Instance Monoid__WrappedMonoid {m : Type} `{GHC.Base.Monoid m}
   : GHC.Base.Monoid (WrappedMonoid m) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__WrappedMonoid_mappend ;
           GHC.Base.mconcat__ := Monoid__WrappedMonoid_mconcat ;
           GHC.Base.mempty__ := Monoid__WrappedMonoid_mempty |}.

(* Skipping all instances of class `GHC.Enum.Enum', including
   `Data.Semigroup.Enum__WrappedMonoid' *)

(* Skipping definition `Data.Semigroup.cycle1' *)

#[global] Definition diff {m : Type} `{GHC.Base.Semigroup m}
   : m -> Data.SemigroupInternal.Endo m :=
  Data.SemigroupInternal.Mk_Endo GHC.Base.∘ _GHC.Base.<<>>_.

(* Skipping definition `Data.Semigroup.mtimesDefault' *)

Instance Unpeel_Min a : HsToRocq.Unpeel.Unpeel (Min a) a :=
  HsToRocq.Unpeel.Build_Unpeel _ _ getMin Mk_Min.

Instance Unpeel_Max a : HsToRocq.Unpeel.Unpeel (Max a) a :=
  HsToRocq.Unpeel.Build_Unpeel _ _ getMax Mk_Max.

Instance Unpeel_First a : HsToRocq.Unpeel.Unpeel (First a) a :=
  HsToRocq.Unpeel.Build_Unpeel _ _ getFirst Mk_First.

Instance Unpeel_Last a : HsToRocq.Unpeel.Unpeel (Last a) a :=
  HsToRocq.Unpeel.Build_Unpeel _ _ getLast Mk_Last.

Instance Unpeel_WrappedMonoid a : HsToRocq.Unpeel.Unpeel (WrappedMonoid a) a :=
  HsToRocq.Unpeel.Build_Unpeel _ _ unwrapMonoid WrapMonoid.

(* External variables:
     Type bool false list negb true Corelib.Program.Basics.compose
     Data.Bifoldable.Bifoldable Data.Bifoldable.bifoldMap__ Data.Bifoldable.bifold__
     Data.Bifoldable.bifoldl__ Data.Bifoldable.bifoldr__ Data.Bifunctor.Bifunctor
     Data.Bifunctor.bimap__ Data.Bifunctor.first__ Data.Bifunctor.second__
     Data.Bitraversable.Bitraversable Data.Bitraversable.bitraverse__
     Data.Foldable.Foldable Data.Foldable.foldMap'__ Data.Foldable.foldMap__
     Data.Foldable.fold__ Data.Foldable.foldl'__ Data.Foldable.foldl__
     Data.Foldable.foldr'__ Data.Foldable.foldr__ Data.Foldable.length__
     Data.Foldable.null__ Data.Foldable.product__ Data.Foldable.sum__
     Data.Foldable.toList__ Data.Functor.op_zlzdzg__ Data.SemigroupInternal.Endo
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     Data.Traversable.Traversable Data.Traversable.mapM__
     Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse__ GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup GHC.Base.build'
     GHC.Base.const GHC.Base.flip GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id
     GHC.Base.liftA2__ GHC.Base.map GHC.Base.mappend GHC.Base.mappend__ GHC.Base.max
     GHC.Base.mconcat GHC.Base.mconcat__ GHC.Base.mempty GHC.Base.mempty__
     GHC.Base.min GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zgzg____ GHC.Base.op_zgzgze____ GHC.Base.op_zlzd____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Base.op_zlztzg__
     GHC.Base.op_zlztzg____ GHC.Base.op_zsze____ GHC.Base.op_ztzg__
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Base.return___
     GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Prim.seq
     HsToRocq.Unpeel.Build_Unpeel HsToRocq.Unpeel.Unpeel
*)
