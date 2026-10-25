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

Require Data.Foldable.
Require Data.Functor.
Require Data.Functor.Classes.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Import Data.Functor.Notations.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Compose {k : Type} {k1 : Type} (f : k -> Type) (g : k1 -> k) (a : k1)
   : Type :=
  | Mk_Compose (getCompose : f (g a)) : Compose f g a.

Arguments Mk_Compose {_} {_} {_} {_} {_} _.

#[global] Definition getCompose {k : Type} {k1 : Type} {f : k -> Type} {g
   : k1 -> k} {a : k1} (arg_0__ : Compose f g a) :=
  let 'Mk_Compose getCompose := arg_0__ in
  getCompose.

(* Midamble *)

(* Semigroup and Monoid for Compose -- generated code has duplicate {k : Type}
   bindings and uses coerce. We define these manually with correct type vars
   and explicit pattern matching. *)

#[local] Definition Semigroup__Compose_op_zlzlzgzg__ {k : Type} {f
   : k -> Type} {k1 : Type} {g : k1 -> k} {a : k1}
  `{GHC.Base.Semigroup (f (g a))}
   : Compose f g a -> Compose f g a -> Compose f g a :=
  fun x y => match x, y with | Mk_Compose p, Mk_Compose q => Mk_Compose (p GHC.Base.<<>> q) end.

#[global]
Program Instance Semigroup__Compose {k : Type} {f : k -> Type} {k1 : Type}
  {g : k1 -> k} {a : k1} `{GHC.Base.Semigroup (f (g a))}
   : GHC.Base.Semigroup (Compose f g a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Compose_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Compose_mappend {k : Type} {f
   : k -> Type} {k1 : Type} {g : k1 -> k} {a : k1}
  `{GHC.Base.Monoid (f (g a))}
   : Compose f g a -> Compose f g a -> Compose f g a :=
  fun x y => match x, y with | Mk_Compose p, Mk_Compose q => Mk_Compose (GHC.Base.mappend p q) end.

#[local] Definition Monoid__Compose_mconcat {k : Type} {f
   : k -> Type} {k1 : Type} {g : k1 -> k} {a : k1}
  `{GHC.Base.Monoid (f (g a))}
   : list (Compose f g a) -> Compose f g a :=
  fun xs => Mk_Compose (GHC.Base.mconcat (GHC.Base.map (fun x => match x with | Mk_Compose p => p end) xs)).

#[local] Definition Monoid__Compose_mempty {k : Type} {f
   : k -> Type} {k1 : Type} {g : k1 -> k} {a : k1}
  `{GHC.Base.Monoid (f (g a))}
   : Compose f g a :=
  Mk_Compose GHC.Base.mempty.

#[global]
Program Instance Monoid__Compose {k : Type} {f : k -> Type} {k1 : Type}
  {g : k1 -> k} {a : k1} `{GHC.Base.Monoid (f (g a))}
   : GHC.Base.Monoid (Compose f g a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Compose_mappend ;
           GHC.Base.mconcat__ := Monoid__Compose_mconcat ;
           GHC.Base.mempty__ := Monoid__Compose_mempty |}.

(* Converted value declarations: *)

(* Skipping instance `Data.Functor.Compose.Semigroup__Compose' of class
   `GHC.Base.Semigroup' *)

(* Skipping instance `Data.Functor.Compose.Monoid__Compose' of class
   `GHC.Base.Monoid' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Functor.Compose.Read__Compose' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Functor.Compose.Show__Compose' *)

#[local] Definition Eq1__Compose_liftEq {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Functor.Classes.Eq1 inst_f} `{Data.Functor.Classes.Eq1
  inst_g}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> bool) ->
     Compose inst_f inst_g a -> Compose inst_f inst_g b -> bool :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Mk_Compose x, Mk_Compose y =>
          Data.Functor.Classes.liftEq (Data.Functor.Classes.liftEq eq) x y
      end.

#[global]
Program Instance Eq1__Compose {f : Type -> Type} {g : Type -> Type}
  `{Data.Functor.Classes.Eq1 f} `{Data.Functor.Classes.Eq1 g}
   : Data.Functor.Classes.Eq1 (Compose f g) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftEq__ := fun (a : Type) (b : Type) =>
             Eq1__Compose_liftEq |}.

#[local] Definition Ord1__Compose_liftCompare {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1
  inst_g}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> comparison) ->
     Compose inst_f inst_g a -> Compose inst_f inst_g b -> comparison :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Mk_Compose x, Mk_Compose y =>
          Data.Functor.Classes.liftCompare (Data.Functor.Classes.liftCompare comp) x y
      end.

#[global]
Program Instance Ord1__Compose {f : Type -> Type} {g : Type -> Type}
  `{Data.Functor.Classes.Ord1 f} `{Data.Functor.Classes.Ord1 g}
   : Data.Functor.Classes.Ord1 (Compose f g) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftCompare__ := fun (a : Type) (b : Type) =>
             Ord1__Compose_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.Functor.Compose.Read1__Compose' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.Functor.Compose.Show1__Compose' *)

#[local] Definition Functor__Compose_fmap {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{GHC.Base.Functor inst_f} `{GHC.Base.Functor inst_g}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) -> Compose inst_f inst_g a -> Compose inst_f inst_g b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Compose x => Mk_Compose (GHC.Base.fmap (GHC.Base.fmap f) x)
      end.

#[local] Definition Functor__Compose_op_zlzd__ {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{GHC.Base.Functor inst_f} `{GHC.Base.Functor inst_g}
   : forall {a : Type},
     forall {b : Type}, a -> Compose inst_f inst_g b -> Compose inst_f inst_g a :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | a, Mk_Compose x => Mk_Compose (GHC.Base.fmap (GHC.Base.op_zlzd__ a) x)
      end.

#[global]
Program Instance Functor__Compose {f : Type -> Type} {g : Type -> Type}
  `{GHC.Base.Functor f} `{GHC.Base.Functor g}
   : GHC.Base.Functor (Compose f g) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Compose_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__Compose_op_zlzd__ |}.

#[local] Definition Foldable__Compose_fold {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {m : Type},
     forall `{GHC.Base.Monoid m}, Compose inst_f inst_g m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} arg =>
    let 'Mk_Compose t := arg in
    Data.Foldable.foldMap Data.Foldable.fold t.

#[local] Definition Foldable__Compose_foldMap {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Compose inst_f inst_g a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Compose t => Data.Foldable.foldMap (Data.Foldable.foldMap f) t
      end.

#[local] Definition Foldable__Compose_foldMap' {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Compose inst_f inst_g a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Compose t => Data.Foldable.foldMap' (Data.Foldable.foldMap' f) t
      end.

#[local] Definition Foldable__Compose_foldl {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Compose inst_f inst_g a -> b :=
  fun {b : Type} {a : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, b, Mk_Compose fga =>
          Data.Foldable.foldl (fun acc ga => Data.Foldable.foldl f acc ga) b fga
      end.

#[local] Definition Foldable__Compose_foldl' {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Compose inst_f inst_g a -> b :=
  fun {b : Type} {a : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, b, Mk_Compose fga =>
          Data.Foldable.foldl' (fun acc ga => Data.Foldable.foldl' f acc ga) b fga
      end.

#[local] Definition Foldable__Compose_foldr {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Compose inst_f inst_g a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, b, Mk_Compose fga =>
          Data.Foldable.foldr (fun ga acc => Data.Foldable.foldr f acc ga) b fga
      end.

#[local] Definition Foldable__Compose_foldr' {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Compose inst_f inst_g a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, b, Mk_Compose fga =>
          Data.Foldable.foldr' (fun ga acc => Data.Foldable.foldr' f acc ga) b fga
      end.

#[local] Definition Foldable__Compose_length {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type}, Compose inst_f inst_g a -> GHC.Num.Int :=
  fun {a : Type} arg =>
    let 'Mk_Compose t := arg in
    Data.SemigroupInternal.getSum (Data.Foldable.foldMap (fun x =>
                                                            Data.SemigroupInternal.Mk_Sum (Data.Foldable.length x)) t).

#[local] Definition Foldable__Compose_null {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type}, Compose inst_f inst_g a -> bool :=
  fun {a : Type} arg =>
    let 'Mk_Compose t := arg in
    orb (Data.Foldable.null t) (Data.SemigroupInternal.getAll (Data.Foldable.foldMap
                                                               (Data.SemigroupInternal.Mk_All GHC.Base.∘
                                                                Data.Foldable.null) t)).

#[local] Definition Foldable__Compose_product {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Compose inst_f inst_g a -> a :=
  fun {a : Type} `{GHC.Num.Num a} arg =>
    let 'Mk_Compose t := arg in
    Data.SemigroupInternal.getProduct (Data.Foldable.foldMap (fun x =>
                                                                Data.SemigroupInternal.Mk_Product (Data.Foldable.product
                                                                                                   x)) t).

#[local] Definition Foldable__Compose_sum {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Compose inst_f inst_g a -> a :=
  fun {a : Type} `{GHC.Num.Num a} arg =>
    let 'Mk_Compose t := arg in
    Data.SemigroupInternal.getSum (Data.Foldable.foldMap (fun x =>
                                                            Data.SemigroupInternal.Mk_Sum (Data.Foldable.sum x)) t).

#[local] Definition Foldable__Compose_toList {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type}, Compose inst_f inst_g a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Compose_foldr c n t)).

#[global]
Program Instance Foldable__Compose {f : Type -> Type} {g : Type -> Type}
  `{Data.Foldable.Foldable f} `{Data.Foldable.Foldable g}
   : Data.Foldable.Foldable (Compose f g) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Foldable__Compose_fold ;
           Data.Foldable.foldMap__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Compose_foldMap ;
           Data.Foldable.foldMap'__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Compose_foldMap' ;
           Data.Foldable.foldl__ := fun (b : Type) (a : Type) => Foldable__Compose_foldl ;
           Data.Foldable.foldl'__ := fun (b : Type) (a : Type) =>
             Foldable__Compose_foldl' ;
           Data.Foldable.foldr__ := fun (a : Type) (b : Type) => Foldable__Compose_foldr ;
           Data.Foldable.foldr'__ := fun (a : Type) (b : Type) =>
             Foldable__Compose_foldr' ;
           Data.Foldable.length__ := fun (a : Type) => Foldable__Compose_length ;
           Data.Foldable.null__ := fun (a : Type) => Foldable__Compose_null ;
           Data.Foldable.product__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__Compose_product ;
           Data.Foldable.sum__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__Compose_sum ;
           Data.Foldable.toList__ := fun (a : Type) => Foldable__Compose_toList |}.

#[local] Definition Traversable__Compose_traverse {inst_f : Type -> Type}
  {inst_g : Type -> Type} `{Data.Traversable.Traversable inst_f}
  `{Data.Traversable.Traversable inst_g}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> Compose inst_f inst_g a -> f (Compose inst_f inst_g b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Compose t =>
          Data.Functor.op_zlzdzg__ Mk_Compose (Data.Traversable.traverse
                                    (Data.Traversable.traverse f) t)
      end.

#[local] Definition Traversable__Compose_mapM {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Traversable.Traversable inst_f}
  `{Data.Traversable.Traversable inst_g}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> Compose inst_f inst_g a -> m (Compose inst_f inst_g b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Compose_traverse.

#[local] Definition Traversable__Compose_sequenceA {inst_f : Type -> Type}
  {inst_g : Type -> Type} `{Data.Traversable.Traversable inst_f}
  `{Data.Traversable.Traversable inst_g}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     Compose inst_f inst_g (f a) -> f (Compose inst_f inst_g a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Compose_traverse GHC.Base.id.

#[local] Definition Traversable__Compose_sequence {inst_f : Type -> Type}
  {inst_g : Type -> Type} `{Data.Traversable.Traversable inst_f}
  `{Data.Traversable.Traversable inst_g}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     Compose inst_f inst_g (m a) -> m (Compose inst_f inst_g a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Compose_sequenceA.

#[global]
Program Instance Traversable__Compose {f : Type -> Type} {g : Type -> Type}
  `{Data.Traversable.Traversable f} `{Data.Traversable.Traversable g}
   : Data.Traversable.Traversable (Compose f g) :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun (m : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Monad m) =>
             Traversable__Compose_mapM ;
           Data.Traversable.sequence__ := fun (m : Type -> Type)
           (a : Type)
           `(GHC.Base.Monad m) =>
             Traversable__Compose_sequence ;
           Data.Traversable.sequenceA__ := fun (f : Type -> Type)
           (a : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__Compose_sequenceA ;
           Data.Traversable.traverse__ := fun (f : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__Compose_traverse |}.

#[local] Definition Applicative__Compose_liftA2 {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{GHC.Base.Applicative inst_f} `{GHC.Base.Applicative inst_g}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) ->
     Compose inst_f inst_g a -> Compose inst_f inst_g b -> Compose inst_f inst_g c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, Mk_Compose x, Mk_Compose y =>
          Mk_Compose (GHC.Base.liftA2 (GHC.Base.liftA2 f) x y)
      end.

#[local] Definition Applicative__Compose_op_zlztzg__ {inst_f : Type -> Type}
  {inst_g : Type -> Type} `{GHC.Base.Applicative inst_f} `{GHC.Base.Applicative
  inst_g}
   : forall {a : Type},
     forall {b : Type},
     Compose inst_f inst_g (a -> b) ->
     Compose inst_f inst_g a -> Compose inst_f inst_g b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Compose f, Mk_Compose x => Mk_Compose (GHC.Base.liftA2 _GHC.Base.<*>_ f x)
      end.

#[local] Definition Applicative__Compose_op_ztzg__ {inst_f : Type -> Type}
  {inst_g : Type -> Type} `{GHC.Base.Applicative inst_f} `{GHC.Base.Applicative
  inst_g}
   : forall {a : Type},
     forall {b : Type},
     Compose inst_f inst_g a -> Compose inst_f inst_g b -> Compose inst_f inst_g b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 =>
      Applicative__Compose_op_zlztzg__ (GHC.Base.op_zlzd__ GHC.Base.id a1) a2.

#[local] Definition Applicative__Compose_pure {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{GHC.Base.Applicative inst_f} `{GHC.Base.Applicative inst_g}
   : forall {a : Type}, a -> Compose inst_f inst_g a :=
  fun {a : Type} => fun x => Mk_Compose (GHC.Base.pure (GHC.Base.pure x)).

#[global]
Program Instance Applicative__Compose {f : Type -> Type} {g : Type -> Type}
  `{GHC.Base.Applicative f} `{GHC.Base.Applicative g}
   : GHC.Base.Applicative (Compose f g) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__Compose_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Compose_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Compose_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__Compose_pure |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Data.Functor.Compose.Alternative__Compose' *)

(* Skipping all instances of class
   `GHC.Internal.Data.Type.Equality.TestEquality', including
   `Data.Functor.Compose.TestEquality__Compose' *)

(* Skipping definition `Data.Functor.Compose.liftReadPrecCompose' *)

(* Skipping definition `Data.Functor.Compose.liftShowsPrecCompose' *)

(* External variables:
     Type bool comparison list orb Data.Foldable.Foldable Data.Foldable.fold
     Data.Foldable.foldMap Data.Foldable.foldMap' Data.Foldable.foldMap'__
     Data.Foldable.foldMap__ Data.Foldable.fold__ Data.Foldable.foldl
     Data.Foldable.foldl' Data.Foldable.foldl'__ Data.Foldable.foldl__
     Data.Foldable.foldr Data.Foldable.foldr' Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length Data.Foldable.length__
     Data.Foldable.null Data.Foldable.null__ Data.Foldable.product
     Data.Foldable.product__ Data.Foldable.sum Data.Foldable.sum__
     Data.Foldable.toList__ Data.Functor.op_zlzdzg__ Data.Functor.Classes.Eq1
     Data.Functor.Classes.Ord1 Data.Functor.Classes.liftCompare
     Data.Functor.Classes.liftCompare__ Data.Functor.Classes.liftEq
     Data.Functor.Classes.liftEq__ Data.SemigroupInternal.Mk_All
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.getAll Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum Data.Traversable.Traversable
     Data.Traversable.mapM__ Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ GHC.Base.Applicative
     GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.build' GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2 GHC.Base.liftA2__
     GHC.Base.op_z2218U__ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____
     GHC.Base.op_zlztzg__ GHC.Base.op_zlztzg____ GHC.Base.op_ztzg____ GHC.Base.pure
     GHC.Base.pure__ GHC.Num.Int GHC.Num.Num
*)
