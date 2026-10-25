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
Require GHC.Base.
Require GHC.Num.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Identity a : Type := | Mk_Identity (runIdentity : a) : Identity a.

Arguments Mk_Identity {_} _.

#[global] Definition runIdentity {a} (arg_0__ : Identity a) :=
  let 'Mk_Identity runIdentity := arg_0__ in
  runIdentity.

(* Midamble *)

Instance Unpeel_Identity a : HsToRocq.Unpeel.Unpeel (Identity a) a :=
 HsToRocq.Unpeel.Build_Unpeel _ _  (fun arg => match arg with | Mk_Identity x => x end) Mk_Identity.

(* Converted value declarations: *)

#[local] Definition Semigroup__Identity_op_zlzlzgzg__ {inst_a : Type}
  `{GHC.Base.Semigroup inst_a}
   : Identity inst_a -> Identity inst_a -> Identity inst_a :=
  fun arg_0__ arg_1__ =>
    Mk_Identity (_GHC.Base.<<>>_ (runIdentity arg_0__) (runIdentity arg_1__)).

#[global]
Program Instance Semigroup__Identity {a : Type} `{GHC.Base.Semigroup a}
   : GHC.Base.Semigroup (Identity a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Identity_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Identity_mappend {inst_a : Type} `{GHC.Base.Monoid
  inst_a}
   : Identity inst_a -> Identity inst_a -> Identity inst_a :=
  fun arg_0__ arg_1__ =>
    Mk_Identity (GHC.Base.mappend (runIdentity arg_0__) (runIdentity arg_1__)).

#[local] Definition Monoid__Identity_mconcat {inst_a : Type} `{GHC.Base.Monoid
  inst_a}
   : list (Identity inst_a) -> Identity inst_a :=
  fun arg_0__ =>
    Mk_Identity (GHC.Base.mconcat (GHC.Base.map runIdentity arg_0__)).

#[local] Definition Monoid__Identity_mempty {inst_a : Type} `{GHC.Base.Monoid
  inst_a}
   : Identity inst_a :=
  Mk_Identity GHC.Base.mempty.

#[global]
Program Instance Monoid__Identity {a : Type} `{GHC.Base.Monoid a}
   : GHC.Base.Monoid (Identity a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Identity_mappend ;
           GHC.Base.mconcat__ := Monoid__Identity_mconcat ;
           GHC.Base.mempty__ := Monoid__Identity_mempty |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Functor.Identity.Read__Identity' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Functor.Identity.Show__Identity' *)

#[local] Definition Foldable__Identity_foldMap
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> Identity a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => arg_0__ (runIdentity arg_1__).

#[local] Definition Foldable__Identity_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Identity m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Identity_foldMap GHC.Base.id.

#[local] Definition Foldable__Identity_foldl'
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Identity a -> b :=
  fun {b : Type} {a : Type} =>
    fun arg_0__ arg_1__ arg_2__ => arg_0__ arg_1__ (runIdentity arg_2__).

#[local] Definition Foldable__Identity_foldMap'
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> Identity a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Identity_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Identity_foldl
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Identity a -> b :=
  fun {b : Type} {a : Type} =>
    fun arg_0__ arg_1__ arg_2__ => arg_0__ arg_1__ (runIdentity arg_2__).

#[local] Definition Foldable__Identity_foldr
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Identity a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Mk_Identity x => f x z
      end.

#[local] Definition Foldable__Identity_foldr'
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Identity a -> b :=
  fun {a : Type} {b : Type} => Foldable__Identity_foldr.

#[local] Definition Foldable__Identity_length
   : forall {a : Type}, Identity a -> GHC.Num.Int :=
  fun {a : Type} => fun arg_0__ => #1.

#[local] Definition Foldable__Identity_null
   : forall {a : Type}, Identity a -> bool :=
  fun {a : Type} => fun arg_0__ => false.

#[local] Definition Foldable__Identity_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, Identity a -> a :=
  fun {a : Type} `{GHC.Num.Num a} => runIdentity.

#[local] Definition Foldable__Identity_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, Identity a -> a :=
  fun {a : Type} `{GHC.Num.Num a} => runIdentity.

#[local] Definition Foldable__Identity_toList
   : forall {a : Type}, Identity a -> list a :=
  fun {a : Type} => fun '(Mk_Identity x) => cons x nil.

#[global]
Program Instance Foldable__Identity : Data.Foldable.Foldable Identity :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Foldable__Identity_fold ;
           Data.Foldable.foldMap__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Identity_foldMap ;
           Data.Foldable.foldMap'__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Identity_foldMap' ;
           Data.Foldable.foldl__ := fun (b : Type) (a : Type) => Foldable__Identity_foldl ;
           Data.Foldable.foldl'__ := fun (b : Type) (a : Type) =>
             Foldable__Identity_foldl' ;
           Data.Foldable.foldr__ := fun (a : Type) (b : Type) => Foldable__Identity_foldr ;
           Data.Foldable.foldr'__ := fun (a : Type) (b : Type) =>
             Foldable__Identity_foldr' ;
           Data.Foldable.length__ := fun (a : Type) => Foldable__Identity_length ;
           Data.Foldable.null__ := fun (a : Type) => Foldable__Identity_null ;
           Data.Foldable.product__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__Identity_product ;
           Data.Foldable.sum__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__Identity_sum ;
           Data.Foldable.toList__ := fun (a : Type) => Foldable__Identity_toList |}.

#[local] Definition Functor__Identity_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Identity a -> Identity b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Identity (arg_0__ (runIdentity arg_1__)).

#[local] Definition Functor__Identity_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> Identity b -> Identity a :=
  fun {a : Type} {b : Type} => Functor__Identity_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__Identity : GHC.Base.Functor Identity :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Identity_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__Identity_op_zlzd__ |}.

#[local] Definition Applicative__Identity_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Identity a -> Identity b -> Identity c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      Mk_Identity (arg_0__ (runIdentity arg_1__) (runIdentity arg_2__)).

#[local] Definition Applicative__Identity_op_zlztzg__
   : forall {a : Type},
     forall {b : Type}, Identity (a -> b) -> Identity a -> Identity b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Identity (runIdentity arg_0__ (runIdentity arg_1__)).

#[local] Definition Applicative__Identity_op_ztzg__
   : forall {a : Type},
     forall {b : Type}, Identity a -> Identity b -> Identity b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 =>
      Applicative__Identity_op_zlztzg__ (GHC.Base.op_zlzd__ GHC.Base.id a1) a2.

#[local] Definition Applicative__Identity_pure
   : forall {a : Type}, a -> Identity a :=
  fun {a : Type} => Mk_Identity.

#[global]
Program Instance Applicative__Identity : GHC.Base.Applicative Identity :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__Identity_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Identity_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Identity_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__Identity_pure |}.

#[local] Definition Monad__Identity_op_zgzgze__
   : forall {a : Type},
     forall {b : Type}, Identity a -> (a -> Identity b) -> Identity b :=
  fun {a : Type} {b : Type} => fun m k => k (runIdentity m).

#[local] Definition Monad__Identity_op_zgzg__
   : forall {a : Type},
     forall {b : Type}, Identity a -> Identity b -> Identity b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__Identity_op_zgzgze__ m (fun arg_0__ => k).

#[local] Definition Monad__Identity_return_
   : forall {a : Type}, a -> Identity a :=
  fun {a : Type} => GHC.Base.pure.

#[global]
Program Instance Monad__Identity : GHC.Base.Monad Identity :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__Identity_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) =>
             Monad__Identity_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__Identity_return_ |}.

(* Skipping all instances of class `GHC.Internal.Control.Monad.Fix.MonadFix',
   including `Data.Functor.Identity.MonadFix__Identity' *)

(* External variables:
     Type bool cons false list nil Data.Foldable.Foldable Data.Foldable.foldMap'__
     Data.Foldable.foldMap__ Data.Foldable.fold__ Data.Foldable.foldl'__
     Data.Foldable.foldl__ Data.Foldable.foldr'__ Data.Foldable.foldr__
     Data.Foldable.length__ Data.Foldable.null__ Data.Foldable.product__
     Data.Foldable.sum__ Data.Foldable.toList__ GHC.Base.Applicative GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Semigroup GHC.Base.const GHC.Base.fmap__
     GHC.Base.id GHC.Base.liftA2__ GHC.Base.map GHC.Base.mappend GHC.Base.mappend__
     GHC.Base.mconcat GHC.Base.mconcat__ GHC.Base.mempty GHC.Base.mempty__
     GHC.Base.op_z2218U__ GHC.Base.op_zgzg____ GHC.Base.op_zgzgze____
     GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlzlzgzg__
     GHC.Base.op_zlzlzgzg____ GHC.Base.op_zlztzg____ GHC.Base.op_ztzg____
     GHC.Base.pure GHC.Base.pure__ GHC.Base.return___ GHC.Num.Int GHC.Num.Num
     GHC.Num.fromInteger
*)
