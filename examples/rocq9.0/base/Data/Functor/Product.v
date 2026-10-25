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

Require Control.Monad.Zip.
Require Corelib.Program.Basics.
Require Data.Foldable.
Require Data.Functor.Classes.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Tuple.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Product {k : Type} (f : k -> Type) (g : k -> Type) (a : k) : Type :=
  | Pair : (f a) -> (g a) -> Product f g a.

Arguments Pair {_} {_} {_} {_} _ _.

(* Converted value declarations: *)

#[local] Definition Eq1__Product_liftEq {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Functor.Classes.Eq1 inst_f} `{Data.Functor.Classes.Eq1
  inst_g}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> bool) ->
     Product inst_f inst_g a -> Product inst_f inst_g b -> bool :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Pair x1 y1, Pair x2 y2 =>
          andb (Data.Functor.Classes.liftEq eq x1 x2) (Data.Functor.Classes.liftEq eq y1
                y2)
      end.

#[global]
Program Instance Eq1__Product {f : Type -> Type} {g : Type -> Type}
  `{Data.Functor.Classes.Eq1 f} `{Data.Functor.Classes.Eq1 g}
   : Data.Functor.Classes.Eq1 (Product f g) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftEq__ := fun (a : Type) (b : Type) =>
             Eq1__Product_liftEq |}.

#[local] Definition Ord1__Product_liftCompare {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1
  inst_g}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> comparison) ->
     Product inst_f inst_g a -> Product inst_f inst_g b -> comparison :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Pair x1 y1, Pair x2 y2 =>
          GHC.Base.mappend (Data.Functor.Classes.liftCompare comp x1 x2)
                           (Data.Functor.Classes.liftCompare comp y1 y2)
      end.

#[global]
Program Instance Ord1__Product {f : Type -> Type} {g : Type -> Type}
  `{Data.Functor.Classes.Ord1 f} `{Data.Functor.Classes.Ord1 g}
   : Data.Functor.Classes.Ord1 (Product f g) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftCompare__ := fun (a : Type) (b : Type) =>
             Ord1__Product_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.Functor.Product.Read1__Product' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.Functor.Product.Show1__Product' *)

#[local] Definition Functor__Product_fmap {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{GHC.Base.Functor inst_f} `{GHC.Base.Functor inst_g}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) -> Product inst_f inst_g a -> Product inst_f inst_g b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Pair x y => Pair (GHC.Base.fmap f x) (GHC.Base.fmap f y)
      end.

#[local] Definition Functor__Product_op_zlzd__ {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{GHC.Base.Functor inst_f} `{GHC.Base.Functor inst_g}
   : forall {a : Type},
     forall {b : Type}, a -> Product inst_f inst_g b -> Product inst_f inst_g a :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | a, Pair x y => Pair (GHC.Base.op_zlzd__ a x) (GHC.Base.op_zlzd__ a y)
      end.

#[global]
Program Instance Functor__Product {f : Type -> Type} {g : Type -> Type}
  `{GHC.Base.Functor f} `{GHC.Base.Functor g}
   : GHC.Base.Functor (Product f g) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Product_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__Product_op_zlzd__ |}.

#[local] Definition Foldable__Product_foldMap {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Product inst_f inst_g a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Pair x y =>
          GHC.Base.mappend (Data.Foldable.foldMap f x) (Data.Foldable.foldMap f y)
      end.

#[local] Definition Foldable__Product_fold {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {m : Type},
     forall `{GHC.Base.Monoid m}, Product inst_f inst_g m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Product_foldMap GHC.Base.id.

#[local] Definition Foldable__Product_foldr {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Product inst_f inst_g a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Product_foldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__Product_foldl' {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Product inst_f inst_g a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__Product_foldr (fun arg_0__ arg_1__ =>
                                   match arg_0__, arg_1__ with
                                   | x, k => (fun '(z) => GHC.Prim.seq z (k (f z x)))
                                   end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__Product_foldMap' {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Product inst_f inst_g a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Product_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Product_foldl {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Product inst_f inst_g a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Product_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                  (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                   GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__Product_foldr' {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Product inst_f inst_g a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__Product_foldl (fun arg_0__ arg_1__ =>
                                   match arg_0__, arg_1__ with
                                   | k, x => (fun '(z) => GHC.Prim.seq z (k (f x z)))
                                   end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__Product_length {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type}, Product inst_f inst_g a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__Product_foldl' (fun arg_0__ arg_1__ =>
                                match arg_0__, arg_1__ with
                                | c, _ => c GHC.Num.+ #1
                                end) #0.

#[local] Definition Foldable__Product_null {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type}, Product inst_f inst_g a -> bool :=
  fun {a : Type} => Foldable__Product_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__Product_product {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Product inst_f inst_g a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getProduct
                                   (Foldable__Product_foldMap' Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__Product_sum {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Product inst_f inst_g a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getSum
                                   (Foldable__Product_foldMap' Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__Product_toList {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable
  inst_g}
   : forall {a : Type}, Product inst_f inst_g a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Product_foldr c n t)).

#[global]
Program Instance Foldable__Product {f : Type -> Type} {g : Type -> Type}
  `{Data.Foldable.Foldable f} `{Data.Foldable.Foldable g}
   : Data.Foldable.Foldable (Product f g) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Foldable__Product_fold ;
           Data.Foldable.foldMap__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Product_foldMap ;
           Data.Foldable.foldMap'__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Product_foldMap' ;
           Data.Foldable.foldl__ := fun (b : Type) (a : Type) => Foldable__Product_foldl ;
           Data.Foldable.foldl'__ := fun (b : Type) (a : Type) =>
             Foldable__Product_foldl' ;
           Data.Foldable.foldr__ := fun (a : Type) (b : Type) => Foldable__Product_foldr ;
           Data.Foldable.foldr'__ := fun (a : Type) (b : Type) =>
             Foldable__Product_foldr' ;
           Data.Foldable.length__ := fun (a : Type) => Foldable__Product_length ;
           Data.Foldable.null__ := fun (a : Type) => Foldable__Product_null ;
           Data.Foldable.product__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__Product_product ;
           Data.Foldable.sum__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__Product_sum ;
           Data.Foldable.toList__ := fun (a : Type) => Foldable__Product_toList |}.

#[local] Definition Traversable__Product_traverse {inst_f : Type -> Type}
  {inst_g : Type -> Type} `{Data.Traversable.Traversable inst_f}
  `{Data.Traversable.Traversable inst_g}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> Product inst_f inst_g a -> f (Product inst_f inst_g b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Pair x y =>
          GHC.Base.liftA2 Pair (Data.Traversable.traverse f x) (Data.Traversable.traverse
                                                                f y)
      end.

#[local] Definition Traversable__Product_mapM {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Data.Traversable.Traversable inst_f}
  `{Data.Traversable.Traversable inst_g}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> Product inst_f inst_g a -> m (Product inst_f inst_g b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Product_traverse.

#[local] Definition Traversable__Product_sequenceA {inst_f : Type -> Type}
  {inst_g : Type -> Type} `{Data.Traversable.Traversable inst_f}
  `{Data.Traversable.Traversable inst_g}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     Product inst_f inst_g (f a) -> f (Product inst_f inst_g a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Product_traverse GHC.Base.id.

#[local] Definition Traversable__Product_sequence {inst_f : Type -> Type}
  {inst_g : Type -> Type} `{Data.Traversable.Traversable inst_f}
  `{Data.Traversable.Traversable inst_g}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m},
     Product inst_f inst_g (m a) -> m (Product inst_f inst_g a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Product_sequenceA.

#[global]
Program Instance Traversable__Product {f : Type -> Type} {g : Type -> Type}
  `{Data.Traversable.Traversable f} `{Data.Traversable.Traversable g}
   : Data.Traversable.Traversable (Product f g) :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun (m : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Monad m) =>
             Traversable__Product_mapM ;
           Data.Traversable.sequence__ := fun (m : Type -> Type)
           (a : Type)
           `(GHC.Base.Monad m) =>
             Traversable__Product_sequence ;
           Data.Traversable.sequenceA__ := fun (f : Type -> Type)
           (a : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__Product_sequenceA ;
           Data.Traversable.traverse__ := fun (f : Type -> Type)
           (a : Type)
           (b : Type)
           `(GHC.Base.Applicative f) =>
             Traversable__Product_traverse |}.

#[local] Definition Applicative__Product_liftA2 {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{GHC.Base.Applicative inst_f} `{GHC.Base.Applicative inst_g}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) ->
     Product inst_f inst_g a -> Product inst_f inst_g b -> Product inst_f inst_g c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, Pair a b, Pair x y => Pair (GHC.Base.liftA2 f a x) (GHC.Base.liftA2 f b y)
      end.

#[local] Definition Applicative__Product_op_zlztzg__ {inst_f : Type -> Type}
  {inst_g : Type -> Type} `{GHC.Base.Applicative inst_f} `{GHC.Base.Applicative
  inst_g}
   : forall {a : Type},
     forall {b : Type},
     Product inst_f inst_g (a -> b) ->
     Product inst_f inst_g a -> Product inst_f inst_g b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Pair f g, Pair x y => Pair (f GHC.Base.<*> x) (g GHC.Base.<*> y)
      end.

#[local] Definition Applicative__Product_op_ztzg__ {inst_f : Type -> Type}
  {inst_g : Type -> Type} `{GHC.Base.Applicative inst_f} `{GHC.Base.Applicative
  inst_g}
   : forall {a : Type},
     forall {b : Type},
     Product inst_f inst_g a -> Product inst_f inst_g b -> Product inst_f inst_g b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 =>
      Applicative__Product_op_zlztzg__ (GHC.Base.op_zlzd__ GHC.Base.id a1) a2.

#[local] Definition Applicative__Product_pure {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{GHC.Base.Applicative inst_f} `{GHC.Base.Applicative inst_g}
   : forall {a : Type}, a -> Product inst_f inst_g a :=
  fun {a : Type} => fun x => Pair (GHC.Base.pure x) (GHC.Base.pure x).

#[global]
Program Instance Applicative__Product {f : Type -> Type} {g : Type -> Type}
  `{GHC.Base.Applicative f} `{GHC.Base.Applicative g}
   : GHC.Base.Applicative (Product f g) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__Product_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Product_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Product_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__Product_pure |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Data.Functor.Product.Alternative__Product' *)

#[local] Definition Monad__Product_op_zgzgze__ {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{GHC.Base.Monad inst_f} `{GHC.Base.Monad inst_g}
   : forall {a : Type},
     forall {b : Type},
     Product inst_f inst_g a ->
     (a -> Product inst_f inst_g b) -> Product inst_f inst_g b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Pair m n, f =>
          let sndP := fun '(Pair _ b) => b in
          let fstP := fun '(Pair a _) => a in
          Pair (m GHC.Base.>>= (fstP GHC.Base.∘ f)) (n GHC.Base.>>= (sndP GHC.Base.∘ f))
      end.

#[local] Definition Monad__Product_op_zgzg__ {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{GHC.Base.Monad inst_f} `{GHC.Base.Monad inst_g}
   : forall {a : Type},
     forall {b : Type},
     Product inst_f inst_g a -> Product inst_f inst_g b -> Product inst_f inst_g b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__Product_op_zgzgze__ m (fun arg_0__ => k).

#[local] Definition Monad__Product_return_ {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{GHC.Base.Monad inst_f} `{GHC.Base.Monad inst_g}
   : forall {a : Type}, a -> Product inst_f inst_g a :=
  fun {a : Type} => GHC.Base.pure.

#[global]
Program Instance Monad__Product {f : Type -> Type} {g : Type -> Type}
  `{GHC.Base.Monad f} `{GHC.Base.Monad g}
   : GHC.Base.Monad (Product f g) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__Product_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) =>
             Monad__Product_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__Product_return_ |}.

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `Data.Functor.Product.MonadPlus__Product' *)

(* Skipping all instances of class `GHC.Internal.Control.Monad.Fix.MonadFix',
   including `Data.Functor.Product.MonadFix__Product' *)

#[local] Definition MonadZip__Product_munzip {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Control.Monad.Zip.MonadZip inst_f}
  `{Control.Monad.Zip.MonadZip inst_g}
   : forall {a : Type},
     forall {b : Type},
     Product inst_f inst_g (a * b)%type ->
     (Product inst_f inst_g a * Product inst_f inst_g b)%type :=
  fun {a : Type} {b : Type} =>
    fun mab =>
      pair (GHC.Base.liftM Data.Tuple.fst mab) (GHC.Base.liftM Data.Tuple.snd mab).

#[local] Definition MonadZip__Product_mzipWith {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Control.Monad.Zip.MonadZip inst_f}
  `{Control.Monad.Zip.MonadZip inst_g}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) ->
     Product inst_f inst_g a -> Product inst_f inst_g b -> Product inst_f inst_g c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, Pair x1 y1, Pair x2 y2 =>
          Pair (Control.Monad.Zip.mzipWith f x1 x2) (Control.Monad.Zip.mzipWith f y1 y2)
      end.

#[local] Definition MonadZip__Product_mzip {inst_f : Type -> Type} {inst_g
   : Type -> Type} `{Control.Monad.Zip.MonadZip inst_f}
  `{Control.Monad.Zip.MonadZip inst_g}
   : forall {a : Type},
     forall {b : Type},
     Product inst_f inst_g a ->
     Product inst_f inst_g b -> Product inst_f inst_g (a * b)%type :=
  fun {a : Type} {b : Type} => MonadZip__Product_mzipWith GHC.Tuple.pair2.

#[global]
Program Instance MonadZip__Product {f : Type -> Type} {g : Type -> Type}
  `{Control.Monad.Zip.MonadZip f} `{Control.Monad.Zip.MonadZip g}
   : Control.Monad.Zip.MonadZip (Product f g) :=
  fun _ k__ =>
    k__ {| Control.Monad.Zip.munzip__ := fun (a : Type) (b : Type) =>
             MonadZip__Product_munzip ;
           Control.Monad.Zip.mzip__ := fun (a : Type) (b : Type) =>
             MonadZip__Product_mzip ;
           Control.Monad.Zip.mzipWith__ := fun (a : Type) (b : Type) (c : Type) =>
             MonadZip__Product_mzipWith |}.

#[local] Definition Semigroup__Product_op_zlzlzgzg__ {inst_k : Type} {inst_f
   : inst_k -> Type} {inst_a : inst_k} {inst_g : inst_k -> Type}
  `{GHC.Base.Semigroup (inst_f inst_a)} `{GHC.Base.Semigroup (inst_g inst_a)}
   : Product inst_f inst_g inst_a ->
     Product inst_f inst_g inst_a -> Product inst_f inst_g inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Pair x1 y1, Pair x2 y2 => Pair (x1 GHC.Base.<<>> x2) (y1 GHC.Base.<<>> y2)
    end.

#[global]
Program Instance Semigroup__Product {k : Type} {f : k -> Type} {a : k} {g
   : k -> Type} `{GHC.Base.Semigroup (f a)} `{GHC.Base.Semigroup (g a)}
   : GHC.Base.Semigroup (Product f g a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Product_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Product_mappend {inst_k : Type} {inst_f
   : inst_k -> Type} {inst_a : inst_k} {inst_g : inst_k -> Type} `{GHC.Base.Monoid
  (inst_f inst_a)} `{GHC.Base.Monoid (inst_g inst_a)}
   : Product inst_f inst_g inst_a ->
     Product inst_f inst_g inst_a -> Product inst_f inst_g inst_a :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__Product_mempty {inst_k : Type} {inst_f
   : inst_k -> Type} {inst_a : inst_k} {inst_g : inst_k -> Type} `{GHC.Base.Monoid
  (inst_f inst_a)} `{GHC.Base.Monoid (inst_g inst_a)}
   : Product inst_f inst_g inst_a :=
  Pair GHC.Base.mempty GHC.Base.mempty.

#[local] Definition Monoid__Product_mconcat {inst_k : Type} {inst_f
   : inst_k -> Type} {inst_a : inst_k} {inst_g : inst_k -> Type} `{GHC.Base.Monoid
  (inst_f inst_a)} `{GHC.Base.Monoid (inst_g inst_a)}
   : list (Product inst_f inst_g inst_a) -> Product inst_f inst_g inst_a :=
  GHC.Base.foldr Monoid__Product_mappend Monoid__Product_mempty.

#[global]
Program Instance Monoid__Product {k : Type} {f : k -> Type} {a : k} {g
   : k -> Type} `{GHC.Base.Monoid (f a)} `{GHC.Base.Monoid (g a)}
   : GHC.Base.Monoid (Product f g a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Product_mappend ;
           GHC.Base.mconcat__ := Monoid__Product_mconcat ;
           GHC.Base.mempty__ := Monoid__Product_mempty |}.

(* External variables:
     Type andb bool comparison false list op_zt__ pair true
     Control.Monad.Zip.MonadZip Control.Monad.Zip.munzip__ Control.Monad.Zip.mzipWith
     Control.Monad.Zip.mzipWith__ Control.Monad.Zip.mzip__
     Corelib.Program.Basics.compose Data.Foldable.Foldable Data.Foldable.foldMap
     Data.Foldable.foldMap'__ Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl'__ Data.Foldable.foldl__ Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length__ Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.Functor.Classes.Eq1 Data.Functor.Classes.Ord1
     Data.Functor.Classes.liftCompare Data.Functor.Classes.liftCompare__
     Data.Functor.Classes.liftEq Data.Functor.Classes.liftEq__
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     Data.Traversable.Traversable Data.Traversable.mapM__
     Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ Data.Tuple.fst
     Data.Tuple.snd GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.Semigroup GHC.Base.build' GHC.Base.flip GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.foldr GHC.Base.id GHC.Base.liftA2 GHC.Base.liftA2__
     GHC.Base.liftM GHC.Base.mappend GHC.Base.mappend__ GHC.Base.mconcat__
     GHC.Base.mempty GHC.Base.mempty__ GHC.Base.op_z2218U__ GHC.Base.op_zgzg____
     GHC.Base.op_zgzgze__ GHC.Base.op_zgzgze____ GHC.Base.op_zlzd__
     GHC.Base.op_zlzd____ GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____
     GHC.Base.op_zlztzg__ GHC.Base.op_zlztzg____ GHC.Base.op_ztzg____ GHC.Base.pure
     GHC.Base.pure__ GHC.Base.return___ GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger
     GHC.Num.op_zp__ GHC.Prim.seq GHC.Tuple.pair2
*)
