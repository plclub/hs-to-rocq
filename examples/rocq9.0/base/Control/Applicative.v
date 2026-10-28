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

Require Control.Arrow.
Require Control.Category.
Require Data.Tuple.
Require GHC.Base.
Require HsToRocq.Unpeel.
Import Control.Arrow.Notations.
Import Control.Category.Notations.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive WrappedMonad (m : Type -> Type) a : Type :=
  | WrapMonad (unwrapMonad : m a) : WrappedMonad m a.

Inductive WrappedArrow (a : Type -> Type -> Type) b c : Type :=
  | WrapArrow (unwrapArrow : a b c) : WrappedArrow a b c.

Arguments WrapMonad {_} {_} _.

Arguments WrapArrow {_} {_} {_} _.

#[global] Definition unwrapMonad {m : Type -> Type} {a} (arg_0__
    : WrappedMonad m a) :=
  let 'WrapMonad unwrapMonad := arg_0__ in
  unwrapMonad.

#[global] Definition unwrapArrow {a : Type -> Type -> Type} {b} {c} (arg_0__
    : WrappedArrow a b c) :=
  let 'WrapArrow unwrapArrow := arg_0__ in
  unwrapArrow.

(* Converted value declarations: *)

Instance Unpeel_WrappedMonad {m} {a}
   : HsToRocq.Unpeel.Unpeel (WrappedMonad m a) (m a) :=
  HsToRocq.Unpeel.Build_Unpeel _ _ unwrapMonad WrapMonad.

#[local] Definition Monad__WrappedMonad_op_zgzg__ {inst_m : Type -> Type}
  `{GHC.Base.Monad inst_m}
   : forall {a : Type},
     forall {b : Type},
     WrappedMonad inst_m a -> WrappedMonad inst_m b -> WrappedMonad inst_m b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      WrapMonad (_GHC.Base.>>_ (unwrapMonad arg_0__) (unwrapMonad arg_1__)).

#[local] Definition Monad__WrappedMonad_op_zgzgze__ {inst_m : Type -> Type}
  `{GHC.Base.Monad inst_m}
   : forall {a : Type},
     forall {b : Type},
     WrappedMonad inst_m a ->
     (a -> WrappedMonad inst_m b) -> WrappedMonad inst_m b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      WrapMonad (_GHC.Base.>>=_ (unwrapMonad arg_0__) (fun v_0__ =>
                                                         unwrapMonad (arg_1__ v_0__))).

#[local] Definition Monad__WrappedMonad_return_ {inst_m : Type -> Type}
  `{GHC.Base.Monad inst_m}
   : forall {a : Type}, a -> WrappedMonad inst_m a :=
  fun {a : Type} => fun arg_0__ => WrapMonad (GHC.Base.return_ arg_0__).

#[local] Definition Applicative__WrappedMonad_liftA2 {inst_m : Type -> Type}
  `{GHC.Base.Monad inst_m}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) ->
     WrappedMonad inst_m a -> WrappedMonad inst_m b -> WrappedMonad inst_m c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, WrapMonad x, WrapMonad y => WrapMonad (GHC.Base.liftM2 f x y)
      end.

#[local] Definition Applicative__WrappedMonad_op_zlztzg__ {inst_m
   : Type -> Type} `{GHC.Base.Monad inst_m}
   : forall {a : Type},
     forall {b : Type},
     WrappedMonad inst_m (a -> b) ->
     WrappedMonad inst_m a -> WrappedMonad inst_m b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | WrapMonad f, WrapMonad v => WrapMonad (GHC.Base.ap f v)
      end.

#[local] Definition Functor__WrappedMonad_fmap {inst_m : Type -> Type}
  `{GHC.Base.Monad inst_m}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> WrappedMonad inst_m a -> WrappedMonad inst_m b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, WrapMonad v => WrapMonad (GHC.Base.liftM f v)
      end.

#[local] Definition Functor__WrappedMonad_op_zlzd__ {inst_m : Type -> Type}
  `{GHC.Base.Monad inst_m}
   : forall {a : Type},
     forall {b : Type}, a -> WrappedMonad inst_m b -> WrappedMonad inst_m a :=
  fun {a : Type} {b : Type} =>
    Functor__WrappedMonad_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__WrappedMonad {m : Type -> Type} `{GHC.Base.Monad m}
   : GHC.Base.Functor (WrappedMonad m) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) =>
             Functor__WrappedMonad_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__WrappedMonad_op_zlzd__ |}.

#[local] Definition Applicative__WrappedMonad_op_ztzg__ {inst_m : Type -> Type}
  `{GHC.Base.Monad inst_m}
   : forall {a : Type},
     forall {b : Type},
     WrappedMonad inst_m a -> WrappedMonad inst_m b -> WrappedMonad inst_m b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 =>
      Applicative__WrappedMonad_op_zlztzg__ (GHC.Base.op_zlzd__ GHC.Base.id a1) a2.

#[local] Definition Applicative__WrappedMonad_pure {inst_m : Type -> Type}
  `{GHC.Base.Monad inst_m}
   : forall {a : Type}, a -> WrappedMonad inst_m a :=
  fun {a : Type} => WrapMonad GHC.Base.∘ GHC.Base.pure.

#[global]
Program Instance Applicative__WrappedMonad {m : Type -> Type} `{GHC.Base.Monad
  m}
   : GHC.Base.Applicative (WrappedMonad m) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__WrappedMonad_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__WrappedMonad_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__WrappedMonad_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__WrappedMonad_pure |}.

#[global]
Program Instance Monad__WrappedMonad {m : Type -> Type} `{GHC.Base.Monad m}
   : GHC.Base.Monad (WrappedMonad m) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__WrappedMonad_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) =>
             Monad__WrappedMonad_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__WrappedMonad_return_ |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Control.Applicative.Alternative__WrappedMonad' *)

#[local] Definition Functor__WrappedArrow_fmap {inst_a : Type -> Type -> Type}
  {inst_b : Type} `{Control.Arrow.Arrow inst_a}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) -> WrappedArrow inst_a inst_b a -> WrappedArrow inst_a inst_b b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, WrapArrow a => WrapArrow (a Control.Category.>>> Control.Arrow.arr f)
      end.

#[local] Definition Functor__WrappedArrow_op_zlzd__ {inst_a
   : Type -> Type -> Type} {inst_b : Type} `{Control.Arrow.Arrow inst_a}
   : forall {a : Type},
     forall {b : Type},
     a -> WrappedArrow inst_a inst_b b -> WrappedArrow inst_a inst_b a :=
  fun {a : Type} {b : Type} =>
    Functor__WrappedArrow_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__WrappedArrow {a : Type -> Type -> Type} {b : Type}
  `{Control.Arrow.Arrow a}
   : GHC.Base.Functor (WrappedArrow a b) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) =>
             Functor__WrappedArrow_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__WrappedArrow_op_zlzd__ |}.

#[local] Definition Applicative__WrappedArrow_liftA2 {inst_a
   : Type -> Type -> Type} {inst_b : Type} `{Control.Arrow.Arrow inst_a}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) ->
     WrappedArrow inst_a inst_b a ->
     WrappedArrow inst_a inst_b b -> WrappedArrow inst_a inst_b c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, WrapArrow u, WrapArrow v =>
          WrapArrow ((u Control.Arrow.&&& v) Control.Category.>>>
                     Control.Arrow.arr (Data.Tuple.uncurry f))
      end.

#[local] Definition Applicative__WrappedArrow_op_zlztzg__ {inst_a
   : Type -> Type -> Type} {inst_b : Type} `{Control.Arrow.Arrow inst_a}
   : forall {a : Type},
     forall {b : Type},
     WrappedArrow inst_a inst_b (a -> b) ->
     WrappedArrow inst_a inst_b a -> WrappedArrow inst_a inst_b b :=
  fun {a : Type} {b : Type} => Applicative__WrappedArrow_liftA2 GHC.Base.id.

#[local] Definition Applicative__WrappedArrow_op_ztzg__ {inst_a
   : Type -> Type -> Type} {inst_b : Type} `{Control.Arrow.Arrow inst_a}
   : forall {a : Type},
     forall {b : Type},
     WrappedArrow inst_a inst_b a ->
     WrappedArrow inst_a inst_b b -> WrappedArrow inst_a inst_b b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 =>
      Applicative__WrappedArrow_op_zlztzg__ (GHC.Base.op_zlzd__ GHC.Base.id a1) a2.

#[local] Definition Applicative__WrappedArrow_pure {inst_a
   : Type -> Type -> Type} {inst_b : Type} `{Control.Arrow.Arrow inst_a}
   : forall {a : Type}, a -> WrappedArrow inst_a inst_b a :=
  fun {a : Type} => fun x => WrapArrow (Control.Arrow.arr (GHC.Base.const x)).

#[global]
Program Instance Applicative__WrappedArrow {a : Type -> Type -> Type} {b : Type}
  `{Control.Arrow.Arrow a}
   : GHC.Base.Applicative (WrappedArrow a b) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__WrappedArrow_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__WrappedArrow_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__WrappedArrow_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__WrappedArrow_pure |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Control.Applicative.Alternative__WrappedArrow' *)

(* Skipping definition `Control.Applicative.optional' *)

Instance Unpeel_WrappedArrow {a} {b} {c}
   : HsToRocq.Unpeel.Unpeel (WrappedArrow a b c) (a b c) :=
  HsToRocq.Unpeel.Build_Unpeel _ _ unwrapArrow WrapArrow.

(* External variables:
     Type Control.Arrow.Arrow Control.Arrow.arr Control.Arrow.op_zazaza__
     Control.Category.op_zgzgzg__ Data.Tuple.uncurry GHC.Base.Applicative
     GHC.Base.Functor GHC.Base.Monad GHC.Base.ap GHC.Base.const GHC.Base.fmap__
     GHC.Base.id GHC.Base.liftA2__ GHC.Base.liftM GHC.Base.liftM2
     GHC.Base.op_z2218U__ GHC.Base.op_zgzg__ GHC.Base.op_zgzg____
     GHC.Base.op_zgzgze__ GHC.Base.op_zgzgze____ GHC.Base.op_zlzd__
     GHC.Base.op_zlzd____ GHC.Base.op_zlztzg____ GHC.Base.op_ztzg____ GHC.Base.pure
     GHC.Base.pure__ GHC.Base.return_ GHC.Base.return___ HsToRocq.Unpeel.Build_Unpeel
     HsToRocq.Unpeel.Unpeel
*)
