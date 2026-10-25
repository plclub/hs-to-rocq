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

Require GHC.Base.
Require HsToRocq.Unpeel.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Down a : Type := | Mk_Down (getDown : a) : Down a.

Arguments Mk_Down {_} _.

#[global] Definition getDown {a} (arg_0__ : Down a) :=
  let 'Mk_Down getDown := arg_0__ in
  getDown.

(* Midamble *)

(* Eq instance for Down -- the derived instance uses coerce which gets lost *)
#[local] Definition Eq___Down_op_zeze__ {inst_a : Type} `{GHC.Base.Eq_ inst_a}
   : Down inst_a -> Down inst_a -> bool :=
  fun x y => match x, y with | Mk_Down a, Mk_Down b => a GHC.Base.== b end.

#[local] Definition Eq___Down_op_zsze__ {inst_a : Type} `{GHC.Base.Eq_ inst_a}
   : Down inst_a -> Down inst_a -> bool :=
  fun x y => match x, y with | Mk_Down a, Mk_Down b => a GHC.Base./= b end.

#[global]
Program Instance Eq___Down {a : Type} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Down a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Down_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Down_op_zsze__ |}.

(* Converted value declarations: *)

#[local] Definition Semigroup__Down_op_zlzlzgzg__ {inst_a : Type}
  `{GHC.Base.Semigroup inst_a}
   : Down inst_a -> Down inst_a -> Down inst_a :=
  fun arg_0__ arg_1__ =>
    Mk_Down (_GHC.Base.<<>>_ (getDown arg_0__) (getDown arg_1__)).

#[global]
Program Instance Semigroup__Down {a : Type} `{GHC.Base.Semigroup a}
   : GHC.Base.Semigroup (Down a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Down_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Down_mappend {inst_a : Type} `{GHC.Base.Monoid
  inst_a}
   : Down inst_a -> Down inst_a -> Down inst_a :=
  fun arg_0__ arg_1__ =>
    Mk_Down (GHC.Base.mappend (getDown arg_0__) (getDown arg_1__)).

#[local] Definition Monoid__Down_mconcat {inst_a : Type} `{GHC.Base.Monoid
  inst_a}
   : list (Down inst_a) -> Down inst_a :=
  fun arg_0__ => Mk_Down (GHC.Base.mconcat (GHC.Base.map getDown arg_0__)).

#[local] Definition Monoid__Down_mempty {inst_a : Type} `{GHC.Base.Monoid
  inst_a}
   : Down inst_a :=
  Mk_Down GHC.Base.mempty.

#[global]
Program Instance Monoid__Down {a : Type} `{GHC.Base.Monoid a}
   : GHC.Base.Monoid (Down a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Down_mappend ;
           GHC.Base.mconcat__ := Monoid__Down_mconcat ;
           GHC.Base.mempty__ := Monoid__Down_mempty |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Ord.Read__Down' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Ord.Show__Down' *)

#[local] Definition Ord__Down_op_zl__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Down inst_a -> Down inst_a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Down x, Mk_Down y => y GHC.Base.< x
    end.

#[local] Definition Ord__Down_op_zlze__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Down inst_a -> Down inst_a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Down x, Mk_Down y => y GHC.Base.<= x
    end.

#[local] Definition Ord__Down_op_zg__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Down inst_a -> Down inst_a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Down x, Mk_Down y => y GHC.Base.> x
    end.

#[local] Definition Ord__Down_op_zgze__ {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Down inst_a -> Down inst_a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Down x, Mk_Down y => y GHC.Base.>= x
    end.

#[local] Definition Ord__Down_compare {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Down inst_a -> Down inst_a -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Down x, Mk_Down y => GHC.Base.compare y x
    end.

#[local] Definition Ord__Down_max {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Down inst_a -> Down inst_a -> Down inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Down x, Mk_Down y => Mk_Down (GHC.Base.min x y)
    end.

#[local] Definition Ord__Down_min {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Down inst_a -> Down inst_a -> Down inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Down x, Mk_Down y => Mk_Down (GHC.Base.max x y)
    end.

#[global]
Program Instance Ord__Down {a : Type} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Down a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Down_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Down_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Down_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Down_op_zgze__ ;
           GHC.Base.compare__ := Ord__Down_compare ;
           GHC.Base.max__ := Ord__Down_max ;
           GHC.Base.min__ := Ord__Down_min |}.

(* Skipping all instances of class `GHC.Enum.Bounded', including
   `Data.Ord.Bounded__Down' *)

(* Skipping all instances of class `GHC.Enum.Enum', including
   `Data.Ord.Enum__Down' *)

#[local] Definition Functor__Down_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Down a -> Down b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Down (arg_0__ (getDown arg_1__)).

#[local] Definition Functor__Down_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> Down b -> Down a :=
  fun {a : Type} {b : Type} => Functor__Down_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__Down : GHC.Base.Functor Down :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Down_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) => Functor__Down_op_zlzd__ |}.

#[local] Definition Applicative__Down_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, Down (a -> b) -> Down a -> Down b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Down (getDown arg_0__ (getDown arg_1__)).

#[local] Definition Applicative__Down_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Down a -> Down b -> Down c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__Down_op_zlztzg__ (GHC.Base.fmap f x).

#[local] Definition Applicative__Down_op_ztzg__
   : forall {a : Type}, forall {b : Type}, Down a -> Down b -> Down b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 =>
      Applicative__Down_op_zlztzg__ (GHC.Base.op_zlzd__ GHC.Base.id a1) a2.

#[local] Definition Applicative__Down_pure : forall {a : Type}, a -> Down a :=
  fun {a : Type} => Mk_Down.

#[global]
Program Instance Applicative__Down : GHC.Base.Applicative Down :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__Down_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Down_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Down_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__Down_pure |}.

#[local] Definition Monad__Down_op_zgzgze__
   : forall {a : Type}, forall {b : Type}, Down a -> (a -> Down b) -> Down b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | Mk_Down a, k => k a end.

#[local] Definition Monad__Down_op_zgzg__
   : forall {a : Type}, forall {b : Type}, Down a -> Down b -> Down b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__Down_op_zgzgze__ m (fun arg_0__ => k).

#[local] Definition Monad__Down_return_ : forall {a : Type}, a -> Down a :=
  fun {a : Type} => GHC.Base.pure.

#[global]
Program Instance Monad__Down : GHC.Base.Monad Down :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__Down_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) => Monad__Down_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__Down_return_ |}.

#[global] Definition comparing {a : Type} {b : Type} `{GHC.Base.Ord a}
   : (b -> a) -> b -> b -> comparison :=
  fun p x y => GHC.Base.compare (p x) (p y).

#[global] Definition clamp {a : Type} `{GHC.Base.Ord a}
   : (a * a)%type -> a -> a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair low high, a => GHC.Base.min high (GHC.Base.max a low)
    end.

Instance Unpeel_Down a : HsToRocq.Unpeel.Unpeel (Down a) a :=
  HsToRocq.Unpeel.Build_Unpeel _ _ (fun '(Mk_Down x) => x) Mk_Down.

(* External variables:
     Type bool comparison list op_zt__ pair GHC.Base.Applicative GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup GHC.Base.compare
     GHC.Base.compare__ GHC.Base.const GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id
     GHC.Base.liftA2__ GHC.Base.map GHC.Base.mappend GHC.Base.mappend__ GHC.Base.max
     GHC.Base.max__ GHC.Base.mconcat GHC.Base.mconcat__ GHC.Base.mempty
     GHC.Base.mempty__ GHC.Base.min GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zg__ GHC.Base.op_zg____ GHC.Base.op_zgze__ GHC.Base.op_zgze____
     GHC.Base.op_zgzg____ GHC.Base.op_zgzgze____ GHC.Base.op_zl__ GHC.Base.op_zl____
     GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlze__ GHC.Base.op_zlze____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Base.op_zlztzg____
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Base.return___
     HsToRocq.Unpeel.Build_Unpeel HsToRocq.Unpeel.Unpeel
*)
