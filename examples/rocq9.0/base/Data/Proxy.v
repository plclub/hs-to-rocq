(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Stdlib.Program.Tactics.
Require Stdlib.Program.Wf.
Require Import Stdlib.Program.WfExtensionality.

(* Preamble *)

Require Import GHC.Base.

(* Converted imports: *)

Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Proxy {k : Type} (t : k) : Set := | Mk_Proxy : Proxy t.

Inductive KProxy (t : Type) : Set := | Mk_KProxy : KProxy t.

Arguments Mk_Proxy {_} {_}.

Arguments Mk_KProxy {_}.

(* Converted value declarations: *)

#[local] Definition Eq___Proxy_op_zeze__ {inst_k : Type} {inst_s : inst_k}
   : Proxy inst_s -> Proxy inst_s -> bool :=
  fun arg_0__ arg_1__ => true.

#[local] Definition Eq___Proxy_op_zsze__ {inst_k : Type} {inst_s : inst_k}
   : Proxy inst_s -> Proxy inst_s -> bool :=
  fun x y => negb (Eq___Proxy_op_zeze__ x y).

#[global]
Program Instance Eq___Proxy {k : Type} {s : k} : GHC.Base.Eq_ (Proxy s) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Proxy_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Proxy_op_zsze__ |}.

#[local] Definition Ord__Proxy_compare {inst_k : Type} {inst_s : inst_k}
   : Proxy inst_s -> Proxy inst_s -> comparison :=
  fun arg_0__ arg_1__ => Eq.

#[local] Definition Ord__Proxy_op_zl__ {inst_k : Type} {inst_s : inst_k}
   : Proxy inst_s -> Proxy inst_s -> bool :=
  fun x y => Ord__Proxy_compare x y GHC.Base.== Lt.

#[local] Definition Ord__Proxy_op_zlze__ {inst_k : Type} {inst_s : inst_k}
   : Proxy inst_s -> Proxy inst_s -> bool :=
  fun x y => Ord__Proxy_compare x y GHC.Base./= Gt.

#[local] Definition Ord__Proxy_op_zg__ {inst_k : Type} {inst_s : inst_k}
   : Proxy inst_s -> Proxy inst_s -> bool :=
  fun x y => Ord__Proxy_compare x y GHC.Base.== Gt.

#[local] Definition Ord__Proxy_op_zgze__ {inst_k : Type} {inst_s : inst_k}
   : Proxy inst_s -> Proxy inst_s -> bool :=
  fun x y => Ord__Proxy_compare x y GHC.Base./= Lt.

#[local] Definition Ord__Proxy_max {inst_k : Type} {inst_s : inst_k}
   : Proxy inst_s -> Proxy inst_s -> Proxy inst_s :=
  fun x y => if Ord__Proxy_op_zlze__ x y : bool then y else x.

#[local] Definition Ord__Proxy_min {inst_k : Type} {inst_s : inst_k}
   : Proxy inst_s -> Proxy inst_s -> Proxy inst_s :=
  fun x y => if Ord__Proxy_op_zlze__ x y : bool then x else y.

#[global]
Program Instance Ord__Proxy {k : Type} {s : k} : GHC.Base.Ord (Proxy s) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Proxy_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Proxy_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Proxy_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Proxy_op_zgze__ ;
           GHC.Base.compare__ := Ord__Proxy_compare ;
           GHC.Base.max__ := Ord__Proxy_max ;
           GHC.Base.min__ := Ord__Proxy_min |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Proxy.Show__Proxy' *)

(* Skipping all instances of class `GHC.Enum.Enum', including
   `Data.Proxy.Enum__Proxy' *)

(* Skipping all instances of class `GHC.Ix.Ix', including
   `Data.Proxy.Ix__Proxy' *)

#[local] Definition Semigroup__Proxy_op_zlzlzgzg__ {inst_k : Type} {inst_s
   : inst_k}
   : Proxy inst_s -> Proxy inst_s -> Proxy inst_s :=
  fun arg_0__ arg_1__ => Mk_Proxy.

#[global]
Program Instance Semigroup__Proxy {k : Type} {s : k}
   : GHC.Base.Semigroup (Proxy s) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Proxy_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Proxy_mappend {inst_k : Type} {inst_s : inst_k}
   : Proxy inst_s -> Proxy inst_s -> Proxy inst_s :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__Proxy_mconcat {inst_k : Type} {inst_s : inst_k}
   : list (Proxy inst_s) -> Proxy inst_s :=
  fun arg_0__ => Mk_Proxy.

#[local] Definition Monoid__Proxy_mempty {inst_k : Type} {inst_s : inst_k}
   : Proxy inst_s :=
  Mk_Proxy.

#[global]
Program Instance Monoid__Proxy {k : Type} {s : k} : GHC.Base.Monoid (Proxy s) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Proxy_mappend ;
           GHC.Base.mconcat__ := Monoid__Proxy_mconcat ;
           GHC.Base.mempty__ := Monoid__Proxy_mempty |}.

#[local] Definition Functor__Proxy_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Proxy a -> Proxy b :=
  fun {a : Type} {b : Type} => fun arg_0__ arg_1__ => Mk_Proxy.

#[local] Definition Functor__Proxy_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> Proxy b -> Proxy a :=
  fun {a : Type} {b : Type} => Functor__Proxy_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__Proxy : GHC.Base.Functor Proxy :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Proxy_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__Proxy_op_zlzd__ |}.

#[local] Definition Applicative__Proxy_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, Proxy (a -> b) -> Proxy a -> Proxy b :=
  fun {a : Type} {b : Type} => fun arg_0__ arg_1__ => Mk_Proxy.

#[local] Definition Applicative__Proxy_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Proxy a -> Proxy b -> Proxy c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__Proxy_op_zlztzg__ (GHC.Base.fmap f x).

#[local] Definition Applicative__Proxy_op_ztzg__
   : forall {a : Type}, forall {b : Type}, Proxy a -> Proxy b -> Proxy b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 =>
      Applicative__Proxy_op_zlztzg__ (GHC.Base.op_zlzd__ GHC.Base.id a1) a2.

#[local] Definition Applicative__Proxy_pure : forall {a : Type}, a -> Proxy a :=
  fun {a : Type} => fun arg_0__ => Mk_Proxy.

#[global]
Program Instance Applicative__Proxy : GHC.Base.Applicative Proxy :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__Proxy_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Proxy_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Proxy_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__Proxy_pure |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Data.Proxy.Alternative__Proxy' *)

#[local] Definition Monad__Proxy_op_zgzgze__
   : forall {a : Type}, forall {b : Type}, Proxy a -> (a -> Proxy b) -> Proxy b :=
  fun {a : Type} {b : Type} => fun arg_0__ arg_1__ => Mk_Proxy.

#[local] Definition Monad__Proxy_op_zgzg__
   : forall {a : Type}, forall {b : Type}, Proxy a -> Proxy b -> Proxy b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__Proxy_op_zgzgze__ m (fun arg_0__ => k).

#[local] Definition Monad__Proxy_return_ : forall {a : Type}, a -> Proxy a :=
  fun {a : Type} => GHC.Base.pure.

#[global]
Program Instance Monad__Proxy : GHC.Base.Monad Proxy :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__Proxy_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) =>
             Monad__Proxy_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__Proxy_return_ |}.

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `Data.Proxy.MonadPlus__Proxy' *)

#[global] Definition asProxyTypeOf {a : Type} {proxy : Type -> Type}
   : a -> proxy a -> a :=
  GHC.Base.const.

(* External variables:
     Eq Gt Lt Type bool comparison list negb true GHC.Base.Applicative GHC.Base.Eq_
     GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup
     GHC.Base.compare__ GHC.Base.const GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id
     GHC.Base.liftA2__ GHC.Base.mappend__ GHC.Base.max__ GHC.Base.mconcat__
     GHC.Base.mempty__ GHC.Base.min__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____
     GHC.Base.op_zgzg____ GHC.Base.op_zgzgze____ GHC.Base.op_zl____
     GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlze____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Base.op_zlztzg____
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Base.op_ztzg____ GHC.Base.pure
     GHC.Base.pure__ GHC.Base.return___
*)
