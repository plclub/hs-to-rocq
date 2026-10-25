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

(* A hack to make a few kind-polymorpic definitions go through *)
Class unit_class.
Instance unit_class_instance : unit_class := {}.
Implicit Type inst_k: unit_class.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Num.
Require HsToRocq.Err.
Require HsToRocq.Unpeel.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Sum a : Type := | Mk_Sum (getSum : a) : Sum a.

Inductive Product a : Type := | Mk_Product (getProduct : a) : Product a.

Inductive Endo a : Type := | Mk_Endo (appEndo : a -> a) : Endo a.

Inductive Dual a : Type := | Mk_Dual (getDual : a) : Dual a.

Inductive Any : Type := | Mk_Any (getAny : bool) : Any.

Inductive Alt {k : Type} (f : k -> Type) (a : k) : Type :=
  | Mk_Alt (getAlt : f a) : Alt f a.

Inductive All : Type := | Mk_All (getAll : bool) : All.

Arguments Mk_Sum {_} _.

Arguments Mk_Product {_} _.

Arguments Mk_Endo {_} _.

Arguments Mk_Dual {_} _.

Arguments Mk_Alt {_} {_} {_} _.

Instance Default__Any : HsToRocq.Err.Default Any :=
  HsToRocq.Err.Build_Default _ (Mk_Any HsToRocq.Err.default).

Instance Default__All : HsToRocq.Err.Default All :=
  HsToRocq.Err.Build_Default _ (Mk_All HsToRocq.Err.default).

#[global] Definition getSum {a} (arg_0__ : Sum a) :=
  let 'Mk_Sum getSum := arg_0__ in
  getSum.

#[global] Definition getProduct {a} (arg_0__ : Product a) :=
  let 'Mk_Product getProduct := arg_0__ in
  getProduct.

#[global] Definition appEndo {a} (arg_0__ : Endo a) :=
  let 'Mk_Endo appEndo := arg_0__ in
  appEndo.

#[global] Definition getDual {a} (arg_0__ : Dual a) :=
  let 'Mk_Dual getDual := arg_0__ in
  getDual.

#[global] Definition getAny (arg_0__ : Any) :=
  let 'Mk_Any getAny := arg_0__ in
  getAny.

#[global] Definition getAlt {k : Type} {f : k -> Type} {a : k} (arg_0__
    : Alt f a) :=
  let 'Mk_Alt getAlt := arg_0__ in
  getAlt.

#[global] Definition getAll (arg_0__ : All) :=
  let 'Mk_All getAll := arg_0__ in
  getAll.

(* Midamble *)

Instance Unpeel_Alt (k : Type) (f : k -> Type) (a : k) : HsToRocq.Unpeel.Unpeel (Alt f a) (f a) :=
    HsToRocq.Unpeel.Build_Unpeel _ _ getAlt Mk_Alt.

(* Converted value declarations: *)

#[local] Definition Monad__Alt_op_zgzg__ {inst_f : Type -> Type}
  `{GHC.Base.Monad inst_f}
   : forall {a : Type},
     forall {b : Type}, Alt inst_f a -> Alt inst_f b -> Alt inst_f b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Alt (_GHC.Base.>>_ (getAlt arg_0__) (getAlt arg_1__)).

#[local] Definition Monad__Alt_op_zgzgze__ {inst_f : Type -> Type}
  `{GHC.Base.Monad inst_f}
   : forall {a : Type},
     forall {b : Type}, Alt inst_f a -> (a -> Alt inst_f b) -> Alt inst_f b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      Mk_Alt (_GHC.Base.>>=_ (getAlt arg_0__) (fun v_0__ => getAlt (arg_1__ v_0__))).

#[local] Definition Monad__Alt_return_ {inst_f : Type -> Type} `{GHC.Base.Monad
  inst_f}
   : forall {a : Type}, a -> Alt inst_f a :=
  fun {a : Type} => fun arg_0__ => Mk_Alt (GHC.Base.return_ arg_0__).

#[local] Definition Applicative__Alt_liftA2 {inst_f : Type -> Type}
  `{GHC.Base.Applicative inst_f}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) -> Alt inst_f a -> Alt inst_f b -> Alt inst_f c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      Mk_Alt (GHC.Base.liftA2 arg_0__ (getAlt arg_1__) (getAlt arg_2__)).

#[local] Definition Applicative__Alt_op_zlztzg__ {inst_f : Type -> Type}
  `{GHC.Base.Applicative inst_f}
   : forall {a : Type},
     forall {b : Type}, Alt inst_f (a -> b) -> Alt inst_f a -> Alt inst_f b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      Mk_Alt (_GHC.Base.<*>_ (getAlt arg_0__) (getAlt arg_1__)).

#[local] Definition Applicative__Alt_op_ztzg__ {inst_f : Type -> Type}
  `{GHC.Base.Applicative inst_f}
   : forall {a : Type},
     forall {b : Type}, Alt inst_f a -> Alt inst_f b -> Alt inst_f b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Alt (_GHC.Base.*>_ (getAlt arg_0__) (getAlt arg_1__)).

#[local] Definition Applicative__Alt_pure {inst_f : Type -> Type}
  `{GHC.Base.Applicative inst_f}
   : forall {a : Type}, a -> Alt inst_f a :=
  fun {a : Type} => fun arg_0__ => Mk_Alt (GHC.Base.pure arg_0__).

#[local] Definition Functor__Alt_fmap {inst_f : Type -> Type} `{GHC.Base.Functor
  inst_f}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> Alt inst_f a -> Alt inst_f b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Alt (GHC.Base.fmap arg_0__ (getAlt arg_1__)).

#[local] Definition Functor__Alt_op_zlzd__ {inst_f : Type -> Type}
  `{GHC.Base.Functor inst_f}
   : forall {a : Type}, forall {b : Type}, a -> Alt inst_f b -> Alt inst_f a :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Alt (GHC.Base.op_zlzd__ arg_0__ (getAlt arg_1__)).

#[global]
Program Instance Functor__Alt {f : Type -> Type} `{GHC.Base.Functor f}
   : GHC.Base.Functor (Alt f) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Alt_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) => Functor__Alt_op_zlzd__ |}.

#[global]
Program Instance Applicative__Alt {f : Type -> Type} `{GHC.Base.Applicative f}
   : GHC.Base.Applicative (Alt f) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__Alt_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Alt_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Alt_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__Alt_pure |}.

#[global]
Program Instance Monad__Alt {f : Type -> Type} `{GHC.Base.Monad f}
   : GHC.Base.Monad (Alt f) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__Alt_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) => Monad__Alt_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__Alt_return_ |}.

Instance Unpeel_Dual a : HsToRocq.Unpeel.Unpeel (Dual a) a :=
  HsToRocq.Unpeel.Build_Unpeel _ _ getDual Mk_Dual.

#[local] Definition Semigroup__Dual_op_zlzlzgzg__ {inst_a : Type}
  `{GHC.Base.Semigroup inst_a}
   : Dual inst_a -> Dual inst_a -> Dual inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Dual a, Mk_Dual b => Mk_Dual (b GHC.Base.<<>> a)
    end.

#[global]
Program Instance Semigroup__Dual {a : Type} `{GHC.Base.Semigroup a}
   : GHC.Base.Semigroup (Dual a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Dual_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Dual_mappend {inst_a : Type} `{GHC.Base.Monoid
  inst_a}
   : Dual inst_a -> Dual inst_a -> Dual inst_a :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__Dual_mempty {inst_a : Type} `{GHC.Base.Monoid
  inst_a}
   : Dual inst_a :=
  Mk_Dual GHC.Base.mempty.

#[local] Definition Monoid__Dual_mconcat {inst_a : Type} `{GHC.Base.Monoid
  inst_a}
   : list (Dual inst_a) -> Dual inst_a :=
  GHC.Base.foldr Monoid__Dual_mappend Monoid__Dual_mempty.

#[global]
Program Instance Monoid__Dual {a : Type} `{GHC.Base.Monoid a}
   : GHC.Base.Monoid (Dual a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Dual_mappend ;
           GHC.Base.mconcat__ := Monoid__Dual_mconcat ;
           GHC.Base.mempty__ := Monoid__Dual_mempty |}.

#[local] Definition Functor__Dual_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Dual a -> Dual b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Dual (arg_0__ (getDual arg_1__)).

#[local] Definition Functor__Dual_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> Dual b -> Dual a :=
  fun {a : Type} {b : Type} => Functor__Dual_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__Dual : GHC.Base.Functor Dual :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Dual_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) => Functor__Dual_op_zlzd__ |}.

#[local] Definition Applicative__Dual_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, Dual (a -> b) -> Dual a -> Dual b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Dual (getDual arg_0__ (getDual arg_1__)).

#[local] Definition Applicative__Dual_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Dual a -> Dual b -> Dual c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__Dual_op_zlztzg__ (GHC.Base.fmap f x).

#[local] Definition Applicative__Dual_op_ztzg__
   : forall {a : Type}, forall {b : Type}, Dual a -> Dual b -> Dual b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 =>
      Applicative__Dual_op_zlztzg__ (GHC.Base.op_zlzd__ GHC.Base.id a1) a2.

#[local] Definition Applicative__Dual_pure : forall {a : Type}, a -> Dual a :=
  fun {a : Type} => Mk_Dual.

#[global]
Program Instance Applicative__Dual : GHC.Base.Applicative Dual :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__Dual_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Dual_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Dual_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__Dual_pure |}.

#[local] Definition Monad__Dual_op_zgzgze__
   : forall {a : Type}, forall {b : Type}, Dual a -> (a -> Dual b) -> Dual b :=
  fun {a : Type} {b : Type} => fun m k => k (getDual m).

#[local] Definition Monad__Dual_op_zgzg__
   : forall {a : Type}, forall {b : Type}, Dual a -> Dual b -> Dual b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__Dual_op_zgzgze__ m (fun arg_0__ => k).

#[local] Definition Monad__Dual_return_ : forall {a : Type}, a -> Dual a :=
  fun {a : Type} => GHC.Base.pure.

#[global]
Program Instance Monad__Dual : GHC.Base.Monad Dual :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__Dual_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) => Monad__Dual_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__Dual_return_ |}.

Instance Unpeel_Endo a : HsToRocq.Unpeel.Unpeel (Endo a) (a -> a) :=
  HsToRocq.Unpeel.Build_Unpeel _ _ appEndo Mk_Endo.

#[local] Definition Semigroup__Endo_op_zlzlzgzg__ {inst_a : Type}
   : Endo inst_a -> Endo inst_a -> Endo inst_a :=
  fun arg_0__ arg_1__ =>
    Mk_Endo (_GHC.Base.∘_ (appEndo arg_0__) (appEndo arg_1__)).

#[global]
Program Instance Semigroup__Endo {a : Type} : GHC.Base.Semigroup (Endo a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Endo_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Endo_mappend {inst_a : Type}
   : Endo inst_a -> Endo inst_a -> Endo inst_a :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__Endo_mempty {inst_a : Type} : Endo inst_a :=
  Mk_Endo GHC.Base.id.

#[local] Definition Monoid__Endo_mconcat {inst_a : Type}
   : list (Endo inst_a) -> Endo inst_a :=
  GHC.Base.foldr Monoid__Endo_mappend Monoid__Endo_mempty.

#[global]
Program Instance Monoid__Endo {a : Type} : GHC.Base.Monoid (Endo a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Endo_mappend ;
           GHC.Base.mconcat__ := Monoid__Endo_mconcat ;
           GHC.Base.mempty__ := Monoid__Endo_mempty |}.

Instance Unpeel_All : HsToRocq.Unpeel.Unpeel All bool :=
  HsToRocq.Unpeel.Build_Unpeel _ _ getAll Mk_All.

#[local] Definition Semigroup__All_op_zlzlzgzg__ : All -> All -> All :=
  fun arg_0__ arg_1__ => Mk_All (andb (getAll arg_0__) (getAll arg_1__)).

#[global]
Program Instance Semigroup__All : GHC.Base.Semigroup All :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__All_op_zlzlzgzg__ |}.

#[local] Definition Monoid__All_mappend : All -> All -> All :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__All_mempty : All :=
  Mk_All true.

#[local] Definition Monoid__All_mconcat : list All -> All :=
  GHC.Base.foldr Monoid__All_mappend Monoid__All_mempty.

#[global]
Program Instance Monoid__All : GHC.Base.Monoid All :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__All_mappend ;
           GHC.Base.mconcat__ := Monoid__All_mconcat ;
           GHC.Base.mempty__ := Monoid__All_mempty |}.

Instance Unpeel_Any : HsToRocq.Unpeel.Unpeel Any bool :=
  HsToRocq.Unpeel.Build_Unpeel _ _ getAny Mk_Any.

#[local] Definition Semigroup__Any_op_zlzlzgzg__ : Any -> Any -> Any :=
  fun arg_0__ arg_1__ => Mk_Any (orb (getAny arg_0__) (getAny arg_1__)).

#[global]
Program Instance Semigroup__Any : GHC.Base.Semigroup Any :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Any_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Any_mappend : Any -> Any -> Any :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__Any_mempty : Any :=
  Mk_Any false.

#[local] Definition Monoid__Any_mconcat : list Any -> Any :=
  GHC.Base.foldr Monoid__Any_mappend Monoid__Any_mempty.

#[global]
Program Instance Monoid__Any : GHC.Base.Monoid Any :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Any_mappend ;
           GHC.Base.mconcat__ := Monoid__Any_mconcat ;
           GHC.Base.mempty__ := Monoid__Any_mempty |}.

Instance Unpeel_Sum a : HsToRocq.Unpeel.Unpeel (Sum a) a :=
  HsToRocq.Unpeel.Build_Unpeel _ _ getSum Mk_Sum.

#[local] Definition Semigroup__Sum_op_zlzlzgzg__ {inst_a : Type} `{GHC.Num.Num
  inst_a}
   : Sum inst_a -> Sum inst_a -> Sum inst_a :=
  fun arg_0__ arg_1__ => Mk_Sum (_GHC.Num.+_ (getSum arg_0__) (getSum arg_1__)).

#[global]
Program Instance Semigroup__Sum {a : Type} `{GHC.Num.Num a}
   : GHC.Base.Semigroup (Sum a) :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Sum_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Sum_mappend {inst_a : Type} `{GHC.Num.Num inst_a}
   : Sum inst_a -> Sum inst_a -> Sum inst_a :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__Sum_mempty {inst_a : Type} `{GHC.Num.Num inst_a}
   : Sum inst_a :=
  Mk_Sum #0.

#[local] Definition Monoid__Sum_mconcat {inst_a : Type} `{GHC.Num.Num inst_a}
   : list (Sum inst_a) -> Sum inst_a :=
  GHC.Base.foldr Monoid__Sum_mappend Monoid__Sum_mempty.

#[global]
Program Instance Monoid__Sum {a : Type} `{GHC.Num.Num a}
   : GHC.Base.Monoid (Sum a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Sum_mappend ;
           GHC.Base.mconcat__ := Monoid__Sum_mconcat ;
           GHC.Base.mempty__ := Monoid__Sum_mempty |}.

#[local] Definition Functor__Sum_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Sum a -> Sum b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Sum (arg_0__ (getSum arg_1__)).

#[local] Definition Functor__Sum_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> Sum b -> Sum a :=
  fun {a : Type} {b : Type} => Functor__Sum_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__Sum : GHC.Base.Functor Sum :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Sum_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) => Functor__Sum_op_zlzd__ |}.

#[local] Definition Applicative__Sum_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, Sum (a -> b) -> Sum a -> Sum b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Sum (getSum arg_0__ (getSum arg_1__)).

#[local] Definition Applicative__Sum_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Sum a -> Sum b -> Sum c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__Sum_op_zlztzg__ (GHC.Base.fmap f x).

#[local] Definition Applicative__Sum_op_ztzg__
   : forall {a : Type}, forall {b : Type}, Sum a -> Sum b -> Sum b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 =>
      Applicative__Sum_op_zlztzg__ (GHC.Base.op_zlzd__ GHC.Base.id a1) a2.

#[local] Definition Applicative__Sum_pure : forall {a : Type}, a -> Sum a :=
  fun {a : Type} => Mk_Sum.

#[global]
Program Instance Applicative__Sum : GHC.Base.Applicative Sum :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__Sum_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Sum_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Sum_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__Sum_pure |}.

#[local] Definition Monad__Sum_op_zgzgze__
   : forall {a : Type}, forall {b : Type}, Sum a -> (a -> Sum b) -> Sum b :=
  fun {a : Type} {b : Type} => fun m k => k (getSum m).

#[local] Definition Monad__Sum_op_zgzg__
   : forall {a : Type}, forall {b : Type}, Sum a -> Sum b -> Sum b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__Sum_op_zgzgze__ m (fun arg_0__ => k).

#[local] Definition Monad__Sum_return_ : forall {a : Type}, a -> Sum a :=
  fun {a : Type} => GHC.Base.pure.

#[global]
Program Instance Monad__Sum : GHC.Base.Monad Sum :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__Sum_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) => Monad__Sum_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__Sum_return_ |}.

Instance Unpeel_Product a : HsToRocq.Unpeel.Unpeel (Product a) a :=
  HsToRocq.Unpeel.Build_Unpeel _ _ getProduct Mk_Product.

#[local] Definition Semigroup__Product_op_zlzlzgzg__ {inst_a : Type}
  `{GHC.Num.Num inst_a}
   : Product inst_a -> Product inst_a -> Product inst_a :=
  fun arg_0__ arg_1__ =>
    Mk_Product (_GHC.Num.*_ (getProduct arg_0__) (getProduct arg_1__)).

#[global]
Program Instance Semigroup__Product {a : Type} `{GHC.Num.Num a}
   : GHC.Base.Semigroup (Product a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Product_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Product_mappend {inst_a : Type} `{GHC.Num.Num
  inst_a}
   : Product inst_a -> Product inst_a -> Product inst_a :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__Product_mempty {inst_a : Type} `{GHC.Num.Num inst_a}
   : Product inst_a :=
  Mk_Product #1.

#[local] Definition Monoid__Product_mconcat {inst_a : Type} `{GHC.Num.Num
  inst_a}
   : list (Product inst_a) -> Product inst_a :=
  GHC.Base.foldr Monoid__Product_mappend Monoid__Product_mempty.

#[global]
Program Instance Monoid__Product {a : Type} `{GHC.Num.Num a}
   : GHC.Base.Monoid (Product a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Product_mappend ;
           GHC.Base.mconcat__ := Monoid__Product_mconcat ;
           GHC.Base.mempty__ := Monoid__Product_mempty |}.

#[local] Definition Functor__Product_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Product a -> Product b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Product (arg_0__ (getProduct arg_1__)).

#[local] Definition Functor__Product_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> Product b -> Product a :=
  fun {a : Type} {b : Type} => Functor__Product_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__Product : GHC.Base.Functor Product :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Product_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__Product_op_zlzd__ |}.

#[local] Definition Applicative__Product_op_zlztzg__
   : forall {a : Type},
     forall {b : Type}, Product (a -> b) -> Product a -> Product b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Product (getProduct arg_0__ (getProduct arg_1__)).

#[local] Definition Applicative__Product_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Product a -> Product b -> Product c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__Product_op_zlztzg__ (GHC.Base.fmap f x).

#[local] Definition Applicative__Product_op_ztzg__
   : forall {a : Type}, forall {b : Type}, Product a -> Product b -> Product b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 =>
      Applicative__Product_op_zlztzg__ (GHC.Base.op_zlzd__ GHC.Base.id a1) a2.

#[local] Definition Applicative__Product_pure
   : forall {a : Type}, a -> Product a :=
  fun {a : Type} => Mk_Product.

#[global]
Program Instance Applicative__Product : GHC.Base.Applicative Product :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__Product_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Product_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Product_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__Product_pure |}.

#[local] Definition Monad__Product_op_zgzgze__
   : forall {a : Type},
     forall {b : Type}, Product a -> (a -> Product b) -> Product b :=
  fun {a : Type} {b : Type} => fun m k => k (getProduct m).

#[local] Definition Monad__Product_op_zgzg__
   : forall {a : Type}, forall {b : Type}, Product a -> Product b -> Product b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__Product_op_zgzgze__ m (fun arg_0__ => k).

#[local] Definition Monad__Product_return_
   : forall {a : Type}, a -> Product a :=
  fun {a : Type} => GHC.Base.pure.

#[global]
Program Instance Monad__Product : GHC.Base.Monad Product :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__Product_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) =>
             Monad__Product_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__Product_return_ |}.

(* Skipping instance `Data.SemigroupInternal.Semigroup__Alt' of class
   `GHC.Base.Semigroup' *)

(* Skipping instance `Data.SemigroupInternal.Monoid__Alt' of class
   `GHC.Base.Monoid' *)

(* Skipping definition `Data.SemigroupInternal.stimesIdempotent' *)

(* Skipping definition `Data.SemigroupInternal.stimesIdempotentMonoid' *)

(* Skipping definition `Data.SemigroupInternal.stimesMonoid' *)

(* Skipping definition `Data.SemigroupInternal.stimesEndoError' *)

(* External variables:
     Type andb bool false list orb true GHC.Base.Applicative GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Semigroup GHC.Base.const GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.foldr GHC.Base.id GHC.Base.liftA2 GHC.Base.liftA2__
     GHC.Base.mappend__ GHC.Base.mconcat__ GHC.Base.mempty GHC.Base.mempty__
     GHC.Base.op_z2218U__ GHC.Base.op_zgzg__ GHC.Base.op_zgzg____
     GHC.Base.op_zgzgze__ GHC.Base.op_zgzgze____ GHC.Base.op_zlzd__
     GHC.Base.op_zlzd____ GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____
     GHC.Base.op_zlztzg__ GHC.Base.op_zlztzg____ GHC.Base.op_ztzg__
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Base.return_
     GHC.Base.return___ GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__
     GHC.Num.op_zt__ HsToRocq.Err.Build_Default HsToRocq.Err.Default
     HsToRocq.Err.default HsToRocq.Unpeel.Build_Unpeel HsToRocq.Unpeel.Unpeel
*)
