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

Require Control.Monad.Fail.
Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Last a : Type := | Mk_Last (getLast : option a) : Last a.

Inductive First a : Type := | Mk_First (getFirst : option a) : First a.

Inductive Ap (f : Type -> Type) (a : Type) : Type :=
  | Mk_Ap (getAp : f a) : Ap f a.

Arguments Mk_Last {_} _.

Arguments Mk_First {_} _.

#[global] Definition getLast {a} (arg_0__ : Last a) :=
  let 'Mk_Last getLast := arg_0__ in
  getLast.

#[global] Definition getFirst {a} (arg_0__ : First a) :=
  let 'Mk_First getFirst := arg_0__ in
  getFirst.

(* Midamble *)

(* Fix implicit arguments for Mk_Ap after redefine *)
Arguments Mk_Ap {_} {_} _.

(* getAp accessor -- needed since redefine Inductive doesn't auto-generate it *)
Definition getAp {f : Type -> Type} {a : Type} (x : Ap f a) : f a :=
  let 'Mk_Ap v := x in v.

(* Eq/Ord for First -- GHC 9.10 derives using dataToTag# *)

Definition eq_First {a} `{GHC.Base.Eq_ a} (x y : First a) : bool :=
  match x, y with
  | Mk_First a1, Mk_First b1 => a1 GHC.Base.== b1
  end.

#[global]
Instance Eq___First {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (First a) :=
  fun _ k => k {|
  GHC.Base.op_zeze____ := eq_First;
  GHC.Base.op_zsze____ := fun x y => negb (eq_First x y) |}.

#[global]
Instance Ord__First {a} `{GHC.Base.Ord a} : GHC.Base.Ord (First a) :=
  GHC.Base.ord_default (fun x y =>
    match x, y with
    | Mk_First a1, Mk_First b1 => GHC.Base.compare a1 b1
    end).

(* Eq/Ord for Last -- GHC 9.10 derives using dataToTag# *)

Definition eq_Last {a} `{GHC.Base.Eq_ a} (x y : Last a) : bool :=
  match x, y with
  | Mk_Last a1, Mk_Last b1 => a1 GHC.Base.== b1
  end.

#[global]
Instance Eq___Last {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Last a) :=
  fun _ k => k {|
  GHC.Base.op_zeze____ := eq_Last;
  GHC.Base.op_zsze____ := fun x y => negb (eq_Last x y) |}.

#[global]
Instance Ord__Last {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Last a) :=
  GHC.Base.ord_default (fun x y =>
    match x, y with
    | Mk_Last a1, Mk_Last b1 => GHC.Base.compare a1 b1
    end).

(* Converted value declarations: *)

#[local] Definition Applicative__Ap_liftA2 {inst_f : Type -> Type}
  `{GHC.Base.Applicative inst_f}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Ap inst_f a -> Ap inst_f b -> Ap inst_f c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      Mk_Ap (GHC.Base.liftA2 arg_0__ (getAp arg_1__) (getAp arg_2__)).

#[local] Definition Applicative__Ap_op_zlztzg__ {inst_f : Type -> Type}
  `{GHC.Base.Applicative inst_f}
   : forall {a : Type},
     forall {b : Type}, Ap inst_f (a -> b) -> Ap inst_f a -> Ap inst_f b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Ap (_GHC.Base.<*>_ (getAp arg_0__) (getAp arg_1__)).

#[local] Definition Applicative__Ap_op_ztzg__ {inst_f : Type -> Type}
  `{GHC.Base.Applicative inst_f}
   : forall {a : Type},
     forall {b : Type}, Ap inst_f a -> Ap inst_f b -> Ap inst_f b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Ap (_GHC.Base.*>_ (getAp arg_0__) (getAp arg_1__)).

#[local] Definition Applicative__Ap_pure {inst_f : Type -> Type}
  `{GHC.Base.Applicative inst_f}
   : forall {a : Type}, a -> Ap inst_f a :=
  fun {a : Type} => fun arg_0__ => Mk_Ap (GHC.Base.pure arg_0__).

#[local] Definition Functor__Ap_fmap {inst_f : Type -> Type} `{GHC.Base.Functor
  inst_f}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> Ap inst_f a -> Ap inst_f b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Ap (GHC.Base.fmap arg_0__ (getAp arg_1__)).

#[local] Definition Functor__Ap_op_zlzd__ {inst_f : Type -> Type}
  `{GHC.Base.Functor inst_f}
   : forall {a : Type}, forall {b : Type}, a -> Ap inst_f b -> Ap inst_f a :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Ap (GHC.Base.op_zlzd__ arg_0__ (getAp arg_1__)).

#[global]
Program Instance Functor__Ap {f : Type -> Type} `{GHC.Base.Functor f}
   : GHC.Base.Functor (Ap f) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Ap_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) => Functor__Ap_op_zlzd__ |}.

#[global]
Program Instance Applicative__Ap {f : Type -> Type} `{GHC.Base.Applicative f}
   : GHC.Base.Applicative (Ap f) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__Ap_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Ap_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) => Applicative__Ap_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__Ap_pure |}.

#[local] Definition Monad__Ap_op_zgzg__ {inst_f : Type -> Type} `{GHC.Base.Monad
  inst_f}
   : forall {a : Type},
     forall {b : Type}, Ap inst_f a -> Ap inst_f b -> Ap inst_f b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Ap (_GHC.Base.>>_ (getAp arg_0__) (getAp arg_1__)).

#[local] Definition Monad__Ap_op_zgzgze__ {inst_f : Type -> Type}
  `{GHC.Base.Monad inst_f}
   : forall {a : Type},
     forall {b : Type}, Ap inst_f a -> (a -> Ap inst_f b) -> Ap inst_f b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      Mk_Ap (_GHC.Base.>>=_ (getAp arg_0__) (fun v_0__ => getAp (arg_1__ v_0__))).

#[local] Definition Monad__Ap_return_ {inst_f : Type -> Type} `{GHC.Base.Monad
  inst_f}
   : forall {a : Type}, a -> Ap inst_f a :=
  fun {a : Type} => fun arg_0__ => Mk_Ap (GHC.Base.return_ arg_0__).

#[global]
Program Instance Monad__Ap {f : Type -> Type} `{GHC.Base.Monad f}
   : GHC.Base.Monad (Ap f) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__Ap_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) => Monad__Ap_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__Ap_return_ |}.

#[local] Definition MonadFail__Ap_fail {inst_f : Type -> Type}
  `{Control.Monad.Fail.MonadFail inst_f}
   : forall {a : Type}, GHC.Base.String -> Ap inst_f a :=
  fun {a : Type} => fun arg_0__ => Mk_Ap (Control.Monad.Fail.fail arg_0__).

#[global]
Program Instance MonadFail__Ap {f : Type -> Type} `{Control.Monad.Fail.MonadFail
  f}
   : Control.Monad.Fail.MonadFail (Ap f) :=
  fun _ k__ =>
    k__ {| Control.Monad.Fail.fail__ := fun (a : Type) => MonadFail__Ap_fail |}.

#[local] Definition Functor__Last_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Last a -> Last b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Last (GHC.Base.fmap arg_0__ (getLast arg_1__)).

#[local] Definition Functor__Last_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> Last b -> Last a :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_Last (GHC.Base.op_zlzd__ arg_0__ (getLast arg_1__)).

#[global]
Program Instance Functor__Last : GHC.Base.Functor Last :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Last_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) => Functor__Last_op_zlzd__ |}.

#[local] Definition Applicative__Last_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> Last a -> Last b -> Last c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      Mk_Last (GHC.Base.liftA2 arg_0__ (getLast arg_1__) (getLast arg_2__)).

#[local] Definition Applicative__Last_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, Last (a -> b) -> Last a -> Last b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      Mk_Last (_GHC.Base.<*>_ (getLast arg_0__) (getLast arg_1__)).

#[local] Definition Applicative__Last_op_ztzg__
   : forall {a : Type}, forall {b : Type}, Last a -> Last b -> Last b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      Mk_Last (_GHC.Base.*>_ (getLast arg_0__) (getLast arg_1__)).

#[local] Definition Applicative__Last_pure : forall {a : Type}, a -> Last a :=
  fun {a : Type} => fun arg_0__ => Mk_Last (GHC.Base.pure arg_0__).

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
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      Mk_Last (_GHC.Base.>>_ (getLast arg_0__) (getLast arg_1__)).

#[local] Definition Monad__Last_op_zgzgze__
   : forall {a : Type}, forall {b : Type}, Last a -> (a -> Last b) -> Last b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      Mk_Last (_GHC.Base.>>=_ (getLast arg_0__) (fun v_0__ =>
                                                   getLast (arg_1__ v_0__))).

#[local] Definition Monad__Last_return_ : forall {a : Type}, a -> Last a :=
  fun {a : Type} => fun arg_0__ => Mk_Last (GHC.Base.return_ arg_0__).

#[global]
Program Instance Monad__Last : GHC.Base.Monad Last :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__Last_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) => Monad__Last_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__Last_return_ |}.

#[local] Definition Functor__First_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> First a -> First b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_First (GHC.Base.fmap arg_0__ (getFirst arg_1__)).

#[local] Definition Functor__First_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> First b -> First a :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ => Mk_First (GHC.Base.op_zlzd__ arg_0__ (getFirst arg_1__)).

#[global]
Program Instance Functor__First : GHC.Base.Functor First :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__First_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__First_op_zlzd__ |}.

#[local] Definition Applicative__First_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> First a -> First b -> First c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      Mk_First (GHC.Base.liftA2 arg_0__ (getFirst arg_1__) (getFirst arg_2__)).

#[local] Definition Applicative__First_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, First (a -> b) -> First a -> First b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      Mk_First (_GHC.Base.<*>_ (getFirst arg_0__) (getFirst arg_1__)).

#[local] Definition Applicative__First_op_ztzg__
   : forall {a : Type}, forall {b : Type}, First a -> First b -> First b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      Mk_First (_GHC.Base.*>_ (getFirst arg_0__) (getFirst arg_1__)).

#[local] Definition Applicative__First_pure : forall {a : Type}, a -> First a :=
  fun {a : Type} => fun arg_0__ => Mk_First (GHC.Base.pure arg_0__).

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
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      Mk_First (_GHC.Base.>>_ (getFirst arg_0__) (getFirst arg_1__)).

#[local] Definition Monad__First_op_zgzgze__
   : forall {a : Type}, forall {b : Type}, First a -> (a -> First b) -> First b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      Mk_First (_GHC.Base.>>=_ (getFirst arg_0__) (fun v_0__ =>
                                                     getFirst (arg_1__ v_0__))).

#[local] Definition Monad__First_return_ : forall {a : Type}, a -> First a :=
  fun {a : Type} => fun arg_0__ => Mk_First (GHC.Base.return_ arg_0__).

#[global]
Program Instance Monad__First : GHC.Base.Monad First :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__First_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) =>
             Monad__First_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__First_return_ |}.

#[local] Definition Semigroup__First_op_zlzlzgzg__ {inst_a : Type}
   : First inst_a -> First inst_a -> First inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_First None, b => b
    | a, _ => a
    end.

#[global]
Program Instance Semigroup__First {a : Type} : GHC.Base.Semigroup (First a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__First_op_zlzlzgzg__ |}.

#[local] Definition Monoid__First_mappend {inst_a : Type}
   : First inst_a -> First inst_a -> First inst_a :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__First_mempty {inst_a : Type} : First inst_a :=
  Mk_First None.

#[local] Definition Monoid__First_mconcat {inst_a : Type}
   : list (First inst_a) -> First inst_a :=
  GHC.Base.foldr Monoid__First_mappend Monoid__First_mempty.

#[global]
Program Instance Monoid__First {a : Type} : GHC.Base.Monoid (First a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__First_mappend ;
           GHC.Base.mconcat__ := Monoid__First_mconcat ;
           GHC.Base.mempty__ := Monoid__First_mempty |}.

#[local] Definition Semigroup__Last_op_zlzlzgzg__ {inst_a : Type}
   : Last inst_a -> Last inst_a -> Last inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | a, Mk_Last None => a
    | _, b => b
    end.

#[global]
Program Instance Semigroup__Last {a : Type} : GHC.Base.Semigroup (Last a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Last_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Last_mappend {inst_a : Type}
   : Last inst_a -> Last inst_a -> Last inst_a :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__Last_mempty {inst_a : Type} : Last inst_a :=
  Mk_Last None.

#[local] Definition Monoid__Last_mconcat {inst_a : Type}
   : list (Last inst_a) -> Last inst_a :=
  GHC.Base.foldr Monoid__Last_mappend Monoid__Last_mempty.

#[global]
Program Instance Monoid__Last {a : Type} : GHC.Base.Monoid (Last a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Last_mappend ;
           GHC.Base.mconcat__ := Monoid__Last_mconcat ;
           GHC.Base.mempty__ := Monoid__Last_mempty |}.

#[local] Definition Semigroup__Ap_op_zlzlzgzg__ {inst_f : Type -> Type} {inst_a
   : Type} `{GHC.Base.Applicative inst_f} `{GHC.Base.Semigroup inst_a}
   : Ap inst_f inst_a -> Ap inst_f inst_a -> Ap inst_f inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Ap x, Mk_Ap y => Mk_Ap (GHC.Base.liftA2 _GHC.Base.<<>>_ x y)
    end.

#[global]
Program Instance Semigroup__Ap {f : Type -> Type} {a : Type}
  `{GHC.Base.Applicative f} `{GHC.Base.Semigroup a}
   : GHC.Base.Semigroup (Ap f a) :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Ap_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Ap_mappend {inst_f : Type -> Type} {inst_a : Type}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Monoid inst_a}
   : Ap inst_f inst_a -> Ap inst_f inst_a -> Ap inst_f inst_a :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__Ap_mempty {inst_f : Type -> Type} {inst_a : Type}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Monoid inst_a}
   : Ap inst_f inst_a :=
  Mk_Ap (GHC.Base.pure GHC.Base.mempty).

#[local] Definition Monoid__Ap_mconcat {inst_f : Type -> Type} {inst_a : Type}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Monoid inst_a}
   : list (Ap inst_f inst_a) -> Ap inst_f inst_a :=
  GHC.Base.foldr Monoid__Ap_mappend Monoid__Ap_mempty.

#[global]
Program Instance Monoid__Ap {f : Type -> Type} {a : Type} `{GHC.Base.Applicative
  f} `{GHC.Base.Monoid a}
   : GHC.Base.Monoid (Ap f a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Ap_mappend ;
           GHC.Base.mconcat__ := Monoid__Ap_mconcat ;
           GHC.Base.mempty__ := Monoid__Ap_mempty |}.

(* Skipping all instances of class `GHC.Enum.Bounded', including
   `Data.Monoid.Bounded__Ap' *)

(* Skipping all instances of class `GHC.Num.Num', including
   `Data.Monoid.Num__Ap' *)

(* External variables:
     None Type getAp list option Control.Monad.Fail.MonadFail Control.Monad.Fail.fail
     Control.Monad.Fail.fail__ GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.Semigroup GHC.Base.String GHC.Base.fmap GHC.Base.fmap__
     GHC.Base.foldr GHC.Base.liftA2 GHC.Base.liftA2__ GHC.Base.mappend__
     GHC.Base.mconcat__ GHC.Base.mempty GHC.Base.mempty__ GHC.Base.op_zgzg__
     GHC.Base.op_zgzg____ GHC.Base.op_zgzgze__ GHC.Base.op_zgzgze____
     GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlzlzgzg__
     GHC.Base.op_zlzlzgzg____ GHC.Base.op_zlztzg__ GHC.Base.op_zlztzg____
     GHC.Base.op_ztzg__ GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__
     GHC.Base.return_ GHC.Base.return___
*)
