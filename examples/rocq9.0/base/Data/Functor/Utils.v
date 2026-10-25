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
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive StateR s a : Type :=
  | Mk_StateR (runStateR : s -> (s * a)%type) : StateR s a.

Inductive StateL s a : Type :=
  | Mk_StateL (runStateL : s -> (s * a)%type) : StateL s a.

Inductive Min a : Type := | Mk_Min (getMin : option a) : Min a.

Inductive Max a : Type := | Mk_Max (getMax : option a) : Max a.

Arguments Mk_StateR {_} {_} _.

Arguments Mk_StateL {_} {_} _.

Arguments Mk_Min {_} _.

Arguments Mk_Max {_} _.

#[global] Definition runStateR {s} {a} (arg_0__ : StateR s a) :=
  let 'Mk_StateR runStateR := arg_0__ in
  runStateR.

#[global] Definition runStateL {s} {a} (arg_0__ : StateL s a) :=
  let 'Mk_StateL runStateL := arg_0__ in
  runStateL.

#[global] Definition getMin {a} (arg_0__ : Min a) :=
  let 'Mk_Min getMin := arg_0__ in
  getMin.

#[global] Definition getMax {a} (arg_0__ : Max a) :=
  let 'Mk_Max getMax := arg_0__ in
  getMax.

(* Midamble *)

(* We should be able to automatically generate these *)

Instance Unpeel_StateR {s}{a} : HsToRocq.Unpeel.Unpeel (StateR s a) (s -> (s * a)%type)
:= HsToRocq.Unpeel.Build_Unpeel _ _  (fun arg => match arg with | Mk_StateR x => x end) Mk_StateR.
Instance Unpeel_StateL {s}{a} : HsToRocq.Unpeel.Unpeel (StateL s a) (s -> (s * a)%type)
:= HsToRocq.Unpeel.Build_Unpeel _ _  (fun arg => match arg with | Mk_StateL x => x end) Mk_StateL.
Instance Unpeel_Min {a} : HsToRocq.Unpeel.Unpeel (Min a) (option a)
:= HsToRocq.Unpeel.Build_Unpeel _ _  (fun arg => match arg with | Mk_Min x => x end) Mk_Min.
Instance Unpeel_Max {a} : HsToRocq.Unpeel.Unpeel (Max a) (option a)
:= HsToRocq.Unpeel.Build_Unpeel _ _  (fun arg => match arg with | Mk_Max x => x end) Mk_Max.

(* Converted value declarations: *)

#[local] Definition Semigroup__Max_op_zlzlzgzg__ {inst_a : Type} `{GHC.Base.Ord
  inst_a}
   : Max inst_a -> Max inst_a -> Max inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | m, Mk_Max None => m
    | Mk_Max None, n => n
    | Mk_Max (Some x as m), Mk_Max (Some y as n) =>
        if x GHC.Base.>= y : bool then Mk_Max m else
        Mk_Max n
    end.

#[global]
Program Instance Semigroup__Max {a : Type} `{GHC.Base.Ord a}
   : GHC.Base.Semigroup (Max a) :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Max_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Max_mappend {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Max inst_a -> Max inst_a -> Max inst_a :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__Max_mempty {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Max inst_a :=
  Mk_Max None.

#[local] Definition Monoid__Max_mconcat {inst_a : Type} `{GHC.Base.Ord inst_a}
   : list (Max inst_a) -> Max inst_a :=
  GHC.Base.foldr Monoid__Max_mappend Monoid__Max_mempty.

#[global]
Program Instance Monoid__Max {a : Type} `{GHC.Base.Ord a}
   : GHC.Base.Monoid (Max a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Max_mappend ;
           GHC.Base.mconcat__ := Monoid__Max_mconcat ;
           GHC.Base.mempty__ := Monoid__Max_mempty |}.

#[local] Definition Semigroup__Min_op_zlzlzgzg__ {inst_a : Type} `{GHC.Base.Ord
  inst_a}
   : Min inst_a -> Min inst_a -> Min inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | m, Mk_Min None => m
    | Mk_Min None, n => n
    | Mk_Min (Some x as m), Mk_Min (Some y as n) =>
        if x GHC.Base.<= y : bool then Mk_Min m else
        Mk_Min n
    end.

#[global]
Program Instance Semigroup__Min {a : Type} `{GHC.Base.Ord a}
   : GHC.Base.Semigroup (Min a) :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Min_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Min_mappend {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Min inst_a -> Min inst_a -> Min inst_a :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__Min_mempty {inst_a : Type} `{GHC.Base.Ord inst_a}
   : Min inst_a :=
  Mk_Min None.

#[local] Definition Monoid__Min_mconcat {inst_a : Type} `{GHC.Base.Ord inst_a}
   : list (Min inst_a) -> Min inst_a :=
  GHC.Base.foldr Monoid__Min_mappend Monoid__Min_mempty.

#[global]
Program Instance Monoid__Min {a : Type} `{GHC.Base.Ord a}
   : GHC.Base.Monoid (Min a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Min_mappend ;
           GHC.Base.mconcat__ := Monoid__Min_mconcat ;
           GHC.Base.mempty__ := Monoid__Min_mempty |}.

#[local] Definition Functor__StateL_fmap {inst_s : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> StateL inst_s a -> StateL inst_s b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_StateL k => Mk_StateL (fun s => let 'pair s' v := k s in pair s' (f v))
      end.

#[local] Definition Functor__StateL_op_zlzd__ {inst_s : Type}
   : forall {a : Type},
     forall {b : Type}, a -> StateL inst_s b -> StateL inst_s a :=
  fun {a : Type} {b : Type} => Functor__StateL_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__StateL {s : Type} : GHC.Base.Functor (StateL s) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__StateL_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__StateL_op_zlzd__ |}.

#[local] Definition Applicative__StateL_liftA2 {inst_s : Type}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) -> StateL inst_s a -> StateL inst_s b -> StateL inst_s c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, Mk_StateL kx, Mk_StateL ky =>
          Mk_StateL (fun s =>
                       let 'pair s' x := kx s in
                       let 'pair s'' y := ky s' in
                       pair s'' (f x y))
      end.

#[local] Definition Applicative__StateL_op_zlztzg__ {inst_s : Type}
   : forall {a : Type},
     forall {b : Type},
     StateL inst_s (a -> b) -> StateL inst_s a -> StateL inst_s b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_StateL kf, Mk_StateL kv =>
          Mk_StateL (fun s =>
                       let 'pair s' f := kf s in
                       let 'pair s'' v := kv s' in
                       pair s'' (f v))
      end.

#[local] Definition Applicative__StateL_op_ztzg__ {inst_s : Type}
   : forall {a : Type},
     forall {b : Type}, StateL inst_s a -> StateL inst_s b -> StateL inst_s b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 =>
      Applicative__StateL_op_zlztzg__ (GHC.Base.op_zlzd__ GHC.Base.id a1) a2.

#[local] Definition Applicative__StateL_pure {inst_s : Type}
   : forall {a : Type}, a -> StateL inst_s a :=
  fun {a : Type} => fun x => Mk_StateL (fun s => pair s x).

#[global]
Program Instance Applicative__StateL {s : Type}
   : GHC.Base.Applicative (StateL s) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__StateL_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__StateL_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__StateL_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__StateL_pure |}.

#[local] Definition Functor__StateR_fmap {inst_s : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> StateR inst_s a -> StateR inst_s b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_StateR k => Mk_StateR (fun s => let 'pair s' v := k s in pair s' (f v))
      end.

#[local] Definition Functor__StateR_op_zlzd__ {inst_s : Type}
   : forall {a : Type},
     forall {b : Type}, a -> StateR inst_s b -> StateR inst_s a :=
  fun {a : Type} {b : Type} => Functor__StateR_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__StateR {s : Type} : GHC.Base.Functor (StateR s) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__StateR_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__StateR_op_zlzd__ |}.

#[local] Definition Applicative__StateR_liftA2 {inst_s : Type}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) -> StateR inst_s a -> StateR inst_s b -> StateR inst_s c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, Mk_StateR kx, Mk_StateR ky =>
          Mk_StateR (fun s =>
                       let 'pair s' y := ky s in
                       let 'pair s'' x := kx s' in
                       pair s'' (f x y))
      end.

#[local] Definition Applicative__StateR_op_zlztzg__ {inst_s : Type}
   : forall {a : Type},
     forall {b : Type},
     StateR inst_s (a -> b) -> StateR inst_s a -> StateR inst_s b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_StateR kf, Mk_StateR kv =>
          Mk_StateR (fun s =>
                       let 'pair s' v := kv s in
                       let 'pair s'' f := kf s' in
                       pair s'' (f v))
      end.

#[local] Definition Applicative__StateR_op_ztzg__ {inst_s : Type}
   : forall {a : Type},
     forall {b : Type}, StateR inst_s a -> StateR inst_s b -> StateR inst_s b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 =>
      Applicative__StateR_op_zlztzg__ (GHC.Base.op_zlzd__ GHC.Base.id a1) a2.

#[local] Definition Applicative__StateR_pure {inst_s : Type}
   : forall {a : Type}, a -> StateR inst_s a :=
  fun {a : Type} => fun x => Mk_StateR (fun s => pair s x).

#[global]
Program Instance Applicative__StateR {s : Type}
   : GHC.Base.Applicative (StateR s) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__StateR_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__StateR_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__StateR_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__StateR_pure |}.

(* Skipping instance `Data.Functor.Utils.Functor__StateT' of class
   `GHC.Base.Functor' *)

(* Skipping instance `Data.Functor.Utils.Applicative__StateT' of class
   `GHC.Base.Applicative' *)

(* Skipping instance `Data.Functor.Utils.Monad__StateT' of class
   `GHC.Base.Monad' *)

(* Skipping definition `Data.Functor.Utils.hash_compose' *)

(* External variables:
     None Some Type bool list op_zt__ option pair GHC.Base.Applicative
     GHC.Base.Functor GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup GHC.Base.const
     GHC.Base.fmap__ GHC.Base.foldr GHC.Base.id GHC.Base.liftA2__ GHC.Base.mappend__
     GHC.Base.mconcat__ GHC.Base.mempty__ GHC.Base.op_z2218U__ GHC.Base.op_zgze__
     GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlze__
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Base.op_zlztzg____
     GHC.Base.op_ztzg____ GHC.Base.pure__
*)
