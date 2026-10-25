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

Require Stdlib.Lists.List.
Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Either a b : Type :=
  | Left : a -> Either a b
  | Right : b -> Either a b.

Arguments Left {_} {_} _.

Arguments Right {_} {_} _.

(* Midamble *)

(* Eq/Ord for Either -- GHC 9.10 derives using dataToTag# which hs-to-rocq can't translate *)

Definition eq_Either {a} {b} `{GHC.Base.Eq_ a} `{GHC.Base.Eq_ b}
  (x y : Either a b) : bool :=
  match x, y with
  | Left a1, Left b1 => a1 GHC.Base.== b1
  | Right a1, Right b1 => a1 GHC.Base.== b1
  | _, _ => false
  end.

Definition compare_Either {a} {b} `{GHC.Base.Ord a} `{GHC.Base.Ord b}
  (x y : Either a b) : comparison :=
  match x, y with
  | Left a1, Left b1 => GHC.Base.compare a1 b1
  | Left _, Right _ => Lt
  | Right _, Left _ => Gt
  | Right a1, Right b1 => GHC.Base.compare a1 b1
  end.

#[global]
Instance Eq___Either {a} {b} `{GHC.Base.Eq_ a} `{GHC.Base.Eq_ b}
  : GHC.Base.Eq_ (Either a b) := fun _ k => k {|
  GHC.Base.op_zeze____ := eq_Either;
  GHC.Base.op_zsze____ := fun x y => negb (eq_Either x y) |}.

#[global]
Instance Ord__Either {a} {b} `{GHC.Base.Ord a} `{GHC.Base.Ord b}
  : GHC.Base.Ord (Either a b) :=
  GHC.Base.ord_default compare_Either.

(* Converted value declarations: *)

#[local] Definition Functor__Either_fmap {inst_a : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> Either inst_a a -> Either inst_a b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Left x => Left x
      | f, Right y => Right (f y)
      end.

#[local] Definition Functor__Either_op_zlzd__ {inst_a : Type}
   : forall {a : Type},
     forall {b : Type}, a -> Either inst_a b -> Either inst_a a :=
  fun {a : Type} {b : Type} => Functor__Either_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__Either {a : Type} : GHC.Base.Functor (Either a) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Either_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__Either_op_zlzd__ |}.

#[local] Definition Semigroup__Either_op_zlzlzgzg__ {inst_a : Type} {inst_b
   : Type}
   : Either inst_a inst_b -> Either inst_a inst_b -> Either inst_a inst_b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Left _, b => b
    | a, _ => a
    end.

#[global]
Program Instance Semigroup__Either {a : Type} {b : Type}
   : GHC.Base.Semigroup (Either a b) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Either_op_zlzlzgzg__ |}.

#[local] Definition Applicative__Either_op_zlztzg__ {inst_e : Type}
   : forall {a : Type},
     forall {b : Type},
     Either inst_e (a -> b) -> Either inst_e a -> Either inst_e b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Left e, _ => Left e
      | Right f, r => GHC.Base.fmap f r
      end.

#[local] Definition Applicative__Either_liftA2 {inst_e : Type}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) -> Either inst_e a -> Either inst_e b -> Either inst_e c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__Either_op_zlztzg__ (GHC.Base.fmap f x).

#[local] Definition Applicative__Either_op_ztzg__ {inst_e : Type}
   : forall {a : Type},
     forall {b : Type}, Either inst_e a -> Either inst_e b -> Either inst_e b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 =>
      Applicative__Either_op_zlztzg__ (GHC.Base.op_zlzd__ GHC.Base.id a1) a2.

#[local] Definition Applicative__Either_pure {inst_e : Type}
   : forall {a : Type}, a -> Either inst_e a :=
  fun {a : Type} => Right.

#[global]
Program Instance Applicative__Either {e : Type}
   : GHC.Base.Applicative (Either e) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__Either_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Either_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Either_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__Either_pure |}.

#[local] Definition Monad__Either_op_zgzgze__ {inst_e : Type}
   : forall {a : Type},
     forall {b : Type},
     Either inst_e a -> (a -> Either inst_e b) -> Either inst_e b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Left l, _ => Left l
      | Right r, k => k r
      end.

#[local] Definition Monad__Either_op_zgzg__ {inst_e : Type}
   : forall {a : Type},
     forall {b : Type}, Either inst_e a -> Either inst_e b -> Either inst_e b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__Either_op_zgzgze__ m (fun arg_0__ => k).

#[local] Definition Monad__Either_return_ {inst_e : Type}
   : forall {a : Type}, a -> Either inst_e a :=
  fun {a : Type} => GHC.Base.pure.

#[global]
Program Instance Monad__Either {e : Type} : GHC.Base.Monad (Either e) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__Either_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) =>
             Monad__Either_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__Either_return_ |}.

#[global] Definition either {a : Type} {c : Type} {b : Type}
   : (a -> c) -> (b -> c) -> Either a b -> c :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, _, Left x => f x
    | _, g, Right y => g y
    end.

#[global] Definition lefts {a : Type} {b : Type}
   : list (Either a b) -> list a :=
  fun x =>
    let cont_0__ arg_1__ :=
      match arg_1__ with
      | Left a => cons a nil
      | _ => nil
      end in
    Stdlib.Lists.List.flat_map cont_0__ x.

#[global] Definition rights {a : Type} {b : Type}
   : list (Either a b) -> list b :=
  fun x =>
    let cont_0__ arg_1__ :=
      match arg_1__ with
      | Right a => cons a nil
      | _ => nil
      end in
    Stdlib.Lists.List.flat_map cont_0__ x.

#[global] Definition partitionEithers {a : Type} {b : Type}
   : list (Either a b) -> (list a * list b)%type :=
  let right_ :=
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | a, pair l r => pair l (cons a r)
      end in
  let left_ :=
    fun arg_4__ arg_5__ =>
      match arg_4__, arg_5__ with
      | a, pair l r => pair (cons a l) r
      end in
  GHC.Base.foldr (either left_ right_) (pair nil nil).

#[global] Definition isLeft {a : Type} {b : Type} : Either a b -> bool :=
  fun arg_0__ => match arg_0__ with | Left _ => true | Right _ => false end.

#[global] Definition isRight {a : Type} {b : Type} : Either a b -> bool :=
  fun arg_0__ => match arg_0__ with | Left _ => false | Right _ => true end.

#[global] Definition fromLeft {a : Type} {b : Type} : a -> Either a b -> a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Left a => a
    | a, _ => a
    end.

#[global] Definition fromRight {b : Type} {a : Type} : b -> Either a b -> b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Right b => b
    | b, _ => b
    end.

(* External variables:
     Type bool cons false list nil op_zt__ pair true GHC.Base.Applicative
     GHC.Base.Functor GHC.Base.Monad GHC.Base.Semigroup GHC.Base.const GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.foldr GHC.Base.id GHC.Base.liftA2__
     GHC.Base.op_z2218U__ GHC.Base.op_zgzg____ GHC.Base.op_zgzgze____
     GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlzlzgzg____
     GHC.Base.op_zlztzg____ GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__
     GHC.Base.return___ Stdlib.Lists.List.flat_map
*)
