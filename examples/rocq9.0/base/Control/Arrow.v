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

Open Scope type_scope.

(* Converted imports: *)

Require Control.Category.
Require Data.Either.
Require GHC.Base.
Require GHC.Prim.
Import Control.Category.Notations.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Kleisli (m : Type -> Type) a b : Type :=
  | Mk_Kleisli (runKleisli : a -> m b) : Kleisli m a b.

Inductive ArrowMonad (a : Type -> Type -> Type) b : Type :=
  | Mk_ArrowMonad : (a unit b) -> ArrowMonad a b.

Record Arrow__Dict (a : Type -> Type -> Type) := Arrow__Dict_Build {
  arr__ : forall {b : Type}, forall {c : Type}, (b -> c) -> a b c ;
  first__ : forall {b : Type},
  forall {c : Type}, forall {d : Type}, a b c -> a (b * d)%type (c * d)%type ;
  op_zazaza____ : forall {b : Type},
  forall {c : Type}, forall {c' : Type}, a b c -> a b c' -> a b (c * c')%type ;
  op_ztztzt____ : forall {b : Type},
  forall {c : Type},
  forall {b' : Type},
  forall {c' : Type}, a b c -> a b' c' -> a (b * b')%type (c * c')%type ;
  second__ : forall {b : Type},
  forall {c : Type}, forall {d : Type}, a b c -> a (d * b)%type (d * c)%type }.

#[global] Definition Arrow (a : Type -> Type -> Type)
  `{Control.Category.Category Type a} :=
  forall r__, (Arrow__Dict a -> r__) -> r__.
Existing Class Arrow.

Record ArrowPlus__Dict (a : Type -> Type -> Type) := ArrowPlus__Dict_Build {
  op_zlzpzg____ : forall {b : Type}, forall {c : Type}, a b c -> a b c -> a b c }.

#[global] Definition arr `{g__0__ : Arrow a}
   : forall {b : Type}, forall {c : Type}, (b -> c) -> a b c :=
  g__0__ _ (arr__ a).

#[global] Definition first `{g__0__ : Arrow a}
   : forall {b : Type},
     forall {c : Type}, forall {d : Type}, a b c -> a (b * d)%type (c * d)%type :=
  g__0__ _ (first__ a).

#[global] Definition op_zazaza__ `{g__0__ : Arrow a}
   : forall {b : Type},
     forall {c : Type}, forall {c' : Type}, a b c -> a b c' -> a b (c * c')%type :=
  g__0__ _ (op_zazaza____ a).

#[global] Definition op_ztztzt__ `{g__0__ : Arrow a}
   : forall {b : Type},
     forall {c : Type},
     forall {b' : Type},
     forall {c' : Type}, a b c -> a b' c' -> a (b * b')%type (c * c')%type :=
  g__0__ _ (op_ztztzt____ a).

#[global] Definition second `{g__0__ : Arrow a}
   : forall {b : Type},
     forall {c : Type}, forall {d : Type}, a b c -> a (d * b)%type (d * c)%type :=
  g__0__ _ (second__ a).

Notation "'_&&&_'" := (op_zazaza__).

Infix "&&&" := (_&&&_) (at level 99).

Notation "'_***_'" := (op_ztztzt__).

Infix "***" := (_***_) (at level 99).

Record ArrowApply__Dict (a : Type -> Type -> Type) := ArrowApply__Dict_Build {
  app__ : forall {b : Type}, forall {c : Type}, a (a b c * b)%type c }.

#[global] Definition ArrowApply (a : Type -> Type -> Type) `{Arrow a} :=
  forall r__, (ArrowApply__Dict a -> r__) -> r__.
Existing Class ArrowApply.

#[global] Definition app `{g__0__ : ArrowApply a}
   : forall {b : Type}, forall {c : Type}, a (a b c * b)%type c :=
  g__0__ _ (app__ a).

Record ArrowChoice__Dict (a : Type -> Type -> Type) := ArrowChoice__Dict_Build {
  left___ : forall {b : Type},
  forall {c : Type},
  forall {d : Type},
  a b c -> a (Data.Either.Either b d) (Data.Either.Either c d) ;
  op_zbzbzb____ : forall {b : Type},
  forall {d : Type},
  forall {c : Type}, a b d -> a c d -> a (Data.Either.Either b c) d ;
  op_zpzpzp____ : forall {b : Type},
  forall {c : Type},
  forall {b' : Type},
  forall {c' : Type},
  a b c -> a b' c' -> a (Data.Either.Either b b') (Data.Either.Either c c') ;
  right___ : forall {b : Type},
  forall {c : Type},
  forall {d : Type},
  a b c -> a (Data.Either.Either d b) (Data.Either.Either d c) }.

#[global] Definition ArrowChoice (a : Type -> Type -> Type) `{Arrow a} :=
  forall r__, (ArrowChoice__Dict a -> r__) -> r__.
Existing Class ArrowChoice.

#[global] Definition left_ `{g__0__ : ArrowChoice a}
   : forall {b : Type},
     forall {c : Type},
     forall {d : Type},
     a b c -> a (Data.Either.Either b d) (Data.Either.Either c d) :=
  g__0__ _ (left___ a).

#[global] Definition op_zbzbzb__ `{g__0__ : ArrowChoice a}
   : forall {b : Type},
     forall {d : Type},
     forall {c : Type}, a b d -> a c d -> a (Data.Either.Either b c) d :=
  g__0__ _ (op_zbzbzb____ a).

#[global] Definition op_zpzpzp__ `{g__0__ : ArrowChoice a}
   : forall {b : Type},
     forall {c : Type},
     forall {b' : Type},
     forall {c' : Type},
     a b c -> a b' c' -> a (Data.Either.Either b b') (Data.Either.Either c c') :=
  g__0__ _ (op_zpzpzp____ a).

#[global] Definition right_ `{g__0__ : ArrowChoice a}
   : forall {b : Type},
     forall {c : Type},
     forall {d : Type},
     a b c -> a (Data.Either.Either d b) (Data.Either.Either d c) :=
  g__0__ _ (right___ a).

Notation "'_|||_'" := (op_zbzbzb__).

Infix "|||" := (_|||_) (at level 99).

Notation "'_+++_'" := (op_zpzpzp__).

Infix "+++" := (_+++_) (at level 99).

Record ArrowLoop__Dict (a : Type -> Type -> Type) := ArrowLoop__Dict_Build {
  loop__ : forall {b : Type},
  forall {d : Type}, forall {c : Type}, a (b * d)%type (c * d)%type -> a b c }.

#[global] Definition ArrowLoop (a : Type -> Type -> Type) `{Arrow a} :=
  forall r__, (ArrowLoop__Dict a -> r__) -> r__.
Existing Class ArrowLoop.

#[global] Definition loop `{g__0__ : ArrowLoop a}
   : forall {b : Type},
     forall {d : Type}, forall {c : Type}, a (b * d)%type (c * d)%type -> a b c :=
  g__0__ _ (loop__ a).

Record ArrowZero__Dict (a : Type -> Type -> Type) := ArrowZero__Dict_Build {
  zeroArrow__ : forall {b : Type}, forall {c : Type}, a b c }.

#[global] Definition ArrowZero (a : Type -> Type -> Type) `{Arrow a} :=
  forall r__, (ArrowZero__Dict a -> r__) -> r__.
Existing Class ArrowZero.

#[global] Definition zeroArrow `{g__0__ : ArrowZero a}
   : forall {b : Type}, forall {c : Type}, a b c :=
  g__0__ _ (zeroArrow__ a).

#[global] Definition ArrowPlus (a : Type -> Type -> Type) `{ArrowZero a} :=
  forall r__, (ArrowPlus__Dict a -> r__) -> r__.
Existing Class ArrowPlus.

#[global] Definition op_zlzpzg__ `{g__0__ : ArrowPlus a}
   : forall {b : Type}, forall {c : Type}, a b c -> a b c -> a b c :=
  g__0__ _ (op_zlzpzg____ a).

Notation "'_<+>_'" := (op_zlzpzg__).

Infix "<+>" := (_<+>_) (at level 99).

Arguments Mk_Kleisli {_} {_} {_} _.

Arguments Mk_ArrowMonad {_} {_} _.

#[global] Definition runKleisli {m : Type -> Type} {a} {b} (arg_0__
    : Kleisli m a b) :=
  let 'Mk_Kleisli runKleisli := arg_0__ in
  runKleisli.

(* Midamble *)

(* Specialization of Control.Arrow.first and Control.Arrow.second to the (->) type 
   constructor. 

   Coq often has difficulty with type inference for the Arrow type class. One work 
   around is to add the following to your edit file:
     rename value Control.Arrow.first  = Control.Arrow.arrow_first
     rename value Control.Arrow.second = Control.Arrow.arrow_second

*)

Definition arrow_first {b}{c}{d} (f : (b -> c)) : (b * d)%type -> (c * d)%type :=
  fun p => match p with (x,y)=> (f x, y) end.
Definition arrow_second {b}{c}{d} (f : (b -> c)) : (d * b)%type -> (d * c)%type :=
  fun p => match p with (x,y)=> (x, f y) end.

(* Converted value declarations: *)

#[local] Definition Functor__Kleisli_fmap {inst_m : Type -> Type} {inst_a
   : Type} `{GHC.Base.Functor inst_m}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) -> Kleisli inst_m inst_a a -> Kleisli inst_m inst_a b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Kleisli a1 => Mk_Kleisli (fun b1 => GHC.Base.fmap f (a1 b1))
      end.

#[local] Definition Functor__Kleisli_op_zlzd__ {inst_m : Type -> Type} {inst_a
   : Type} `{GHC.Base.Functor inst_m}
   : forall {a : Type},
     forall {b : Type}, a -> Kleisli inst_m inst_a b -> Kleisli inst_m inst_a a :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | z, Mk_Kleisli a1 => Mk_Kleisli (fun b1 => GHC.Base.op_zlzd__ z (a1 b1))
      end.

#[global]
Program Instance Functor__Kleisli {m : Type -> Type} {a : Type}
  `{GHC.Base.Functor m}
   : GHC.Base.Functor (Kleisli m a) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Kleisli_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__Kleisli_op_zlzd__ |}.

#[local] Definition Arrow__arrow_arr
   : forall {b : Type}, forall {c : Type}, (b -> c) -> GHC.Prim.arrow b c :=
  fun {b : Type} {c : Type} => fun f => f.

#[local] Definition Arrow__arrow_op_ztztzt__
   : forall {b : Type},
     forall {c : Type},
     forall {b' : Type},
     forall {c' : Type},
     GHC.Prim.arrow b c ->
     GHC.Prim.arrow b' c' -> GHC.Prim.arrow (b * b')%type (c * c')%type :=
  fun {b : Type} {c : Type} {b' : Type} {c' : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair x y => pair (f x) (g y)
      end.

#[local] Definition Arrow__arrow_first
   : forall {b : Type},
     forall {c : Type},
     forall {d : Type},
     GHC.Prim.arrow b c -> GHC.Prim.arrow (b * d)%type (c * d)%type :=
  fun {b : Type} {c : Type} {d : Type} =>
    (GHC.Prim.rightSection Arrow__arrow_op_ztztzt__ Control.Category.id).

#[local] Definition Arrow__arrow_op_zazaza__
   : forall {b : Type},
     forall {c : Type},
     forall {c' : Type},
     GHC.Prim.arrow b c -> GHC.Prim.arrow b c' -> GHC.Prim.arrow b (c * c')%type :=
  fun {b : Type} {c : Type} {c' : Type} =>
    fun f g =>
      Arrow__arrow_arr (fun b => pair b b) Control.Category.>>>
      Arrow__arrow_op_ztztzt__ f g.

#[local] Definition Arrow__arrow_second
   : forall {b : Type},
     forall {c : Type},
     forall {d : Type},
     GHC.Prim.arrow b c -> GHC.Prim.arrow (d * b)%type (d * c)%type :=
  fun {b : Type} {c : Type} {d : Type} =>
    (Arrow__arrow_op_ztztzt__ Control.Category.id).

#[global]
Program Instance Arrow__arrow : Arrow GHC.Prim.arrow :=
  fun _ k__ =>
    k__ {| arr__ := fun (b : Type) (c : Type) => Arrow__arrow_arr ;
           first__ := fun (b : Type) (c : Type) (d : Type) => Arrow__arrow_first ;
           op_zazaza____ := fun (b : Type) (c : Type) (c' : Type) =>
             Arrow__arrow_op_zazaza__ ;
           op_ztztzt____ := fun (b : Type) (c : Type) (b' : Type) (c' : Type) =>
             Arrow__arrow_op_ztztzt__ ;
           second__ := fun (b : Type) (c : Type) (d : Type) => Arrow__arrow_second |}.

#[local] Definition Applicative__Kleisli_op_zlztzg__ {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Applicative inst_m}
   : forall {a : Type},
     forall {b : Type},
     Kleisli inst_m inst_a (a -> b) ->
     Kleisli inst_m inst_a a -> Kleisli inst_m inst_a b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Kleisli f, Mk_Kleisli g => Mk_Kleisli (fun x => f x GHC.Base.<*> g x)
      end.

#[local] Definition Applicative__Kleisli_liftA2 {inst_m : Type -> Type} {inst_a
   : Type} `{GHC.Base.Applicative inst_m}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) ->
     Kleisli inst_m inst_a a -> Kleisli inst_m inst_a b -> Kleisli inst_m inst_a c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__Kleisli_op_zlztzg__ (GHC.Base.fmap f x).

#[local] Definition Applicative__Kleisli_op_ztzg__ {inst_m : Type -> Type}
  {inst_a : Type} `{GHC.Base.Applicative inst_m}
   : forall {a : Type},
     forall {b : Type},
     Kleisli inst_m inst_a a -> Kleisli inst_m inst_a b -> Kleisli inst_m inst_a b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Kleisli f, Mk_Kleisli g => Mk_Kleisli (fun x => f x GHC.Base.*> g x)
      end.

#[local] Definition Applicative__Kleisli_pure {inst_m : Type -> Type} {inst_a
   : Type} `{GHC.Base.Applicative inst_m}
   : forall {a : Type}, a -> Kleisli inst_m inst_a a :=
  fun {a : Type} =>
    Mk_Kleisli Control.Category.∘ (GHC.Base.const Control.Category.∘ GHC.Base.pure).

#[global]
Program Instance Applicative__Kleisli {m : Type -> Type} {a : Type}
  `{GHC.Base.Applicative m}
   : GHC.Base.Applicative (Kleisli m a) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__Kleisli_liftA2 ;
           GHC.Base.op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Kleisli_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun (a : Type) (b : Type) =>
             Applicative__Kleisli_op_ztzg__ ;
           GHC.Base.pure__ := fun (a : Type) => Applicative__Kleisli_pure |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Control.Arrow.Alternative__Kleisli' *)

#[local] Definition Monad__Kleisli_op_zgzgze__ {inst_m : Type -> Type} {inst_a
   : Type} `{GHC.Base.Monad inst_m}
   : forall {a : Type},
     forall {b : Type},
     Kleisli inst_m inst_a a ->
     (a -> Kleisli inst_m inst_a b) -> Kleisli inst_m inst_a b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Kleisli f, k =>
          Mk_Kleisli (fun x => f x GHC.Base.>>= (fun a => runKleisli (k a) x))
      end.

#[local] Definition Monad__Kleisli_op_zgzg__ {inst_m : Type -> Type} {inst_a
   : Type} `{GHC.Base.Monad inst_m}
   : forall {a : Type},
     forall {b : Type},
     Kleisli inst_m inst_a a -> Kleisli inst_m inst_a b -> Kleisli inst_m inst_a b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__Kleisli_op_zgzgze__ m (fun arg_0__ => k).

#[local] Definition Monad__Kleisli_return_ {inst_m : Type -> Type} {inst_a
   : Type} `{GHC.Base.Monad inst_m}
   : forall {a : Type}, a -> Kleisli inst_m inst_a a :=
  fun {a : Type} => GHC.Base.pure.

#[global]
Program Instance Monad__Kleisli {m : Type -> Type} {a : Type} `{GHC.Base.Monad
  m}
   : GHC.Base.Monad (Kleisli m a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__Kleisli_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun (a : Type) (b : Type) =>
             Monad__Kleisli_op_zgzgze__ ;
           GHC.Base.return___ := fun (a : Type) => Monad__Kleisli_return_ |}.

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `Control.Arrow.MonadPlus__Kleisli' *)

(* Skipping instance `Control.Arrow.Category__Kleisli' of class
   `Control.Category.Category' *)

(* Skipping instance `Control.Arrow.Arrow__Kleisli' of class
   `Control.Arrow.Arrow' *)

(* Skipping instance `Control.Arrow.ArrowZero__Kleisli' of class
   `Control.Arrow.ArrowZero' *)

(* Skipping instance `Control.Arrow.ArrowPlus__Kleisli' of class
   `Control.Arrow.ArrowPlus' *)

(* Skipping instance `Control.Arrow.ArrowChoice__arrow' of class
   `Control.Arrow.ArrowChoice' *)

(* Skipping instance `Control.Arrow.ArrowChoice__Kleisli' of class
   `Control.Arrow.ArrowChoice' *)

#[local] Definition ArrowApply__arrow_app
   : forall {b : Type},
     forall {c : Type}, GHC.Prim.arrow (GHC.Prim.arrow b c * b)%type c :=
  fun {b : Type} {c : Type} => fun '(pair f x) => f x.

#[global]
Program Instance ArrowApply__arrow : ArrowApply GHC.Prim.arrow :=
  fun _ k__ =>
    k__ {| app__ := fun (b : Type) (c : Type) => ArrowApply__arrow_app |}.

(* Skipping instance `Control.Arrow.ArrowApply__Kleisli' of class
   `Control.Arrow.ArrowApply' *)

#[local] Definition Functor__ArrowMonad_fmap {inst_a : Type -> Type -> Type}
  `{Arrow inst_a}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> ArrowMonad inst_a a -> ArrowMonad inst_a b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_ArrowMonad m => Mk_ArrowMonad (m Control.Category.>>> arr f)
      end.

#[local] Definition Functor__ArrowMonad_op_zlzd__ {inst_a
   : Type -> Type -> Type} `{Arrow inst_a}
   : forall {a : Type},
     forall {b : Type}, a -> ArrowMonad inst_a b -> ArrowMonad inst_a a :=
  fun {a : Type} {b : Type} => Functor__ArrowMonad_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__ArrowMonad {a : Type -> Type -> Type} `{Arrow a}
   : GHC.Base.Functor (ArrowMonad a) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) =>
             Functor__ArrowMonad_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__ArrowMonad_op_zlzd__ |}.

(* Skipping instance `Control.Arrow.Applicative__ArrowMonad' of class
   `GHC.Base.Applicative' *)

(* Skipping instance `Control.Arrow.Monad__ArrowMonad' of class
   `GHC.Base.Monad' *)

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Control.Arrow.Alternative__ArrowMonad' *)

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `Control.Arrow.MonadPlus__ArrowMonad' *)

(* Skipping instance `Control.Arrow.ArrowLoop__arrow' of class
   `Control.Arrow.ArrowLoop' *)

(* Skipping instance `Control.Arrow.ArrowLoop__Kleisli' of class
   `Control.Arrow.ArrowLoop' *)

#[global] Definition returnA {a : Type -> Type -> Type} {b : Type} `{Arrow a}
   : a b b :=
  Control.Category.id.

#[global] Definition op_zczgzg__ {a : Type -> Type -> Type} {b : Type} {c
   : Type} {d : Type} `{Arrow a}
   : (b -> c) -> a c d -> a b d :=
  fun f a => arr f Control.Category.>>> a.

Notation "'_^>>_'" := (op_zczgzg__).

Infix "^>>" := (_^>>_) (at level 99).

#[global] Definition op_zgzgzc__ {a : Type -> Type -> Type} {b : Type} {c
   : Type} {d : Type} `{Arrow a}
   : a b c -> (c -> d) -> a b d :=
  fun a f => a Control.Category.>>> arr f.

Notation "'_>>^_'" := (op_zgzgzc__).

Infix ">>^" := (_>>^_) (at level 99).

#[global] Definition op_zlzlzc__ {a : Type -> Type -> Type} {c : Type} {d
   : Type} {b : Type} `{Arrow a}
   : a c d -> (b -> c) -> a b d :=
  fun a f => a Control.Category.<<< arr f.

Notation "'_<<^_'" := (op_zlzlzc__).

Infix "<<^" := (_<<^_) (at level 99).

#[global] Definition op_zczlzl__ {a : Type -> Type -> Type} {c : Type} {d
   : Type} {b : Type} `{Arrow a}
   : (c -> d) -> a b c -> a b d :=
  fun f a => arr f Control.Category.<<< a.

Notation "'_^<<_'" := (op_zczlzl__).

Infix "^<<" := (_^<<_) (at level 99).

(* Skipping definition `Control.Arrow.leftApp' *)

Module Notations.
Notation "'_Control.Arrow.&&&_'" := (op_zazaza__).
Infix "Control.Arrow.&&&" := (_&&&_) (at level 99).
Notation "'_Control.Arrow.***_'" := (op_ztztzt__).
Infix "Control.Arrow.***" := (_***_) (at level 99).
Notation "'_Control.Arrow.|||_'" := (op_zbzbzb__).
Infix "Control.Arrow.|||" := (_|||_) (at level 99).
Notation "'_Control.Arrow.+++_'" := (op_zpzpzp__).
Infix "Control.Arrow.+++" := (_+++_) (at level 99).
Notation "'_Control.Arrow.<+>_'" := (op_zlzpzg__).
Infix "Control.Arrow.<+>" := (_<+>_) (at level 99).
Notation "'_Control.Arrow.^>>_'" := (op_zczgzg__).
Infix "Control.Arrow.^>>" := (_^>>_) (at level 99).
Notation "'_Control.Arrow.>>^_'" := (op_zgzgzc__).
Infix "Control.Arrow.>>^" := (_>>^_) (at level 99).
Notation "'_Control.Arrow.<<^_'" := (op_zlzlzc__).
Infix "Control.Arrow.<<^" := (_<<^_) (at level 99).
Notation "'_Control.Arrow.^<<_'" := (op_zczlzl__).
Infix "Control.Arrow.^<<" := (_^<<_) (at level 99).
End Notations.

(* External variables:
     Type op_zt__ pair unit Control.Category.Category Control.Category.id
     Control.Category.op_z2218U__ Control.Category.op_zgzgzg__
     Control.Category.op_zlzlzl__ Data.Either.Either GHC.Base.Applicative
     GHC.Base.Functor GHC.Base.Monad GHC.Base.const GHC.Base.fmap GHC.Base.fmap__
     GHC.Base.liftA2__ GHC.Base.op_z2218U__ GHC.Base.op_zgzg____ GHC.Base.op_zgzgze__
     GHC.Base.op_zgzgze____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____
     GHC.Base.op_zlztzg__ GHC.Base.op_zlztzg____ GHC.Base.op_ztzg__
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Base.return___
     GHC.Prim.arrow GHC.Prim.rightSection
*)
