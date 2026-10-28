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


(* Converted imports: *)

Require Corelib.Init.Datatypes.
Require Stdlib.Lists.List.
Require GHC.Tuple.

(* Converted type declarations: *)

Inductive Void : Set :=.

Record Semigroup__Dict (a : Type) := Semigroup__Dict_Build {
  op_zlzlzgzg____ : a -> a -> a }.

#[global] Definition Semigroup (a : Type) :=
  forall r__, (Semigroup__Dict a -> r__) -> r__.
Existing Class Semigroup.

Record Monoid__Dict (a : Type) := Monoid__Dict_Build {
  mappend__ : a -> a -> a ;
  mconcat__ : list a -> a ;
  mempty__ : a }.

#[global] Definition op_zlzlzgzg__ `{g__0__ : Semigroup a} : a -> a -> a :=
  g__0__ _ (op_zlzlzgzg____ a).

Notation "'_<<>>_'" := (op_zlzlzgzg__).

Infix "<<>>" := (_<<>>_) (at level 99).

Inductive NonEmpty a : Type := | NEcons : a -> list a -> NonEmpty a.

#[global] Definition Monoid (a : Type) `{Semigroup a} :=
  forall r__, (Monoid__Dict a -> r__) -> r__.
Existing Class Monoid.

#[global] Definition mappend `{g__0__ : Monoid a} : a -> a -> a :=
  g__0__ _ (mappend__ a).

#[global] Definition mconcat `{g__0__ : Monoid a} : list a -> a :=
  g__0__ _ (mconcat__ a).

#[global] Definition mempty `{g__0__ : Monoid a} : a :=
  g__0__ _ (mempty__ a).

Record Functor__Dict (f : Type -> Type) := Functor__Dict_Build {
  fmap__ : forall {a : Type}, forall {b : Type}, (a -> b) -> f a -> f b ;
  op_zlzd____ : forall {a : Type}, forall {b : Type}, a -> f b -> f a }.

#[global] Definition Functor (f : Type -> Type) :=
  forall r__, (Functor__Dict f -> r__) -> r__.
Existing Class Functor.

Record Applicative__Dict (f : Type -> Type) := Applicative__Dict_Build {
  liftA2__ : forall {a : Type},
  forall {b : Type}, forall {c : Type}, (a -> b -> c) -> f a -> f b -> f c ;
  op_zlztzg____ : forall {a : Type}, forall {b : Type}, f (a -> b) -> f a -> f b ;
  op_ztzg____ : forall {a : Type}, forall {b : Type}, f a -> f b -> f b ;
  pure__ : forall {a : Type}, a -> f a }.

#[global] Definition fmap `{g__0__ : Functor f}
   : forall {a : Type}, forall {b : Type}, (a -> b) -> f a -> f b :=
  g__0__ _ (fmap__ f).

#[global] Definition op_zlzd__ `{g__0__ : Functor f}
   : forall {a : Type}, forall {b : Type}, a -> f b -> f a :=
  g__0__ _ (op_zlzd____ f).

Notation "'_<$_'" := (op_zlzd__).

Infix "<$" := (op_zlzd__) (at level 99).

#[global] Definition Applicative (f : Type -> Type) `{Functor f} :=
  forall r__, (Applicative__Dict f -> r__) -> r__.
Existing Class Applicative.

#[global] Definition liftA2 `{g__0__ : Applicative f}
   : forall {a : Type},
     forall {b : Type}, forall {c : Type}, (a -> b -> c) -> f a -> f b -> f c :=
  g__0__ _ (liftA2__ f).

#[global] Definition op_zlztzg__ `{g__0__ : Applicative f}
   : forall {a : Type}, forall {b : Type}, f (a -> b) -> f a -> f b :=
  g__0__ _ (op_zlztzg____ f).

#[global] Definition op_ztzg__ `{g__0__ : Applicative f}
   : forall {a : Type}, forall {b : Type}, f a -> f b -> f b :=
  g__0__ _ (op_ztzg____ f).

#[global] Definition pure `{g__0__ : Applicative f}
   : forall {a : Type}, a -> f a :=
  g__0__ _ (pure__ f).

Notation "'_<*>_'" := (op_zlztzg__).

Infix "<*>" := (_<*>_) (at level 99).

Notation "'_*>_'" := (op_ztzg__).

Infix "*>" := (_*>_) (at level 99).

Record Monad__Dict (m : Type -> Type) := Monad__Dict_Build {
  op_zgzg____ : forall {a : Type}, forall {b : Type}, m a -> m b -> m b ;
  op_zgzgze____ : forall {a : Type}, forall {b : Type}, m a -> (a -> m b) -> m b ;
  return___ : forall {a : Type}, a -> m a }.

#[global] Definition Monad (m : Type -> Type) `{Applicative m} :=
  forall r__, (Monad__Dict m -> r__) -> r__.
Existing Class Monad.

#[global] Definition op_zgzg__ `{g__0__ : Monad m}
   : forall {a : Type}, forall {b : Type}, m a -> m b -> m b :=
  g__0__ _ (op_zgzg____ m).

#[global] Definition op_zgzgze__ `{g__0__ : Monad m}
   : forall {a : Type}, forall {b : Type}, m a -> (a -> m b) -> m b :=
  g__0__ _ (op_zgzgze____ m).

#[global] Definition return_ `{g__0__ : Monad m}
   : forall {a : Type}, a -> m a :=
  g__0__ _ (return___ m).

Notation "'_>>_'" := (op_zgzg__).

Infix ">>" := (_>>_) (at level 99).

Notation "'_>>=_'" := (op_zgzgze__).

Infix ">>=" := (_>>=_) (at level 99).

Arguments NEcons {_} _ _.

(* Midamble *)

(* This includes everything that should be defined in GHC/Base.hs, but cannot
   be generated from Base.hs.

The types defined in GHC.Base:

  list, (), Int, Bool, Ordering, Char, String

are all mapped to corresponding Coq types. Therefore, the Eq/Ord classes must
be defined in this module so that we can create instances for these types.

 *)


(********************* Types ************************)

Require Export GHC.Prim.

Require Export GHC.Tuple.

(* List notation *)
Require Export Stdlib.Lists.List.

(* Booleans *)
Require Export Bool.Bool.

(* Int and Integer types *)
Require NArith.
Require Import ZArith.
Require Export GHC.Num.

(* Char type *)
Require Export GHC.Char.
Definition unsafeChr := Z.to_N.
Definition ord := Z.of_N.

(* Strings *)
Require Stdlib.Strings.String.
Definition String := list Char.

Bind Scope string_scope with String.string.
Fixpoint hs_string__ (s : String.string) : String :=
  match s with
  | String.EmptyString => nil
  | String.String c s  => &#c :: hs_string__ s
  end.
Notation "'&' s" := (hs_string__ s) (at level 1, format "'&' s").

(* IO --- PUNT *)
Definition FilePath := String.

(* ASZ: I've been assured that this is OK *)
Inductive IO (a : Type) : Set :=.
Inductive IORef (a : Type) : Set :=.
Inductive IOError : Set :=.

(****************************************************)

(* function composition *)
Require Export Corelib.Program.Basics.

Notation "[,]"  := (fun x y => (x,y)).
Notation "[,,]" := (fun x0 y1 z2 => (x0, y1, z2)).
Notation "[,,,]" := (fun x0 x1 x2 x3 => (x0,x1,x2,x3)).
Notation "[,,,,]" := (fun x0 x1 x2 x3 x4 => (x0,x1,x2,x3,x4)).
Notation "[,,,,,]" := (fun x0 x1 x2 x3 x4 x5 => (x0,x1,x2,x3,x4,x5)).
Notation "[,,,,,,]" := (fun x0 x1 x2 x3 x4 x5 x6 => (x0,x1,x2,x3,x4,x5,x6)).
Notation "[,,,,,,,]" := (fun x0 x1 x2 x3 x4 x5 x6 x7 => (x0,x1,x2,x3,x4,x5,x6,x7)).

Notation "'_++_'"   := (fun x y => x ++ y).
Notation "'_::_'"   := (fun x y => x :: y).

Notation "[->]"  := arrow.



(* Configure type argument to be maximally inserted *)
Arguments List.app {_} _ _.

(****************************************************)


Definition Synonym {A : Type} (_uniq : Type) (x : A) : A := x.
Arguments Synonym {A}%_type _uniq%_type x%_type.


(*********** built in classes Eq & Ord **********************)

(* Don't clash with Eq constructor for the comparison type. *)
Record Eq___Dict a := Eq___Dict_Build {
  op_zeze____ : (a -> (a -> bool)) ;
  op_zsze____ : (a -> (a -> bool)) }.

Definition Eq_ a := forall r, (Eq___Dict a -> r) -> r.
Existing Class Eq_.

Definition op_zeze__ {a} {g : Eq_ a} := g _ (op_zeze____ _).
Definition op_zsze__ {a} {g : Eq_ a} := g _ (op_zsze____ _).

Notation "'_/=_'" := (op_zsze__).
Infix "/=" := (op_zsze__) (no associativity, at level 70).
Notation "'_==_'" := (op_zeze__).
Infix "==" := (op_zeze__) (no associativity, at level 70).

Definition eq_default {a} (eq : a -> a -> bool) : Eq_ a :=
  fun _ k => k {|op_zeze____ := eq; op_zsze____ := fun x y => negb (eq x y) |}.

Record Ord__Dict a := Ord__Dict_Build {
  op_zl____ : a -> a -> bool ;
  op_zlze____ : a -> a -> bool ;
  op_zg____ : a -> a -> bool ;
  op_zgze____ : a -> a -> bool ;
  compare__ : a -> a -> comparison ;
  max__ : a -> a -> a ;
  min__ : a -> a -> a }.

Definition Ord a `{Eq_ a} :=
  forall r, (Ord__Dict a -> r) -> r.

Existing Class Ord.

Definition op_zl__ `{g : Ord a} : a -> a -> bool :=
  g _ (op_zl____ a).

Definition op_zlze__ `{g : Ord a} : a -> a -> bool :=
  g _ (op_zlze____ a).

Definition op_zg__ `{g : Ord a} : a -> a -> bool :=
  g _ (op_zg____ a).

Definition op_zgze__ `{g : Ord a} : a -> a -> bool :=
  g _ (op_zgze____ a).

Definition compare `{g : Ord a} : a -> a -> comparison :=
  g _ (compare__ a).

Definition max `{g : Ord a} : a -> a -> a :=
  g _ (max__ a).

Definition min `{g : Ord a} : a -> a -> a :=
  g _ (min__ a).

Notation "'_<_'" := (op_zl__).
Infix "<" := (op_zl__) (no associativity, at level 70).

Notation "'_<=_'" := (op_zlze__).
Infix "<=" := (op_zlze__) (no associativity, at level 70).

Notation "'_>_'" := (op_zg__).
Infix ">" := (op_zg__) (no associativity, at level 70).

Notation "'_>=_'" := (op_zgze__).
Infix ">=" := (op_zgze__) (no associativity, at level 70).

(*********** Eq/Ord for primitive types **************************)

#[global]
Instance Eq_Int___ : Eq_ Int := fun _ k => k {|
                               op_zeze____ := fun x y => (x =? y)%Z;
                               op_zsze____ := fun x y => negb (x =? y)%Z;
                               |}.

#[global]
Instance Ord_Int___ : Ord Int := fun _ k => k {|
  op_zl____   := fun x y => (x <? y)%Z;
  op_zlze____ := fun x y => (x <=? y)%Z;
  op_zg____   := fun x y => (y <? x)%Z;
  op_zgze____ := fun x y => (y <=? x)%Z;
  compare__   := Z.compare%Z ;
  max__       := Z.max%Z;
  min__       := Z.min%Z;
|}.

#[global]
Instance Eq_Integer___ : Eq_ Integer := fun _ k => k {|
                               op_zeze____ := fun x y => (x =? y)%Z;
                               op_zsze____ := fun x y => negb (x =? y)%Z;
                             |}.

#[global]
Instance Ord_Integer___ : Ord Integer := fun _ k => k {|
  op_zl____   := fun x y => (x <? y)%Z;
  op_zlze____ := fun x y => (x <=? y)%Z;
  op_zg____   := fun x y => (y <? x)%Z;
  op_zgze____ := fun x y => (y <=? x)%Z;
  compare__   := Z.compare%Z ;
  max__       := Z.max%Z;
  min__       := Z.min%Z;
|}.

#[global]
Instance Eq_Word___ : Eq_ Word := fun _ k => k {|
                               op_zeze____ := fun x y => (x =? y)%N;
                               op_zsze____ := fun x y => negb (x =? y)%N;
                             |}.

#[global]
Instance Ord_Word___ : Ord Word := fun _ k => k {|
  op_zl____   := fun x y => (x <? y)%N;
  op_zlze____ := fun x y => (x <=? y)%N;
  op_zg____   := fun x y => (y <? x)%N;
  op_zgze____ := fun x y => (y <=? x)%N;
  compare__   := N.compare%N ;
  max__       := N.max%N;
  min__       := N.min%N;
|}.

#[global]
Instance Eq_Char___ : Eq_ Char := fun _ k => k {|
                               op_zeze____ := fun x y => (x =? y)%N;
                               op_zsze____ := fun x y => negb (x =? y)%N;
                             |}.

#[global]
Instance Ord_Char___ : Ord Char := fun _ k => k {|
  op_zl____   := fun x y => (x <? y)%N;
  op_zlze____ := fun x y => (x <=? y)%N;
  op_zg____   := fun x y => (y <? x)%N;
  op_zgze____ := fun x y => (y <=? x)%N;
  compare__   := N.compare%N ;
  max__       := N.max%N;
  min__       := N.min%N;
|}.

#[global]
Instance Eq_bool___ : Eq_ bool := fun _ k => k {|
                               op_zeze____ := eqb;
                               op_zsze____ := fun x y => negb (eqb x y);
                             |}.

Definition compare_bool (b1:bool)(b2:bool) : comparison :=
  match b1 , b2 with
  | true , true => Eq
  | false, false => Eq
  | true , false => Gt
  | false , true => Lt
  end.

#[global]
Instance Ord_bool___ : Ord bool := fun _ k => k {|
  op_zl____   := fun x y => andb (negb x) y;
  op_zlze____ := fun x y => orb (negb x) y;
  op_zg____   := fun x y => orb (negb y) x;
  op_zgze____ := fun x y => andb (negb y) x;
  compare__   := compare_bool;
  max__       := orb;
  min__       := andb
|}.

#[global]
Instance Eq_unit___ : Eq_ unit := fun _ k => k {|
                               op_zeze____ := fun x y => true;
                               op_zsze____ := fun x y => false;
                             |}.

#[global]
Instance Ord_unit___ : Ord unit := fun _ k => k {|
  op_zl____   := fun x y => false;
  op_zlze____ := fun x y => true;
  op_zg____   := fun x y => false;
  op_zgze____ := fun x y => true;
  compare__   := fun x y => Eq ;
  max__       := fun x y => tt;
  min__       := fun x y => tt;
|}.

Definition eq_comparison (x : comparison) (y: comparison) :=
  match x , y with
  | Eq, Eq => true
  | Gt, Gt => true
  | Lt, Lt => true
  | _ , _  => false
end.

#[global]
Instance Eq_comparison___ : Eq_ comparison := fun _ k => k
{|
  op_zeze____ := eq_comparison;
  op_zsze____ := fun x y => negb (eq_comparison x y);
|}.

Definition compare_comparison  (x : comparison) (y: comparison) :=
  match x , y with
  | Eq, Eq => Eq
  | _, Eq  => Gt
  | Eq, _  => Lt
  | Lt, Lt => Eq
  | _, Lt  => Lt
  | Lt, _  => Gt
  | Gt, Gt => Eq
end.

Definition ord_default {a} (comp : a -> a -> comparison) `{Eq_ a} : Ord a :=
  fun _ k => k (Ord__Dict_Build _
  (fun x y => (comp x y) == Lt)
  ( fun x y => negb ((comp y x) == Lt))
  (fun x y => (comp y x) == Lt)
  (fun x y => negb ((comp x y) == Lt))
  comp
  (fun x y =>
     match comp x y with
     | Lt => y
     | _  => x
     end)
  (fun x y =>   match comp x y with
             | Gt => y
             | _  => x
             end)).

#[global]
Instance Ord_comparison___ : Ord comparison := ord_default compare_comparison.

Definition eq_pair {t1} {t2} `{Eq_ t1} `{Eq_ t2} (a b : (t1 * t2)) :=
  match a, b with
  | (a1, a2), (b1, b2) =>
    (a1 == b1) && (a2 == b2)
  end.

Definition compare_pair {t1} {t2} `{Ord t1} `{Ord t2} (a b : (t1 * t2)) :=
  match a, b with
  | (a1, a2), (b1, b2) =>
    match compare a1 b1 with
    | Lt => Lt
    | Gt => Gt
    | Eq => compare a2 b2
    end
  end.

#[global]
Instance Eq_pair___ {a} {b} `{Eq_ a} `{Eq_ b} : Eq_ (a * b) := fun _ k => k
  {| op_zeze____ := eq_pair;
     op_zsze____ := fun x y => negb (eq_pair x y)
  |}.

#[global]
Instance Ord_pair___ {a} {b} `{Ord a} `{Ord b} : Ord (a * b) :=
  ord_default compare_pair.

(* TODO: are these available in a library somewhere? *)
Definition eqlist {a} `{Eq_ a} : list a -> list a -> bool :=
	fix eqlist xs ys :=
	    match xs , ys with
	    | nil , nil => true
	    | x :: xs' , y :: ys' => andb (x == y) (eqlist xs' ys')
	    | _ ,  _ => false
	    end.

Fixpoint compare_list {a} `{Ord a} (xs :  list a) (ys : list a) : comparison :=
    match xs , ys with
    | nil , nil => Eq
    | nil , _   => Lt
    | _   , nil => Gt
    | x :: xs' , y :: ys' =>
      match compare x y with
          | Lt => Lt
          | Gt => Gt
          | Eq => compare_list xs' ys'
      end
    end.

#[global]
Instance Eq_list {a} `{Eq_ a} : Eq_ (list a) := fun _ k => k
  {| op_zeze____ := eqlist;
     op_zsze____ := fun x y => negb (eqlist x y)
  |}.

#[global]
Instance Ord_list {a} `{Ord a}: Ord (list a) :=
  ord_default compare_list.


(* ********************************************************* *)
(* Some Haskell functions we cannot translate (yet)          *)


(* The inner nil case is impossible. So it is left out of the Haskell version. *)
Fixpoint scanr {a b:Type} (f : a -> b -> b) (q0 : b) (xs : list a) : list b :=
  match xs with
  | nil => q0 :: nil
  | y :: ys => match scanr f q0 ys with
              | q :: qs =>  f y q :: (q :: qs)
              | nil => nil
              end
end.


(* The inner nil case is impossible. So it is left out of the Haskell version. *)
Fixpoint scanr1 {a :Type} (f : a -> a -> a) (q0 : a) (xs : list a) : list a :=
  match xs with
  | nil => q0 :: nil
  | y :: nil => y :: nil
  | y :: ys => match scanr1 f q0 ys with
              | q :: qs =>  f y q :: (q :: qs)
              | nil => nil
              end
end.

Definition foldl {a}{b} k z0 xs :=
  fold_right (fun (v:a) (fn:b->b) => (fun (z:b) => fn (k z v))) (id : b -> b) xs z0.

Definition foldl' {a}{b} k z0 xs :=
  fold_right (fun(v:a) (fn:b->b) => (fun(z:b) => fn (k z v))) (id : b -> b) xs z0.

(* Less general type for build *)
Definition build {a} : (forall {b}, (a -> b -> b) -> b -> b) -> list a :=
  fun g => g _ (fun x y => x :: y) nil.

(* A copy of it, to facilitate the rewrite rule in the edits file *)
Definition build' : forall {a}, (forall {b}, (a -> b -> b) -> b -> b) -> list a := @build.

(********************************************************************)

(* Definition oneShot {a} (x:a) := x. *)

(** Qualified notation for the notation defined here **)

Require String Ascii.

Module ManualNotations.
Infix "GHC.Base./=" := (op_zsze__) (no associativity, at level 70).
Notation "'_GHC.Base./=_'" := (op_zsze__).
Infix "GHC.Base.==" := (op_zeze__) (no associativity, at level 70).
Notation "'_GHC.Base.==_'" := (op_zeze__).
Infix "GHC.Base.<" := (op_zl__) (no associativity, at level 70).
Notation "'_GHC.Base.<_'" := (op_zl__).
Infix "GHC.Base.<=" := (op_zlze__) (no associativity, at level 70).
Notation "'_GHC.Base.<=_'" := (op_zlze__).
Infix "GHC.Base.>" := (op_zg__) (no associativity, at level 70).
Notation "'_GHC.Base.>_'" := (op_zg__).
Infix "GHC.Base.>=" := (op_zgze__) (no associativity, at level 70).
Notation "'_GHC.Base.>=_'" := (op_zgze__).

Export String.StringSyntax Ascii.AsciiSyntax.
End ManualNotations.

(* Eq/Ord for option (Maybe) -- GHC 9.10 derives these using dataToTag#
   which hs-to-rocq can't translate *)

Definition eq_option {a} `{Eq_ a} (x y : option a) : bool :=
  match x, y with
  | Some a1, Some b1 => a1 == b1
  | None, None => true
  | _, _ => false
  end.

Definition compare_option {a} `{Ord a} (x y : option a) : comparison :=
  match x, y with
  | None, None => Eq
  | None, Some _ => Lt
  | Some _, None => Gt
  | Some a1, Some b1 => compare a1 b1
  end.

#[global]
Instance Eq___option {a} `{Eq_ a} : Eq_ (option a) := fun _ k => k {|
  op_zeze____ := eq_option;
  op_zsze____ := fun x y => negb (eq_option x y) |}.

#[global]
Instance Ord__option {a} `{Ord a} : Ord (option a) :=
  ord_default compare_option.

(* Eq for NonEmpty -- GHC 9.10 derives using dataToTag# *)

Definition eq_NonEmpty {a} `{Eq_ a} (x y : NonEmpty a) : bool :=
  match x, y with
  | NEcons a1 as1, NEcons b1 bs1 => (a1 == b1) && (as1 == bs1)
  end.

#[global]
Instance Eq___NonEmpty {a} `{Eq_ a} : Eq_ (NonEmpty a) := fun _ k => k {|
  op_zeze____ := eq_NonEmpty;
  op_zsze____ := fun x y => negb (eq_NonEmpty x y) |}.

(* Ord for NonEmpty -- GHC 9.10 derives using dataToTag# *)

Definition compare_NonEmpty {a} `{Ord a} (x y : NonEmpty a) : comparison :=
  match x, y with
  | NEcons a1 as1, NEcons b1 bs1 =>
    match compare a1 b1 with
    | Eq => compare as1 bs1
    | c => c
    end
  end.

#[global]
Instance Ord__NonEmpty {a} `{Ord a} : Ord (NonEmpty a) :=
  ord_default compare_NonEmpty.

(* Converted value declarations: *)

#[local] Definition Semigroup__list_op_zlzlzgzg__ {inst_a : Type}
   : list inst_a -> list inst_a -> list inst_a :=
  Corelib.Init.Datatypes.app.

#[global]
Program Instance Semigroup__list {a : Type} : Semigroup (list a) :=
  fun _ k__ => k__ {| op_zlzlzgzg____ := Semigroup__list_op_zlzlzgzg__ |}.

#[local] Definition Monoid__list_mappend {inst_a : Type}
   : list inst_a -> list inst_a -> list inst_a :=
  _<<>>_.

#[local] Definition Monoid__list_mconcat {inst_a : Type}
   : list (list inst_a) -> list inst_a :=
  fun xss =>
    Stdlib.Lists.List.flat_map (fun xs =>
                                  Stdlib.Lists.List.flat_map (fun x => cons x nil) xs) xss.

#[local] Definition Monoid__list_mempty {inst_a : Type} : list inst_a :=
  nil.

#[global]
Program Instance Monoid__list {a : Type} : Monoid (list a) :=
  fun _ k__ =>
    k__ {| mappend__ := Monoid__list_mappend ;
           mconcat__ := Monoid__list_mconcat ;
           mempty__ := Monoid__list_mempty |}.

#[local] Definition Semigroup__Void_op_zlzlzgzg__ : Void -> Void -> Void :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | a, _ => a end.

#[global]
Program Instance Semigroup__Void : Semigroup Void :=
  fun _ k__ => k__ {| op_zlzlzgzg____ := Semigroup__Void_op_zlzlzgzg__ |}.

#[local] Definition Semigroup__NonEmpty_op_zlzlzgzg__ {inst_a : Type}
   : NonEmpty inst_a -> NonEmpty inst_a -> NonEmpty inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NEcons a as_, NEcons b bs =>
        NEcons a (Corelib.Init.Datatypes.app as_ (cons b bs))
    end.

#[global]
Program Instance Semigroup__NonEmpty {a : Type} : Semigroup (NonEmpty a) :=
  fun _ k__ => k__ {| op_zlzlzgzg____ := Semigroup__NonEmpty_op_zlzlzgzg__ |}.

(* Skipping instance `GHC.Base.Semigroup__arrow' of class
   `GHC.Base.Semigroup' *)

(* Skipping instance `GHC.Base.Monoid__arrow' of class `GHC.Base.Monoid' *)

#[local] Definition Semigroup__unit_op_zlzlzgzg__ : unit -> unit -> unit :=
  fun arg_0__ arg_1__ => tt.

#[global]
Program Instance Semigroup__unit : Semigroup unit :=
  fun _ k__ => k__ {| op_zlzlzgzg____ := Semigroup__unit_op_zlzlzgzg__ |}.

#[local] Definition Monoid__unit_mappend : unit -> unit -> unit :=
  _<<>>_.

#[local] Definition Monoid__unit_mconcat : list unit -> unit :=
  fun arg_0__ => tt.

#[local] Definition Monoid__unit_mempty : unit :=
  tt.

#[global]
Program Instance Monoid__unit : Monoid unit :=
  fun _ k__ =>
    k__ {| mappend__ := Monoid__unit_mappend ;
           mconcat__ := Monoid__unit_mconcat ;
           mempty__ := Monoid__unit_mempty |}.

(* Skipping instance `GHC.Base.Semigroup__Solo' of class `GHC.Base.Semigroup' *)

(* Skipping instance `GHC.Base.Monoid__Solo' of class `GHC.Base.Monoid' *)

(* Skipping instance `GHC.Base.Semigroup__op_zt__' of class
   `GHC.Base.Semigroup' *)

(* Skipping instance `GHC.Base.Monoid__op_zt__' of class `GHC.Base.Monoid' *)

(* Skipping instance `GHC.Base.Semigroup__op_zt____op_zt__' of class
   `GHC.Base.Semigroup' *)

(* Skipping instance `GHC.Base.Monoid__op_zt____op_zt__' of class
   `GHC.Base.Monoid' *)

(* Skipping instance `GHC.Base.Semigroup__op_zt____op_zt____op_zt____23' of
   class `GHC.Base.Semigroup' *)

(* Skipping instance `GHC.Base.Monoid__op_zt____op_zt____op_zt____23' of class
   `GHC.Base.Monoid' *)

(* Skipping instance
   `GHC.Base.Semigroup__op_zt____op_zt____op_zt____op_zt____87' of class
   `GHC.Base.Semigroup' *)

(* Skipping instance `GHC.Base.Monoid__op_zt____op_zt____op_zt____op_zt____87'
   of class `GHC.Base.Monoid' *)

#[local] Definition Semigroup__comparison_op_zlzlzgzg__
   : comparison -> comparison -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Lt, _ => Lt
    | Eq, y => y
    | Gt, _ => Gt
    end.

#[global]
Program Instance Semigroup__comparison : Semigroup comparison :=
  fun _ k__ => k__ {| op_zlzlzgzg____ := Semigroup__comparison_op_zlzlzgzg__ |}.

#[local] Definition Monoid__comparison_mappend
   : comparison -> comparison -> comparison :=
  _<<>>_.

#[local] Definition Monoid__comparison_mempty : comparison :=
  Eq.

#[global] Definition foldr {a : Type} {b : Type}
   : (a -> b -> b) -> b -> list a -> b :=
  fun k z =>
    let fix go arg_0__
      := match arg_0__ with
         | nil => z
         | cons y ys => k y (go ys)
         end in
    go.

#[local] Definition Monoid__comparison_mconcat
   : list comparison -> comparison :=
  foldr Monoid__comparison_mappend Monoid__comparison_mempty.

#[global]
Program Instance Monoid__comparison : Monoid comparison :=
  fun _ k__ =>
    k__ {| mappend__ := Monoid__comparison_mappend ;
           mconcat__ := Monoid__comparison_mconcat ;
           mempty__ := Monoid__comparison_mempty |}.

#[local] Definition Semigroup__option_op_zlzlzgzg__ {inst_a : Type} `{Semigroup
  inst_a}
   : option inst_a -> option inst_a -> option inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | None, b => b
    | a, None => a
    | Some a, Some b => Some (a <<>> b)
    end.

#[global]
Program Instance Semigroup__option {a : Type} `{Semigroup a}
   : Semigroup (option a) :=
  fun _ k__ => k__ {| op_zlzlzgzg____ := Semigroup__option_op_zlzlzgzg__ |}.

#[local] Definition Monoid__option_mappend {inst_a : Type} `{Semigroup inst_a}
   : option inst_a -> option inst_a -> option inst_a :=
  _<<>>_.

#[local] Definition Monoid__option_mempty {inst_a : Type} `{Semigroup inst_a}
   : option inst_a :=
  None.

#[local] Definition Monoid__option_mconcat {inst_a : Type} `{Semigroup inst_a}
   : list (option inst_a) -> option inst_a :=
  foldr Monoid__option_mappend Monoid__option_mempty.

#[global]
Program Instance Monoid__option {a : Type} `{Semigroup a} : Monoid (option a) :=
  fun _ k__ =>
    k__ {| mappend__ := Monoid__option_mappend ;
           mconcat__ := Monoid__option_mconcat ;
           mempty__ := Monoid__option_mempty |}.

(* Skipping instance `GHC.Base.Applicative__Solo' of class
   `GHC.Base.Applicative' *)

#[local] Definition Applicative__pair_type_liftA2 {inst_a : Type} `{Monoid
  inst_a}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) ->
     GHC.Tuple.pair_type inst_a a ->
     GHC.Tuple.pair_type inst_a b -> GHC.Tuple.pair_type inst_a c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, pair u x, pair v y => pair (u <<>> v) (f x y)
      end.

#[local] Definition Applicative__pair_type_op_zlztzg__ {inst_a : Type} `{Monoid
  inst_a}
   : forall {a : Type},
     forall {b : Type},
     GHC.Tuple.pair_type inst_a (a -> b) ->
     GHC.Tuple.pair_type inst_a a -> GHC.Tuple.pair_type inst_a b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | pair u f, pair v x => pair (u <<>> v) (f x)
      end.

#[global] Definition id {a : Type} : a -> a :=
  fun x => x.

#[local] Definition Functor__pair_type_fmap {inst_a : Type}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) -> GHC.Tuple.pair_type inst_a a -> GHC.Tuple.pair_type inst_a b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, pair x y => pair x (f y)
      end.

#[global] Definition op_z2218U__ {b : Type} {c : Type} {a : Type}
   : (b -> c) -> (a -> b) -> a -> c :=
  fun f g => fun x => f (g x).

Notation "'_∘_'" := (op_z2218U__).

Infix "∘" := (_∘_) (left associativity, at level 40).

#[global] Definition const {a : Type} {b : Type} : a -> b -> a :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | x, _ => x end.

#[local] Definition Functor__pair_type_op_zlzd__ {inst_a : Type}
   : forall {a : Type},
     forall {b : Type},
     a -> GHC.Tuple.pair_type inst_a b -> GHC.Tuple.pair_type inst_a a :=
  fun {a : Type} {b : Type} => Functor__pair_type_fmap ∘ const.

#[global]
Program Instance Functor__pair_type {a : Type}
   : Functor (GHC.Tuple.pair_type a) :=
  fun _ k__ =>
    k__ {| fmap__ := fun (a : Type) (b : Type) => Functor__pair_type_fmap ;
           op_zlzd____ := fun (a : Type) (b : Type) => Functor__pair_type_op_zlzd__ |}.

#[local] Definition Applicative__pair_type_op_ztzg__ {inst_a : Type} `{Monoid
  inst_a}
   : forall {a : Type},
     forall {b : Type},
     GHC.Tuple.pair_type inst_a a ->
     GHC.Tuple.pair_type inst_a b -> GHC.Tuple.pair_type inst_a b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__pair_type_op_zlztzg__ (op_zlzd__ id a1) a2.

#[local] Definition Applicative__pair_type_pure {inst_a : Type} `{Monoid inst_a}
   : forall {a : Type}, a -> GHC.Tuple.pair_type inst_a a :=
  fun {a : Type} => fun x => pair mempty x.

#[global]
Program Instance Applicative__pair_type {a : Type} `{Monoid a}
   : Applicative (GHC.Tuple.pair_type a) :=
  fun _ k__ =>
    k__ {| liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__pair_type_liftA2 ;
           op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__pair_type_op_zlztzg__ ;
           op_ztzg____ := fun (a : Type) (b : Type) => Applicative__pair_type_op_ztzg__ ;
           pure__ := fun (a : Type) => Applicative__pair_type_pure |}.

(* Skipping instance `GHC.Base.Monad__Solo' of class `GHC.Base.Monad' *)

#[local] Definition Monad__pair_type_return_ {inst_a : Type} `{Monoid inst_a}
   : forall {a : Type}, a -> GHC.Tuple.pair_type inst_a a :=
  fun {a : Type} => pure.

#[local] Definition Monad__pair_type_op_zgzgze__ {inst_a : Type} `{Monoid
  inst_a}
   : forall {a : Type},
     forall {b : Type},
     GHC.Tuple.pair_type inst_a a ->
     (a -> GHC.Tuple.pair_type inst_a b) -> GHC.Tuple.pair_type inst_a b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | pair u a, k => let 'pair v b := k a in pair (u <<>> v) b
      end.

#[local] Definition Monad__pair_type_op_zgzg__ {inst_a : Type} `{Monoid inst_a}
   : forall {a : Type},
     forall {b : Type},
     GHC.Tuple.pair_type inst_a a ->
     GHC.Tuple.pair_type inst_a b -> GHC.Tuple.pair_type inst_a b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__pair_type_op_zgzgze__ m (fun arg_0__ => k).

#[global]
Program Instance Monad__pair_type {a : Type} `{Monoid a}
   : Monad (GHC.Tuple.pair_type a) :=
  fun _ k__ =>
    k__ {| op_zgzg____ := fun (a : Type) (b : Type) => Monad__pair_type_op_zgzg__ ;
           op_zgzgze____ := fun (a : Type) (b : Type) => Monad__pair_type_op_zgzgze__ ;
           return___ := fun (a : Type) => Monad__pair_type_return_ |}.

#[local] Definition Functor__triple_type_fmap {inst_a : Type} {inst_b : Type}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) ->
     GHC.Tuple.triple_type inst_a inst_b a ->
     GHC.Tuple.triple_type inst_a inst_b b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, pair (pair a b) c => pair (pair a b) (f c)
      end.

#[local] Definition Functor__triple_type_op_zlzd__ {inst_a : Type} {inst_b
   : Type}
   : forall {a : Type},
     forall {b : Type},
     a ->
     GHC.Tuple.triple_type inst_a inst_b b ->
     GHC.Tuple.triple_type inst_a inst_b a :=
  fun {a : Type} {b : Type} => Functor__triple_type_fmap ∘ const.

#[global]
Program Instance Functor__triple_type {a : Type} {b : Type}
   : Functor (GHC.Tuple.triple_type a b) :=
  fun _ k__ =>
    k__ {| fmap__ := fun (a : Type) (b : Type) => Functor__triple_type_fmap ;
           op_zlzd____ := fun (a : Type) (b : Type) => Functor__triple_type_op_zlzd__ |}.

#[local] Definition Applicative__triple_type_op_zlztzg__ {inst_a : Type} {inst_b
   : Type} `{Monoid inst_a} `{Monoid inst_b}
   : forall {a : Type},
     forall {b : Type},
     GHC.Tuple.triple_type inst_a inst_b (a -> b) ->
     GHC.Tuple.triple_type inst_a inst_b a ->
     GHC.Tuple.triple_type inst_a inst_b b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | pair (pair a b) f, pair (pair a' b') x =>
          pair (pair (a <<>> a') (b <<>> b')) (f x)
      end.

#[local] Definition Applicative__triple_type_liftA2 {inst_a : Type} {inst_b
   : Type} `{Monoid inst_a} `{Monoid inst_b}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) ->
     GHC.Tuple.triple_type inst_a inst_b a ->
     GHC.Tuple.triple_type inst_a inst_b b ->
     GHC.Tuple.triple_type inst_a inst_b c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__triple_type_op_zlztzg__ (fmap f x).

#[local] Definition Applicative__triple_type_op_ztzg__ {inst_a : Type} {inst_b
   : Type} `{Monoid inst_a} `{Monoid inst_b}
   : forall {a : Type},
     forall {b : Type},
     GHC.Tuple.triple_type inst_a inst_b a ->
     GHC.Tuple.triple_type inst_a inst_b b ->
     GHC.Tuple.triple_type inst_a inst_b b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__triple_type_op_zlztzg__ (op_zlzd__ id a1) a2.

#[local] Definition Applicative__triple_type_pure {inst_a : Type} {inst_b
   : Type} `{Monoid inst_a} `{Monoid inst_b}
   : forall {a : Type}, a -> GHC.Tuple.triple_type inst_a inst_b a :=
  fun {a : Type} => fun x => pair (pair mempty mempty) x.

#[global]
Program Instance Applicative__triple_type {a : Type} {b : Type} `{Monoid a}
  `{Monoid b}
   : Applicative (GHC.Tuple.triple_type a b) :=
  fun _ k__ =>
    k__ {| liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__triple_type_liftA2 ;
           op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__triple_type_op_zlztzg__ ;
           op_ztzg____ := fun (a : Type) (b : Type) => Applicative__triple_type_op_ztzg__ ;
           pure__ := fun (a : Type) => Applicative__triple_type_pure |}.

#[local] Definition Monad__triple_type_op_zgzgze__ {inst_a : Type} {inst_b
   : Type} `{Monoid inst_a} `{Monoid inst_b}
   : forall {a : Type},
     forall {b : Type},
     GHC.Tuple.triple_type inst_a inst_b a ->
     (a -> GHC.Tuple.triple_type inst_a inst_b b) ->
     GHC.Tuple.triple_type inst_a inst_b b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | pair (pair u v) a, k =>
          let 'pair (pair u' v') b := k a in
          pair (pair (u <<>> u') (v <<>> v')) b
      end.

#[local] Definition Monad__triple_type_op_zgzg__ {inst_a : Type} {inst_b : Type}
  `{Monoid inst_a} `{Monoid inst_b}
   : forall {a : Type},
     forall {b : Type},
     GHC.Tuple.triple_type inst_a inst_b a ->
     GHC.Tuple.triple_type inst_a inst_b b ->
     GHC.Tuple.triple_type inst_a inst_b b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__triple_type_op_zgzgze__ m (fun arg_0__ => k).

#[local] Definition Monad__triple_type_return_ {inst_a : Type} {inst_b : Type}
  `{Monoid inst_a} `{Monoid inst_b}
   : forall {a : Type}, a -> GHC.Tuple.triple_type inst_a inst_b a :=
  fun {a : Type} => pure.

#[global]
Program Instance Monad__triple_type {a : Type} {b : Type} `{Monoid a} `{Monoid
  b}
   : Monad (GHC.Tuple.triple_type a b) :=
  fun _ k__ =>
    k__ {| op_zgzg____ := fun (a : Type) (b : Type) =>
             Monad__triple_type_op_zgzg__ ;
           op_zgzgze____ := fun (a : Type) (b : Type) => Monad__triple_type_op_zgzgze__ ;
           return___ := fun (a : Type) => Monad__triple_type_return_ |}.

#[local] Definition Functor__quad_type_fmap {inst_a : Type} {inst_b : Type}
  {inst_c : Type}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) ->
     GHC.Tuple.quad_type inst_a inst_b inst_c a ->
     GHC.Tuple.quad_type inst_a inst_b inst_c b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, pair (pair (pair a b) c) d => pair (pair (pair a b) c) (f d)
      end.

#[local] Definition Functor__quad_type_op_zlzd__ {inst_a : Type} {inst_b : Type}
  {inst_c : Type}
   : forall {a : Type},
     forall {b : Type},
     a ->
     GHC.Tuple.quad_type inst_a inst_b inst_c b ->
     GHC.Tuple.quad_type inst_a inst_b inst_c a :=
  fun {a : Type} {b : Type} => Functor__quad_type_fmap ∘ const.

#[global]
Program Instance Functor__quad_type {a : Type} {b : Type} {c : Type}
   : Functor (GHC.Tuple.quad_type a b c) :=
  fun _ k__ =>
    k__ {| fmap__ := fun (a : Type) (b : Type) => Functor__quad_type_fmap ;
           op_zlzd____ := fun (a : Type) (b : Type) => Functor__quad_type_op_zlzd__ |}.

#[local] Definition Applicative__quad_type_op_zlztzg__ {inst_a : Type} {inst_b
   : Type} {inst_c : Type} `{Monoid inst_a} `{Monoid inst_b} `{Monoid inst_c}
   : forall {a : Type},
     forall {b : Type},
     GHC.Tuple.quad_type inst_a inst_b inst_c (a -> b) ->
     GHC.Tuple.quad_type inst_a inst_b inst_c a ->
     GHC.Tuple.quad_type inst_a inst_b inst_c b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | pair (pair (pair a b) c) f, pair (pair (pair a' b') c') x =>
          pair (pair (pair (a <<>> a') (b <<>> b')) (c <<>> c')) (f x)
      end.

#[local] Definition Applicative__quad_type_liftA2 {inst_a : Type} {inst_b
   : Type} {inst_c : Type} `{Monoid inst_a} `{Monoid inst_b} `{Monoid inst_c}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) ->
     GHC.Tuple.quad_type inst_a inst_b inst_c a ->
     GHC.Tuple.quad_type inst_a inst_b inst_c b ->
     GHC.Tuple.quad_type inst_a inst_b inst_c c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__quad_type_op_zlztzg__ (fmap f x).

#[local] Definition Applicative__quad_type_op_ztzg__ {inst_a : Type} {inst_b
   : Type} {inst_c : Type} `{Monoid inst_a} `{Monoid inst_b} `{Monoid inst_c}
   : forall {a : Type},
     forall {b : Type},
     GHC.Tuple.quad_type inst_a inst_b inst_c a ->
     GHC.Tuple.quad_type inst_a inst_b inst_c b ->
     GHC.Tuple.quad_type inst_a inst_b inst_c b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__quad_type_op_zlztzg__ (op_zlzd__ id a1) a2.

#[local] Definition Applicative__quad_type_pure {inst_a : Type} {inst_b : Type}
  {inst_c : Type} `{Monoid inst_a} `{Monoid inst_b} `{Monoid inst_c}
   : forall {a : Type}, a -> GHC.Tuple.quad_type inst_a inst_b inst_c a :=
  fun {a : Type} => fun x => pair (pair (pair mempty mempty) mempty) x.

#[global]
Program Instance Applicative__quad_type {a : Type} {b : Type} {c : Type}
  `{Monoid a} `{Monoid b} `{Monoid c}
   : Applicative (GHC.Tuple.quad_type a b c) :=
  fun _ k__ =>
    k__ {| liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__quad_type_liftA2 ;
           op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__quad_type_op_zlztzg__ ;
           op_ztzg____ := fun (a : Type) (b : Type) => Applicative__quad_type_op_ztzg__ ;
           pure__ := fun (a : Type) => Applicative__quad_type_pure |}.

#[local] Definition Monad__quad_type_op_zgzgze__ {inst_a : Type} {inst_b : Type}
  {inst_c : Type} `{Monoid inst_a} `{Monoid inst_b} `{Monoid inst_c}
   : forall {a : Type},
     forall {b : Type},
     GHC.Tuple.quad_type inst_a inst_b inst_c a ->
     (a -> GHC.Tuple.quad_type inst_a inst_b inst_c b) ->
     GHC.Tuple.quad_type inst_a inst_b inst_c b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | pair (pair (pair u v) w) a, k =>
          let 'pair (pair (pair u' v') w') b := k a in
          pair (pair (pair (u <<>> u') (v <<>> v')) (w <<>> w')) b
      end.

#[local] Definition Monad__quad_type_op_zgzg__ {inst_a : Type} {inst_b : Type}
  {inst_c : Type} `{Monoid inst_a} `{Monoid inst_b} `{Monoid inst_c}
   : forall {a : Type},
     forall {b : Type},
     GHC.Tuple.quad_type inst_a inst_b inst_c a ->
     GHC.Tuple.quad_type inst_a inst_b inst_c b ->
     GHC.Tuple.quad_type inst_a inst_b inst_c b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__quad_type_op_zgzgze__ m (fun arg_0__ => k).

#[local] Definition Monad__quad_type_return_ {inst_a : Type} {inst_b : Type}
  {inst_c : Type} `{Monoid inst_a} `{Monoid inst_b} `{Monoid inst_c}
   : forall {a : Type}, a -> GHC.Tuple.quad_type inst_a inst_b inst_c a :=
  fun {a : Type} => pure.

#[global]
Program Instance Monad__quad_type {a : Type} {b : Type} {c : Type} `{Monoid a}
  `{Monoid b} `{Monoid c}
   : Monad (GHC.Tuple.quad_type a b c) :=
  fun _ k__ =>
    k__ {| op_zgzg____ := fun (a : Type) (b : Type) => Monad__quad_type_op_zgzg__ ;
           op_zgzgze____ := fun (a : Type) (b : Type) => Monad__quad_type_op_zgzgze__ ;
           return___ := fun (a : Type) => Monad__quad_type_return_ |}.

#[local] Definition Functor__quint_type_fmap {inst_a : Type} {inst_b : Type}
  {inst_c : Type} {inst_d : Type}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) ->
     GHC.Tuple.quint_type inst_a inst_b inst_c inst_d a ->
     GHC.Tuple.quint_type inst_a inst_b inst_c inst_d b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, pair (pair (pair (pair a b) c) d) e =>
          pair (pair (pair (pair a b) c) d) (f e)
      end.

#[local] Definition Functor__quint_type_op_zlzd__ {inst_a : Type} {inst_b
   : Type} {inst_c : Type} {inst_d : Type}
   : forall {a : Type},
     forall {b : Type},
     a ->
     GHC.Tuple.quint_type inst_a inst_b inst_c inst_d b ->
     GHC.Tuple.quint_type inst_a inst_b inst_c inst_d a :=
  fun {a : Type} {b : Type} => Functor__quint_type_fmap ∘ const.

#[global]
Program Instance Functor__quint_type {a : Type} {b : Type} {c : Type} {d : Type}
   : Functor (GHC.Tuple.quint_type a b c d) :=
  fun _ k__ =>
    k__ {| fmap__ := fun (a : Type) (b : Type) => Functor__quint_type_fmap ;
           op_zlzd____ := fun (a : Type) (b : Type) => Functor__quint_type_op_zlzd__ |}.

#[local] Definition Functor__sext_type_fmap {inst_a : Type} {inst_b : Type}
  {inst_c : Type} {inst_d : Type} {inst_e : Type}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) ->
     GHC.Tuple.sext_type inst_a inst_b inst_c inst_d inst_e a ->
     GHC.Tuple.sext_type inst_a inst_b inst_c inst_d inst_e b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | fun_, pair (pair (pair (pair (pair a b) c) d) e) f =>
          pair (pair (pair (pair (pair a b) c) d) e) (fun_ f)
      end.

#[local] Definition Functor__sext_type_op_zlzd__ {inst_a : Type} {inst_b : Type}
  {inst_c : Type} {inst_d : Type} {inst_e : Type}
   : forall {a : Type},
     forall {b : Type},
     a ->
     GHC.Tuple.sext_type inst_a inst_b inst_c inst_d inst_e b ->
     GHC.Tuple.sext_type inst_a inst_b inst_c inst_d inst_e a :=
  fun {a : Type} {b : Type} => Functor__sext_type_fmap ∘ const.

#[global]
Program Instance Functor__sext_type {a : Type} {b : Type} {c : Type} {d : Type}
  {e : Type}
   : Functor (GHC.Tuple.sext_type a b c d e) :=
  fun _ k__ =>
    k__ {| fmap__ := fun (a : Type) (b : Type) => Functor__sext_type_fmap ;
           op_zlzd____ := fun (a : Type) (b : Type) => Functor__sext_type_op_zlzd__ |}.

#[local] Definition Functor__sept_type_fmap {inst_a : Type} {inst_b : Type}
  {inst_c : Type} {inst_d : Type} {inst_e : Type} {inst_f : Type}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) ->
     GHC.Tuple.sept_type inst_a inst_b inst_c inst_d inst_e inst_f a ->
     GHC.Tuple.sept_type inst_a inst_b inst_c inst_d inst_e inst_f b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | fun_, pair (pair (pair (pair (pair (pair a b) c) d) e) f) g =>
          pair (pair (pair (pair (pair (pair a b) c) d) e) f) (fun_ g)
      end.

#[local] Definition Functor__sept_type_op_zlzd__ {inst_a : Type} {inst_b : Type}
  {inst_c : Type} {inst_d : Type} {inst_e : Type} {inst_f : Type}
   : forall {a : Type},
     forall {b : Type},
     a ->
     GHC.Tuple.sept_type inst_a inst_b inst_c inst_d inst_e inst_f b ->
     GHC.Tuple.sept_type inst_a inst_b inst_c inst_d inst_e inst_f a :=
  fun {a : Type} {b : Type} => Functor__sept_type_fmap ∘ const.

#[global]
Program Instance Functor__sept_type {a : Type} {b : Type} {c : Type} {d : Type}
  {e : Type} {f : Type}
   : Functor (GHC.Tuple.sept_type a b c d e f) :=
  fun _ k__ =>
    k__ {| fmap__ := fun (a : Type) (b : Type) => Functor__sept_type_fmap ;
           op_zlzd____ := fun (a : Type) (b : Type) => Functor__sept_type_op_zlzd__ |}.

(* Skipping instance `GHC.Base.Semigroup__IO' of class `GHC.Base.Semigroup' *)

(* Skipping instance `GHC.Base.Monoid__IO' of class `GHC.Base.Monoid' *)

(* Skipping instance `GHC.Base.Functor__arrow' of class `GHC.Base.Functor' *)

(* Skipping instance `GHC.Base.Applicative__arrow' of class
   `GHC.Base.Applicative' *)

(* Skipping instance `GHC.Base.Monad__arrow' of class `GHC.Base.Monad' *)

(* Skipping instance `GHC.Base.Functor__Solo' of class `GHC.Base.Functor' *)

#[local] Definition Functor__option_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> option a -> option b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, None => None
      | f, Some a => Some (f a)
      end.

#[local] Definition Functor__option_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> option b -> option a :=
  fun {a : Type} {b : Type} => Functor__option_fmap ∘ const.

#[global]
Program Instance Functor__option : Functor option :=
  fun _ k__ =>
    k__ {| fmap__ := fun (a : Type) (b : Type) => Functor__option_fmap ;
           op_zlzd____ := fun (a : Type) (b : Type) => Functor__option_op_zlzd__ |}.

#[local] Definition Applicative__option_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> option a -> option b -> option c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, Some x, Some y => Some (f x y)
      | _, _, _ => None
      end.

#[local] Definition Applicative__option_op_zlztzg__
   : forall {a : Type},
     forall {b : Type}, option (a -> b) -> option a -> option b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Some f, m => fmap f m
      | None, _m => None
      end.

#[local] Definition Applicative__option_op_ztzg__
   : forall {a : Type}, forall {b : Type}, option a -> option b -> option b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Some _m1, m2 => m2
      | None, _m2 => None
      end.

#[local] Definition Applicative__option_pure
   : forall {a : Type}, a -> option a :=
  fun {a : Type} => Some.

#[global]
Program Instance Applicative__option : Applicative option :=
  fun _ k__ =>
    k__ {| liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__option_liftA2 ;
           op_zlztzg____ := fun (a : Type) (b : Type) => Applicative__option_op_zlztzg__ ;
           op_ztzg____ := fun (a : Type) (b : Type) => Applicative__option_op_ztzg__ ;
           pure__ := fun (a : Type) => Applicative__option_pure |}.

#[local] Definition Monad__option_op_zgzg__
   : forall {a : Type}, forall {b : Type}, option a -> option b -> option b :=
  fun {a : Type} {b : Type} => _*>_.

#[local] Definition Monad__option_op_zgzgze__
   : forall {a : Type},
     forall {b : Type}, option a -> (a -> option b) -> option b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Some x, k => k x
      | None, _ => None
      end.

#[local] Definition Monad__option_return_ : forall {a : Type}, a -> option a :=
  fun {a : Type} => pure.

#[global]
Program Instance Monad__option : Monad option :=
  fun _ k__ =>
    k__ {| op_zgzg____ := fun (a : Type) (b : Type) => Monad__option_op_zgzg__ ;
           op_zgzgze____ := fun (a : Type) (b : Type) => Monad__option_op_zgzgze__ ;
           return___ := fun (a : Type) => Monad__option_return_ |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `GHC.Base.Alternative__option' *)

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `GHC.Base.MonadPlus__option' *)

#[global] Definition map {A B : Type} (f : A -> B) xs :=
  Stdlib.Lists.List.map f xs.

#[local] Definition Functor__list_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> list a -> list b :=
  fun {a : Type} {b : Type} => map.

#[local] Definition Functor__list_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> list b -> list a :=
  fun {a : Type} {b : Type} => Functor__list_fmap ∘ const.

#[global]
Program Instance Functor__list : Functor list :=
  fun _ k__ =>
    k__ {| fmap__ := fun (a : Type) (b : Type) => Functor__list_fmap ;
           op_zlzd____ := fun (a : Type) (b : Type) => Functor__list_op_zlzd__ |}.

#[local] Definition Functor__NonEmpty_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> NonEmpty a -> NonEmpty b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, NEcons a as_ => NEcons (f a) (fmap f as_)
      end.

#[local] Definition Functor__NonEmpty_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> NonEmpty b -> NonEmpty a :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | b, NEcons _ as_ => NEcons b (op_zlzd__ b as_)
      end.

#[global]
Program Instance Functor__NonEmpty : Functor NonEmpty :=
  fun _ k__ =>
    k__ {| fmap__ := fun (a : Type) (b : Type) => Functor__NonEmpty_fmap ;
           op_zlzd____ := fun (a : Type) (b : Type) => Functor__NonEmpty_op_zlzd__ |}.

#[local] Definition Applicative__NonEmpty_pure
   : forall {a : Type}, a -> NonEmpty a :=
  fun {a : Type} => fun a => NEcons a nil.

#[local] Definition Applicative__list_liftA2
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type}, (a -> b -> c) -> list a -> list b -> list c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f xs ys =>
      Stdlib.Lists.List.flat_map (fun x =>
                                    Stdlib.Lists.List.flat_map (fun y => cons (f x y) nil) ys) xs.

#[local] Definition Applicative__list_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, list (a -> b) -> list a -> list b :=
  fun {a : Type} {b : Type} =>
    fun fs xs =>
      Stdlib.Lists.List.flat_map (fun f =>
                                    Stdlib.Lists.List.flat_map (fun x => cons (f x) nil) xs) fs.

#[local] Definition Applicative__list_op_ztzg__
   : forall {a : Type}, forall {b : Type}, list a -> list b -> list b :=
  fun {a : Type} {b : Type} =>
    fun xs ys =>
      Stdlib.Lists.List.flat_map (fun _ =>
                                    Stdlib.Lists.List.flat_map (fun y => cons y nil) ys) xs.

#[local] Definition Applicative__list_pure : forall {a : Type}, a -> list a :=
  fun {a : Type} => fun x => cons x nil.

#[global]
Program Instance Applicative__list : Applicative list :=
  fun _ k__ =>
    k__ {| liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__list_liftA2 ;
           op_zlztzg____ := fun (a : Type) (b : Type) => Applicative__list_op_zlztzg__ ;
           op_ztzg____ := fun (a : Type) (b : Type) => Applicative__list_op_ztzg__ ;
           pure__ := fun (a : Type) => Applicative__list_pure |}.

#[local] Definition Monad__list_return_ : forall {a : Type}, a -> list a :=
  fun {a : Type} => pure.

#[local] Definition Monad__list_op_zgzg__
   : forall {a : Type}, forall {b : Type}, list a -> list b -> list b :=
  fun {a : Type} {b : Type} => _*>_.

#[local] Definition Monad__list_op_zgzgze__
   : forall {a : Type}, forall {b : Type}, list a -> (a -> list b) -> list b :=
  fun {a : Type} {b : Type} =>
    fun xs f =>
      Stdlib.Lists.List.flat_map (fun x =>
                                    Stdlib.Lists.List.flat_map (fun y => cons y nil) (f x)) xs.

#[global]
Program Instance Monad__list : Monad list :=
  fun _ k__ =>
    k__ {| op_zgzg____ := fun (a : Type) (b : Type) => Monad__list_op_zgzg__ ;
           op_zgzgze____ := fun (a : Type) (b : Type) => Monad__list_op_zgzgze__ ;
           return___ := fun (a : Type) => Monad__list_return_ |}.

#[local] Definition Monad__NonEmpty_op_zgzgze__
   : forall {a : Type},
     forall {b : Type}, NonEmpty a -> (a -> NonEmpty b) -> NonEmpty b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | NEcons a as_, f =>
          let toList := fun '(NEcons c cs) => cons c cs in
          let bs' := as_ >>= (toList ∘ f) in
          let 'NEcons b bs := f a in
          NEcons b (Corelib.Init.Datatypes.app bs bs')
      end.

#[local] Definition Applicative__NonEmpty_liftA2 {a} {b} {c}
   : (a -> b -> c) -> NonEmpty a -> NonEmpty b -> NonEmpty c :=
  fun f m1 m2 =>
    Monad__NonEmpty_op_zgzgze__ m1 (fun x1 =>
                                   Monad__NonEmpty_op_zgzgze__ m2 (fun x2 =>
                                                                  Applicative__NonEmpty_pure (f x1 x2))).

#[local] Definition Applicative__NonEmpty_op_zlztzg__ {a} {b}
   : NonEmpty (a -> b) -> NonEmpty a -> NonEmpty b :=
  fun m1 m2 =>
    Monad__NonEmpty_op_zgzgze__ m1 (fun x1 =>
                                   Monad__NonEmpty_op_zgzgze__ m2 (fun x2 => Applicative__NonEmpty_pure (x1 x2))).

#[local] Definition Applicative__NonEmpty_op_ztzg__
   : forall {a : Type},
     forall {b : Type}, NonEmpty a -> NonEmpty b -> NonEmpty b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__NonEmpty_op_zlztzg__ (op_zlzd__ id a1) a2.

#[global]
Program Instance Applicative__NonEmpty : Applicative NonEmpty :=
  fun _ k__ =>
    k__ {| liftA2__ := fun (a : Type) (b : Type) (c : Type) =>
             Applicative__NonEmpty_liftA2 ;
           op_zlztzg____ := fun (a : Type) (b : Type) =>
             Applicative__NonEmpty_op_zlztzg__ ;
           op_ztzg____ := fun (a : Type) (b : Type) => Applicative__NonEmpty_op_ztzg__ ;
           pure__ := fun (a : Type) => Applicative__NonEmpty_pure |}.

#[local] Definition Monad__NonEmpty_return_
   : forall {a : Type}, a -> NonEmpty a :=
  fun {a : Type} => pure.

#[local] Definition Monad__NonEmpty_op_zgzg__
   : forall {a : Type},
     forall {b : Type}, NonEmpty a -> NonEmpty b -> NonEmpty b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__NonEmpty_op_zgzgze__ m (fun arg_0__ => k).

#[global]
Program Instance Monad__NonEmpty : Monad NonEmpty :=
  fun _ k__ =>
    k__ {| op_zgzg____ := fun (a : Type) (b : Type) => Monad__NonEmpty_op_zgzg__ ;
           op_zgzgze____ := fun (a : Type) (b : Type) => Monad__NonEmpty_op_zgzgze__ ;
           return___ := fun (a : Type) => Monad__NonEmpty_return_ |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `GHC.Base.Alternative__list' *)

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `GHC.Base.MonadPlus__list' *)

(* Skipping instance `GHC.Base.Functor__IO' of class `GHC.Base.Functor' *)

(* Skipping instance `GHC.Base.Applicative__IO' of class
   `GHC.Base.Applicative' *)

(* Skipping instance `GHC.Base.Monad__IO' of class `GHC.Base.Monad' *)

(* Skipping all instances of class `GHC.Base.Alternative', including
   `GHC.Base.Alternative__IO' *)

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `GHC.Base.MonadPlus__IO' *)

#[global] Definition absurd {a : Type} : Void -> a :=
  fun a => match a with end.

#[global] Definition vacuous {f : Type -> Type} {a : Type} `{Functor f}
   : f Void -> f a :=
  fmap absurd.

#[global] Definition op_zlztztzg__ {f : Type -> Type} {a : Type} {b : Type}
  `{Applicative f}
   : f a -> f (a -> b) -> f b :=
  liftA2 (fun a f => f a).

Notation "'_<**>_'" := (op_zlztztzg__).

Infix "<**>" := (_<**>_) (at level 99).

#[global] Definition liftA {f : Type -> Type} {a : Type} {b : Type}
  `{Applicative f}
   : (a -> b) -> f a -> f b :=
  fun f a => pure f <*> a.

#[global] Definition liftA3 {f : Type -> Type} {a : Type} {b : Type} {c : Type}
  {d : Type} `{Applicative f}
   : (a -> b -> c -> d) -> f a -> f b -> f c -> f d :=
  fun f a b c => liftA2 f a b <*> c.

#[global] Definition join {m : Type -> Type} {a : Type} `{Monad m}
   : m (m a) -> m a :=
  fun x => x >>= id.

#[global] Definition op_zezlzl__ {m : Type -> Type} {a : Type} {b : Type}
  `{Monad m}
   : (a -> m b) -> m a -> m b :=
  fun f x => x >>= f.

Notation "'_=<<_'" := (op_zezlzl__).

Infix "=<<" := (_=<<_) (at level 99).

#[global] Definition when {f : Type -> Type} `{Applicative f}
   : bool -> f unit -> f unit :=
  fun p s => if p : bool then s else pure tt.

#[global] Definition mapM {m : Type -> Type} {a : Type} {b : Type} `{Monad m}
   : (a -> m b) -> list a -> m (list b) :=
  fun f as_ =>
    let k := fun a r => f a >>= (fun x => r >>= (fun xs => return_ (cons x xs))) in
    foldr k (return_ nil) as_.

#[global] Definition sequence {m : Type -> Type} {a : Type} `{Monad m}
   : list (m a) -> m (list a) :=
  mapM id.

#[global] Definition liftM {m : Type -> Type} {a1 : Type} {r : Type} `{Monad m}
   : (a1 -> r) -> m a1 -> m r :=
  fun f m1 => m1 >>= (fun x1 => return_ (f x1)).

#[global] Definition liftM2 {m : Type -> Type} {a1 : Type} {a2 : Type} {r
   : Type} `{Monad m}
   : (a1 -> a2 -> r) -> m a1 -> m a2 -> m r :=
  fun f m1 m2 => m1 >>= (fun x1 => m2 >>= (fun x2 => return_ (f x1 x2))).

#[global] Definition liftM3 {m : Type -> Type} {a1 : Type} {a2 : Type} {a3
   : Type} {r : Type} `{Monad m}
   : (a1 -> a2 -> a3 -> r) -> m a1 -> m a2 -> m a3 -> m r :=
  fun f m1 m2 m3 =>
    m1 >>= (fun x1 => m2 >>= (fun x2 => m3 >>= (fun x3 => return_ (f x1 x2 x3)))).

#[global] Definition liftM4 {m : Type -> Type} {a1 : Type} {a2 : Type} {a3
   : Type} {a4 : Type} {r : Type} `{Monad m}
   : (a1 -> a2 -> a3 -> a4 -> r) -> m a1 -> m a2 -> m a3 -> m a4 -> m r :=
  fun f m1 m2 m3 m4 =>
    m1 >>=
    (fun x1 =>
       m2 >>=
       (fun x2 => m3 >>= (fun x3 => m4 >>= (fun x4 => return_ (f x1 x2 x3 x4))))).

#[global] Definition liftM5 {m : Type -> Type} {a1 : Type} {a2 : Type} {a3
   : Type} {a4 : Type} {a5 : Type} {r : Type} `{Monad m}
   : (a1 -> a2 -> a3 -> a4 -> a5 -> r) ->
     m a1 -> m a2 -> m a3 -> m a4 -> m a5 -> m r :=
  fun f m1 m2 m3 m4 m5 =>
    m1 >>=
    (fun x1 =>
       m2 >>=
       (fun x2 =>
          m3 >>=
          (fun x3 => m4 >>= (fun x4 => m5 >>= (fun x5 => return_ (f x1 x2 x3 x4 x5)))))).

#[global] Definition ap {m : Type -> Type} {a : Type} {b : Type} `{Monad m}
   : m (a -> b) -> m a -> m b :=
  fun m1 m2 => m1 >>= (fun x1 => m2 >>= (fun x2 => return_ (x1 x2))).

(* Skipping definition `GHC.Base.build' *)

(* Skipping definition `GHC.Base.augment' *)

#[global] Definition mapFB {elt : Type} {lst : Type} {a : Type}
   : (elt -> lst -> lst) -> (a -> elt) -> a -> lst -> lst :=
  fun c f => fun x ys => c (f x) ys.

(* Skipping definition `Coq.Init.Datatypes.app' *)

#[global] Definition otherwise : bool :=
  true.

(* Skipping definition `GHC.Base.unsafeChr' *)

(* Skipping definition `GHC.Base.ord' *)

Fixpoint eqString (arg_0__ arg_1__ : String) : bool
  := match arg_0__, arg_1__ with
     | nil, nil => true
     | cons c1 cs1, cons c2 cs2 => andb (c1 == c2) (eqString cs1 cs2)
     | _, _ => false
     end.

(* Skipping definition `GHC.Base.minInt' *)

(* Skipping definition `GHC.Base.maxInt' *)

#[global] Definition assert {a : Type} : bool -> a -> a :=
  fun _pred r => r.

#[global] Definition breakpoint {a : Type} : a -> a :=
  fun r => r.

#[global] Definition breakpointCond {a : Type} : bool -> a -> a :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, r => r end.

#[global] Definition flip {a : Type} {b : Type} {c : Type}
   : (a -> b -> c) -> b -> a -> c :=
  fun f x y => f y x.

#[global] Definition op_zd__ {a} {b} : (a -> b) -> a -> b :=
  fun f x => f x.

#[global] Definition op_zdzn__ {a : Type} {b : Type} : (a -> b) -> a -> b :=
  fun f x => let vx := x in f vx.

(* Skipping definition `GHC.Base.until' *)

#[global] Definition asTypeOf {a : Type} : a -> a -> a :=
  const.

(* Skipping definition `GHC.Base.returnIO' *)

(* Skipping definition `GHC.Base.bindIO' *)

(* Skipping definition `GHC.Base.thenIO' *)

(* Skipping definition `GHC.Base.failIO' *)

(* Skipping definition `GHC.Base.unIO' *)

(* Skipping definition `GHC.Base.getTag' *)

(* Skipping definition `GHC.Base.quotInt' *)

(* Skipping definition `GHC.Base.remInt' *)

(* Skipping definition `GHC.Base.divInt' *)

(* Skipping definition `GHC.Base.modInt' *)

(* Skipping definition `GHC.Base.quotRemInt' *)

(* Skipping definition `GHC.Base.divModInt' *)

(* Skipping definition `GHC.Base.shift_mask' *)

(* Skipping definition `GHC.Base.op_shiftLzh__' *)

(* Skipping definition `GHC.Base.op_shiftRLzh__' *)

(* Skipping definition `GHC.Base.op_iShiftLzh__' *)

(* Skipping definition `GHC.Base.op_iShiftRAzh__' *)

(* Skipping definition `GHC.Base.op_iShiftRLzh__' *)

#[global] Definition op_zlzt__ `{g__0__ : Applicative f}
   : forall {a : Type}, forall {b : Type}, f a -> f b -> f a :=
  fun {a} {b} => (@liftA2 f _ g__0__ a b a (fun x _ => x)).

Module Notations.
Export ManualNotations.
Notation "'_GHC.Base.<<>>_'" := (op_zlzlzgzg__).
Infix "GHC.Base.<<>>" := (_<<>>_) (at level 99).
Notation "'_GHC.Base.<$_'" := (op_zlzd__).
Infix "GHC.Base.<$" := (op_zlzd__) (at level 99).
Notation "'_GHC.Base.<*>_'" := (op_zlztzg__).
Infix "GHC.Base.<*>" := (_<*>_) (at level 99).
Notation "'_GHC.Base.*>_'" := (op_ztzg__).
Infix "GHC.Base.*>" := (_*>_) (at level 99).
Notation "'_GHC.Base.>>_'" := (op_zgzg__).
Infix "GHC.Base.>>" := (_>>_) (at level 99).
Notation "'_GHC.Base.>>=_'" := (op_zgzgze__).
Infix "GHC.Base.>>=" := (_>>=_) (at level 99).
Notation "'_GHC.Base.∘_'" := (op_z2218U__).
Infix "GHC.Base.∘" := (_∘_) (left associativity, at level 40).
Notation "'_GHC.Base.<**>_'" := (op_zlztztzg__).
Infix "GHC.Base.<**>" := (_<**>_) (at level 99).
Notation "'_GHC.Base.=<<_'" := (op_zezlzl__).
Infix "GHC.Base.=<<" := (_=<<_) (at level 99).
End Notations.

(* External variables:
     Eq Gt Lt None Some String Type andb bool comparison cons false list nil
     op_zeze__ option pair true tt unit Corelib.Init.Datatypes.app
     GHC.Tuple.pair_type GHC.Tuple.quad_type GHC.Tuple.quint_type GHC.Tuple.sept_type
     GHC.Tuple.sext_type GHC.Tuple.triple_type Stdlib.Lists.List.flat_map
     Stdlib.Lists.List.map
*)
