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

Require Corelib.Init.Datatypes.
Require Corelib.Program.Basics.
Require Stdlib.ZArith.BinInt.
Require Data.Foldable.
Require Data.Functor.
Require Data.Maybe.
Require Data.SemigroupInternal.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require GHC.Prim.
Require HsToRocq.Err.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive ViewR s a : Type :=
  | EmptyR : ViewR s a
  | op_ZCzg__ : s a -> a -> ViewR s a.

Inductive ViewL s a : Type :=
  | EmptyL : ViewL s a
  | op_ZCzl__ : a -> s a -> ViewL s a.

Inductive Split t a : Type := | MkSplit : t -> a -> t -> Split t a.

Inductive Node v a : Type :=
  | Node2 : v -> a -> a -> Node v a
  | Node3 : v -> a -> a -> a -> Node v a.

Record Measured__Dict (v : Type) (a : Type) := Measured__Dict_Build {
  measure__ : a -> v }.

#[global] Definition Measured (v : Type) (a : Type) `{GHC.Base.Monoid v} :=
  forall r__, (Measured__Dict v a -> r__) -> r__.
Existing Class Measured.

#[global] Definition measure `{g__0__ : Measured v a} : a -> v :=
  g__0__ _ (measure__ v a).

Inductive Digit a : Type :=
  | One : a -> Digit a
  | Two : a -> a -> Digit a
  | Three : a -> a -> a -> Digit a
  | Four : a -> a -> a -> a -> Digit a.

Inductive FingerTree v a : Type :=
  | Empty : FingerTree v a
  | Single : a -> FingerTree v a
  | Deep
   : v -> (Digit a) -> (FingerTree v (Node v a)) -> (Digit a) -> FingerTree v a.

Inductive SearchResult v a : Type :=
  | Position : (FingerTree v a) -> a -> (FingerTree v a) -> SearchResult v a
  | OnLeft : SearchResult v a
  | OnRight : SearchResult v a
  | Nowhere : SearchResult v a.

Arguments EmptyR {_} {_}.

Arguments op_ZCzg__ {_} {_} _ _.

Arguments EmptyL {_} {_}.

Arguments op_ZCzl__ {_} {_} _ _.

Arguments MkSplit {_} {_} _ _ _.

Arguments Node2 {_} {_} _ _ _.

Arguments Node3 {_} {_} _ _ _ _.

Arguments One {_} _.

Arguments Two {_} _ _.

Arguments Three {_} _ _ _.

Arguments Four {_} _ _ _ _.

Arguments Empty {_} {_}.

Arguments Single {_} {_} _.

Arguments Deep {_} {_} _ _ _ _.

Arguments Position {_} {_} _ _ _.

Arguments OnLeft {_} {_}.

Arguments OnRight {_} {_}.

Arguments Nowhere {_} {_}.

Notation "'_:>_'" := (op_ZCzg__).

Infix ":>" := (_:>_) (at level 99).

Notation "'_:<_'" := (op_ZCzl__).

Infix ":<" := (_:<_) (at level 99).

(* Midamble *)

Require Import Stdlib.Program.Program HsToRocq.Err.
(* Program conditionals currently use this relative compatibility path. *)
Module Bool.
  Module Sumbool := Corelib.Init.Sumbool.
End Bool.
Local Obligation Tactic := idtac.

#[local] Instance DefaultFingerTree {v a} : Default (FingerTree v a) :=
  {| default := Empty |}.
#[local] Instance DefaultSplit {t a} `{Default t} `{Default a} : Default (Split t a) :=
  {| default := MkSplit default default default |}.
#[local] Instance DefaultNode {v a} `{GHC.Base.Monoid v} `{Default a}
  : Default (Node v a) :=
  {| default := Node2 GHC.Base.mempty default default |}.

Ltac core_inhabitant :=
  program_simpl;
  match goal with
  | |- Default ?a =>
      match goal with
      | x : a |- _ => exact (Build_Default _ x)
      | t : FingerTree _ a |- _ =>
          destruct t;
          [ cbn in *;
            first [congruence |
              match goal with
              | h : andb (negb ?b) ?b = true |- _ => destruct b; discriminate
              end |
              match goal with
              | h : forall wildcard, ~ (wildcard = ?p /\ _) |- _ =>
                  exfalso; apply (h p); split; reflexivity
              end]
          | constructor; assumption
          | match goal with
            | d : Digit a |- _ => destruct d; constructor; assumption
            end ]
      end
  end.

(* Converted value declarations: *)

#[local] Definition Foldable__Digit_foldMap
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> Digit a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, One a => f a
      | f, Two a b => GHC.Base.mappend (f a) (f b)
      | f, Three a b c => GHC.Base.mappend (GHC.Base.mappend (f a) (f b)) (f c)
      | f, Four a b c d =>
          GHC.Base.mappend (GHC.Base.mappend (GHC.Base.mappend (f a) (f b)) (f c)) (f d)
      end.

#[local] Definition Foldable__Digit_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Digit m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Digit_foldMap GHC.Base.id.

#[local] Definition Foldable__Digit_foldr
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> Digit a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Digit_foldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__Digit_foldl'
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> Digit a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__Digit_foldr (fun arg_0__ arg_1__ =>
                                 match arg_0__, arg_1__ with
                                 | x, k => (fun '(z) => GHC.Prim.seq z (k (f z x)))
                                 end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__Digit_foldMap'
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> Digit a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Digit_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Digit_foldl
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> Digit a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Digit_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                 GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__Digit_foldr'
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> Digit a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__Digit_foldl (fun arg_0__ arg_1__ =>
                                 match arg_0__, arg_1__ with
                                 | k, x => (fun '(z) => GHC.Prim.seq z (k (f x z)))
                                 end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__Digit_length
   : forall {a : Type}, Digit a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__Digit_foldl' (fun arg_0__ arg_1__ =>
                              match arg_0__, arg_1__ with
                              | c, _ => c GHC.Num.+ #1
                              end) #0.

#[local] Definition Foldable__Digit_null : forall {a : Type}, Digit a -> bool :=
  fun {a : Type} => Foldable__Digit_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__Digit_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, Digit a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getProduct
                                   (Foldable__Digit_foldMap' Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__Digit_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, Digit a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getSum
                                   (Foldable__Digit_foldMap' Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__Digit_toList
   : forall {a : Type}, Digit a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Digit_foldr c n t)).

#[global]
Program Instance Foldable__Digit : Data.Foldable.Foldable Digit :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Foldable__Digit_fold ;
           Data.Foldable.foldMap__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Digit_foldMap ;
           Data.Foldable.foldMap'__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Digit_foldMap' ;
           Data.Foldable.foldl__ := fun (b : Type) (a : Type) => Foldable__Digit_foldl ;
           Data.Foldable.foldl'__ := fun (b : Type) (a : Type) => Foldable__Digit_foldl' ;
           Data.Foldable.foldr__ := fun (a : Type) (b : Type) => Foldable__Digit_foldr ;
           Data.Foldable.foldr'__ := fun (a : Type) (b : Type) => Foldable__Digit_foldr' ;
           Data.Foldable.length__ := fun (a : Type) => Foldable__Digit_length ;
           Data.Foldable.null__ := fun (a : Type) => Foldable__Digit_null ;
           Data.Foldable.product__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__Digit_product ;
           Data.Foldable.sum__ := fun (a : Type) `(GHC.Num.Num a) => Foldable__Digit_sum ;
           Data.Foldable.toList__ := fun (a : Type) => Foldable__Digit_toList |}.

#[local] Definition Foldable__Node_foldMap {inst_v : Type}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Node inst_v a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Node2 _ a b => GHC.Base.mappend (f a) (f b)
      | f, Node3 _ a b c => GHC.Base.mappend (GHC.Base.mappend (f a) (f b)) (f c)
      end.

#[local] Definition Foldable__Node_fold {inst_v : Type}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Node inst_v m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Node_foldMap GHC.Base.id.

#[local] Definition Foldable__Node_foldr {inst_v : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Node inst_v a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Node_foldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__Node_foldl' {inst_v : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Node inst_v a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__Node_foldr (fun arg_0__ arg_1__ =>
                                match arg_0__, arg_1__ with
                                | x, k => (fun '(z) => GHC.Prim.seq z (k (f z x)))
                                end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__Node_foldMap' {inst_v : Type}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Node inst_v a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Node_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Node_foldl {inst_v : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Node inst_v a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Node_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                               (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__Node_foldr' {inst_v : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Node inst_v a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__Node_foldl (fun arg_0__ arg_1__ =>
                                match arg_0__, arg_1__ with
                                | k, x => (fun '(z) => GHC.Prim.seq z (k (f x z)))
                                end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__Node_length {inst_v : Type}
   : forall {a : Type}, Node inst_v a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__Node_foldl' (fun arg_0__ arg_1__ =>
                             match arg_0__, arg_1__ with
                             | c, _ => c GHC.Num.+ #1
                             end) #0.

#[local] Definition Foldable__Node_null {inst_v : Type}
   : forall {a : Type}, Node inst_v a -> bool :=
  fun {a : Type} => Foldable__Node_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__Node_product {inst_v : Type}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Node inst_v a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getProduct
                                   (Foldable__Node_foldMap' Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__Node_sum {inst_v : Type}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Node inst_v a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getSum
                                   (Foldable__Node_foldMap' Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__Node_toList {inst_v : Type}
   : forall {a : Type}, Node inst_v a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Node_foldr c n t)).

#[global]
Program Instance Foldable__Node {v : Type} : Data.Foldable.Foldable (Node v) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Foldable__Node_fold ;
           Data.Foldable.foldMap__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Node_foldMap ;
           Data.Foldable.foldMap'__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Node_foldMap' ;
           Data.Foldable.foldl__ := fun (b : Type) (a : Type) => Foldable__Node_foldl ;
           Data.Foldable.foldl'__ := fun (b : Type) (a : Type) => Foldable__Node_foldl' ;
           Data.Foldable.foldr__ := fun (a : Type) (b : Type) => Foldable__Node_foldr ;
           Data.Foldable.foldr'__ := fun (a : Type) (b : Type) => Foldable__Node_foldr' ;
           Data.Foldable.length__ := fun (a : Type) => Foldable__Node_length ;
           Data.Foldable.null__ := fun (a : Type) => Foldable__Node_null ;
           Data.Foldable.product__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__Node_product ;
           Data.Foldable.sum__ := fun (a : Type) `(GHC.Num.Num a) => Foldable__Node_sum ;
           Data.Foldable.toList__ := fun (a : Type) => Foldable__Node_toList |}.

#[local] Definition Foldable__FingerTree_foldMap
   : forall {inst_v : Type} {m : Type} {a : Type} `{GHC.Base.Monoid m},
     (a -> m) -> FingerTree inst_v a -> m :=
  fix Foldable__FingerTree_foldMap {inst_v m a : Type} `{GHC.Base.Monoid m}
                                   (arg_0__ : a -> m) (arg_1__ : FingerTree inst_v a) : m
    := match arg_0__, arg_1__ with
       | _, Empty => GHC.Base.mempty
       | f, Single x => f x
       | f, Deep _ pr m sf =>
           GHC.Base.mappend (GHC.Base.mappend (Data.Foldable.foldMap f pr)
                                              (Foldable__FingerTree_foldMap (Data.Foldable.foldMap f) m))
                            (Data.Foldable.foldMap f sf)
       end.

#[local] Definition Foldable__FingerTree_fold {inst_v : Type}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, FingerTree inst_v m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__FingerTree_foldMap GHC.Base.id.

#[local] Definition Foldable__FingerTree_foldr {inst_v : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> FingerTree inst_v a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__FingerTree_foldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__FingerTree_foldl' {inst_v : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> FingerTree inst_v a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__FingerTree_foldr (fun arg_0__ arg_1__ =>
                                      match arg_0__, arg_1__ with
                                      | x, k => (fun '(z) => GHC.Prim.seq z (k (f z x)))
                                      end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__FingerTree_foldMap' {inst_v : Type}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> FingerTree inst_v a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__FingerTree_foldl' (fun acc a => acc GHC.Base.<<>> f a)
      GHC.Base.mempty.

#[local] Definition Foldable__FingerTree_foldl {inst_v : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> FingerTree inst_v a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__FingerTree_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                     (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                      GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__FingerTree_foldr' {inst_v : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> FingerTree inst_v a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__FingerTree_foldl (fun arg_0__ arg_1__ =>
                                      match arg_0__, arg_1__ with
                                      | k, x => (fun '(z) => GHC.Prim.seq z (k (f x z)))
                                      end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__FingerTree_length {inst_v : Type}
   : forall {a : Type}, FingerTree inst_v a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__FingerTree_foldl' (fun arg_0__ arg_1__ =>
                                   match arg_0__, arg_1__ with
                                   | c, _ => c GHC.Num.+ #1
                                   end) #0.

#[local] Definition Foldable__FingerTree_null {inst_v : Type}
   : forall {a : Type}, FingerTree inst_v a -> bool :=
  fun {a : Type} =>
    fun arg_0__ => match arg_0__ with | Empty => true | _ => false end.

#[local] Definition Foldable__FingerTree_product {inst_v : Type}
   : forall {a : Type}, forall `{GHC.Num.Num a}, FingerTree inst_v a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getProduct
                                   (Foldable__FingerTree_foldMap' Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__FingerTree_sum {inst_v : Type}
   : forall {a : Type}, forall `{GHC.Num.Num a}, FingerTree inst_v a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getSum
                                   (Foldable__FingerTree_foldMap' Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__FingerTree_toList {inst_v : Type}
   : forall {a : Type}, FingerTree inst_v a -> list a :=
  fun {a : Type} =>
    fun t =>
      GHC.Base.build' (fun _ => (fun c n => Foldable__FingerTree_foldr c n t)).

#[global]
Program Instance Foldable__FingerTree {v : Type}
   : Data.Foldable.Foldable (FingerTree v) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Foldable__FingerTree_fold ;
           Data.Foldable.foldMap__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__FingerTree_foldMap ;
           Data.Foldable.foldMap'__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__FingerTree_foldMap' ;
           Data.Foldable.foldl__ := fun (b : Type) (a : Type) =>
             Foldable__FingerTree_foldl ;
           Data.Foldable.foldl'__ := fun (b : Type) (a : Type) =>
             Foldable__FingerTree_foldl' ;
           Data.Foldable.foldr__ := fun (a : Type) (b : Type) =>
             Foldable__FingerTree_foldr ;
           Data.Foldable.foldr'__ := fun (a : Type) (b : Type) =>
             Foldable__FingerTree_foldr' ;
           Data.Foldable.length__ := fun (a : Type) => Foldable__FingerTree_length ;
           Data.Foldable.null__ := fun (a : Type) => Foldable__FingerTree_null ;
           Data.Foldable.product__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__FingerTree_product ;
           Data.Foldable.sum__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__FingerTree_sum ;
           Data.Foldable.toList__ := fun (a : Type) => Foldable__FingerTree_toList |}.

#[local] Definition Eq___FingerTree_op_zeze__ {inst_a : Type} {inst_v : Type}
  `{(GHC.Base.Eq_ inst_a)}
   : FingerTree inst_v inst_a -> FingerTree inst_v inst_a -> bool :=
  fun xs ys => Data.Foldable.toList xs GHC.Base.== Data.Foldable.toList ys.

#[local] Definition Eq___FingerTree_op_zsze__ {inst_a : Type} {inst_v : Type}
  `{(GHC.Base.Eq_ inst_a)}
   : FingerTree inst_v inst_a -> FingerTree inst_v inst_a -> bool :=
  fun x y => negb (Eq___FingerTree_op_zeze__ x y).

#[global]
Program Instance Eq___FingerTree {a : Type} {v : Type} `{(GHC.Base.Eq_ a)}
   : GHC.Base.Eq_ (FingerTree v a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___FingerTree_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___FingerTree_op_zsze__ |}.

#[local] Definition Eq___SearchResult_op_zeze__ {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Eq_ inst_a}
   : SearchResult inst_v inst_a -> SearchResult inst_v inst_a -> bool :=
  fun a b =>
    let 'num_7__ := (let 'lop_azh__ := (match a with
                                          | Position _ _ _ => 0%Z
                                          | OnLeft => 1%Z
                                          | OnRight => 2%Z
                                          | Nowhere => 3%Z
                                          end) in
                       let 'lop_bzh__ := (match b with
                                            | Position _ _ _ => 0%Z
                                            | OnLeft => 1%Z
                                            | OnRight => 2%Z
                                            | Nowhere => 3%Z
                                            end) in
                       if Stdlib.ZArith.BinInt.Z.eqb lop_azh__ lop_bzh__
                       then #0 : GHC.Num.Int
                       else #1 : GHC.Num.Int) in
    if num_7__ GHC.Base.== #1 : bool then false else
    match a with
    | Position a1 a2 a3 =>
        match b with
        | Position b1 b2 b3 =>
            (andb ((a1 GHC.Base.== b1)) (andb ((a2 GHC.Base.== b2)) ((a3 GHC.Base.== b3))))
        | _ => GHC.Err.patternFailure
        end
    | _ => true
    end.

#[local] Definition Eq___SearchResult_op_zsze__ {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Eq_ inst_a}
   : SearchResult inst_v inst_a -> SearchResult inst_v inst_a -> bool :=
  fun x y => negb (Eq___SearchResult_op_zeze__ x y).

#[global]
Program Instance Eq___SearchResult {v : Type} {a : Type} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (SearchResult v a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___SearchResult_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___SearchResult_op_zsze__ |}.

#[local] Definition Ord__FingerTree_compare {inst_a : Type} {inst_v : Type}
  `{(GHC.Base.Ord inst_a)}
   : FingerTree inst_v inst_a -> FingerTree inst_v inst_a -> comparison :=
  fun xs ys =>
    GHC.Base.compare (Data.Foldable.toList xs) (Data.Foldable.toList ys).

#[local] Definition Ord__FingerTree_op_zlze__ {inst_a : Type} {inst_v : Type}
  `{(GHC.Base.Ord inst_a)}
   : FingerTree inst_v inst_a -> FingerTree inst_v inst_a -> bool :=
  fun x y => Ord__FingerTree_compare x y GHC.Base./= Gt.

#[local] Definition Ord__FingerTree_max {inst_a : Type} {inst_v : Type}
  `{(GHC.Base.Ord inst_a)}
   : FingerTree inst_v inst_a ->
     FingerTree inst_v inst_a -> FingerTree inst_v inst_a :=
  fun x y => if Ord__FingerTree_op_zlze__ x y : bool then y else x.

#[local] Definition Ord__FingerTree_min {inst_a : Type} {inst_v : Type}
  `{(GHC.Base.Ord inst_a)}
   : FingerTree inst_v inst_a ->
     FingerTree inst_v inst_a -> FingerTree inst_v inst_a :=
  fun x y => if Ord__FingerTree_op_zlze__ x y : bool then x else y.

#[local] Definition Ord__FingerTree_op_zg__ {inst_a : Type} {inst_v : Type}
  `{(GHC.Base.Ord inst_a)}
   : FingerTree inst_v inst_a -> FingerTree inst_v inst_a -> bool :=
  fun x y => Ord__FingerTree_compare x y GHC.Base.== Gt.

#[local] Definition Ord__FingerTree_op_zgze__ {inst_a : Type} {inst_v : Type}
  `{(GHC.Base.Ord inst_a)}
   : FingerTree inst_v inst_a -> FingerTree inst_v inst_a -> bool :=
  fun x y => Ord__FingerTree_compare x y GHC.Base./= Lt.

#[local] Definition Ord__FingerTree_op_zl__ {inst_a : Type} {inst_v : Type}
  `{(GHC.Base.Ord inst_a)}
   : FingerTree inst_v inst_a -> FingerTree inst_v inst_a -> bool :=
  fun x y => Ord__FingerTree_compare x y GHC.Base.== Lt.

#[global]
Program Instance Ord__FingerTree {a : Type} {v : Type} `{(GHC.Base.Ord a)}
   : GHC.Base.Ord (FingerTree v a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__FingerTree_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__FingerTree_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__FingerTree_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__FingerTree_op_zgze__ ;
           GHC.Base.compare__ := Ord__FingerTree_compare ;
           GHC.Base.max__ := Ord__FingerTree_max ;
           GHC.Base.min__ := Ord__FingerTree_min |}.

#[local] Definition Ord__SearchResult_compare {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a}
   : SearchResult inst_v inst_a -> SearchResult inst_v inst_a -> comparison :=
  fun a b =>
    match a with
    | Position a1 a2 a3 =>
        match b with
        | Position b1 b2 b3 =>
            match (GHC.Base.compare a1 b1) with
            | Lt => Lt
            | Eq =>
                match (GHC.Base.compare a2 b2) with
                | Lt => Lt
                | Eq => (GHC.Base.compare a3 b3)
                | Gt => Gt
                end
            | Gt => Gt
            end
        | _ => Lt
        end
    | _ =>
        let 'lop_azh__ := (match a with
                             | Position _ _ _ => 0%Z
                             | OnLeft => 1%Z
                             | OnRight => 2%Z
                             | Nowhere => 3%Z
                             end) in
        let 'lop_bzh__ := (match b with
                             | Position _ _ _ => 0%Z
                             | OnLeft => 1%Z
                             | OnRight => 2%Z
                             | Nowhere => 3%Z
                             end) in
        if ((Stdlib.ZArith.BinInt.Z.ltb lop_azh__ lop_bzh__) : bool) : bool
        then Lt
        else if ((Stdlib.ZArith.BinInt.Z.eqb lop_azh__ lop_bzh__) : bool) : bool
             then Eq
             else Gt
    end.

#[local] Definition Ord__SearchResult_op_zl__ {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a}
   : SearchResult inst_v inst_a -> SearchResult inst_v inst_a -> bool :=
  fun x y => Ord__SearchResult_compare x y GHC.Base.== Lt.

#[local] Definition Ord__SearchResult_op_zlze__ {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a}
   : SearchResult inst_v inst_a -> SearchResult inst_v inst_a -> bool :=
  fun x y => Ord__SearchResult_compare x y GHC.Base./= Gt.

#[local] Definition Ord__SearchResult_op_zg__ {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a}
   : SearchResult inst_v inst_a -> SearchResult inst_v inst_a -> bool :=
  fun x y => Ord__SearchResult_compare x y GHC.Base.== Gt.

#[local] Definition Ord__SearchResult_op_zgze__ {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a}
   : SearchResult inst_v inst_a -> SearchResult inst_v inst_a -> bool :=
  fun x y => Ord__SearchResult_compare x y GHC.Base./= Lt.

#[local] Definition Ord__SearchResult_max {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a}
   : SearchResult inst_v inst_a ->
     SearchResult inst_v inst_a -> SearchResult inst_v inst_a :=
  fun x y => if Ord__SearchResult_op_zlze__ x y : bool then y else x.

#[local] Definition Ord__SearchResult_min {inst_v : Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a}
   : SearchResult inst_v inst_a ->
     SearchResult inst_v inst_a -> SearchResult inst_v inst_a :=
  fun x y => if Ord__SearchResult_op_zlze__ x y : bool then x else y.

#[global]
Program Instance Ord__SearchResult {v : Type} {a : Type} `{GHC.Base.Ord a}
   : GHC.Base.Ord (SearchResult v a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__SearchResult_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__SearchResult_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__SearchResult_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__SearchResult_op_zgze__ ;
           GHC.Base.compare__ := Ord__SearchResult_compare ;
           GHC.Base.max__ := Ord__SearchResult_max ;
           GHC.Base.min__ := Ord__SearchResult_min |}.

#[local] Definition Eq___ViewR_op_zeze__ {inst_s : Type -> Type} {inst_a : Type}
  `{GHC.Base.Eq_ inst_a} `{GHC.Base.Eq_ (inst_s inst_a)}
   : ViewR inst_s inst_a -> ViewR inst_s inst_a -> bool :=
  fun a b =>
    let 'num_7__ := (let 'lop_azh__ := (match a with
                                          | EmptyR => 0%Z
                                          | op_ZCzg__ _ _ => 1%Z
                                          end) in
                       let 'lop_bzh__ := (match b with
                                            | EmptyR => 0%Z
                                            | op_ZCzg__ _ _ => 1%Z
                                            end) in
                       if Stdlib.ZArith.BinInt.Z.eqb lop_azh__ lop_bzh__
                       then #0 : GHC.Num.Int
                       else #1 : GHC.Num.Int) in
    if num_7__ GHC.Base.== #1 : bool then false else
    match a with
    | op_ZCzg__ a1 a2 =>
        match b with
        | op_ZCzg__ b1 b2 => (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
        | _ => GHC.Err.patternFailure
        end
    | _ => true
    end.

#[local] Definition Eq___ViewR_op_zsze__ {inst_s : Type -> Type} {inst_a : Type}
  `{GHC.Base.Eq_ inst_a} `{GHC.Base.Eq_ (inst_s inst_a)}
   : ViewR inst_s inst_a -> ViewR inst_s inst_a -> bool :=
  fun x y => negb (Eq___ViewR_op_zeze__ x y).

#[global]
Program Instance Eq___ViewR {s : Type -> Type} {a : Type} `{GHC.Base.Eq_ a}
  `{GHC.Base.Eq_ (s a)}
   : GHC.Base.Eq_ (ViewR s a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___ViewR_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___ViewR_op_zsze__ |}.

#[local] Definition Ord__ViewR_op_zl__ {inst_s : Type -> Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord (inst_s inst_a)}
   : ViewR inst_s inst_a -> ViewR inst_s inst_a -> bool :=
  fun a b =>
    match a with
    | EmptyR => match b with | EmptyR => false | _ => true end
    | op_ZCzg__ a1 a2 =>
        match b with
        | op_ZCzg__ b1 b2 =>
            match (GHC.Base.compare a1 b1) with
            | Lt => true
            | Eq => (a2 GHC.Base.< b2)
            | Gt => false
            end
        | _ => false
        end
    end.

#[local] Definition Ord__ViewR_op_zlze__ {inst_s : Type -> Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord (inst_s inst_a)}
   : ViewR inst_s inst_a -> ViewR inst_s inst_a -> bool :=
  fun a b => negb (Ord__ViewR_op_zl__ b a).

#[local] Definition Ord__ViewR_op_zg__ {inst_s : Type -> Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord (inst_s inst_a)}
   : ViewR inst_s inst_a -> ViewR inst_s inst_a -> bool :=
  fun a b => Ord__ViewR_op_zl__ b a.

#[local] Definition Ord__ViewR_op_zgze__ {inst_s : Type -> Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord (inst_s inst_a)}
   : ViewR inst_s inst_a -> ViewR inst_s inst_a -> bool :=
  fun a b => negb (Ord__ViewR_op_zl__ a b).

#[local] Definition Ord__ViewR_compare {inst_s : Type -> Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord (inst_s inst_a)}
   : ViewR inst_s inst_a -> ViewR inst_s inst_a -> comparison :=
  fun a b =>
    match a with
    | EmptyR => match b with | EmptyR => Eq | _ => Lt end
    | op_ZCzg__ a1 a2 =>
        match b with
        | op_ZCzg__ b1 b2 =>
            match (GHC.Base.compare a1 b1) with
            | Lt => Lt
            | Eq => (GHC.Base.compare a2 b2)
            | Gt => Gt
            end
        | _ => Gt
        end
    end.

#[local] Definition Ord__ViewR_max {inst_s : Type -> Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord (inst_s inst_a)}
   : ViewR inst_s inst_a -> ViewR inst_s inst_a -> ViewR inst_s inst_a :=
  fun x y => if Ord__ViewR_op_zlze__ x y : bool then y else x.

#[local] Definition Ord__ViewR_min {inst_s : Type -> Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord (inst_s inst_a)}
   : ViewR inst_s inst_a -> ViewR inst_s inst_a -> ViewR inst_s inst_a :=
  fun x y => if Ord__ViewR_op_zlze__ x y : bool then x else y.

#[global]
Program Instance Ord__ViewR {s : Type -> Type} {a : Type} `{GHC.Base.Ord a}
  `{GHC.Base.Ord (s a)}
   : GHC.Base.Ord (ViewR s a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__ViewR_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__ViewR_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__ViewR_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__ViewR_op_zgze__ ;
           GHC.Base.compare__ := Ord__ViewR_compare ;
           GHC.Base.max__ := Ord__ViewR_max ;
           GHC.Base.min__ := Ord__ViewR_min |}.

#[local] Definition Eq___ViewL_op_zeze__ {inst_s : Type -> Type} {inst_a : Type}
  `{GHC.Base.Eq_ inst_a} `{GHC.Base.Eq_ (inst_s inst_a)}
   : ViewL inst_s inst_a -> ViewL inst_s inst_a -> bool :=
  fun a b =>
    let 'num_7__ := (let 'lop_azh__ := (match a with
                                          | EmptyL => 0%Z
                                          | op_ZCzl__ _ _ => 1%Z
                                          end) in
                       let 'lop_bzh__ := (match b with
                                            | EmptyL => 0%Z
                                            | op_ZCzl__ _ _ => 1%Z
                                            end) in
                       if Stdlib.ZArith.BinInt.Z.eqb lop_azh__ lop_bzh__
                       then #0 : GHC.Num.Int
                       else #1 : GHC.Num.Int) in
    if num_7__ GHC.Base.== #1 : bool then false else
    match a with
    | op_ZCzl__ a1 a2 =>
        match b with
        | op_ZCzl__ b1 b2 => (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
        | _ => GHC.Err.patternFailure
        end
    | _ => true
    end.

#[local] Definition Eq___ViewL_op_zsze__ {inst_s : Type -> Type} {inst_a : Type}
  `{GHC.Base.Eq_ inst_a} `{GHC.Base.Eq_ (inst_s inst_a)}
   : ViewL inst_s inst_a -> ViewL inst_s inst_a -> bool :=
  fun x y => negb (Eq___ViewL_op_zeze__ x y).

#[global]
Program Instance Eq___ViewL {s : Type -> Type} {a : Type} `{GHC.Base.Eq_ a}
  `{GHC.Base.Eq_ (s a)}
   : GHC.Base.Eq_ (ViewL s a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___ViewL_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___ViewL_op_zsze__ |}.

#[local] Definition Ord__ViewL_op_zl__ {inst_s : Type -> Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord (inst_s inst_a)}
   : ViewL inst_s inst_a -> ViewL inst_s inst_a -> bool :=
  fun a b =>
    match a with
    | EmptyL => match b with | EmptyL => false | _ => true end
    | op_ZCzl__ a1 a2 =>
        match b with
        | op_ZCzl__ b1 b2 =>
            match (GHC.Base.compare a1 b1) with
            | Lt => true
            | Eq => (a2 GHC.Base.< b2)
            | Gt => false
            end
        | _ => false
        end
    end.

#[local] Definition Ord__ViewL_op_zlze__ {inst_s : Type -> Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord (inst_s inst_a)}
   : ViewL inst_s inst_a -> ViewL inst_s inst_a -> bool :=
  fun a b => negb (Ord__ViewL_op_zl__ b a).

#[local] Definition Ord__ViewL_op_zg__ {inst_s : Type -> Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord (inst_s inst_a)}
   : ViewL inst_s inst_a -> ViewL inst_s inst_a -> bool :=
  fun a b => Ord__ViewL_op_zl__ b a.

#[local] Definition Ord__ViewL_op_zgze__ {inst_s : Type -> Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord (inst_s inst_a)}
   : ViewL inst_s inst_a -> ViewL inst_s inst_a -> bool :=
  fun a b => negb (Ord__ViewL_op_zl__ a b).

#[local] Definition Ord__ViewL_compare {inst_s : Type -> Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord (inst_s inst_a)}
   : ViewL inst_s inst_a -> ViewL inst_s inst_a -> comparison :=
  fun a b =>
    match a with
    | EmptyL => match b with | EmptyL => Eq | _ => Lt end
    | op_ZCzl__ a1 a2 =>
        match b with
        | op_ZCzl__ b1 b2 =>
            match (GHC.Base.compare a1 b1) with
            | Lt => Lt
            | Eq => (GHC.Base.compare a2 b2)
            | Gt => Gt
            end
        | _ => Gt
        end
    end.

#[local] Definition Ord__ViewL_max {inst_s : Type -> Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord (inst_s inst_a)}
   : ViewL inst_s inst_a -> ViewL inst_s inst_a -> ViewL inst_s inst_a :=
  fun x y => if Ord__ViewL_op_zlze__ x y : bool then y else x.

#[local] Definition Ord__ViewL_min {inst_s : Type -> Type} {inst_a : Type}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord (inst_s inst_a)}
   : ViewL inst_s inst_a -> ViewL inst_s inst_a -> ViewL inst_s inst_a :=
  fun x y => if Ord__ViewL_op_zlze__ x y : bool then x else y.

#[global]
Program Instance Ord__ViewL {s : Type -> Type} {a : Type} `{GHC.Base.Ord a}
  `{GHC.Base.Ord (s a)}
   : GHC.Base.Ord (ViewL s a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__ViewL_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__ViewL_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__ViewL_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__ViewL_op_zgze__ ;
           GHC.Base.compare__ := Ord__ViewL_compare ;
           GHC.Base.max__ := Ord__ViewL_max ;
           GHC.Base.min__ := Ord__ViewL_min |}.

#[local] Definition Functor__ViewL_fmap {inst_s : Type -> Type}
  `{(GHC.Base.Functor inst_s)}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> ViewL inst_s a -> ViewL inst_s b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, EmptyL => EmptyL
      | f, op_ZCzl__ x xs => f x :< GHC.Base.fmap f xs
      end.

#[local] Definition Functor__ViewL_op_zlzd__ {inst_s : Type -> Type}
  `{(GHC.Base.Functor inst_s)}
   : forall {a : Type},
     forall {b : Type}, a -> ViewL inst_s b -> ViewL inst_s a :=
  fun {a : Type} {b : Type} => Functor__ViewL_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__ViewL {s : Type -> Type} `{(GHC.Base.Functor s)}
   : GHC.Base.Functor (ViewL s) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__ViewL_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__ViewL_op_zlzd__ |}.

#[local] Definition Functor__ViewR_fmap {inst_s : Type -> Type}
  `{(GHC.Base.Functor inst_s)}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> ViewR inst_s a -> ViewR inst_s b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, EmptyR => EmptyR
      | f, op_ZCzg__ xs x => GHC.Base.fmap f xs :> f x
      end.

#[local] Definition Functor__ViewR_op_zlzd__ {inst_s : Type -> Type}
  `{(GHC.Base.Functor inst_s)}
   : forall {a : Type},
     forall {b : Type}, a -> ViewR inst_s b -> ViewR inst_s a :=
  fun {a : Type} {b : Type} => Functor__ViewR_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__ViewR {s : Type -> Type} `{(GHC.Base.Functor s)}
   : GHC.Base.Functor (ViewR s) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__ViewR_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__ViewR_op_zlzd__ |}.

#[global] Definition illegal_argument {a} `{HsToRocq.Err.Default a}
   : GHC.Base.String -> a :=
  fun name =>
    GHC.Err.error (Corelib.Init.Datatypes.app (GHC.Base.hs_string__ "Logic error: ")
                                              (Corelib.Init.Datatypes.app name (GHC.Base.hs_string__
                                                                           " called with illegal argument"))).

#[global] Definition consDigit {a} : a -> Digit a -> Digit a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | a, One b => Two a b
    | a, Two b c => Three a b c
    | a, Three b c d => Four a b c d
    | _, Four _ _ _ _ =>
        (@illegal_argument _ (HsToRocq.Err.Build_Default _ arg_1__))
        (GHC.Base.hs_string__ "consDigit")
    end.

#[local] Definition Measured__Digit__5_measure {inst_v : Type} {inst_a : Type}
  `{(Measured inst_v inst_a)}
   : Digit inst_a -> inst_v :=
  Data.Foldable.foldMap measure.

#[global]
Program Instance Measured__Digit__5 {v : Type} {a : Type} `{(Measured v a)}
   : Measured v (Digit a) :=
  fun _ k__ => k__ {| measure__ := Measured__Digit__5_measure |}.

#[local] Definition Measured__FingerTree__5_measure {inst_v : Type} {inst_a
   : Type} `{(Measured inst_v inst_a)}
   : FingerTree inst_v inst_a -> inst_v :=
  fun arg_0__ =>
    match arg_0__ with
    | Empty => GHC.Base.mempty
    | Single x => measure x
    | Deep v _ _ _ => v
    end.

#[global]
Program Instance Measured__FingerTree__5 {v : Type} {a : Type} `{(Measured v a)}
   : Measured v (FingerTree v a) :=
  fun _ k__ => k__ {| measure__ := Measured__FingerTree__5_measure |}.

#[local] Definition Measured__Node__5_measure {inst_v : Type} {inst_a : Type}
  `{(GHC.Base.Monoid inst_v)}
   : Node inst_v inst_a -> inst_v :=
  fun arg_0__ => match arg_0__ with | Node2 v _ _ => v | Node3 v _ _ _ => v end.

#[global]
Program Instance Measured__Node__5 {v : Type} {a : Type} `{(GHC.Base.Monoid v)}
   : Measured v (Node v a) :=
  fun _ k__ => k__ {| measure__ := Measured__Node__5_measure |}.

#[global] Definition deep {v : Type} {a : Type} `{Measured v a}
   : Digit a -> FingerTree v (Node v a) -> Digit a -> FingerTree v a :=
  fun pr m sf =>
    Deep (GHC.Base.mappend (GHC.Base.mappend (measure pr) (measure m)) (measure sf))
    pr m sf.

#[global] Definition node3 {v : Type} {a : Type} `{Measured v a}
   : a -> a -> a -> Node v a :=
  fun a b c =>
    Node3 (GHC.Base.mappend (GHC.Base.mappend (measure a) (measure b)) (measure c))
    a b c.

Fixpoint consTree {v : Type} {a : Type} `{Measured v a} (arg_0__ : a) (arg_1__
                    : FingerTree v a) : FingerTree v a
  := match arg_0__, arg_1__ with
     | a, Empty => Single a
     | a, Single b => deep (One a) Empty (One b)
     | a, Deep v (Four b c d e) m sf =>
         GHC.Prim.seq m (Deep (GHC.Base.mappend (measure a) v) (Two a b) (consTree (node3
                                                                                    c d e) m) sf)
     | a, Deep v pr m sf =>
         Deep (GHC.Base.mappend (measure a) v) (consDigit a pr) m sf
     end.

#[global] Definition node2 {v : Type} {a : Type} `{Measured v a}
   : a -> a -> Node v a :=
  fun a b => Node2 (GHC.Base.mappend (measure a) (measure b)) a b.

#[global] Definition snocDigit {a} : Digit a -> a -> Digit a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | One a, b => Two a b
    | Two a b, c => Three a b c
    | Three a b c, d => Four a b c d
    | Four _ _ _ _, _ =>
        (@illegal_argument _ (HsToRocq.Err.Build_Default _ arg_0__))
        (GHC.Base.hs_string__ "snocDigit")
    end.

Fixpoint snocTree {v : Type} {a : Type} `{Measured v a} (arg_0__
                    : FingerTree v a) (arg_1__ : a) : FingerTree v a
  := match arg_0__, arg_1__ with
     | Empty, a => Single a
     | Single a, b => deep (One a) Empty (One b)
     | Deep v pr m (Four a b c d), e =>
         GHC.Prim.seq m (Deep (GHC.Base.mappend v (measure e)) pr (snocTree m (node3 a b
                                                                             c)) (Two d e))
     | Deep v pr m sf, x =>
         Deep (GHC.Base.mappend v (measure x)) pr m (snocDigit sf x)
     end.

#[global] Definition appendTree2
   : forall {v} {a} `{(Measured v a)},
     FingerTree v a -> a -> a -> FingerTree v a -> FingerTree v a :=
  fix appendTree2 {v} {a} `{(Measured v a)} (arg_0__ : FingerTree v a) (arg_1__
                   arg_2__
                    : a) (arg_3__ : FingerTree v a) : FingerTree v a
    := let addDigits2 {v}
       {a}
       `{(Measured v a)}
       (arg_0__ : FingerTree v (Node v a))
       (arg_1__ : Digit a)
       (arg_2__ arg_3__ : a)
       (arg_4__ : Digit a)
       (arg_5__ : FingerTree v (Node v a))
        : FingerTree v (Node v a) :=
         match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__ with
         | m1, One a, b, c, One d, m2 => appendTree2 m1 (node2 a b) (node2 c d) m2
         | m1, One a, b, c, Two d e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
         | m1, One a, b, c, Three d e f, m2 =>
             appendTree2 m1 (node3 a b c) (node3 d e f) m2
         | m1, One a, b, c, Four d e f g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Two a b, c, d, One e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
         | m1, Two a b, c, d, Two e f, m2 =>
             appendTree2 m1 (node3 a b c) (node3 d e f) m2
         | m1, Two a b, c, d, Three e f g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Two a b, c, d, Four e f g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Three a b c, d, e, One f, m2 =>
             appendTree2 m1 (node3 a b c) (node3 d e f) m2
         | m1, Three a b c, d, e, Two f g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Three a b c, d, e, Three f g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Three a b c, d, e, Four f g h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Four a b c d, e, f, One g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Four a b c d, e, f, Two g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Four a b c d, e, f, Three g h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Four a b c d, e, f, Four g h i j, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
         end in
       match arg_0__, arg_1__, arg_2__, arg_3__ with
       | Empty, a, b, xs => consTree a (consTree b xs)
       | xs, a, b, Empty => snocTree (snocTree xs a) b
       | Single x, a, b, xs => consTree x (consTree a (consTree b xs))
       | xs, a, b, Single x => snocTree (snocTree (snocTree xs a) b) x
       | Deep _ pr1 m1 sf1, a, b, Deep _ pr2 m2 sf2 =>
           deep pr1 (addDigits2 m1 sf1 a b pr2 m2) sf2
       end
  with appendTree3 {v} {a} `{(Measured v a)} (arg_0__ : FingerTree v a) (arg_1__
                    arg_2__ arg_3__
                     : a) (arg_4__ : FingerTree v a) : FingerTree v a
    := let addDigits3 {v}
       {a}
       `{(Measured v a)}
       (arg_0__ : FingerTree v (Node v a))
       (arg_1__ : Digit a)
       (arg_2__ arg_3__ arg_4__ : a)
       (arg_5__ : Digit a)
       (arg_6__ : FingerTree v (Node v a))
        : FingerTree v (Node v a) :=
         match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__, arg_6__ with
         | m1, One a, b, c, d, One e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
         | m1, One a, b, c, d, Two e f, m2 =>
             appendTree2 m1 (node3 a b c) (node3 d e f) m2
         | m1, One a, b, c, d, Three e f g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, One a, b, c, d, Four e f g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Two a b, c, d, e, One f, m2 =>
             appendTree2 m1 (node3 a b c) (node3 d e f) m2
         | m1, Two a b, c, d, e, Two f g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Two a b, c, d, e, Three f g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Two a b, c, d, e, Four f g h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Three a b c, d, e, f, One g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Three a b c, d, e, f, Two g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Three a b c, d, e, f, Three g h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Three a b c, d, e, f, Four g h i j, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
         | m1, Four a b c d, e, f, g, One h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Four a b c d, e, f, g, Two h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Four a b c d, e, f, g, Three h i j, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
         | m1, Four a b c d, e, f, g, Four h i j k, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
         end in
       match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
       | Empty, a, b, c, xs => consTree a (consTree b (consTree c xs))
       | xs, a, b, c, Empty => snocTree (snocTree (snocTree xs a) b) c
       | Single x, a, b, c, xs => consTree x (consTree a (consTree b (consTree c xs)))
       | xs, a, b, c, Single x => snocTree (snocTree (snocTree (snocTree xs a) b) c) x
       | Deep _ pr1 m1 sf1, a, b, c, Deep _ pr2 m2 sf2 =>
           deep pr1 (addDigits3 m1 sf1 a b c pr2 m2) sf2
       end
  with appendTree4 {v} {a} `{(Measured v a)} (arg_0__ : FingerTree v a) (arg_1__
                    arg_2__ arg_3__ arg_4__
                     : a) (arg_5__ : FingerTree v a) : FingerTree v a
    := let addDigits4 {v}
       {a}
       `{(Measured v a)}
       (arg_0__ : FingerTree v (Node v a))
       (arg_1__ : Digit a)
       (arg_2__ arg_3__ arg_4__ arg_5__ : a)
       (arg_6__ : Digit a)
       (arg_7__ : FingerTree v (Node v a))
        : FingerTree v (Node v a) :=
         match arg_0__
             , arg_1__
             , arg_2__
             , arg_3__
             , arg_4__
             , arg_5__
             , arg_6__
             , arg_7__ with
         | m1, One a, b, c, d, e, One f, m2 =>
             appendTree2 m1 (node3 a b c) (node3 d e f) m2
         | m1, One a, b, c, d, e, Two f g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, One a, b, c, d, e, Three f g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, One a, b, c, d, e, Four f g h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Two a b, c, d, e, f, One g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Two a b, c, d, e, f, Two g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Two a b, c, d, e, f, Three g h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Two a b, c, d, e, f, Four g h i j, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
         | m1, Three a b c, d, e, f, g, One h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Three a b c, d, e, f, g, Two h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Three a b c, d, e, f, g, Three h i j, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
         | m1, Three a b c, d, e, f, g, Four h i j k, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
         | m1, Four a b c d, e, f, g, h, One i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Four a b c d, e, f, g, h, Two i j, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
         | m1, Four a b c d, e, f, g, h, Three i j k, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
         | m1, Four a b c d, e, f, g, h, Four i j k l, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l) m2
         end in
       match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__ with
       | Empty, a, b, c, d, xs => consTree a (consTree b (consTree c (consTree d xs)))
       | xs, a, b, c, d, Empty => snocTree (snocTree (snocTree (snocTree xs a) b) c) d
       | Single x, a, b, c, d, xs =>
           consTree x (consTree a (consTree b (consTree c (consTree d xs))))
       | xs, a, b, c, d, Single x =>
           snocTree (snocTree (snocTree (snocTree (snocTree xs a) b) c) d) x
       | Deep _ pr1 m1 sf1, a, b, c, d, Deep _ pr2 m2 sf2 =>
           deep pr1 (addDigits4 m1 sf1 a b c d pr2 m2) sf2
       end for appendTree2.

#[global] Definition appendTree3
   : forall {v} {a} `{(Measured v a)},
     FingerTree v a -> a -> a -> a -> FingerTree v a -> FingerTree v a :=
  fix appendTree2 {v} {a} `{(Measured v a)} (arg_0__ : FingerTree v a) (arg_1__
                   arg_2__
                    : a) (arg_3__ : FingerTree v a) : FingerTree v a
    := let addDigits2 {v}
       {a}
       `{(Measured v a)}
       (arg_0__ : FingerTree v (Node v a))
       (arg_1__ : Digit a)
       (arg_2__ arg_3__ : a)
       (arg_4__ : Digit a)
       (arg_5__ : FingerTree v (Node v a))
        : FingerTree v (Node v a) :=
         match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__ with
         | m1, One a, b, c, One d, m2 => appendTree2 m1 (node2 a b) (node2 c d) m2
         | m1, One a, b, c, Two d e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
         | m1, One a, b, c, Three d e f, m2 =>
             appendTree2 m1 (node3 a b c) (node3 d e f) m2
         | m1, One a, b, c, Four d e f g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Two a b, c, d, One e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
         | m1, Two a b, c, d, Two e f, m2 =>
             appendTree2 m1 (node3 a b c) (node3 d e f) m2
         | m1, Two a b, c, d, Three e f g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Two a b, c, d, Four e f g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Three a b c, d, e, One f, m2 =>
             appendTree2 m1 (node3 a b c) (node3 d e f) m2
         | m1, Three a b c, d, e, Two f g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Three a b c, d, e, Three f g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Three a b c, d, e, Four f g h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Four a b c d, e, f, One g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Four a b c d, e, f, Two g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Four a b c d, e, f, Three g h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Four a b c d, e, f, Four g h i j, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
         end in
       match arg_0__, arg_1__, arg_2__, arg_3__ with
       | Empty, a, b, xs => consTree a (consTree b xs)
       | xs, a, b, Empty => snocTree (snocTree xs a) b
       | Single x, a, b, xs => consTree x (consTree a (consTree b xs))
       | xs, a, b, Single x => snocTree (snocTree (snocTree xs a) b) x
       | Deep _ pr1 m1 sf1, a, b, Deep _ pr2 m2 sf2 =>
           deep pr1 (addDigits2 m1 sf1 a b pr2 m2) sf2
       end
  with appendTree3 {v} {a} `{(Measured v a)} (arg_0__ : FingerTree v a) (arg_1__
                    arg_2__ arg_3__
                     : a) (arg_4__ : FingerTree v a) : FingerTree v a
    := let addDigits3 {v}
       {a}
       `{(Measured v a)}
       (arg_0__ : FingerTree v (Node v a))
       (arg_1__ : Digit a)
       (arg_2__ arg_3__ arg_4__ : a)
       (arg_5__ : Digit a)
       (arg_6__ : FingerTree v (Node v a))
        : FingerTree v (Node v a) :=
         match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__, arg_6__ with
         | m1, One a, b, c, d, One e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
         | m1, One a, b, c, d, Two e f, m2 =>
             appendTree2 m1 (node3 a b c) (node3 d e f) m2
         | m1, One a, b, c, d, Three e f g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, One a, b, c, d, Four e f g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Two a b, c, d, e, One f, m2 =>
             appendTree2 m1 (node3 a b c) (node3 d e f) m2
         | m1, Two a b, c, d, e, Two f g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Two a b, c, d, e, Three f g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Two a b, c, d, e, Four f g h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Three a b c, d, e, f, One g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Three a b c, d, e, f, Two g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Three a b c, d, e, f, Three g h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Three a b c, d, e, f, Four g h i j, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
         | m1, Four a b c d, e, f, g, One h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Four a b c d, e, f, g, Two h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Four a b c d, e, f, g, Three h i j, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
         | m1, Four a b c d, e, f, g, Four h i j k, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
         end in
       match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
       | Empty, a, b, c, xs => consTree a (consTree b (consTree c xs))
       | xs, a, b, c, Empty => snocTree (snocTree (snocTree xs a) b) c
       | Single x, a, b, c, xs => consTree x (consTree a (consTree b (consTree c xs)))
       | xs, a, b, c, Single x => snocTree (snocTree (snocTree (snocTree xs a) b) c) x
       | Deep _ pr1 m1 sf1, a, b, c, Deep _ pr2 m2 sf2 =>
           deep pr1 (addDigits3 m1 sf1 a b c pr2 m2) sf2
       end
  with appendTree4 {v} {a} `{(Measured v a)} (arg_0__ : FingerTree v a) (arg_1__
                    arg_2__ arg_3__ arg_4__
                     : a) (arg_5__ : FingerTree v a) : FingerTree v a
    := let addDigits4 {v}
       {a}
       `{(Measured v a)}
       (arg_0__ : FingerTree v (Node v a))
       (arg_1__ : Digit a)
       (arg_2__ arg_3__ arg_4__ arg_5__ : a)
       (arg_6__ : Digit a)
       (arg_7__ : FingerTree v (Node v a))
        : FingerTree v (Node v a) :=
         match arg_0__
             , arg_1__
             , arg_2__
             , arg_3__
             , arg_4__
             , arg_5__
             , arg_6__
             , arg_7__ with
         | m1, One a, b, c, d, e, One f, m2 =>
             appendTree2 m1 (node3 a b c) (node3 d e f) m2
         | m1, One a, b, c, d, e, Two f g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, One a, b, c, d, e, Three f g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, One a, b, c, d, e, Four f g h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Two a b, c, d, e, f, One g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Two a b, c, d, e, f, Two g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Two a b, c, d, e, f, Three g h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Two a b, c, d, e, f, Four g h i j, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
         | m1, Three a b c, d, e, f, g, One h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Three a b c, d, e, f, g, Two h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Three a b c, d, e, f, g, Three h i j, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
         | m1, Three a b c, d, e, f, g, Four h i j k, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
         | m1, Four a b c d, e, f, g, h, One i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Four a b c d, e, f, g, h, Two i j, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
         | m1, Four a b c d, e, f, g, h, Three i j k, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
         | m1, Four a b c d, e, f, g, h, Four i j k l, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l) m2
         end in
       match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__ with
       | Empty, a, b, c, d, xs => consTree a (consTree b (consTree c (consTree d xs)))
       | xs, a, b, c, d, Empty => snocTree (snocTree (snocTree (snocTree xs a) b) c) d
       | Single x, a, b, c, d, xs =>
           consTree x (consTree a (consTree b (consTree c (consTree d xs))))
       | xs, a, b, c, d, Single x =>
           snocTree (snocTree (snocTree (snocTree (snocTree xs a) b) c) d) x
       | Deep _ pr1 m1 sf1, a, b, c, d, Deep _ pr2 m2 sf2 =>
           deep pr1 (addDigits4 m1 sf1 a b c d pr2 m2) sf2
       end for appendTree3.

Fixpoint appendTree1 {v} {a} `{(Measured v a)} (arg_0__ : FingerTree v a)
                     (arg_1__ : a) (arg_2__ : FingerTree v a) : FingerTree v a
  := let addDigits1 (arg_0__ : FingerTree v (Node v a))
     (arg_1__ : Digit a)
     (arg_2__ : a)
     (arg_3__ : Digit a)
     (arg_4__ : FingerTree v (Node v a))
      : FingerTree v (Node v a) :=
       match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
       | m1, One a, b, One c, m2 => appendTree1 m1 (node3 a b c) m2
       | m1, One a, b, Two c d, m2 => appendTree2 m1 (node2 a b) (node2 c d) m2
       | m1, One a, b, Three c d e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
       | m1, One a, b, Four c d e f, m2 =>
           appendTree2 m1 (node3 a b c) (node3 d e f) m2
       | m1, Two a b, c, One d, m2 => appendTree2 m1 (node2 a b) (node2 c d) m2
       | m1, Two a b, c, Two d e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
       | m1, Two a b, c, Three d e f, m2 =>
           appendTree2 m1 (node3 a b c) (node3 d e f) m2
       | m1, Two a b, c, Four d e f g, m2 =>
           appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
       | m1, Three a b c, d, One e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
       | m1, Three a b c, d, Two e f, m2 =>
           appendTree2 m1 (node3 a b c) (node3 d e f) m2
       | m1, Three a b c, d, Three e f g, m2 =>
           appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
       | m1, Three a b c, d, Four e f g h, m2 =>
           appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
       | m1, Four a b c d, e, One f, m2 =>
           appendTree2 m1 (node3 a b c) (node3 d e f) m2
       | m1, Four a b c d, e, Two f g, m2 =>
           appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
       | m1, Four a b c d, e, Three f g h, m2 =>
           appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
       | m1, Four a b c d, e, Four f g h i, m2 =>
           appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
       end in
     match arg_0__, arg_1__, arg_2__ with
     | Empty, a, xs => consTree a xs
     | xs, a, Empty => snocTree xs a
     | Single x, a, xs => consTree x (consTree a xs)
     | xs, a, Single x => snocTree (snocTree xs a) x
     | Deep _ pr1 m1 sf1, a, Deep _ pr2 m2 sf2 =>
         deep pr1 (addDigits1 m1 sf1 a pr2 m2) sf2
     end.

#[global] Definition addDigits0 {v} {a} `{(Measured v a)}
   : FingerTree v (Node v a) ->
     Digit a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a) :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | m1, One a, One b, m2 => appendTree1 m1 (node2 a b) m2
    | m1, One a, Two b c, m2 => appendTree1 m1 (node3 a b c) m2
    | m1, One a, Three b c d, m2 => appendTree2 m1 (node2 a b) (node2 c d) m2
    | m1, One a, Four b c d e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
    | m1, Two a b, One c, m2 => appendTree1 m1 (node3 a b c) m2
    | m1, Two a b, Two c d, m2 => appendTree2 m1 (node2 a b) (node2 c d) m2
    | m1, Two a b, Three c d e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
    | m1, Two a b, Four c d e f, m2 => appendTree2 m1 (node3 a b c) (node3 d e f) m2
    | m1, Three a b c, One d, m2 => appendTree2 m1 (node2 a b) (node2 c d) m2
    | m1, Three a b c, Two d e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
    | m1, Three a b c, Three d e f, m2 =>
        appendTree2 m1 (node3 a b c) (node3 d e f) m2
    | m1, Three a b c, Four d e f g, m2 =>
        appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
    | m1, Four a b c d, One e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
    | m1, Four a b c d, Two e f, m2 => appendTree2 m1 (node3 a b c) (node3 d e f) m2
    | m1, Four a b c d, Three e f g, m2 =>
        appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
    | m1, Four a b c d, Four e f g h, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
    end.

#[global] Definition appendTree0 {v} {a} `{(Measured v a)}
   : FingerTree v a -> FingerTree v a -> FingerTree v a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Empty, xs => xs
    | xs, Empty => xs
    | Single x, xs => consTree x xs
    | xs, Single x => snocTree xs x
    | Deep _ pr1 m1 sf1, Deep _ pr2 m2 sf2 =>
        deep pr1 (addDigits0 m1 sf1 pr2 m2) sf2
    end.

#[global] Definition op_zgzl__ {v : Type} {a : Type} `{Measured v a}
   : FingerTree v a -> FingerTree v a -> FingerTree v a :=
  appendTree0.

Notation "'_><_'" := (op_zgzl__).

Infix "><" := (_><_) (at level 99).

#[local] Definition Semigroup__FingerTree_op_zlzlzgzg__ {inst_v : Type} {inst_a
   : Type} `{(Measured inst_v inst_a)}
   : FingerTree inst_v inst_a ->
     FingerTree inst_v inst_a -> FingerTree inst_v inst_a :=
  _><_.

#[global]
Program Instance Semigroup__FingerTree {v : Type} {a : Type} `{(Measured v a)}
   : GHC.Base.Semigroup (FingerTree v a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__FingerTree_op_zlzlzgzg__ |}.

#[local] Definition Monoid__FingerTree_mappend {inst_v : Type} {inst_a : Type}
  `{(Measured inst_v inst_a)}
   : FingerTree inst_v inst_a ->
     FingerTree inst_v inst_a -> FingerTree inst_v inst_a :=
  _GHC.Base.<<>>_.

#[global] Definition empty {v : Type} {a : Type} `{Measured v a}
   : FingerTree v a :=
  Empty.

#[local] Definition Monoid__FingerTree_mempty {inst_v : Type} {inst_a : Type}
  `{(Measured inst_v inst_a)}
   : FingerTree inst_v inst_a :=
  empty.

#[local] Definition Monoid__FingerTree_mconcat {inst_v : Type} {inst_a : Type}
  `{(Measured inst_v inst_a)}
   : list (FingerTree inst_v inst_a) -> FingerTree inst_v inst_a :=
  GHC.Base.foldr Monoid__FingerTree_mappend Monoid__FingerTree_mempty.

#[global]
Program Instance Monoid__FingerTree {v : Type} {a : Type} `{(Measured v a)}
   : GHC.Base.Monoid (FingerTree v a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__FingerTree_mappend ;
           GHC.Base.mconcat__ := Monoid__FingerTree_mconcat ;
           GHC.Base.mempty__ := Monoid__FingerTree_mempty |}.

#[global] Definition nodeToDigit {v} {a} : Node v a -> Digit a :=
  fun arg_0__ =>
    match arg_0__ with
    | Node2 _ a b => Two a b
    | Node3 _ a b c => Three a b c
    end.

#[global] Definition mapDigit {a} {b} : (a -> b) -> Digit a -> Digit b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, One a => One (f a)
    | f, Two a b => Two (f a) (f b)
    | f, Three a b c => Three (f a) (f b) (f c)
    | f, Four a b c d => Four (f a) (f b) (f c) (f d)
    end.

#[global] Definition mapNode {v2} {a2} {a1} {v1} `{(Measured v2 a2)}
   : (a1 -> a2) -> Node v1 a1 -> Node v2 a2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Node2 _ a b => node2 (f a) (f b)
    | f, Node3 _ a b c => node3 (f a) (f b) (f c)
    end.

Fixpoint mapTree {v2} {a2} {a1} {v1} `{(Measured v2 a2)} (arg_0__ : (a1 -> a2))
                 (arg_1__ : FingerTree v1 a1) : FingerTree v2 a2
  := match arg_0__, arg_1__ with
     | _, Empty => Empty
     | f, Single x => Single (f x)
     | f, Deep _ pr m sf =>
         deep (mapDigit f pr) (mapTree (mapNode f) m) (mapDigit f sf)
     end.

#[global] Definition fmap' {v1 : Type} {a1 : Type} {v2 : Type} {a2 : Type}
  `{Measured v1 a1} `{Measured v2 a2}
   : (a1 -> a2) -> FingerTree v1 a1 -> FingerTree v2 a2 :=
  mapTree.

#[global] Definition mapWPDigit {v} {a} {b} `{(Measured v a)}
   : (v -> a -> b) -> v -> Digit a -> Digit b :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, vl, One a => One (f vl a)
    | f, vl, Two a b =>
        let vla := GHC.Base.mappend vl (measure a) in Two (f vl a) (f vla b)
    | f, vl, Three a b c =>
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in
        Three (f vl a) (f vla b) (f vlab c)
    | f, vl, Four a b c d =>
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in
        let vlabc := GHC.Base.mappend vlab (measure c) in
        Four (f vl a) (f vla b) (f vlab c) (f vlabc d)
    end.

#[global] Definition mapWPNode {v1} {a1} {v2} {a2} `{Measured v1 a1} `{Measured
  v2 a2}
   : (v1 -> a1 -> a2) -> v1 -> Node v1 a1 -> Node v2 a2 :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, vl, Node2 _ a b =>
        let vla := GHC.Base.mappend vl (measure a) in node2 (f vl a) (f vla b)
    | f, vl, Node3 _ a b c =>
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in
        let va := GHC.Base.mappend vl (measure a) in node3 (f vl a) (f vla b) (f vlab c)
    end.

Fixpoint mapWPTree {v1} {a1} {v2} {a2} `{Measured v1 a1} `{Measured v2 a2}
                   (arg_0__ : (v1 -> a1 -> a2)) (arg_1__ : v1) (arg_2__ : FingerTree v1 a1)
  : FingerTree v2 a2
  := match arg_0__, arg_1__, arg_2__ with
     | _, _, Empty => Empty
     | f, vl, Single x => Single (f vl x)
     | f, vl, Deep _ pr m sf =>
         let vlp := GHC.Base.mappend vl (measure pr) in
         let vlpm := GHC.Base.mappend vlp (measure m) in
         deep (mapWPDigit f vl pr) (mapWPTree (mapWPNode f) vlp m) (mapWPDigit f vlpm sf)
     end.

#[global] Definition fmapWithPos {v1 : Type} {a1 : Type} {v2 : Type} {a2 : Type}
  `{Measured v1 a1} `{Measured v2 a2}
   : (v1 -> a1 -> a2) -> FingerTree v1 a1 -> FingerTree v2 a2 :=
  fun f => mapWPTree f GHC.Base.mempty.

#[global] Definition mapWCDigit {v} {a} {b} `{(Measured v a)}
   : (v -> a -> v -> b) -> v -> Digit a -> v -> Digit b :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | f, vl, One a, vr => One (f vl a vr)
    | f, vl, Two a b, vr =>
        let vbr := GHC.Base.mappend (measure b) vr in
        let vla := GHC.Base.mappend vl (measure a) in Two (f vl a vbr) (f vla b vr)
    | f, vl, Three a b c, vr =>
        let vcr := GHC.Base.mappend (measure c) vr in
        let vbcr := GHC.Base.mappend (measure b) vcr in
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in
        Three (f vl a vbcr) (f vla b vcr) (f vlab c vr)
    | f, vl, Four a b c d, vr =>
        let vdr := GHC.Base.mappend (measure d) vr in
        let vcdr := GHC.Base.mappend (measure c) vdr in
        let vbcdr := GHC.Base.mappend (measure b) vcdr in
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in
        let vlabc := GHC.Base.mappend vlab (measure c) in
        Four (f vl a vbcdr) (f vla b vcdr) (f vlab c vdr) (f vlabc d vr)
    end.

#[global] Definition mapWCNode {v1} {a1} {v2} {a2} `{Measured v1 a1} `{Measured
  v2 a2}
   : (v1 -> a1 -> v1 -> a2) -> v1 -> Node v1 a1 -> v1 -> Node v2 a2 :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | f, vl, Node2 _ a b, vr =>
        let vbr := GHC.Base.mappend (measure b) vr in
        let vla := GHC.Base.mappend vl (measure a) in node2 (f vl a vbr) (f vla b vr)
    | f, vl, Node3 _ a b c, vr =>
        let vcr := GHC.Base.mappend (measure c) vr in
        let vbcr := GHC.Base.mappend (measure b) vcr in
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in
        node3 (f vl a vbcr) (f vla b vcr) (f vlab c vr)
    end.

Fixpoint mapWCTree {v1} {a1} {v2} {a2} `{Measured v1 a1} `{Measured v2 a2}
                   (arg_0__ : (v1 -> a1 -> v1 -> a2)) (arg_1__ : v1) (arg_2__ : FingerTree v1 a1)
                   (arg_3__ : v1) : FingerTree v2 a2
  := match arg_0__, arg_1__, arg_2__, arg_3__ with
     | _, _, Empty, _ => Empty
     | f, vl, Single x, vr => Single (f vl x vr)
     | f, vl, Deep _ pr m sf, vr =>
         let vm := measure m in
         let vsr := GHC.Base.mappend (measure sf) vr in
         let vmsr := GHC.Base.mappend vm vsr in
         let vlp := GHC.Base.mappend vl (measure pr) in
         let vlpm := GHC.Base.mappend vlp vm in
         deep (mapWCDigit f vl pr vmsr) (mapWCTree (mapWCNode f) vlp m vsr) (mapWCDigit f
                                                                             vlpm sf vr)
     end.

#[global] Definition fmapWithContext {v1 : Type} {a1 : Type} {v2 : Type} {a2
   : Type} `{Measured v1 a1} `{Measured v2 a2}
   : (v1 -> a1 -> v1 -> a2) -> FingerTree v1 a1 -> FingerTree v2 a2 :=
  fun f t => mapWCTree f GHC.Base.mempty t GHC.Base.mempty.

#[global] Definition unsafeFmapNode {a} {b} {v}
   : (a -> b) -> Node v a -> Node v b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Node2 v a b => Node2 v (f a) (f b)
    | f, Node3 v a b c => Node3 v (f a) (f b) (f c)
    end.

Fixpoint unsafeFmap {a : Type} {b : Type} {v : Type} (arg_0__ : a -> b) (arg_1__
                      : FingerTree v a) : FingerTree v b
  := match arg_0__, arg_1__ with
     | _, Empty => Empty
     | f, Single x => Single (f x)
     | f, Deep v pr m sf =>
         Deep v (mapDigit f pr) (unsafeFmap (unsafeFmapNode f) m) (mapDigit f sf)
     end.

#[global] Definition foldlWPDigit {v} {a} {b} `{(Measured v a)}
   : (b -> v -> a -> b) -> b -> v -> Digit a -> b :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | f, z, vl, One a => f z vl a
    | f, z, vl, Two a b =>
        let vla := GHC.Base.mappend vl (measure a) in f (f z vl a) vla b
    | f, z, vl, Three a b c =>
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in f (f (f z vl a) vla b) vlab c
    | f, z, vl, Four a b c d =>
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in
        let vlabc := GHC.Base.mappend vlab (measure c) in
        f (f (f (f z vl a) vla b) vlab c) vlabc d
    end.

#[global] Definition foldlWPNode {v} {a} {b} `{(Measured v a)}
   : (b -> v -> a -> b) -> b -> v -> Node v a -> b :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | f, z, vl, Node2 _ a b =>
        let vla := GHC.Base.mappend vl (measure a) in f (f z vl a) vla b
    | f, z, vl, Node3 _ a b c =>
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in f (f (f z vl a) vla b) vlab c
    end.

Fixpoint foldlWPTree {v} {a} {b} `{(Measured v a)} (arg_0__
                       : (b -> v -> a -> b)) (arg_1__ : b) (arg_2__ : v) (arg_3__ : FingerTree v a)
  : b
  := match arg_0__, arg_1__, arg_2__, arg_3__ with
     | _, z, _, Empty => z
     | f, z, vl, Single x => f z vl x
     | f, z, vl, Deep _ pr m sf =>
         let zp := foldlWPDigit f z vl pr in
         let vlp := GHC.Base.mappend vl (measure pr) in
         let vlpm := GHC.Base.mappend vlp (measure m) in
         let zpm := foldlWPTree (foldlWPNode f) zp vlp m in
         let zpms := foldlWPDigit f zpm vlpm sf in zpms
     end.

#[global] Definition foldlWithPos {v : Type} {a : Type} {b : Type} `{Measured v
                                                                              a}
   : (b -> v -> a -> b) -> b -> FingerTree v a -> b :=
  fun f z => foldlWPTree f z GHC.Base.mempty.

#[global] Definition foldrWPDigit {v} {a} {b} `{(Measured v a)}
   : (v -> a -> b -> b) -> b -> v -> Digit a -> b :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | f, z, vl, One a => f vl a z
    | f, z, vl, Two a b =>
        let vla := GHC.Base.mappend vl (measure a) in f vl a (f vla b z)
    | f, z, vl, Three a b c =>
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in f vl a (f vla b (f vlab c z))
    | f, z, vl, Four a b c d =>
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in
        let vlabc := GHC.Base.mappend vlab (measure c) in
        f vl a (f vla b (f vlab c (f vlabc d z)))
    end.

#[global] Definition foldrWPNode {v} {a} {b} `{(Measured v a)}
   : (v -> a -> b -> b) -> v -> Node v a -> b -> b :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | f, vl, Node2 _ a b, z =>
        let vla := GHC.Base.mappend vl (measure a) in f vl a (f vla b z)
    | f, vl, Node3 _ a b c, z =>
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in f vl a (f vla b (f vlab c z))
    end.

Fixpoint foldrWPTree {v} {a} {b} `{(Measured v a)} (arg_0__
                       : (v -> a -> b -> b)) (arg_1__ : b) (arg_2__ : v) (arg_3__ : FingerTree v a)
  : b
  := match arg_0__, arg_1__, arg_2__, arg_3__ with
     | _, z, _, Empty => z
     | f, z, vl, Single x => f vl x z
     | f, z, vl, Deep _ pr m sf =>
         let vlp := GHC.Base.mappend vl (measure pr) in
         let vlpm := GHC.Base.mappend vlp (measure m) in
         let zs := foldrWPDigit f z vlpm sf in
         let zms := foldrWPTree (foldrWPNode f) zs vlp m in
         let zpms := foldrWPDigit f zms vl pr in zpms
     end.

#[global] Definition foldrWithPos {v : Type} {a : Type} {b : Type} `{Measured v
                                                                              a}
   : (v -> a -> b -> b) -> b -> FingerTree v a -> b :=
  fun f z => foldrWPTree f z GHC.Base.mempty.

#[global] Definition foldlWCDigit {v} {a} {b} `{(Measured v a)}
   : (b -> v -> a -> v -> b) -> b -> v -> Digit a -> v -> b :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | f, z, vl, One a, vr => f z vl a vr
    | f, z, vl, Two a b, vr =>
        let vbr := GHC.Base.mappend (measure b) vr in
        let vla := GHC.Base.mappend vl (measure a) in f (f z vl a vbr) vla b vr
    | f, z, vl, Three a b c, vr =>
        let vcr := GHC.Base.mappend (measure c) vr in
        let vbcr := GHC.Base.mappend (measure b) vcr in
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in
        f (f (f z vl a vbcr) vla b vcr) vlab c vr
    | f, z, vl, Four a b c d, vr =>
        let vdr := GHC.Base.mappend (measure d) vr in
        let vcdr := GHC.Base.mappend (measure c) vdr in
        let vbcdr := GHC.Base.mappend (measure b) vcdr in
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in
        let vlabc := GHC.Base.mappend vlab (measure c) in
        f (f (f (f z vl a vbcdr) vla b vcdr) vlab c vdr) vlabc d vr
    end.

#[global] Definition foldlWCNode {v} {a} {b} `{(Measured v a)}
   : (b -> v -> a -> v -> b) -> b -> v -> Node v a -> v -> b :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | f, z, vl, Node2 _ a b, vr =>
        let vbr := GHC.Base.mappend (measure b) vr in
        let vla := GHC.Base.mappend vl (measure a) in f (f z vl a vbr) vla b vr
    | f, z, vl, Node3 _ a b c, vr =>
        let vcr := GHC.Base.mappend (measure c) vr in
        let vbcr := GHC.Base.mappend (measure b) vcr in
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in
        f (f (f z vl a vbcr) vla b vcr) vlab c vr
    end.

Fixpoint foldlWCTree {v} {a} {b} `{(Measured v a)} (arg_0__
                       : (b -> v -> a -> v -> b)) (arg_1__ : b) (arg_2__ : v) (arg_3__
                       : FingerTree v a) (arg_4__ : v) : b
  := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
     | _, z, _, Empty, _ => z
     | f, z, vl, Single x, vr => f z vl x vr
     | f, z, vl, Deep _ pr m sf, vr =>
         let vm := measure m in
         let vsr := GHC.Base.mappend (measure sf) vr in
         let vmsr := GHC.Base.mappend vm vsr in
         let zp := foldlWCDigit f z vl pr vmsr in
         let vlp := GHC.Base.mappend vl (measure pr) in
         let vlpm := GHC.Base.mappend vlp vm in
         let zpm := foldlWCTree (foldlWCNode f) zp vlp m vsr in
         let zpms := foldlWCDigit f zpm vlpm sf vr in zpms
     end.

#[global] Definition foldlWithContext {v : Type} {a : Type} {b : Type}
  `{Measured v a}
   : (b -> v -> a -> v -> b) -> b -> FingerTree v a -> b :=
  fun f z t => foldlWCTree f z GHC.Base.mempty t GHC.Base.mempty.

#[global] Definition foldrWCDigit {v} {a} {b} `{(Measured v a)}
   : (v -> a -> v -> b -> b) -> b -> v -> Digit a -> v -> b :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | f, z, vl, One a, vr => f vl a vr z
    | f, z, vl, Two a b, vr =>
        let vbr := GHC.Base.mappend (measure b) vr in
        let vla := GHC.Base.mappend vl (measure a) in f vl a vbr (f vla b vr z)
    | f, z, vl, Three a b c, vr =>
        let vcr := GHC.Base.mappend (measure c) vr in
        let vbcr := GHC.Base.mappend (measure b) vcr in
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in
        f vl a vbcr (f vla b vcr (f vlab c vr z))
    | f, z, vl, Four a b c d, vr =>
        let vdr := GHC.Base.mappend (measure d) vr in
        let vcdr := GHC.Base.mappend (measure c) vdr in
        let vbcdr := GHC.Base.mappend (measure b) vcdr in
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in
        let vlabc := GHC.Base.mappend vlab (measure c) in
        f vl a vbcdr (f vla b vcdr (f vlab c vdr (f vlabc d vr z)))
    end.

#[global] Definition foldrWCNode {v} {a} {b} `{(Measured v a)}
   : (v -> a -> v -> b -> b) -> v -> Node v a -> v -> b -> b :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | f, vl, Node2 _ a b, vr, z =>
        let vbr := GHC.Base.mappend (measure b) vr in
        let vla := GHC.Base.mappend vl (measure a) in f vl a vbr (f vla b vr z)
    | f, vl, Node3 _ a b c, vr, z =>
        let vcr := GHC.Base.mappend (measure c) vr in
        let vbcr := GHC.Base.mappend (measure b) vcr in
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in
        f vl a vbcr (f vla b vcr (f vlab c vr z))
    end.

Fixpoint foldrWCTree {v} {a} {b} `{(Measured v a)} (arg_0__
                       : (v -> a -> v -> b -> b)) (arg_1__ : b) (arg_2__ : v) (arg_3__
                       : FingerTree v a) (arg_4__ : v) : b
  := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
     | _, z, _, Empty, _ => z
     | f, z, vl, Single x, vr => f vl x vr z
     | f, z, vl, Deep _ pr m sf, vr =>
         let vm := measure m in
         let vsr := GHC.Base.mappend (measure sf) vr in
         let vmsr := GHC.Base.mappend vm vsr in
         let vlp := GHC.Base.mappend vl (measure pr) in
         let vlpm := GHC.Base.mappend vlp vm in
         let zs := foldrWCDigit f z vlpm sf vr in
         let zms := foldrWCTree (foldrWCNode f) zs vlp m vsr in
         let zpms := foldrWCDigit f zms vl pr vmsr in zpms
     end.

#[global] Definition foldrWithContext {v : Type} {a : Type} {b : Type}
  `{Measured v a}
   : (v -> a -> v -> b -> b) -> b -> FingerTree v a -> b :=
  fun f z t => foldrWCTree f z GHC.Base.mempty t GHC.Base.mempty.

#[global] Definition traverseDigit {f} {a} {b} `{(GHC.Base.Applicative f)}
   : (a -> f b) -> Digit a -> f (Digit b) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, One a => Data.Functor.op_zlzdzg__ One (f a)
    | f, Two a b => Data.Functor.op_zlzdzg__ Two (f a) GHC.Base.<*> f b
    | f, Three a b c =>
        (Data.Functor.op_zlzdzg__ Three (f a) GHC.Base.<*> f b) GHC.Base.<*> f c
    | f, Four a b c d =>
        ((Data.Functor.op_zlzdzg__ Four (f a) GHC.Base.<*> f b) GHC.Base.<*> f c)
        GHC.Base.<*>
        f d
    end.

#[global] Definition traverseNode {v2} {a2} {f} {a1} {v1} `{Measured v2 a2}
  `{GHC.Base.Applicative f}
   : (a1 -> f a2) -> Node v1 a1 -> f (Node v2 a2) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Node2 _ a b => Data.Functor.op_zlzdzg__ node2 (f a) GHC.Base.<*> f b
    | f, Node3 _ a b c =>
        (Data.Functor.op_zlzdzg__ node3 (f a) GHC.Base.<*> f b) GHC.Base.<*> f c
    end.

Fixpoint traverseTree {v2} {a2} {f} {a1} {v1} `{Measured v2 a2}
                      `{GHC.Base.Applicative f} (arg_0__ : (a1 -> f a2)) (arg_1__ : FingerTree v1 a1)
  : f (FingerTree v2 a2)
  := match arg_0__, arg_1__ with
     | _, Empty => GHC.Base.pure Empty
     | f, Single x => Data.Functor.op_zlzdzg__ Single (f x)
     | f, Deep _ pr m sf =>
         (Data.Functor.op_zlzdzg__ deep (traverseDigit f pr) GHC.Base.<*>
          traverseTree (traverseNode f) m) GHC.Base.<*>
         traverseDigit f sf
     end.

#[global] Definition traverse' {v1 : Type} {a1 : Type} {v2 : Type} {a2 : Type}
  {f : Type -> Type} `{Measured v1 a1} `{Measured v2 a2} `{GHC.Base.Applicative f}
   : (a1 -> f a2) -> FingerTree v1 a1 -> f (FingerTree v2 a2) :=
  traverseTree.

#[global] Definition traverseWPDigit {v} {a} {f} {b} `{Measured v a}
  `{GHC.Base.Applicative f}
   : (v -> a -> f b) -> v -> Digit a -> f (Digit b) :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, v, One a => Data.Functor.op_zlzdzg__ One (f v a)
    | f, v, Two a b =>
        let va := GHC.Base.mappend v (measure a) in
        Data.Functor.op_zlzdzg__ Two (f v a) GHC.Base.<*> f va b
    | f, v, Three a b c =>
        let va := GHC.Base.mappend v (measure a) in
        let vab := GHC.Base.mappend va (measure b) in
        (Data.Functor.op_zlzdzg__ Three (f v a) GHC.Base.<*> f va b) GHC.Base.<*>
        f vab c
    | f, v, Four a b c d =>
        let va := GHC.Base.mappend v (measure a) in
        let vab := GHC.Base.mappend va (measure b) in
        let vabc := GHC.Base.mappend vab (measure c) in
        ((Data.Functor.op_zlzdzg__ Four (f v a) GHC.Base.<*> f va b) GHC.Base.<*>
         f vab c) GHC.Base.<*>
        f vabc d
    end.

#[global] Definition traverseWPNode {v1} {a1} {v2} {a2} {f} `{Measured v1 a1}
  `{Measured v2 a2} `{GHC.Base.Applicative f}
   : (v1 -> a1 -> f a2) -> v1 -> Node v1 a1 -> f (Node v2 a2) :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, v, Node2 _ a b =>
        let va := GHC.Base.mappend v (measure a) in
        Data.Functor.op_zlzdzg__ node2 (f v a) GHC.Base.<*> f va b
    | f, v, Node3 _ a b c =>
        let va := GHC.Base.mappend v (measure a) in
        let vab := GHC.Base.mappend va (measure b) in
        (Data.Functor.op_zlzdzg__ node3 (f v a) GHC.Base.<*> f va b) GHC.Base.<*>
        f vab c
    end.

Fixpoint traverseWPTree {v1} {a1} {v2} {a2} {f} `{Measured v1 a1} `{Measured v2
                        a2} `{GHC.Base.Applicative f} (arg_0__ : (v1 -> a1 -> f a2)) (arg_1__ : v1)
                        (arg_2__ : FingerTree v1 a1) : f (FingerTree v2 a2)
  := match arg_0__, arg_1__, arg_2__ with
     | _, _, Empty => GHC.Base.pure Empty
     | f, v, Single x => Data.Functor.op_zlzdzg__ Single (f v x)
     | f, v, Deep _ pr m sf =>
         let vpr := GHC.Base.mappend v (measure pr) in
         let vm := GHC.Base.mappend vpr (measure m) in
         (Data.Functor.op_zlzdzg__ deep (traverseWPDigit f v pr) GHC.Base.<*>
          traverseWPTree (traverseWPNode f) vpr m) GHC.Base.<*>
         traverseWPDigit f vm sf
     end.

#[global] Definition traverseWithPos {v1 : Type} {a1 : Type} {v2 : Type} {a2
   : Type} {f : Type -> Type} `{Measured v1 a1} `{Measured v2 a2}
  `{GHC.Base.Applicative f}
   : (v1 -> a1 -> f a2) -> FingerTree v1 a1 -> f (FingerTree v2 a2) :=
  fun f => traverseWPTree f GHC.Base.mempty.

#[global] Definition traverseWCDigit {v} {a} {f} {b} `{Measured v a}
  `{GHC.Base.Applicative f}
   : (v -> a -> v -> f b) -> v -> Digit a -> v -> f (Digit b) :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | f, vl, One a, vr => Data.Functor.op_zlzdzg__ One (f vl a vr)
    | f, vl, Two a b, vr =>
        let vbr := GHC.Base.mappend (measure b) vr in
        let vla := GHC.Base.mappend vl (measure a) in
        Data.Functor.op_zlzdzg__ Two (f vl a vbr) GHC.Base.<*> f vla b vr
    | f, vl, Three a b c, vr =>
        let vcr := GHC.Base.mappend (measure c) vr in
        let vbcr := GHC.Base.mappend (measure b) vcr in
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in
        (Data.Functor.op_zlzdzg__ Three (f vl a vbcr) GHC.Base.<*> f vla b vcr)
        GHC.Base.<*>
        f vlab c vr
    | f, vl, Four a b c d, vr =>
        let vdr := GHC.Base.mappend (measure d) vr in
        let vcdr := GHC.Base.mappend (measure c) vdr in
        let vbcdr := GHC.Base.mappend (measure b) vcdr in
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in
        let vlabc := GHC.Base.mappend vlab (measure c) in
        ((Data.Functor.op_zlzdzg__ Four (f vl a vbcdr) GHC.Base.<*> f vla b vcdr)
         GHC.Base.<*>
         f vlab c vdr) GHC.Base.<*>
        f vlabc d vr
    end.

#[global] Definition traverseWCNode {v1} {a1} {v2} {a2} {f} `{Measured v1 a1}
  `{Measured v2 a2} `{GHC.Base.Applicative f}
   : (v1 -> a1 -> v1 -> f a2) -> v1 -> Node v1 a1 -> v1 -> f (Node v2 a2) :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | f, vl, Node2 _ a b, vr =>
        let vbr := GHC.Base.mappend (measure b) vr in
        let vla := GHC.Base.mappend vl (measure a) in
        Data.Functor.op_zlzdzg__ node2 (f vl a vbr) GHC.Base.<*> f vla b vr
    | f, vl, Node3 _ a b c, vr =>
        let vcr := GHC.Base.mappend (measure c) vr in
        let vbcr := GHC.Base.mappend (measure b) vcr in
        let vla := GHC.Base.mappend vl (measure a) in
        let vlab := GHC.Base.mappend vla (measure b) in
        (Data.Functor.op_zlzdzg__ node3 (f vl a vbcr) GHC.Base.<*> f vla b vcr)
        GHC.Base.<*>
        f vlab c vr
    end.

Fixpoint traverseWCTree {v1} {a1} {v2} {a2} {f} `{Measured v1 a1} `{Measured v2
                        a2} `{GHC.Base.Applicative f} (arg_0__ : (v1 -> a1 -> v1 -> f a2)) (arg_1__
                          : v1) (arg_2__ : FingerTree v1 a1) (arg_3__ : v1) : f (FingerTree v2 a2)
  := match arg_0__, arg_1__, arg_2__, arg_3__ with
     | _, _, Empty, _ => GHC.Base.pure Empty
     | f, vl, Single x, vr => Data.Functor.op_zlzdzg__ Single (f vl x vr)
     | f, vl, Deep _ pr m sf, vr =>
         let vm := measure m in
         let vsr := GHC.Base.mappend (measure sf) vr in
         let vmsr := GHC.Base.mappend vm vsr in
         let vlp := GHC.Base.mappend vl (measure pr) in
         let vlpm := GHC.Base.mappend vlp vm in
         (Data.Functor.op_zlzdzg__ deep (traverseWCDigit f vl pr vmsr) GHC.Base.<*>
          traverseWCTree (traverseWCNode f) vlp m vsr) GHC.Base.<*>
         traverseWCDigit f vlpm sf vr
     end.

#[global] Definition traverseWithContext {v1 : Type} {a1 : Type} {v2 : Type} {a2
   : Type} {f : Type -> Type} `{Measured v1 a1} `{Measured v2 a2}
  `{GHC.Base.Applicative f}
   : (v1 -> a1 -> v1 -> f a2) -> FingerTree v1 a1 -> f (FingerTree v2 a2) :=
  fun f t => traverseWCTree f GHC.Base.mempty t GHC.Base.mempty.

#[global] Definition unsafeTraverseNode {f} {a} {b} {v} `{(GHC.Base.Applicative
   f)}
   : (a -> f b) -> Node v a -> f (Node v b) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Node2 v a b => Data.Functor.op_zlzdzg__ (Node2 v) (f a) GHC.Base.<*> f b
    | f, Node3 v a b c =>
        (Data.Functor.op_zlzdzg__ (Node3 v) (f a) GHC.Base.<*> f b) GHC.Base.<*> f c
    end.

Fixpoint unsafeTraverse {f : Type -> Type} {a : Type} {b : Type} {v : Type}
                        `{GHC.Base.Applicative f} (arg_0__ : a -> f b) (arg_1__ : FingerTree v a) : f
                                                                                                    (FingerTree v b)
  := match arg_0__, arg_1__ with
     | _, Empty => GHC.Base.pure Empty
     | f, Single x => Data.Functor.op_zlzdzg__ Single (f x)
     | f, Deep v pr m sf =>
         (Data.Functor.op_zlzdzg__ (Deep v) (traverseDigit f pr) GHC.Base.<*>
          unsafeTraverse (unsafeTraverseNode f) m) GHC.Base.<*>
         traverseDigit f sf
     end.

#[global] Definition singleton {v : Type} {a : Type} `{Measured v a}
   : a -> FingerTree v a :=
  Single.

#[global] Definition fromList {v : Type} {a : Type} `{Measured v a}
   : list a -> FingerTree v a :=
  Data.Foldable.foldr consTree Empty.

#[global] Definition null {v : Type} {a : Type} : FingerTree v a -> bool :=
  fun arg_0__ => match arg_0__ with | Empty => true | _ => false end.

#[global] Definition digitToTree {v} {a} `{(Measured v a)}
   : Digit a -> FingerTree v a :=
  fun arg_0__ =>
    match arg_0__ with
    | One a => Single a
    | Two a b => deep (One a) Empty (One b)
    | Three a b c => deep (Two a b) Empty (One c)
    | Four a b c d => deep (Two a b) Empty (Two c d)
    end.

#[global] Definition lheadDigit {a} : Digit a -> a :=
  fun arg_0__ =>
    match arg_0__ with
    | One a => a
    | Two a _ => a
    | Three a _ _ => a
    | Four a _ _ _ => a
    end.

#[global] Definition ltailDigit {a} : Digit a -> Digit a :=
  fun arg_0__ =>
    match arg_0__ with
    | One _ =>
        (@illegal_argument _ (HsToRocq.Err.Build_Default _ arg_0__))
        (GHC.Base.hs_string__ "ltailDigit")
    | Two _ b => One b
    | Three _ b c => Two b c
    | Four _ b c d => Three b c d
    end.

Fixpoint viewl {v a : Type} `{Measured v a} (arg_0__ : FingerTree v a) : ViewL
                                                                         (FingerTree v) a
  := let rotL {v}
     {a}
     `{(Measured v a)}
     (m : FingerTree v (Node v a))
     (sf : Digit a)
      : FingerTree v a :=
       match viewl m with
       | EmptyL => digitToTree sf
       | op_ZCzl__ a m' =>
           Deep (GHC.Base.mappend (measure m) (measure sf)) (nodeToDigit a) m' sf
       end in
     match arg_0__ with
     | Empty => EmptyL
     | Single x => x :< Empty
     | Deep _ (One x) m sf => x :< rotL m sf
     | Deep _ pr m sf => lheadDigit pr :< deep (ltailDigit pr) m sf
     end.

#[global] Definition rotL {v} {a} `{(Measured v a)}
   : FingerTree v (Node v a) -> Digit a -> FingerTree v a :=
  fun m sf =>
    match viewl m with
    | EmptyL => digitToTree sf
    | op_ZCzl__ a m' =>
        Deep (GHC.Base.mappend (measure m) (measure sf)) (nodeToDigit a) m' sf
    end.

#[global] Definition rheadDigit {a} : Digit a -> a :=
  fun arg_0__ =>
    match arg_0__ with
    | One a => a
    | Two _ b => b
    | Three _ _ c => c
    | Four _ _ _ d => d
    end.

#[global] Definition rtailDigit {a} : Digit a -> Digit a :=
  fun arg_0__ =>
    match arg_0__ with
    | One _ =>
        (@illegal_argument _ (HsToRocq.Err.Build_Default _ arg_0__))
        (GHC.Base.hs_string__ "rtailDigit")
    | Two a _ => One a
    | Three a b _ => Two a b
    | Four a b c _ => Three a b c
    end.

Fixpoint viewr {v a : Type} `{Measured v a} (arg_0__ : FingerTree v a) : ViewR
                                                                         (FingerTree v) a
  := let rotR {v}
     {a}
     `{(Measured v a)}
     (pr : Digit a)
     (m : FingerTree v (Node v a))
      : FingerTree v a :=
       match viewr m with
       | EmptyR => digitToTree pr
       | op_ZCzg__ m' a =>
           Deep (GHC.Base.mappend (measure pr) (measure m)) pr m' (nodeToDigit a)
       end in
     match arg_0__ with
     | Empty => EmptyR
     | Single x => Empty :> x
     | Deep _ pr m (One x) => rotR pr m :> x
     | Deep _ pr m sf => deep pr m (rtailDigit sf) :> rheadDigit sf
     end.

#[global] Definition rotR {v} {a} `{(Measured v a)}
   : Digit a -> FingerTree v (Node v a) -> FingerTree v a :=
  fun pr m =>
    match viewr m with
    | EmptyR => digitToTree pr
    | op_ZCzg__ m' a =>
        Deep (GHC.Base.mappend (measure pr) (measure m)) pr m' (nodeToDigit a)
    end.

#[global] Definition addDigits1 {v} {a} `{(Measured v a)}
   : FingerTree v (Node v a) ->
     Digit a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a) :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | m1, One a, b, One c, m2 => appendTree1 m1 (node3 a b c) m2
    | m1, One a, b, Two c d, m2 => appendTree2 m1 (node2 a b) (node2 c d) m2
    | m1, One a, b, Three c d e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
    | m1, One a, b, Four c d e f, m2 =>
        appendTree2 m1 (node3 a b c) (node3 d e f) m2
    | m1, Two a b, c, One d, m2 => appendTree2 m1 (node2 a b) (node2 c d) m2
    | m1, Two a b, c, Two d e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
    | m1, Two a b, c, Three d e f, m2 =>
        appendTree2 m1 (node3 a b c) (node3 d e f) m2
    | m1, Two a b, c, Four d e f g, m2 =>
        appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
    | m1, Three a b c, d, One e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
    | m1, Three a b c, d, Two e f, m2 =>
        appendTree2 m1 (node3 a b c) (node3 d e f) m2
    | m1, Three a b c, d, Three e f g, m2 =>
        appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
    | m1, Three a b c, d, Four e f g h, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
    | m1, Four a b c d, e, One f, m2 =>
        appendTree2 m1 (node3 a b c) (node3 d e f) m2
    | m1, Four a b c d, e, Two f g, m2 =>
        appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
    | m1, Four a b c d, e, Three f g h, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
    | m1, Four a b c d, e, Four f g h i, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
    end.

#[global] Definition appendTree4
   : forall {v} {a} `{(Measured v a)},
     FingerTree v a -> a -> a -> a -> a -> FingerTree v a -> FingerTree v a :=
  fix appendTree2 {v} {a} `{(Measured v a)} (arg_0__ : FingerTree v a) (arg_1__
                   arg_2__
                    : a) (arg_3__ : FingerTree v a) : FingerTree v a
    := let addDigits2 {v}
       {a}
       `{(Measured v a)}
       (arg_0__ : FingerTree v (Node v a))
       (arg_1__ : Digit a)
       (arg_2__ arg_3__ : a)
       (arg_4__ : Digit a)
       (arg_5__ : FingerTree v (Node v a))
        : FingerTree v (Node v a) :=
         match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__ with
         | m1, One a, b, c, One d, m2 => appendTree2 m1 (node2 a b) (node2 c d) m2
         | m1, One a, b, c, Two d e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
         | m1, One a, b, c, Three d e f, m2 =>
             appendTree2 m1 (node3 a b c) (node3 d e f) m2
         | m1, One a, b, c, Four d e f g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Two a b, c, d, One e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
         | m1, Two a b, c, d, Two e f, m2 =>
             appendTree2 m1 (node3 a b c) (node3 d e f) m2
         | m1, Two a b, c, d, Three e f g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Two a b, c, d, Four e f g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Three a b c, d, e, One f, m2 =>
             appendTree2 m1 (node3 a b c) (node3 d e f) m2
         | m1, Three a b c, d, e, Two f g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Three a b c, d, e, Three f g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Three a b c, d, e, Four f g h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Four a b c d, e, f, One g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Four a b c d, e, f, Two g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Four a b c d, e, f, Three g h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Four a b c d, e, f, Four g h i j, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
         end in
       match arg_0__, arg_1__, arg_2__, arg_3__ with
       | Empty, a, b, xs => consTree a (consTree b xs)
       | xs, a, b, Empty => snocTree (snocTree xs a) b
       | Single x, a, b, xs => consTree x (consTree a (consTree b xs))
       | xs, a, b, Single x => snocTree (snocTree (snocTree xs a) b) x
       | Deep _ pr1 m1 sf1, a, b, Deep _ pr2 m2 sf2 =>
           deep pr1 (addDigits2 m1 sf1 a b pr2 m2) sf2
       end
  with appendTree3 {v} {a} `{(Measured v a)} (arg_0__ : FingerTree v a) (arg_1__
                    arg_2__ arg_3__
                     : a) (arg_4__ : FingerTree v a) : FingerTree v a
    := let addDigits3 {v}
       {a}
       `{(Measured v a)}
       (arg_0__ : FingerTree v (Node v a))
       (arg_1__ : Digit a)
       (arg_2__ arg_3__ arg_4__ : a)
       (arg_5__ : Digit a)
       (arg_6__ : FingerTree v (Node v a))
        : FingerTree v (Node v a) :=
         match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__, arg_6__ with
         | m1, One a, b, c, d, One e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
         | m1, One a, b, c, d, Two e f, m2 =>
             appendTree2 m1 (node3 a b c) (node3 d e f) m2
         | m1, One a, b, c, d, Three e f g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, One a, b, c, d, Four e f g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Two a b, c, d, e, One f, m2 =>
             appendTree2 m1 (node3 a b c) (node3 d e f) m2
         | m1, Two a b, c, d, e, Two f g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Two a b, c, d, e, Three f g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Two a b, c, d, e, Four f g h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Three a b c, d, e, f, One g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Three a b c, d, e, f, Two g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Three a b c, d, e, f, Three g h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Three a b c, d, e, f, Four g h i j, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
         | m1, Four a b c d, e, f, g, One h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Four a b c d, e, f, g, Two h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Four a b c d, e, f, g, Three h i j, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
         | m1, Four a b c d, e, f, g, Four h i j k, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
         end in
       match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
       | Empty, a, b, c, xs => consTree a (consTree b (consTree c xs))
       | xs, a, b, c, Empty => snocTree (snocTree (snocTree xs a) b) c
       | Single x, a, b, c, xs => consTree x (consTree a (consTree b (consTree c xs)))
       | xs, a, b, c, Single x => snocTree (snocTree (snocTree (snocTree xs a) b) c) x
       | Deep _ pr1 m1 sf1, a, b, c, Deep _ pr2 m2 sf2 =>
           deep pr1 (addDigits3 m1 sf1 a b c pr2 m2) sf2
       end
  with appendTree4 {v} {a} `{(Measured v a)} (arg_0__ : FingerTree v a) (arg_1__
                    arg_2__ arg_3__ arg_4__
                     : a) (arg_5__ : FingerTree v a) : FingerTree v a
    := let addDigits4 {v}
       {a}
       `{(Measured v a)}
       (arg_0__ : FingerTree v (Node v a))
       (arg_1__ : Digit a)
       (arg_2__ arg_3__ arg_4__ arg_5__ : a)
       (arg_6__ : Digit a)
       (arg_7__ : FingerTree v (Node v a))
        : FingerTree v (Node v a) :=
         match arg_0__
             , arg_1__
             , arg_2__
             , arg_3__
             , arg_4__
             , arg_5__
             , arg_6__
             , arg_7__ with
         | m1, One a, b, c, d, e, One f, m2 =>
             appendTree2 m1 (node3 a b c) (node3 d e f) m2
         | m1, One a, b, c, d, e, Two f g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, One a, b, c, d, e, Three f g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, One a, b, c, d, e, Four f g h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Two a b, c, d, e, f, One g, m2 =>
             appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
         | m1, Two a b, c, d, e, f, Two g h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Two a b, c, d, e, f, Three g h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Two a b, c, d, e, f, Four g h i j, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
         | m1, Three a b c, d, e, f, g, One h, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
         | m1, Three a b c, d, e, f, g, Two h i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Three a b c, d, e, f, g, Three h i j, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
         | m1, Three a b c, d, e, f, g, Four h i j k, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
         | m1, Four a b c d, e, f, g, h, One i, m2 =>
             appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
         | m1, Four a b c d, e, f, g, h, Two i j, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
         | m1, Four a b c d, e, f, g, h, Three i j k, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
         | m1, Four a b c d, e, f, g, h, Four i j k l, m2 =>
             appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l) m2
         end in
       match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__ with
       | Empty, a, b, c, d, xs => consTree a (consTree b (consTree c (consTree d xs)))
       | xs, a, b, c, d, Empty => snocTree (snocTree (snocTree (snocTree xs a) b) c) d
       | Single x, a, b, c, d, xs =>
           consTree x (consTree a (consTree b (consTree c (consTree d xs))))
       | xs, a, b, c, d, Single x =>
           snocTree (snocTree (snocTree (snocTree (snocTree xs a) b) c) d) x
       | Deep _ pr1 m1 sf1, a, b, c, d, Deep _ pr2 m2 sf2 =>
           deep pr1 (addDigits4 m1 sf1 a b c d pr2 m2) sf2
       end for appendTree4.

#[global] Definition addDigits2 {v} {a} `{(Measured v a)}
   : FingerTree v (Node v a) ->
     Digit a ->
     a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a) :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__ with
    | m1, One a, b, c, One d, m2 => appendTree2 m1 (node2 a b) (node2 c d) m2
    | m1, One a, b, c, Two d e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
    | m1, One a, b, c, Three d e f, m2 =>
        appendTree2 m1 (node3 a b c) (node3 d e f) m2
    | m1, One a, b, c, Four d e f g, m2 =>
        appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
    | m1, Two a b, c, d, One e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
    | m1, Two a b, c, d, Two e f, m2 =>
        appendTree2 m1 (node3 a b c) (node3 d e f) m2
    | m1, Two a b, c, d, Three e f g, m2 =>
        appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
    | m1, Two a b, c, d, Four e f g h, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
    | m1, Three a b c, d, e, One f, m2 =>
        appendTree2 m1 (node3 a b c) (node3 d e f) m2
    | m1, Three a b c, d, e, Two f g, m2 =>
        appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
    | m1, Three a b c, d, e, Three f g h, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
    | m1, Three a b c, d, e, Four f g h i, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
    | m1, Four a b c d, e, f, One g, m2 =>
        appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
    | m1, Four a b c d, e, f, Two g h, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
    | m1, Four a b c d, e, f, Three g h i, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
    | m1, Four a b c d, e, f, Four g h i j, m2 =>
        appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
    end.

#[global] Definition addDigits3 {v} {a} `{(Measured v a)}
   : FingerTree v (Node v a) ->
     Digit a ->
     a -> a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a) :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ arg_6__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__, arg_6__ with
    | m1, One a, b, c, d, One e, m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
    | m1, One a, b, c, d, Two e f, m2 =>
        appendTree2 m1 (node3 a b c) (node3 d e f) m2
    | m1, One a, b, c, d, Three e f g, m2 =>
        appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
    | m1, One a, b, c, d, Four e f g h, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
    | m1, Two a b, c, d, e, One f, m2 =>
        appendTree2 m1 (node3 a b c) (node3 d e f) m2
    | m1, Two a b, c, d, e, Two f g, m2 =>
        appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
    | m1, Two a b, c, d, e, Three f g h, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
    | m1, Two a b, c, d, e, Four f g h i, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
    | m1, Three a b c, d, e, f, One g, m2 =>
        appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
    | m1, Three a b c, d, e, f, Two g h, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
    | m1, Three a b c, d, e, f, Three g h i, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
    | m1, Three a b c, d, e, f, Four g h i j, m2 =>
        appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
    | m1, Four a b c d, e, f, g, One h, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
    | m1, Four a b c d, e, f, g, Two h i, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
    | m1, Four a b c d, e, f, g, Three h i j, m2 =>
        appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
    | m1, Four a b c d, e, f, g, Four h i j k, m2 =>
        appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
    end.

#[global] Definition addDigits4 {v} {a} `{(Measured v a)}
   : FingerTree v (Node v a) ->
     Digit a ->
     a ->
     a -> a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a) :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ arg_6__ arg_7__ =>
    match arg_0__
        , arg_1__
        , arg_2__
        , arg_3__
        , arg_4__
        , arg_5__
        , arg_6__
        , arg_7__ with
    | m1, One a, b, c, d, e, One f, m2 =>
        appendTree2 m1 (node3 a b c) (node3 d e f) m2
    | m1, One a, b, c, d, e, Two f g, m2 =>
        appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
    | m1, One a, b, c, d, e, Three f g h, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
    | m1, One a, b, c, d, e, Four f g h i, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
    | m1, Two a b, c, d, e, f, One g, m2 =>
        appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
    | m1, Two a b, c, d, e, f, Two g h, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
    | m1, Two a b, c, d, e, f, Three g h i, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
    | m1, Two a b, c, d, e, f, Four g h i j, m2 =>
        appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
    | m1, Three a b c, d, e, f, g, One h, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
    | m1, Three a b c, d, e, f, g, Two h i, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
    | m1, Three a b c, d, e, f, g, Three h i j, m2 =>
        appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
    | m1, Three a b c, d, e, f, g, Four h i j k, m2 =>
        appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
    | m1, Four a b c d, e, f, g, h, One i, m2 =>
        appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
    | m1, Four a b c d, e, f, g, h, Two i j, m2 =>
        appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
    | m1, Four a b c d, e, f, g, h, Three i j k, m2 =>
        appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
    | m1, Four a b c d, e, f, g, h, Four i j k l, m2 =>
        appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l) m2
    end.

#[global] Definition deepL {v} {a} `{(Measured v a)}
   : option (Digit a) -> FingerTree v (Node v a) -> Digit a -> FingerTree v a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | None, m, sf => rotL m sf
    | Some pr, m, sf => deep pr m sf
    end.

#[global] Definition deepR {v} {a} `{(Measured v a)}
   : Digit a -> FingerTree v (Node v a) -> option (Digit a) -> FingerTree v a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | pr, m, None => rotR pr m
    | pr, m, Some sf => deep pr m sf
    end.

#[global] Definition searchDigit {v} {a} `{(Measured v a)}
   : (v -> v -> bool) -> v -> Digit a -> v -> Split (option (Digit a)) a :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | _, vl, One a, vr => GHC.Prim.seq vl (GHC.Prim.seq vr (MkSplit None a None))
    | p, vl, Two a b, vr =>
        let vb := GHC.Base.mappend (measure b) vr in
        let va := GHC.Base.mappend vl (measure a) in
        if p va vb : bool then MkSplit None a (Some (One b)) else
        MkSplit (Some (One a)) b None
    | p, vl, Three a b c, vr =>
        let vc := GHC.Base.mappend (measure c) vr in
        let vbc := GHC.Base.mappend (measure b) vc in
        let va := GHC.Base.mappend vl (measure a) in
        let vab := GHC.Base.mappend va (measure b) in
        if p va vbc : bool then MkSplit None a (Some (Two b c)) else
        if p vab vc : bool then MkSplit (Some (One a)) b (Some (One c)) else
        MkSplit (Some (Two a b)) c None
    | p, vl, Four a b c d, vr =>
        let vd := GHC.Base.mappend (measure d) vr in
        let vcd := GHC.Base.mappend (measure c) vd in
        let vbcd := GHC.Base.mappend (measure b) vcd in
        let va := GHC.Base.mappend vl (measure a) in
        let vab := GHC.Base.mappend va (measure b) in
        let vabc := GHC.Base.mappend vab (measure c) in
        if p va vbcd : bool then MkSplit None a (Some (Three b c d)) else
        if p vab vcd : bool then MkSplit (Some (One a)) b (Some (Two c d)) else
        if p vabc vd : bool then MkSplit (Some (Two a b)) c (Some (One d)) else
        MkSplit (Some (Three a b c)) d None
    end.

#[global] Definition searchNode {v} {a} `{(Measured v a)}
   : (v -> v -> bool) -> v -> Node v a -> v -> Split (option (Digit a)) a :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | p, vl, Node2 _ a b, vr =>
        let vb := GHC.Base.mappend (measure b) vr in
        let va := GHC.Base.mappend vl (measure a) in
        if p va vb : bool then MkSplit None a (Some (One b)) else
        MkSplit (Some (One a)) b None
    | p, vl, Node3 _ a b c, vr =>
        let vc := GHC.Base.mappend (measure c) vr in
        let vbc := GHC.Base.mappend (measure b) vc in
        let va := GHC.Base.mappend vl (measure a) in
        let vab := GHC.Base.mappend va (measure b) in
        if p va vbc : bool then MkSplit None a (Some (Two b c)) else
        if p vab vc : bool then MkSplit (Some (One a)) b (Some (One c)) else
        MkSplit (Some (Two a b)) c None
    end.

Fixpoint searchTree {v a} `{Measured v a} `{HsToRocq.Err.Default a} (arg_0__
                      : v -> v -> bool) (arg_1__ : v) (arg_2__ : FingerTree v a) (arg_3__ : v)
  : Split (FingerTree v a) a
  := match arg_0__, arg_1__, arg_2__, arg_3__ with
     | _, _, Empty, _ => illegal_argument (GHC.Base.hs_string__ "searchTree")
     | _, _, Single x, _ => MkSplit Empty x Empty
     | p, vl, Deep _ pr m sf, vr =>
         let vm := measure m in
         let vsr := GHC.Base.mappend (measure sf) vr in
         let vmsr := GHC.Base.mappend vm vsr in
         let vlp := GHC.Base.mappend vl (measure pr) in
         let vlpm := GHC.Base.mappend vlp vm in
         if p vlp vmsr : bool
         then let 'MkSplit l x r := searchDigit p vl pr vmsr in
              MkSplit (Data.Maybe.maybe Empty digitToTree l) x (deepL r m sf) else
         if p vlpm vsr : bool
         then let 'MkSplit ml xs mr := searchTree p vlp m vsr in
              let 'MkSplit l x r := searchNode p (GHC.Base.mappend vlp (measure ml)) xs
                                      (GHC.Base.mappend (measure mr) vsr) in
              MkSplit (deepR pr ml l) x (deepL r mr sf) else
         let 'MkSplit l x r := searchDigit p vlpm sf vr in
         MkSplit (deepR pr m l) x (Data.Maybe.maybe Empty digitToTree r)
     end.

#[global] Program Definition search {v : Type} {a : Type} `{Measured v a}
   : (v -> v -> bool) -> FingerTree v a -> SearchResult v a :=
  fun p t =>
    let vt := measure t in
    let p_right := p vt GHC.Base.mempty in
    let p_left := p GHC.Base.mempty vt in
    if Bool.Sumbool.sumbool_of_bool (andb p_left p_right) then OnLeft else
    if Bool.Sumbool.sumbool_of_bool (andb (negb p_left) p_right)
    then let 'MkSplit l x r := (@searchTree _ _ _ _ _ _) p GHC.Base.mempty t
                                 GHC.Base.mempty in
         Position l x r else
    if Bool.Sumbool.sumbool_of_bool (andb (negb p_left) (negb p_right))
    then OnRight else
    Nowhere.
Solve Obligations with (core_inhabitant).

#[global] Definition splitDigit {v} {a} `{(Measured v a)}
   : (v -> bool) -> v -> Digit a -> Split (option (Digit a)) a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | _, i, One a => GHC.Prim.seq i (MkSplit None a None)
    | p, i, Two a b =>
        let va := GHC.Base.mappend i (measure a) in
        if p va : bool then MkSplit None a (Some (One b)) else
        MkSplit (Some (One a)) b None
    | p, i, Three a b c =>
        let va := GHC.Base.mappend i (measure a) in
        let vab := GHC.Base.mappend va (measure b) in
        if p va : bool then MkSplit None a (Some (Two b c)) else
        if p vab : bool then MkSplit (Some (One a)) b (Some (One c)) else
        MkSplit (Some (Two a b)) c None
    | p, i, Four a b c d =>
        let va := GHC.Base.mappend i (measure a) in
        let vab := GHC.Base.mappend va (measure b) in
        let vabc := GHC.Base.mappend vab (measure c) in
        if p va : bool then MkSplit None a (Some (Three b c d)) else
        if p vab : bool then MkSplit (Some (One a)) b (Some (Two c d)) else
        if p vabc : bool then MkSplit (Some (Two a b)) c (Some (One d)) else
        MkSplit (Some (Three a b c)) d None
    end.

#[global] Definition splitNode {v} {a} `{(Measured v a)}
   : (v -> bool) -> v -> Node v a -> Split (option (Digit a)) a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | p, i, Node2 _ a b =>
        let va := GHC.Base.mappend i (measure a) in
        if p va : bool then MkSplit None a (Some (One b)) else
        MkSplit (Some (One a)) b None
    | p, i, Node3 _ a b c =>
        let va := GHC.Base.mappend i (measure a) in
        let vab := GHC.Base.mappend va (measure b) in
        if p va : bool then MkSplit None a (Some (Two b c)) else
        if p vab : bool then MkSplit (Some (One a)) b (Some (One c)) else
        MkSplit (Some (Two a b)) c None
    end.

Fixpoint splitTree {v a} `{Measured v a} `{HsToRocq.Err.Default a} (arg_0__
                     : v -> bool) (arg_1__ : v) (arg_2__ : FingerTree v a) : Split (FingerTree v a)
                                                                                   a
  := match arg_0__, arg_1__, arg_2__ with
     | _, _, Empty => illegal_argument (GHC.Base.hs_string__ "splitTree")
     | _, _, Single x => MkSplit Empty x Empty
     | p, i, Deep _ pr m sf =>
         let vpr := GHC.Base.mappend i (measure pr) in
         let vm := GHC.Base.mappend vpr (measure m) in
         if p vpr : bool
         then let 'MkSplit l x r := splitDigit p i pr in
              MkSplit (Data.Maybe.maybe Empty digitToTree l) x (deepL r m sf) else
         if p vm : bool
         then let 'MkSplit ml xs mr := splitTree p vpr m in
              let 'MkSplit l x r := splitNode p (GHC.Base.mappend vpr (measure ml)) xs in
              MkSplit (deepR pr ml l) x (deepL r mr sf) else
         let 'MkSplit l x r := splitDigit p vm sf in
         MkSplit (deepR pr m l) x (Data.Maybe.maybe Empty digitToTree r)
     end.

#[global] Program Definition split {v : Type} {a : Type} `{Measured v a}
   : (v -> bool) -> FingerTree v a -> (FingerTree v a * FingerTree v a)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Empty => pair Empty Empty
    | p, xs =>
        let 'MkSplit l x r := (@splitTree _ _ _ _ _ _) p GHC.Base.mempty xs in
        if Bool.Sumbool.sumbool_of_bool (p (measure xs)) then pair l (consTree x r) else
        pair xs Empty
    end.
Solve Obligations with (core_inhabitant).

#[global] Definition takeUntil {v : Type} {a : Type} `{Measured v a}
   : (v -> bool) -> FingerTree v a -> FingerTree v a :=
  fun p => Data.Tuple.fst GHC.Base.∘ split p.

#[global] Definition dropUntil {v : Type} {a : Type} `{Measured v a}
   : (v -> bool) -> FingerTree v a -> FingerTree v a :=
  fun p => Data.Tuple.snd GHC.Base.∘ split p.

#[global] Definition reverseDigit {a} {b} : (a -> b) -> Digit a -> Digit b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, One a => One (f a)
    | f, Two a b => Two (f b) (f a)
    | f, Three a b c => Three (f c) (f b) (f a)
    | f, Four a b c d => Four (f d) (f c) (f b) (f a)
    end.

#[global] Definition reverseNode {v2} {a2} {a1} {v1} `{(Measured v2 a2)}
   : (a1 -> a2) -> Node v1 a1 -> Node v2 a2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Node2 _ a b => node2 (f b) (f a)
    | f, Node3 _ a b c => node3 (f c) (f b) (f a)
    end.

Fixpoint reverseTree {v2} {a2} {a1} {v1} `{(Measured v2 a2)} (arg_0__
                       : (a1 -> a2)) (arg_1__ : FingerTree v1 a1) : FingerTree v2 a2
  := match arg_0__, arg_1__ with
     | _, Empty => Empty
     | f, Single x => Single (f x)
     | f, Deep _ pr m sf =>
         deep (reverseDigit f sf) (reverseTree (reverseNode f) m) (reverseDigit f pr)
     end.

#[global] Definition reverse {v : Type} {a : Type} `{Measured v a}
   : FingerTree v a -> FingerTree v a :=
  reverseTree GHC.Base.id.

Module Notations.
Notation "'_Data.FingerTree.:>_'" := (op_ZCzg__).
Infix "Data.FingerTree.:>" := (_:>_) (at level 99).
Notation "'_Data.FingerTree.:<_'" := (op_ZCzl__).
Infix "Data.FingerTree.:<" := (_:<_) (at level 99).
Notation "'_Data.FingerTree.><_'" := (op_zgzl__).
Infix "Data.FingerTree.><" := (_><_) (at level 99).
End Notations.

(* External variables:
     Bool.Sumbool.sumbool_of_bool Eq Gt Lt None Some Type andb bool comparison false
     list negb op_zt__ option pair true Corelib.Init.Datatypes.app
     Corelib.Program.Basics.compose Data.Foldable.Foldable Data.Foldable.foldMap
     Data.Foldable.foldMap'__ Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl'__ Data.Foldable.foldl__ Data.Foldable.foldr
     Data.Foldable.foldr'__ Data.Foldable.foldr__ Data.Foldable.length__
     Data.Foldable.null__ Data.Foldable.product__ Data.Foldable.sum__
     Data.Foldable.toList Data.Foldable.toList__ Data.Functor.op_zlzdzg__
     Data.Maybe.maybe Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum Data.Tuple.fst
     Data.Tuple.snd GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup GHC.Base.String GHC.Base.build'
     GHC.Base.compare GHC.Base.compare__ GHC.Base.const GHC.Base.flip GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.foldr GHC.Base.id GHC.Base.mappend GHC.Base.mappend__
     GHC.Base.max__ GHC.Base.mconcat__ GHC.Base.mempty GHC.Base.mempty__
     GHC.Base.min__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zg____ GHC.Base.op_zgze____ GHC.Base.op_zl__ GHC.Base.op_zl____
     GHC.Base.op_zlzd____ GHC.Base.op_zlze____ GHC.Base.op_zlzlzgzg__
     GHC.Base.op_zlzlzgzg____ GHC.Base.op_zlztzg__ GHC.Base.op_zsze__
     GHC.Base.op_zsze____ GHC.Base.pure GHC.Err.error GHC.Err.patternFailure
     GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Prim.seq
     HsToRocq.Err.Build_Default HsToRocq.Err.Default Stdlib.ZArith.BinInt.Z.eqb
     Stdlib.ZArith.BinInt.Z.ltb
*)
