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
Require Corelib.Program.Basics.
Require Data.FingerTree.
Require Data.Foldable.
Require Data.OldList.
Require Data.SemigroupInternal.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require GHC.Prim.
Require HsToRocq.DeferredFix.
Import Control.Arrow.Notations.
Import Data.FingerTree.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Prio k v : Type := | NoPrio : Prio k v | MkPrio : k -> v -> Prio k v.

Inductive Entry k v : Type := | MkEntry : k -> v -> Entry k v.

Inductive PQueue k v : Type :=
  | MkPQueue : (Data.FingerTree.FingerTree (Prio k v) (Entry k v)) -> PQueue k v.

Arguments NoPrio {_} {_}.

Arguments MkPrio {_} {_} _ _.

Arguments MkEntry {_} {_} _ _.

Arguments MkPQueue {_} {_} _.

(* Midamble *)

Require Import HsToRocq.Err.
Require Import FingerTreeProofs.CoreSize.

(* The source's partial branches use `error`; Coq needs an arbitrary result
   inhabitant.  The adjacent core midamble supplies the same kind of local
   default for `FingerTree`.  This is internal error infrastructure, not a
   public operation premise. *)
#[local] Instance DefaultPQueue {k v : Type} : Default (PQueue k v) :=
  {| default := MkPQueue Data.FingerTree.Empty |}.

(* Raw structural size of the queue's underlying finger tree.  Cached Prio
   measurements are ignored.  This helper is retained for the termination
   analysis and later correctness work; the measure obligation itself is not
   discharged. *)
Definition pqueue_size {k v : Type} (q : PQueue k v) : nat :=
  match q with MkPQueue t => size t end.
(* Converted value declarations: *)

#[local] Definition Functor__Entry_fmap {inst_k : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> Entry inst_k a -> Entry inst_k b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, MkEntry k v => MkEntry k (f v)
      end.

#[local] Definition Functor__Entry_op_zlzd__ {inst_k : Type}
   : forall {a : Type},
     forall {b : Type}, a -> Entry inst_k b -> Entry inst_k a :=
  fun {a : Type} {b : Type} => Functor__Entry_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__Entry {k : Type} : GHC.Base.Functor (Entry k) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__Entry_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__Entry_op_zlzd__ |}.

#[local] Definition Foldable__Entry_foldMap {inst_k : Type}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Entry inst_k a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, MkEntry _ v => f v end.

#[local] Definition Foldable__Entry_fold {inst_k : Type}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Entry inst_k m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Entry_foldMap GHC.Base.id.

#[local] Definition Foldable__Entry_foldr {inst_k : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Entry inst_k a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Entry_foldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__Entry_foldl' {inst_k : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Entry inst_k a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__Entry_foldr (fun arg_0__ arg_1__ =>
                                 match arg_0__, arg_1__ with
                                 | x, k => (fun '(z) => GHC.Prim.seq z (k (f z x)))
                                 end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__Entry_foldMap' {inst_k : Type}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Entry inst_k a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__Entry_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__Entry_foldl {inst_k : Type}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Entry inst_k a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Entry_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                 GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__Entry_foldr' {inst_k : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Entry inst_k a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__Entry_foldl (fun arg_0__ arg_1__ =>
                                 match arg_0__, arg_1__ with
                                 | k, x => (fun '(z) => GHC.Prim.seq z (k (f x z)))
                                 end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__Entry_length {inst_k : Type}
   : forall {a : Type}, Entry inst_k a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__Entry_foldl' (fun arg_0__ arg_1__ =>
                              match arg_0__, arg_1__ with
                              | c, _ => c GHC.Num.+ #1
                              end) #0.

#[local] Definition Foldable__Entry_null {inst_k : Type}
   : forall {a : Type}, Entry inst_k a -> bool :=
  fun {a : Type} => Foldable__Entry_foldr (fun arg_0__ arg_1__ => false) true.

#[local] Definition Foldable__Entry_product {inst_k : Type}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Entry inst_k a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getProduct
                                   (Foldable__Entry_foldMap' Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__Entry_sum {inst_k : Type}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Entry inst_k a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getSum
                                   (Foldable__Entry_foldMap' Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__Entry_toList {inst_k : Type}
   : forall {a : Type}, Entry inst_k a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Entry_foldr c n t)).

#[global]
Program Instance Foldable__Entry {k : Type}
   : Data.Foldable.Foldable (Entry k) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Foldable__Entry_fold ;
           Data.Foldable.foldMap__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Entry_foldMap ;
           Data.Foldable.foldMap'__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__Entry_foldMap' ;
           Data.Foldable.foldl__ := fun (b : Type) (a : Type) => Foldable__Entry_foldl ;
           Data.Foldable.foldl'__ := fun (b : Type) (a : Type) => Foldable__Entry_foldl' ;
           Data.Foldable.foldr__ := fun (a : Type) (b : Type) => Foldable__Entry_foldr ;
           Data.Foldable.foldr'__ := fun (a : Type) (b : Type) => Foldable__Entry_foldr' ;
           Data.Foldable.length__ := fun (a : Type) => Foldable__Entry_length ;
           Data.Foldable.null__ := fun (a : Type) => Foldable__Entry_null ;
           Data.Foldable.product__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__Entry_product ;
           Data.Foldable.sum__ := fun (a : Type) `(GHC.Num.Num a) => Foldable__Entry_sum ;
           Data.Foldable.toList__ := fun (a : Type) => Foldable__Entry_toList |}.

#[global] Definition unionPrio {k} {v} `{GHC.Base.Ord k}
   : Prio k v -> Prio k v -> Prio k v :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | x, NoPrio => x
    | NoPrio, y => y
    | (MkPrio kx _ as x), (MkPrio ky _ as y) =>
        if kx GHC.Base.<= ky : bool then x else
        y
    end.

#[local] Definition Semigroup__Prio_op_zlzlzgzg__ {inst_k : Type} {inst_v
   : Type} `{GHC.Base.Ord inst_k}
   : Prio inst_k inst_v -> Prio inst_k inst_v -> Prio inst_k inst_v :=
  unionPrio.

#[global]
Program Instance Semigroup__Prio {k : Type} {v : Type} `{GHC.Base.Ord k}
   : GHC.Base.Semigroup (Prio k v) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Prio_op_zlzlzgzg__ |}.

#[local] Definition Monoid__Prio_mappend {inst_k : Type} {inst_v : Type}
  `{GHC.Base.Ord inst_k}
   : Prio inst_k inst_v -> Prio inst_k inst_v -> Prio inst_k inst_v :=
  _GHC.Base.<<>>_.

#[local] Definition Monoid__Prio_mempty {inst_k : Type} {inst_v : Type}
  `{GHC.Base.Ord inst_k}
   : Prio inst_k inst_v :=
  NoPrio.

#[local] Definition Monoid__Prio_mconcat {inst_k : Type} {inst_v : Type}
  `{GHC.Base.Ord inst_k}
   : list (Prio inst_k inst_v) -> Prio inst_k inst_v :=
  GHC.Base.foldr Monoid__Prio_mappend Monoid__Prio_mempty.

#[global]
Program Instance Monoid__Prio {k : Type} {v : Type} `{GHC.Base.Ord k}
   : GHC.Base.Monoid (Prio k v) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Prio_mappend ;
           GHC.Base.mconcat__ := Monoid__Prio_mconcat ;
           GHC.Base.mempty__ := Monoid__Prio_mempty |}.

#[local] Definition Measured__Prio__Entry_measure {inst_k : Type} {inst_v
   : Type} `{GHC.Base.Ord inst_k}
   : Entry inst_k inst_v -> Prio inst_k inst_v :=
  fun '(MkEntry k v) => MkPrio k v.

#[global]
Program Instance Measured__Prio__Entry {k : Type} {v : Type} `{GHC.Base.Ord k}
   : Data.FingerTree.Measured (Prio k v) (Entry k v) :=
  fun _ k__ =>
    k__ {| Data.FingerTree.measure__ := Measured__Prio__Entry_measure |}.

#[local] Definition Functor__PQueue_fmap {inst_k : Type} `{GHC.Base.Ord inst_k}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> PQueue inst_k a -> PQueue inst_k b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, MkPQueue xs => MkPQueue (Data.FingerTree.fmap' (GHC.Base.fmap f) xs)
      end.

#[local] Definition Functor__PQueue_op_zlzd__ {inst_k : Type} `{GHC.Base.Ord
  inst_k}
   : forall {a : Type},
     forall {b : Type}, a -> PQueue inst_k b -> PQueue inst_k a :=
  fun {a : Type} {b : Type} => Functor__PQueue_fmap GHC.Base.∘ GHC.Base.const.

#[global]
Program Instance Functor__PQueue {k : Type} `{GHC.Base.Ord k}
   : GHC.Base.Functor (PQueue k) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun (a : Type) (b : Type) => Functor__PQueue_fmap ;
           GHC.Base.op_zlzd____ := fun (a : Type) (b : Type) =>
             Functor__PQueue_op_zlzd__ |}.

#[global] Definition below {k} {v} `{GHC.Base.Ord k} : k -> Prio k v -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, NoPrio => false
    | k, MkPrio k' _ => k' GHC.Base.<= k
    end.

#[global] Definition minViewWithKey {k v : Type} `{GHC.Base.Ord k}
   : PQueue k v -> option (k * v * PQueue k v) :=
  fun '(MkPQueue q) =>
    if Data.FingerTree.null q
    then None
    else match Data.FingerTree.measure q with
         | MkPrio k v =>
             let 'pair l r := Data.FingerTree.split (below k) q in
             Some (pair (pair k v) (match Data.FingerTree.viewl r with
                         | Data.FingerTree.op_ZCzl__ _ r' => MkPQueue (l Data.FingerTree.>< r')
                         | _ => GHC.Err.error (GHC.Base.hs_string__ "can't happen")
                         end))
         | _ => GHC.Err.patternFailure
         end.

#[global] Definition minView {k : Type} {v : Type} `{GHC.Base.Ord k}
   : PQueue k v -> option (v * PQueue k v)%type :=
  fun q =>
    GHC.Base.fmap (Data.Tuple.snd Control.Arrow.*** GHC.Base.id) (minViewWithKey q).

#[local] Definition Foldable__PQueue_foldMap {inst_k : Type} `{GHC.Base.Ord
  inst_k} {m : Type} {a : Type} `{GHC.Base.Monoid m}
   : (a -> m) -> PQueue inst_k a -> m :=
  HsToRocq.DeferredFix.deferredFix2 (fun Foldable__PQueue_foldMap
                                     (f : a -> m)
                                     (q : PQueue inst_k a) =>
                                       match minView q with
                                       | None => GHC.Base.mempty
                                       | Some (pair v q') => GHC.Base.mappend (f v) (Foldable__PQueue_foldMap f q')
                                       end).

#[local] Definition Foldable__PQueue_fold {inst_k : Type} `{GHC.Base.Ord inst_k}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, PQueue inst_k m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__PQueue_foldMap GHC.Base.id.

#[local] Definition Foldable__PQueue_foldr {inst_k : Type} `{GHC.Base.Ord
  inst_k}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> PQueue inst_k a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__PQueue_foldMap
                                      (Corelib.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

#[local] Definition Foldable__PQueue_foldl' {inst_k : Type} `{GHC.Base.Ord
  inst_k}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> PQueue inst_k a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__PQueue_foldr (fun arg_0__ arg_1__ =>
                                  match arg_0__, arg_1__ with
                                  | x, k => (fun '(z) => GHC.Prim.seq z (k (f z x)))
                                  end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__PQueue_foldMap' {inst_k : Type} `{GHC.Base.Ord
  inst_k}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> PQueue inst_k a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__PQueue_foldl' (fun acc a => acc GHC.Base.<<>> f a) GHC.Base.mempty.

#[local] Definition Foldable__PQueue_foldl {inst_k : Type} `{GHC.Base.Ord
  inst_k}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> PQueue inst_k a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__PQueue_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                 (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                  GHC.Base.flip f)) t)) z.

#[local] Definition Foldable__PQueue_foldr' {inst_k : Type} `{GHC.Base.Ord
  inst_k}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> PQueue inst_k a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 =>
      fun xs =>
        Foldable__PQueue_foldl (fun arg_0__ arg_1__ =>
                                  match arg_0__, arg_1__ with
                                  | k, x => (fun '(z) => GHC.Prim.seq z (k (f x z)))
                                  end) (GHC.Base.id) xs z0.

#[local] Definition Foldable__PQueue_length {inst_k : Type} `{GHC.Base.Ord
  inst_k}
   : forall {a : Type}, PQueue inst_k a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__PQueue_foldl' (fun arg_0__ arg_1__ =>
                               match arg_0__, arg_1__ with
                               | c, _ => c GHC.Num.+ #1
                               end) #0.

#[local] Definition Foldable__PQueue_null {inst_k : Type} `{GHC.Base.Ord inst_k}
   : forall {a : Type}, PQueue inst_k a -> bool :=
  fun {a : Type} => fun '(MkPQueue q) => Data.FingerTree.null q.

#[local] Definition Foldable__PQueue_product {inst_k : Type} `{GHC.Base.Ord
  inst_k}
   : forall {a : Type}, forall `{GHC.Num.Num a}, PQueue inst_k a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getProduct
                                   (Foldable__PQueue_foldMap' Data.SemigroupInternal.Mk_Product).

#[local] Definition Foldable__PQueue_sum {inst_k : Type} `{GHC.Base.Ord inst_k}
   : forall {a : Type}, forall `{GHC.Num.Num a}, PQueue inst_k a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Corelib.Program.Basics.compose Data.SemigroupInternal.getSum
                                   (Foldable__PQueue_foldMap' Data.SemigroupInternal.Mk_Sum).

#[local] Definition Foldable__PQueue_toList {inst_k : Type} `{GHC.Base.Ord
  inst_k}
   : forall {a : Type}, PQueue inst_k a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__PQueue_foldr c n t)).

#[global]
Program Instance Foldable__PQueue {k : Type} `{GHC.Base.Ord k}
   : Data.Foldable.Foldable (PQueue k) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun (m : Type) `(GHC.Base.Monoid m) =>
             Foldable__PQueue_fold ;
           Data.Foldable.foldMap__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__PQueue_foldMap ;
           Data.Foldable.foldMap'__ := fun (m : Type) (a : Type) `(GHC.Base.Monoid m) =>
             Foldable__PQueue_foldMap' ;
           Data.Foldable.foldl__ := fun (b : Type) (a : Type) => Foldable__PQueue_foldl ;
           Data.Foldable.foldl'__ := fun (b : Type) (a : Type) => Foldable__PQueue_foldl' ;
           Data.Foldable.foldr__ := fun (a : Type) (b : Type) => Foldable__PQueue_foldr ;
           Data.Foldable.foldr'__ := fun (a : Type) (b : Type) => Foldable__PQueue_foldr' ;
           Data.Foldable.length__ := fun (a : Type) => Foldable__PQueue_length ;
           Data.Foldable.null__ := fun (a : Type) => Foldable__PQueue_null ;
           Data.Foldable.product__ := fun (a : Type) `(GHC.Num.Num a) =>
             Foldable__PQueue_product ;
           Data.Foldable.sum__ := fun (a : Type) `(GHC.Num.Num a) => Foldable__PQueue_sum ;
           Data.Foldable.toList__ := fun (a : Type) => Foldable__PQueue_toList |}.

#[global] Definition union {k : Type} {v : Type} `{GHC.Base.Ord k}
   : PQueue k v -> PQueue k v -> PQueue k v :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkPQueue xs, MkPQueue ys => MkPQueue (xs Data.FingerTree.>< ys)
    end.

#[local] Definition Semigroup__PQueue_op_zlzlzgzg__ {inst_k : Type} {inst_v
   : Type} `{GHC.Base.Ord inst_k}
   : PQueue inst_k inst_v -> PQueue inst_k inst_v -> PQueue inst_k inst_v :=
  union.

#[global]
Program Instance Semigroup__PQueue {k : Type} {v : Type} `{GHC.Base.Ord k}
   : GHC.Base.Semigroup (PQueue k v) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__PQueue_op_zlzlzgzg__ |}.

#[local] Definition Monoid__PQueue_mappend {inst_k : Type} {inst_v : Type}
  `{GHC.Base.Ord inst_k}
   : PQueue inst_k inst_v -> PQueue inst_k inst_v -> PQueue inst_k inst_v :=
  _GHC.Base.<<>>_.

#[global] Definition empty {k : Type} {v : Type} `{GHC.Base.Ord k}
   : PQueue k v :=
  MkPQueue Data.FingerTree.empty.

#[local] Definition Monoid__PQueue_mempty {inst_k : Type} {inst_v : Type}
  `{GHC.Base.Ord inst_k}
   : PQueue inst_k inst_v :=
  empty.

#[local] Definition Monoid__PQueue_mconcat {inst_k : Type} {inst_v : Type}
  `{GHC.Base.Ord inst_k}
   : list (PQueue inst_k inst_v) -> PQueue inst_k inst_v :=
  GHC.Base.foldr Monoid__PQueue_mappend Monoid__PQueue_mempty.

#[global]
Program Instance Monoid__PQueue {k : Type} {v : Type} `{GHC.Base.Ord k}
   : GHC.Base.Monoid (PQueue k v) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__PQueue_mappend ;
           GHC.Base.mconcat__ := Monoid__PQueue_mconcat ;
           GHC.Base.mempty__ := Monoid__PQueue_mempty |}.

#[global] Definition assocs {k} {v} `{GHC.Base.Ord k}
   : PQueue k v -> list (k * v)%type :=
  Data.OldList.unfoldr minViewWithKey.

#[local] Definition Eq___PQueue_op_zeze__ {inst_k : Type} {inst_v : Type}
  `{GHC.Base.Ord inst_k} `{GHC.Base.Eq_ inst_v}
   : PQueue inst_k inst_v -> PQueue inst_k inst_v -> bool :=
  fun xs ys => assocs xs GHC.Base.== assocs ys.

#[local] Definition Eq___PQueue_op_zsze__ {inst_k : Type} {inst_v : Type}
  `{GHC.Base.Ord inst_k} `{GHC.Base.Eq_ inst_v}
   : PQueue inst_k inst_v -> PQueue inst_k inst_v -> bool :=
  fun x y => negb (Eq___PQueue_op_zeze__ x y).

#[global]
Program Instance Eq___PQueue {k : Type} {v : Type} `{GHC.Base.Ord k}
  `{GHC.Base.Eq_ v}
   : GHC.Base.Eq_ (PQueue k v) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___PQueue_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___PQueue_op_zsze__ |}.

#[local] Definition Ord__PQueue_compare {inst_k : Type} {inst_v : Type}
  `{GHC.Base.Ord inst_k} `{GHC.Base.Ord inst_v}
   : PQueue inst_k inst_v -> PQueue inst_k inst_v -> comparison :=
  fun xs ys => GHC.Base.compare (assocs xs) (assocs ys).

#[local] Definition Ord__PQueue_op_zl__ {inst_k : Type} {inst_v : Type}
  `{GHC.Base.Ord inst_k} `{GHC.Base.Ord inst_v}
   : PQueue inst_k inst_v -> PQueue inst_k inst_v -> bool :=
  fun x y => Ord__PQueue_compare x y GHC.Base.== Lt.

#[local] Definition Ord__PQueue_op_zlze__ {inst_k : Type} {inst_v : Type}
  `{GHC.Base.Ord inst_k} `{GHC.Base.Ord inst_v}
   : PQueue inst_k inst_v -> PQueue inst_k inst_v -> bool :=
  fun x y => Ord__PQueue_compare x y GHC.Base./= Gt.

#[local] Definition Ord__PQueue_op_zg__ {inst_k : Type} {inst_v : Type}
  `{GHC.Base.Ord inst_k} `{GHC.Base.Ord inst_v}
   : PQueue inst_k inst_v -> PQueue inst_k inst_v -> bool :=
  fun x y => Ord__PQueue_compare x y GHC.Base.== Gt.

#[local] Definition Ord__PQueue_op_zgze__ {inst_k : Type} {inst_v : Type}
  `{GHC.Base.Ord inst_k} `{GHC.Base.Ord inst_v}
   : PQueue inst_k inst_v -> PQueue inst_k inst_v -> bool :=
  fun x y => Ord__PQueue_compare x y GHC.Base./= Lt.

#[local] Definition Ord__PQueue_max {inst_k : Type} {inst_v : Type}
  `{GHC.Base.Ord inst_k} `{GHC.Base.Ord inst_v}
   : PQueue inst_k inst_v -> PQueue inst_k inst_v -> PQueue inst_k inst_v :=
  fun x y => if Ord__PQueue_op_zlze__ x y : bool then y else x.

#[local] Definition Ord__PQueue_min {inst_k : Type} {inst_v : Type}
  `{GHC.Base.Ord inst_k} `{GHC.Base.Ord inst_v}
   : PQueue inst_k inst_v -> PQueue inst_k inst_v -> PQueue inst_k inst_v :=
  fun x y => if Ord__PQueue_op_zlze__ x y : bool then x else y.

#[global]
Program Instance Ord__PQueue {k : Type} {v : Type} `{GHC.Base.Ord k}
  `{GHC.Base.Ord v}
   : GHC.Base.Ord (PQueue k v) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__PQueue_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__PQueue_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__PQueue_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__PQueue_op_zgze__ ;
           GHC.Base.compare__ := Ord__PQueue_compare ;
           GHC.Base.max__ := Ord__PQueue_max ;
           GHC.Base.min__ := Ord__PQueue_min |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.PriorityQueue.FingerTree.Show__PQueue' *)

#[global] Definition singleton {k : Type} {v : Type} `{GHC.Base.Ord k}
   : k -> v -> PQueue k v :=
  fun k v => MkPQueue (Data.FingerTree.singleton (MkEntry k v)).

#[global] Definition insert {k : Type} {v : Type} `{GHC.Base.Ord k}
   : k -> v -> PQueue k v -> PQueue k v :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | k, v, MkPQueue q => MkPQueue (Data.FingerTree.consTree (MkEntry k v) q)
    end.

#[global] Definition add {k : Type} {v : Type} `{GHC.Base.Ord k}
   : k -> v -> PQueue k v -> PQueue k v :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | k, v, MkPQueue q => MkPQueue (Data.FingerTree.snocTree q (MkEntry k v))
    end.

#[global] Definition fromList {k : Type} {v : Type} `{GHC.Base.Ord k}
   : list (k * v)%type -> PQueue k v :=
  Data.Foldable.foldr (Data.Tuple.uncurry insert) empty.

#[global] Definition null {k : Type} {v : Type} `{GHC.Base.Ord k}
   : PQueue k v -> bool :=
  fun '(MkPQueue q) => Data.FingerTree.null q.

(* External variables:
     Gt Lt None Some Type bool comparison false list negb op_zt__ option pair true
     Control.Arrow.op_ztztzt__ Corelib.Program.Basics.compose
     Data.FingerTree.FingerTree Data.FingerTree.Measured Data.FingerTree.consTree
     Data.FingerTree.empty Data.FingerTree.fmap' Data.FingerTree.measure
     Data.FingerTree.measure__ Data.FingerTree.null Data.FingerTree.op_ZCzl__
     Data.FingerTree.op_zgzl__ Data.FingerTree.singleton Data.FingerTree.snocTree
     Data.FingerTree.split Data.FingerTree.viewl Data.Foldable.Foldable
     Data.Foldable.foldMap'__ Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl'__ Data.Foldable.foldl__ Data.Foldable.foldr
     Data.Foldable.foldr'__ Data.Foldable.foldr__ Data.Foldable.length__
     Data.Foldable.null__ Data.Foldable.product__ Data.Foldable.sum__
     Data.Foldable.toList__ Data.OldList.unfoldr Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Endo Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.appEndo
     Data.SemigroupInternal.getDual Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum Data.Tuple.snd Data.Tuple.uncurry GHC.Base.Eq_
     GHC.Base.Functor GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup GHC.Base.build'
     GHC.Base.compare GHC.Base.compare__ GHC.Base.const GHC.Base.flip GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.foldr GHC.Base.hs_string__ GHC.Base.id GHC.Base.mappend
     GHC.Base.mappend__ GHC.Base.max__ GHC.Base.mconcat__ GHC.Base.mempty
     GHC.Base.mempty__ GHC.Base.min__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____ GHC.Base.op_zl____
     GHC.Base.op_zlzd____ GHC.Base.op_zlze__ GHC.Base.op_zlze____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Base.op_zsze__
     GHC.Base.op_zsze____ GHC.Err.error GHC.Err.patternFailure GHC.Num.Int
     GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Prim.seq
     HsToRocq.DeferredFix.deferredFix2
*)
