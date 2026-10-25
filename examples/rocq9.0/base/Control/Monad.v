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

Require Import GHC.Base.   (* bind notation *)
Open Scope type_scope. (* resolve  (a * b) types *)
(* Converted imports: *)

Require Data.Foldable.
Require Data.Functor.
Require Data.Traversable.
Require GHC.Base.
Require GHC.List.
Require GHC.Prim.
Import Data.Functor.Notations.
Import GHC.Base.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

(* Skipping definition `Control.Monad.guard' *)

#[global] Definition filterM {m : Type -> Type} {a : Type}
  `{GHC.Base.Applicative m}
   : (a -> m bool) -> list a -> m (list a) :=
  fun p =>
    GHC.Base.foldr (fun x =>
                      GHC.Base.liftA2 (fun flg => if flg : bool then (cons x) else GHC.Base.id) (p x))
    (GHC.Base.pure nil).

#[global] Definition op_zgzezg__ {m : Type -> Type} {a : Type} {b : Type} {c
   : Type} `{GHC.Base.Monad m}
   : (a -> m b) -> (b -> m c) -> a -> m c :=
  fun f g => fun x => f x GHC.Base.>>= g.

Notation "'_>=>_'" := (op_zgzezg__).

Infix ">=>" := (_>=>_) (at level 99).

#[global] Definition op_zlzezl__ {m : Type -> Type} {b : Type} {c : Type} {a
   : Type} `{GHC.Base.Monad m}
   : (b -> m c) -> (a -> m b) -> a -> m c :=
  GHC.Base.flip _>=>_.

Notation "'_<=<_'" := (op_zlzezl__).

Infix "<=<" := (_<=<_) (at level 99).

(* Skipping definition `Control.Monad.forever' *)

#[global] Definition mapAndUnzipM {m : Type -> Type} {a : Type} {b : Type} {c
   : Type} `{GHC.Base.Applicative m}
   : (a -> m (b * c)%type) -> list a -> m (list b * list c)%type :=
  fun f xs =>
    Data.Functor.op_zlzdzg__ GHC.List.unzip (Data.Traversable.traverse f xs).

#[global] Definition zipWithM {m} {a} {b} {c} `{_ : GHC.Base.Applicative m}
   : (a -> b -> m c) -> list a -> list b -> m (list c) :=
  fun f xs ys =>
    (@Data.Traversable.sequenceA _ _ _ _ m _ _ _ (GHC.List.zipWith f xs ys)).

#[global] Definition zipWithM_ {m : Type -> Type} {a : Type} {b : Type} {c
   : Type} `{GHC.Base.Applicative m}
   : (a -> b -> m c) -> list a -> list b -> m unit :=
  fun f xs ys => Data.Foldable.sequenceA_ (GHC.List.zipWith f xs ys).

#[global] Definition foldM {t : Type -> Type} {m : Type -> Type} {b : Type} {a
   : Type} `{Data.Foldable.Foldable t} `{GHC.Base.Monad m}
   : (b -> a -> m b) -> b -> t a -> m b :=
  Data.Foldable.foldlM.

#[global] Definition foldM_ {t : Type -> Type} {m : Type -> Type} {b : Type} {a
   : Type} `{Data.Foldable.Foldable t} `{GHC.Base.Monad m}
   : (b -> a -> m b) -> b -> t a -> m unit :=
  fun f a xs => Data.Foldable.foldlM f a xs GHC.Base.>> GHC.Base.return_ tt.

(* Skipping definition `Control.Monad.replicateM' *)

(* Skipping definition `Control.Monad.replicateM_' *)

#[global] Definition unless {f : Type -> Type} `{GHC.Base.Applicative f}
   : bool -> f unit -> f unit :=
  fun p s => if p : bool then GHC.Base.pure tt else s.

#[global] Definition op_zlzdznzg__ {m : Type -> Type} {a : Type} {b : Type}
  `{GHC.Base.Monad m}
   : (a -> b) -> m a -> m b :=
  fun f m =>
    m GHC.Base.>>= (fun x => let z := f x in GHC.Prim.seq z (GHC.Base.return_ z)).

Notation "'_<$!>_'" := (op_zlzdznzg__).

Infix "<$!>" := (op_zlzdznzg__) (at level 99).

(* Skipping definition `Control.Monad.mfilter' *)

Module Notations.
Notation "'_Control.Monad.>=>_'" := (op_zgzezg__).
Infix "Control.Monad.>=>" := (_>=>_) (at level 99).
Notation "'_Control.Monad.<=<_'" := (op_zlzezl__).
Infix "Control.Monad.<=<" := (_<=<_) (at level 99).
Notation "'_Control.Monad.<$!>_'" := (op_zlzdznzg__).
Infix "Control.Monad.<$!>" := (op_zlzdznzg__) (at level 99).
End Notations.

(* External variables:
     Type bool cons list nil op_zt__ tt unit Data.Foldable.Foldable
     Data.Foldable.foldlM Data.Foldable.sequenceA_ Data.Functor.op_zlzdzg__
     Data.Traversable.sequenceA Data.Traversable.traverse GHC.Base.Applicative
     GHC.Base.Monad GHC.Base.flip GHC.Base.foldr GHC.Base.id GHC.Base.liftA2
     GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__ GHC.Base.pure GHC.Base.return_
     GHC.List.unzip GHC.List.zipWith GHC.Prim.seq
*)
