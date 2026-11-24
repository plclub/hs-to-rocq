(* Diagnostics for the isolated foundation build; no additional proof theory. *)
From Stdlib Require Import ssreflect ssrbool ssrfun.

Require Import Proofs.GHC.Base Proofs.GHC.List.
Require Import Proofs.Data.Foldable Proofs.Data.Traversable.
Require Import Proofs.Data.Functor.Identity.

Print LoadPath.
Locate Library GHC.Base.
Locate Library GHC.List.
Locate Library Data.Foldable.
Locate Library Data.Traversable.
Locate Library Data.Functor.Identity.
Locate Library Proofs.GHC.Base.
Locate Library Proofs.GHC.List.
Locate Library Proofs.Data.Foldable.
Locate Library Proofs.Data.Traversable.
Locate Library Proofs.Data.Functor.Identity.
