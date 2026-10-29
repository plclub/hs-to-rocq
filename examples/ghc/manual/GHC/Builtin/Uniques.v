(* Selected declarations from GHC.Builtin.Uniques. *)
Require Import Coq.Strings.Ascii.
Require Import Coq.NArith.BinNat.
Require GHC.Char.
Require Unique.

Axiom mkBuiltinUnique : nat -> Unique.Unique.

Definition initExitJoinUnique : Unique.Unique :=
  Unique.mkUnique (GHC.Char.hs_char__ "s"%char) 0%N.
