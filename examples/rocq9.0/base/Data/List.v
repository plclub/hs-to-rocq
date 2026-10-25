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

(* No type declarations to convert. *)

(* Converted value declarations: *)

Fixpoint isSubsequenceOf {a : Type} `{GHC.Base.Eq_ a} (arg_0__ arg_1__ : list a)
  : bool
  := match arg_0__, arg_1__ with
     | nil, _ => true
     | _, nil => false
     | (cons x a' as a), cons y b =>
         if x GHC.Base.== y : bool then isSubsequenceOf a' b else
         isSubsequenceOf a b
     end.

(* External variables:
     Type bool cons false list nil true GHC.Base.Eq_ GHC.Base.op_zeze__
*)
