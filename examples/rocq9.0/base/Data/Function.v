(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Stdlib.Program.Tactics.
Require Stdlib.Program.Wf.
Require Import Stdlib.Program.WfExtensionality.

(* No imports to convert. *)

(* No type declarations to convert. *)

(* Converted value declarations: *)

(* Skipping definition `Data.Function.fix_' *)

#[global] Definition on {b : Type} {c : Type} {a : Type}
   : (b -> b -> c) -> (a -> b) -> a -> a -> c :=
  fun lop_ziztzi__ f => fun x y => lop_ziztzi__ (f x) (f y).

#[global] Definition op_za__ {a : Type} {b : Type} : a -> (a -> b) -> b :=
  fun x f => f x.

#[global] Definition applyWhen {a : Type} : bool -> (a -> a) -> a -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | true, f, x => f x
    | false, _, x => x
    end.

(* External variables:
     Type bool false true
*)
