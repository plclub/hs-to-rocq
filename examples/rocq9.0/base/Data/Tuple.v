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


(* No imports to convert. *)

(* No type declarations to convert. *)

(* Converted value declarations: *)

#[global] Definition fst {a : Type} {b : Type} : (a * b)%type -> a :=
  fun '(pair x _) => x.

#[global] Definition snd {a : Type} {b : Type} : (a * b)%type -> b :=
  fun '(pair _ y) => y.

#[global] Definition curry {a : Type} {b : Type} {c : Type}
   : ((a * b)%type -> c) -> a -> b -> c :=
  fun f x y => f (pair x y).

#[global] Definition uncurry {a : Type} {b : Type} {c : Type}
   : (a -> b -> c) -> (a * b)%type -> c :=
  fun f p => f (fst p) (snd p).

#[global] Definition swap {a : Type} {b : Type}
   : (a * b)%type -> (b * a)%type :=
  fun '(pair a b) => pair b a.

(* External variables:
     Type op_zt__ pair
*)
