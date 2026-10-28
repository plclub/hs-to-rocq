Require Import HsToRocq.Unpeel.
Require Import GHC.Types.

Definition arrow  := (fun (x y :Type) => x -> y).

Definition seq {A} {B} (a : A) (b:B) := b.

(* Coq has no levity polymorphism, so map everything to Type *)
Definition TYPE (_ : RuntimeRep) := Type.

(* GHC 9.10 desugars right operator sections `(op x)` to `rightSection op x` *)
Definition rightSection {a b c : Type} (op : a -> b -> c) (x : b) : a -> c :=
  fun y => op y x.

Class Coercible a b := { coerce : a -> b }.

(* Empty Notations module for generated code that imports GHC.Prim.Notations *)
Module Notations.
End Notations.

(* HasCallStack is a trivial constraint in Coq — always satisfiable *)
Class HasCallStack := {}.
#[global] Instance hasCallStack : HasCallStack := {}.

#[global]
Instance Coercible_Unpeel
  a b c
  {U1 : Unpeel a c}
  {U2 : Unpeel b c}
  : Coercible a b :=
  { coerce x := @repeel b c U2 (@unpeel a c U1 x) }.
