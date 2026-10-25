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

Require Data.Tuple.
Require GHC.Base.
Import GHC.Base.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

#[global] Definition op_zlzdzg__ {f : Type -> Type} {a : Type} {b : Type}
  `{GHC.Base.Functor f}
   : (a -> b) -> f a -> f b :=
  GHC.Base.fmap.

Notation "'_<$>_'" := (op_zlzdzg__).

Infix "<$>" := (op_zlzdzg__) (at level 99).

#[global] Definition op_zlzazg__ {f : Type -> Type} {a : Type} {b : Type}
  `{GHC.Base.Functor f}
   : f a -> (a -> b) -> f b :=
  fun as_ f => op_zlzdzg__ f as_.

Notation "'_<&>_'" := (op_zlzazg__).

Infix "<&>" := (_<&>_) (at level 99).

#[global] Definition op_zdzg__ {f : Type -> Type} {a : Type} {b : Type}
  `{GHC.Base.Functor f}
   : f a -> b -> f b :=
  GHC.Base.flip GHC.Base.op_zlzd__.

Notation "'_$>_'" := (op_zdzg__).

Infix "$>" := (op_zdzg__) (at level 99).

#[global] Definition unzip {f : Type -> Type} {a : Type} {b : Type}
  `{GHC.Base.Functor f}
   : f (a * b)%type -> (f a * f b)%type :=
  fun xs => pair (op_zlzdzg__ Data.Tuple.fst xs) (op_zlzdzg__ Data.Tuple.snd xs).

#[global] Definition void {f : Type -> Type} {a : Type} `{GHC.Base.Functor f}
   : f a -> f unit :=
  fun x => GHC.Base.op_zlzd__ tt x.

Module Notations.
Notation "'_Data.Functor.<$>_'" := (op_zlzdzg__).
Infix "Data.Functor.<$>" := (op_zlzdzg__) (at level 99).
Notation "'_Data.Functor.<&>_'" := (op_zlzazg__).
Infix "Data.Functor.<&>" := (_<&>_) (at level 99).
Notation "'_Data.Functor.$>_'" := (op_zdzg__).
Infix "Data.Functor.$>" := (op_zdzg__) (at level 99).
End Notations.

(* External variables:
     Type op_zt__ pair tt unit Data.Tuple.fst Data.Tuple.snd GHC.Base.Functor
     GHC.Base.flip GHC.Base.fmap GHC.Base.op_zlzd__
*)
