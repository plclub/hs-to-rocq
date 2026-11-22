From Stdlib Require Lists.List NArith.BinNat.
From Stdlib Require Import Strings.String.
Require GHC.Base.

(* Network constructors carry the sender's Show and receiver's Read
   capability. The concrete backend performs the actual wire I/O. *)
#[mode="-"] Class Show (a : Type) := show : a -> GHC.Base.String.
#[mode="-"] Class Read (a : Type) := read : GHC.Base.String -> option a.
Definition matches (x y : GHC.Base.String) := List.list_eq_dec BinNat.N.eq_dec x y.

#[global] Instance show_bool : Show bool :=
  fun b => if b then GHC.Base.hs_string__ "True" else GHC.Base.hs_string__ "False".
#[global] Instance read_bool : Read bool :=
  fun s => if matches s (GHC.Base.hs_string__ "True") then Some true
           else if matches s (GHC.Base.hs_string__ "False") then Some false
           else None.
#[global] Instance show_unit : Show unit := fun _ => GHC.Base.hs_string__ "()".
#[global] Instance read_unit : Read unit :=
  fun s => if matches s (GHC.Base.hs_string__ "()") then Some tt else None.
