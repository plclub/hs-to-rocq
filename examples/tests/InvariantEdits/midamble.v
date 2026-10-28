(* The edit must retain the raw representation and add a distinct sigma type. *)
Check MkFlag_Raw : bool -> RawFlag.
Check Flag : Type.
Check @projT1 RawFlag EnabledInv : Flag -> RawFlag.

(* The raw representation admits false, but the sigma type requires evidence. *)
Example raw_flag_can_be_invalid : valid (MkFlag_Raw false) = false := eq_refl.
Fail Definition invalid_sigma : Flag :=
  @existT RawFlag EnabledInv (MkFlag_Raw false) eq_refl.
