(* add type and promote appear here, including the promoted dependency. *)
Check MkToken : bool -> Token.
Example type_phase_value : typePhaseValue = true := eq_refl.
Example promoted_leaf_value : promotedLeaf = true := eq_refl.
Example promoted_dependency_value : promotedSeed = true := eq_refl.

(* Ordinary values and add stay after this boundary, even with an order edit. *)
Fail Check ordinaryValue.
Fail Check termPhaseValue.
Fail Check zOrdered.
