(* Choreography.Location has an older located type with an Empty constructor.
   Unlike Choreo2.At, this type does not carry equality evidence. *)
Require GHC.Base.

Inductive Located (a : Type) (l : GHC.Base.String) :=
| Wrap : a -> Located a l
| Empty : Located a l.

Definition LegacyUnwrap := forall a l, Located a l -> a.

Lemma no_total_legacy_unwrap (unwrap : LegacyUnwrap) : False.
Proof. destruct (unwrap Empty_set nil (Empty Empty_set nil)). Qed.

Print Assumptions no_total_legacy_unwrap.
