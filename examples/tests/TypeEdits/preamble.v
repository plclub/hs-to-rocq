(* Named aliases let the assertions distinguish annotations from inference. *)
Definition typeEditsSort := Set.
Definition typeEditsBool := bool.

Declare Scope type_edits_value_scope.
Delimit Scope type_edits_value_scope with type_edits_value.
Notation "'typeEditsValue'" := false (at level 0).
Notation "'typeEditsValue'" := true (at level 0) : type_edits_value_scope.

Declare Scope type_edits_constructor_scope.
Delimit Scope type_edits_constructor_scope with type_edits_constructor.
Notation "'typeEditsCarrier'" := unit (at level 0).
Notation "'typeEditsCarrier'" := bool (at level 0) : type_edits_constructor_scope.
