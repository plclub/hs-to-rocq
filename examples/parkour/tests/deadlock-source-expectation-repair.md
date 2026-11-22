# Source expectation syntax repair

The v1 prose manifest remains unchanged. The original expectation file had
not typechecked: generated Choreo2's unqualified notation conflicts with ITree,
the generated constructor Arguments require explicit declarations after the
section, and BinNat's numeral scope is not imported by Require.

The v2 digest freezes the first typechecked expectation file, before proving
the ordering cases. It changes imports/local aliases, constructor application
syntax, and the spelling of binary one. It does not change a role, outcome,
queue, program, or affirmative/negative proposition in the prose manifest.
The v1 digest is retained as a historical record, not a passing rerun check.
