# Local-effect contracts

Source `Locally` and target `Exec` use the same
[`local_model`](../theories/Semantics/LocalEffects.v). Each branch receives the
current shared store. The local tests exercise this model independently of the
generated choreography and network.

[`LocalEffectContracts.v`](Semantics/LocalEffectContracts.v) and its
[witnesses](Semantics/LocalEffectWitnesses.v) fix a `Get : request bool` at
role 7, store 3: the reply `true` sets the store to 4 and resumes the
continuation with result 11. The tests reject a different role, a blocked
store, and an invented reply. A second event stays suspended after one step.

[`ExactObservations.v`](Semantics/ExactObservations.v) and its
[equivalence proofs](Semantics/ObservationEquivalences.v) characterize return
as a finite view ending in `RetF`. An event step requires a finite view ending
in `VisF`, an enabled typed reply, and resumption at that reply. An infinite
sequence of `Tau` steps admits neither observation.

## Standalone gate

Install the [switch dependencies](../ITREE-INSTALL.md), then run this command
from the repository root:

```sh
opam exec --switch="$switch" --set-switch -- make -C examples/parkour check-deadlock-local
```

The [checker](../scripts/check-deadlock-local.py) verifies
[`deadlock-local-v1.sha256`](deadlock-local-v1.sha256) and
[`deadlock-local-exact.sha256`](deadlock-local-exact.sha256) through the
[namespace mapping](namespace-migration.tsv), then compiles the five modules.
Each of the 20 exports must independently report `Closed under the global
context`. The standalone command writes its evidence under `build/deadlock-local/`;
`check-required` uses the already compiled project and writes the same audits
under `build/run/local/`.
