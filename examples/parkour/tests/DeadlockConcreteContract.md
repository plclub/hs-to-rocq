# Concrete library and client acceptance gate

`theories/DeadlockContract.v` directly type-checks these five real exports:

- `DeadlockFreedom.epp_preserves_deadlock_freedom`
- `DeadlockFreedom.network_run_has_source`
- `DeadlockFreedom.matched_ready`
- `DeadlockFreedom.deadlock_reflection`
- `DeadlockQuorum.quorum_deadlock_freedom`

The first four use the unchanged quantified expectations from
`tests/DeadlockLibraryExpect.v`. The last three library types instantiate the
relation with `DeadlockMatch.matches model stores input R A c`, not a fixture
or a simulation hypothesis. The permanent gate unconditionally imports the
actual library modules and directly references all five qualified constants.
It is intentionally red until those exports exist with the required types.

## Frozen client expectation

`tests/DeadlockQuorumFreedomExpect.v` freezes
`quorum_deadlock_freedom_expected` before any client corollary is provided.
Its SHA-256 is
`51b8f65f751facc8bf3b90e645a29a9a9411fa623363fd7a31278e75ce5ffd37`.

The type quantifies over `E`, `Store`, `Input`, the actual
`local_model Parkour.Runtime.IO E Symbol (Store * Input)`, initial role stores,
and initial input. Its only substantive premise is deadlock freedom of the
actual source `@Main.quorumVoting`, expressed as final-or-enabled at the end of
every finite source run. Its conclusion is final-or-enabled at the end of
every finite network run of the actual generated Root projections.
It fixes exactly `candidate`, `voter1`, `voter2`, and `voter3`, in that order.
Both machines use `shared_model model` and the same initial state.
There is no well-formedness premise and no unconditional progress claim.

`tests/DeadlockConcreteContract.sha256` freezes the independent library
expectation, new client expectation, permanent witnesses, and binder-only
validation module. Its own digest is
`8996f8d5c8167285255418f402fadddccf50ae0f82e44ab913bbbec1a072977d`.
Check it from the repository root:

```
shasum -a 256 -c examples/parkour/tests/DeadlockConcreteContract.sha256
```

## Positive type validation

`tests/DeadlockContractParametric.v` validates all five expected types with
ordinary term binders. These identities do not prove any of the five claims.
They introduce no axioms or admissions. They compile against the actual
`DeadlockMatch` module.

Validation used Rocq 9.0.1 through `opam exec --switch=rocq9`, verified private
ITree pins, the production `parkour_rocq.py` invocation (`-q -w +all` and
warning rejection), and a 120-second per-file timeout. Fresh actual modules
and expectations were compiled in `build/deadlock-concrete-contract-v2`.
Dependencies were recursively compiled from source; generated base,
transformers, manual, local and Parkour library dependencies used existing
production objects. No source theorem was replaced by a test theorem.

An additional `ParametricExact.v` in that evidence directory mechanically
extracts all five type annotations from the permanent gate and compiles each
as `Definition name (w : EXPECTED) : EXPECTED := w`. This checks the exact
permanent annotations, rather than trusting that the hand-written validation
module copied them correctly. Both validations passed without warnings.

The actual client module `DeadlockQuorum` also compiled freshly. An isolated
query requiring that actual module and checking its corollary failed with:

```
The reference DeadlockQuorum.quorum_deadlock_freedom was not found
in the current environment.
```

## Library red-gate status

After concurrent proof repairs, the actual partial `DeadlockFreedom` module
and its updated `DeadlockRoster` dependency compiled freshly without warnings.
The permanent `DeadlockContract.v` then failed specifically on:

```
The reference DeadlockFreedom.epp_preserves_deadlock_freedom
was not found in the current environment.
```

Four separate queries, each requiring the successfully compiled actual
`DeadlockFreedom` module, independently failed on its corresponding missing
qualified export: `epp_preserves_deadlock_freedom`, `network_run_has_source`,
`matched_ready`, and `deadlock_reflection`. Together with the separate client
query above, all five absent exports therefore have independently validated
red diagnostics. These are not syntax, expected-type, or load-path failures.
No fake module or preservation proof was supplied.

`make -C examples/parkour check-final SCRATCH=1` now runs the independent
gate after all slice checks. `check-required` compiles the positive type
validation without treating its binder-only definitions as public proofs.
Under the `ParkourTheories` migration ([`namespace-migration.tsv`](namespace-migration.tsv)
and [`../scripts/frozen_inputs.py`](../scripts/frozen_inputs.py)), the four
files in `DeadlockConcreteContract.sha256` live at
[`Projection/RunCorrespondenceTypes.v`](Projection/RunCorrespondenceTypes.v),
[`Protocols/QuorumProgress.v`](Protocols/QuorumProgress.v),
[`Projection/RunAndProgressTypes.v`](Projection/RunAndProgressTypes.v), and
[`Projection/QuantifiedGuarantees.v`](Projection/QuantifiedGuarantees.v),
checking `ParkourTheories.Projection.RunCorrespondence.network_run_has_source`,
`ParkourTheories.Projection.Progress.{epp_preserves_deadlock_freedom,matched_ready,deadlock_reflection}`,
and `ParkourTheories.Protocols.QuorumVoting.quorum_deadlock_freedom`.
