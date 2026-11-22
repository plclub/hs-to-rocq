# Abstract run glue contracts

`DeadlockRunsExpect.v` defines six literal contracts without importing the
implementation. Its SHA-256 manifest is `DeadlockRunsExpect.sha256`.
The contracts fix readiness, stuckness, DF, empty traces, prefix extension,
and append composition. They use execution-order lists. They make no source,
network, simulation, or EPP claim.

The original signature-only expectation failed compilation before
`DeadlockRuns.v` existed. The corrected equation contracts were written and
hashed after the implementation, but before `DeadlockRunsCases.v` was written.
This is a retrospective contract correction, not a pre-implementation freeze.
The separately verified expectation-file digest is
`647e7d0ead28e84c72de5f5d0d36b8a01b8f7ad20f69a62e37f093302f3e061f`;
the manifest itself hashes to
`9874357e3c0422a9192628130303e1000cd0fa30e7f8639d21e1af3ae5526ad7`.

## Registration

Implementation: `theories/DeadlockRuns.v`.
Fixed contracts: `tests/DeadlockRunsExpect.v`.
Contract witnesses: `tests/DeadlockRunsCases.v`.

Fixed contract names in `DeadlockRunsExpect`:

- `ready_equation`, `stuck_equation`, `DF_equation`
- `run_empty`, `run_extension`, `run_composition`

Closed contract witnesses in `DeadlockRunsCases`:

- `ready_exact`, `stuck_exact`, `DF_exact`
- `run_empty_exact`, `run_extension_exact`, `run_composition_exact`

Closed implementation proofs in `DeadlockRuns`:

- `run_nil`, `run_snoc_iff`, `run_singleton`
- `run_append`, `run_append_iff`, `run_cons_iff`
- `stuck_iff_not_ready`, `DF_ready`, `DF_after_run`, `DF_no_stuck`
- `ready_stuck_reflection`

## Validation

Rocq 9.0.1 (`opam` switch `rocq9`) compiled all three modules through
`parkour_rocq.py`, which applies `-q -w +all` and rejects printed warnings.
Each of the 17 witnesses/proofs above separately passed
`check-assumptions.py closed`, with a 45-second timeout per command. Every
query returned `Closed under the global context`. The original Rocq 9.2
multi-query assurance module was removed, including its stale build products.

From the repository root, compile the expectation, implementation, and cases
in that order:

```sh
opam exec --switch=rocq9 -- python3 examples/parkour/parkour_rocq.py \
  -Q examples/parkour/theories "" -Q examples/parkour/tests "" FILE
```

For each qualified proof export listed above, run a separate command:

```sh
opam exec --switch=rocq9 -- python3 examples/parkour/check-assumptions.py \
  closed examples/parkour/theories MODULE.EXPORT \
  -Q examples/parkour/tests ""
```

The `DF` definition quantifies over all finite reachable runs and asserts
readiness of their endpoints. Reflection takes a readiness implication as an
explicit lemma premise; no such premise is built into the public predicates.
