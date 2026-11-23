# Well-formedness expectation import repair

The original `DeadlockWellFormedExpect.v` digest was
`ba772f535fb5d0b5d4ebd37f6d9beb77b89dec247d7a8a5661066ae68487a160`.
The corrected digest is
`76728a1d98baa477085221a31c1e6c319b0e86f67dab87f041254828686e820b`;
`DeadlockWellFormedExpect.sha256` now checks this corrected file.

The original `Require Import NArith.BinNat` activates a deprecated notation
under Rocq 9.0.1's strict `-w +all` policy. The repair imports only
`NArith.BinNatDef`, requires `NArith.BinNat` without importing its notations,
and defines a local module name `N` containing `BinNatDef.N` and the transparent
alias `eq_dec := BinNat.N.eq_dec`. No warning override is used.
Every original declaration, comment, example, and proposition after the import
line is byte-identical. The added module preserves the existing `N.eq_dec`
spelling. No role, codec, program, quantifier, or expected outcome changed.

`DeadlockWellFormedPartialExpect.v` is unchanged. Its digest remains
`e9f4ddf94de4ae5dac8496d40384fcf24becacb48d979e640e7df4805da49e1b`.

## Conversion diagnostic

The independent side-by-side diagnostic in
`build/well-formed-import-repair/` reconstructs the genuine original by replacing
the new six-line header with its original single import line. It checks the
reconstructed bytes against the original digest above before compiling.
The original compiles with `rocq c -q` and default warning policy, not a warning
override; the corrected fixture and every subsequent diagnostic compile through
`parkour_rocq.py` with `+all`.

`OriginalExpect` and `CorrectedExpect` are separate compiled modules.
`OriginalPartial` and `CorrectedPartial` differ only in which expectation module
they import. `Conversion.v` proves 30 equalities with `eq_refl`: all 24 original
definitions and all six partial-expectation definitions, including every
affirmative and negative expected proposition. These are kernel conversion
checks, not merely matching theorem names or comparing printed text.

## Production validation, 2026-11-22

The focused validation compiled the actual repository sources, not repaired
diagnostic substitutes, using Rocq 9.0.1, `parkour_rocq.py`, `+all`, and a
120-second timeout per compilation. To reproduce these checks with the
standard build, activate the Rocq switch and run:

```sh
make -C examples/parkour check-required
```

Both expectation manifests pass `shasum -a 256 -c` from the repository root.
Fresh `check-assumptions.py closed` queries against the compiled production
modules report `Closed under the global context` for exactly these 19 lemmas:

- `DeadlockWellFormed.structural_head`
- `DeadlockWellFormed.structural_head_roles`
- `DeadlockWellFormed.structural_wire`
- `DeadlockWellFormedCases.participants_distinct`
- `DeadlockWellFormedCases.local_prefix_results`
- `DeadlockWellFormedCases.opposed_bind_heads`
- `DeadlockWellFormedCases.empty_bind_rejected`
- `DeadlockWellFormedCases.bool_wire`
- `DeadlockWellFormedCases.communicating_accepted`
- `DeadlockWellFormedCases.located_accepted`
- `DeadlockWellFormedCases.two_receivers_rejected`
- `DeadlockWellFormedCases.absent_receiver_rejected`
- `DeadlockWellFormedCases.wrong_codec_rejected`
- `DeadlockWellFormedCases.self_accepted`
- `DeadlockWellFormedCases.empty_complete_impossible`
- `DeadlockWellFormedCases.empty_partial_related`
- `DeadlockWellFormedCases.empty_partial_continuations_disagree`
- `DeadlockWellFormedCases.empty_bind_partial_obligation_rejected`
- `DeadlockWellFormedCases.other_constructors_accepted`

Production compiler logs, individual assumption logs, and the exact export list
are in `build/well-formed-import-repair/`. This focused check does not claim that
the full Parkour build or the generated EPP assumption audit ran.
