# Install the Parkour ITree dependencies

[`parkour-deps.opam`](parkour-deps.opam) pins `coq-ext-lib`, `coq-paco`, and
`coq-itree` to immutable Git revisions in the compiler's opam switch (Rocq
9.0.1 or Rocq 9.2.x). The switch must include the `rocq-released` opam
repository (`https://rocq-prover.org/opam/released`) so opam can resolve
`coq-paco` metadata, which is not in the pinned `paco` Git repository.

From the repository root, select the target switch. Add the repository once
if the switch does not already have it, then install the pins:

```sh
switch=cs2-rocq92  # use rocq9 for the Rocq 9.0.1 switch
opam repo add --switch="$switch" rocq-released https://rocq-prover.org/opam/released  # if needed
opam install --switch="$switch" --deps-only ./examples/parkour/parkour-deps.opam
```

| Package | Logical root | Source revision |
| --- | --- | --- |
| `coq-ext-lib.dev` | `ExtLib` | [`dd32f1c56f41d699ed2ffd4193a876c87fc44926`](https://github.com/rocq-community/coq-ext-lib/commit/dd32f1c56f41d699ed2ffd4193a876c87fc44926) |
| `coq-paco.4.2.3` | `Paco` | [`d0561bf7f0a96cac486ba3bd8ca0b72ce01fb9cf`](https://github.com/snu-sf/paco/commit/d0561bf7f0a96cac486ba3bd8ca0b72ce01fb9cf) |
| `coq-itree.dev` | `ITree` | [`a2bc2c38ad998dccadb932559c922139dd957c4f`](https://github.com/DeepSpec/InteractionTrees/commit/a2bc2c38ad998dccadb932559c922139dd957c4f) |

Parkour builds use the installed packages directly. Run the full check in
the same switch:

```sh
opam exec --switch="$switch" --set-switch -- make -C examples/parkour check
```

The [build check](scripts/itree_pins.py) clears Rocq load-path overrides,
checks that the compiler uses the switch's libraries, and rejects missing,
different, or pending pins. Rerun the installation command if a pin is stale.

If an editor still uses the old `build/run/pins` load paths, close its Rocq
session, run `make -C examples/parkour` in your switch, and reopen the project.
You can then delete `examples/parkour/.itree-cache/`.

## Local resumption and assumption checks

`make -C examples/parkour check-deadlock-local`
([`scripts/check-deadlock-local.py`](scripts/check-deadlock-local.py)) and
`make -C examples/parkour check-required` verify the [frozen local resumption
contracts](tests/DEADLOCK-LOCAL-FREEZE.md) and check that all 20 local exports
are closed under the global context:

```sh
opam exec --switch="$switch" --set-switch -- make -C examples/parkour check-deadlock-local
```

This gate compiles [`theories/Semantics/LocalEffects.v`](theories/Semantics/LocalEffects.v)
and the four modules under [`tests/Semantics/`](tests/Semantics/)
(`LocalEffectContracts.v`, `LocalEffectWitnesses.v`, `ExactObservations.v`, and
`ObservationEquivalences.v`), where `LocalEffectWitnesses.finite_action` and
`ObservationEquivalences.step_exact` exercise ITree reply continuation
resumption against the installed switch libraries.

**Opam validation (2026-11-22).** Opam 2.5.1 rebuilt all three pinned packages
in both the Rocq 9.0.1 and Rocq 9.2 (`rocq-core.9.2.0`) switches. In each
switch, `Locate Library` found `ExtLib.Structures.Monad`, `Paco.paco`, and
`ITree.ITree` in that switch's `user-contrib`. The full
`make -C examples/parkour check SCRATCH=1` passed on both compilers, including
the local and public theorem assumption checks.

**Historical private-prefix validation (2026-11-22).** A fresh private root on macOS with Rocq 9.0.1,
Stdlib 9.0.0 and OCaml 4.14.2 passed the initial missing-import checks and
the final resumption check. The installation contained 117 ExtLib, 41 Paco
and 68 ITree `.vo` files. Recompiling `Resume.v` exited 0 without diagnostics;
a separate `Print Assumptions Resume.reply_resumes.` reported
`Closed under the global context`.

The same three Git revisions also built from scratch on macOS with Rocq
9.2 (opam `rocq-core.9.2.0`), Stdlib 9.2.0 and OCaml 5.4.1. The verifier
matched all 226 installed objects to their pinned builds. On both switches,
a smoke file explicitly imported `ExtLib.Structures.Monad`, `Paco.paco` and
`ITree.ITree`, compiled the resumption proof under `-w +all`, and reported
`reply_resumes` closed under the global context.
