# Tool tests

This directory contains the Haskell test suites, shell integration runners, and
Python audit/build-wiring checks for hs-to-rocq. The Coq 8.20 and Rocq 9.0 Make
wrappers share compiler fixtures in
[`examples/tests/`](../examples/tests/README.md). Base-dependent fixtures remain in
`examples/base-tests/`.

Run the commands below from the repository root.

## Haskell test suites

Run all three Cabal suites with either build tool:

```bash
stack test
# Or, with cabal-install:
cabal test all
```

Use the project's Haskell toolchain (currently GHC 9.10.3); Stack selects it
through `stack.yaml`. The build tool resolves the Haskell dependencies declared
in [`hs-to-rocq.cabal`](../hs-to-rocq.cabal). These suites do not need a Coq/Rocq
compiler, a generated base library, or a separately built translator executable.
The `ci-catalog` suite also requires Bash on `PATH`.

| Suite | Main file | Checks |
| --- | --- | --- |
| `edits` | [`test/Edits.hs`](Edits.hs) | Public edits parser/builder APIs and the finger-tree source-policy invocation boundary. |
| `rocq-version` | [`test/RocqVersion.hs`](RocqVersion.hs) | Target-version parsing and AST/text namespace rewriting. |
| `ci-catalog` | [`test/CiCatalog.hs`](CiCatalog.hs) | Workflow/catalog agreement, `/ci-fix` delegation, failure propagation, Bash syntax, and catalog regressions. |

To focus on one suite:

| Stack | Cabal |
| --- | --- |
| `stack test hs-to-rocq:edits` | `cabal test edits` |
| `stack test hs-to-rocq:rocq-version` | `cabal test rocq-version` |
| `stack test hs-to-rocq:ci-catalog` | `cabal test ci-catalog` |

The `edits` suite runs the existing **237 parser/API assertions** plus **184
source-policy cases** in [SourcePolicyTests.hs](SourcePolicyTests.hs). The policy
cases invoke the public `runPolicy` boundary with real temporary files, covering
approvals, scopes, file-local aliases, renaming, parsed rewrite pins, handwritten
declaration forms, and diagnostics. Quoted-comment controls require harmless
documentation to pass while following axioms and protected declarations remain
visible to the policy checker. These parser/scanner tests need Haskell;
the Python Make controls below stub Stack and need no Haskell installation.
See the [source-policy brief](../examples/fingertree/SOURCE-POLICY.md) for the
guard's scope and limits.

`CiCatalog` runs its complete self-tests with no arguments. It reads the
workflow, both command documents, and the pinned `ci-catalog-old-head.md`
fixture. Its guards and mutation tests cover the assumption runner's CI wiring,
compiler pins, pinned submodule setup, switch isolation, check ordering, and
unconditional failure propagation. Its shell regressions use stubbed tools;
they do not run the documented builds or regeneration. The `--self-test`
argument remains accepted for direct compatibility:

```bash
stack exec -- runghc -package=yaml test/CiCatalog.hs --self-test
```

## Shell integration checks

Shell runners are explicit checks, not part of `stack test` or `cabal test all`.
They require Bash and standard Unix utilities. The fake-tool harness also needs
Make, but no Haskell or Coq/Rocq toolchain:

```bash
bash test/harness.sh
```

The real-translator checks use Stack to invoke `hs-to-rocq`, so build the
executable with Stack first, even if you ran the Haskell suites with Cabal:

```bash
stack build
bash test/edits.sh
bash test/concurrent.sh
```

Neither script needs a Coq/Rocq compiler or a compiled base library:

- `edits.sh` checks translation output and rejection diagnostics. With no
  arguments it checks both targets; select one with
  `bash test/edits.sh --target-version 8.20` or `--target-version 9.0`.
- `concurrent.sh` runs translators concurrently with a shared Haskell dependency
  on both targets. It checks output files, the absence of shared GHC object
  artifacts by default, and the explicit GHC code-generation override.

The runners use temporary directories and remove them on exit. The
[coverage matrix](../examples/tests/README.md#edit-coverage-matrix) records the
edits API, CLI, and compiler witnesses and their limitations.

## Assumption-audit checks

Run the fingertree assumption, source-inventory, and Make-wiring controls with
Python 3.8+ (standard library), Make on `PATH`, and standard Unix utilities.
This is a separate runner, not part of the Cabal suites:

```bash
python3 test/assumptions.py
```

The default mode runs **48 compiler-independent cases**:

* The 28 cases check theory/priority export inventories, report parsing,
  missing or malformed reports, and exact dependency sets. CLI controls require
  failure when the compiler is missing, prints a plausible report but exits
  nonzero, or exits zero without reports.
* The 20 cases in [source_policy_checks.py](source_policy_checks.py) exercise the
  public source-inventory CLI and production Make rules in temporary layouts.
  They check the 234 protected names, missing/duplicate inventory entries,
  two-way queue coverage, and failure before dependent compilation. Make controls
  cover serial/parallel runs, direct targets, stale outputs, input selection,
  cleanup, and failure propagation. They use the real inventory helper but fake
  Stack, translation, foundations, and proof/compiler stages; the Haskell suite
  above tests the policy parser/scanner itself.

Inventory regressions distinguish real declaration heads from mentions in nested
comments and multiline strings, including doubled-quote escapes. Such mentions
must neither reject a present dictionary nor stand in for a missing one; the
production Make gate is checked for both outcomes.
The theory inventory also checks all seven named assertion forms, so an omitted
`Remark` or `Example` cannot escape the audit by using a different theorem keyword.

To add real compiler controls, use Rocq 9.2:

```bash
# With Rocq 9.2 on PATH:
python3 test/assumptions.py --rocq rocq
# Or select an existing Rocq 9.2 opam switch:
opam exec --switch="${ROCQ92_SWITCH:?Select a Rocq 9.2 switch}" -- \
  python3 test/assumptions.py --rocq rocq
```

This adds **nine cases, for 57 total**. The fixtures under
[`test/assumptions/`](assumptions/) exercise direct and transitive dependencies
on an unexpected axiom, plus an independent closed proof. Both checkers must
accept the exact dependency sets and reject unexpected axioms; the theory CLI
must also reject a nonempty expectation for the closed control and unaudited
assertions that the real compiler accepts. Once `--rocq` is requested, an
unavailable or erroring compiler fails the runner rather than
skipping the real cases or reporting success.

The runner locates its helpers and fixtures relative to the script, independently
of the caller's working directory. All generated inputs, temporary manifests,
logs, and compiler products stay in temporary directories removed on exit.
Neither mode needs Haskell, a generated base, or a built translator; the default
mode also needs no Coq/Rocq installation. These controls test the audit tools and
build wiring, not the finger-tree proofs themselves; use the
[example checks](../examples/fingertree/README.md#build-and-check) for those.

## Compiler and base checks

Build the translator with Stack first. For each command, use the matching
Coq 8.20 or Rocq 9.0 environment with its Equations plugin installed:

```bash
make -C examples/tests
make -C examples/rocq9.0/tests
```

These shared compiler suites do not need the translated base library. Each
Make entry point also runs `edit-checks`: the `edits` Cabal suite via
`stack --allow-different-user test hs-to-rocq:edits`, followed by `test/edits.sh`
for that wrapper's target version. See the
[shared test guide](../examples/tests/README.md#run-the-tests) for focused Make
targets and expected-failure categories.

Base checks require the matching compiler and compiled base library; building
the base also requires the matching `coq_makefile`. Their existing Make entry
points include the relocated `test/deriving.sh` and `test/identity-traversal.sh`
runners:

```bash
# Coq 8.20; requires compiled base/
make -C examples/base-tests
# Rocq 9.0; compiles its base before running the checks
make -C examples/rocq9.0 base
```

The deriving runner also needs the Stack-built translator. The traversal runner
locates the repository relative to its script path and compiles
`examples/base-tests/IdentityTraversal.v`. The fake-tool harness exercises this
runner from the repository root and both Make caller directories with Git
rejecting repository access. See
[deriving and base integration](../examples/tests/README.md#deriving-and-base-integration)
for direct commands, prerequisites, and the scope of the assumption checks.

## Local CI and validation records

Use [`.claude/commands/ci.md`](../.claude/commands/ci.md) for the authoritative
seven-job catalog and compiler environments;
[`ci-fix.md`](../.claude/commands/ci-fix.md) adds repair guidance.
The existing `build-haskell` job runs the Haskell suites, then the harness,
concurrent translation, and default assumption-audit checks as separate steps.
The existing `test-rocq9` job keeps the Rocq 9.0 suite first, then uses an isolated
Rocq 9.2 switch for the real assumption controls, clean foundations, and full
fingertree checks. Both jobs install Python through the existing setup action.
See the catalog's [test-rocq9 section](../.claude/commands/ci.md#job-test-rocq9)
for the ordered commands and compiler pins. The workflow still has seven jobs;
expected-failure categories are unchanged, and every nonzero check status fails
its job.

The [historical validation records](../examples/tests/README.md#issue-228-validation)
remain scoped to their recorded revisions. This guide describes commands and
coverage, not a new verification result.
