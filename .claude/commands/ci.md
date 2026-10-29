---
description: Run the seven GitHub Actions job checks locally with verified prerequisites
allowed-tools: Bash, Read, Glob, Grep
argument-hint: "[job-name] (hlint|build-haskell|test-coq-files|tests|test-rocq9|test-rocq9-translation|test-translation|all; aliases: build, test-coq)"
---

Run the checks from `.github/workflows/hs-to-rocq.yml` locally and report their results. This file is the shared command catalog for `/ci` and `/ci-fix`. Read the current workflow, `.github/actions/setup-hs-to-rocq/action.yml`, and the root `CLAUDE.md` before running it. The commands reproduce the job checks, not Docker setup, permissions, or caching.

Run from the workspace root using relative paths. `/ci` reports failures; use `/ci-fix` when repairs are requested.

The argument is: $ARGUMENTS

## Select jobs

An empty argument or `all` selects all seven jobs in this order. Otherwise, select the named workflow job or its legacy alias. If the name is not listed, ask for a valid job name.

| Workflow job | Local alias | Requires `build-haskell` to pass first |
| --- | --- | --- |
| `hlint` | | No |
| `build-haskell` | `build` | No |
| `test-coq-files` | `test-coq` | No |
| `tests` | | Yes |
| `test-rocq9` | | Yes |
| `test-rocq9-translation` | | Yes |
| `test-translation` | | Yes |

For a single job, also run its prerequisite unless it already passed for the current source state. Report that prerequisite separately. Run jobs sequentially in this checkout: regeneration and compilation share output directories. In particular, never run Rocq tests alongside a Rocq clean or regeneration.

Stop a job at its first failed command and record the command and exit status. Continue independent selected jobs, but mark jobs with failed prerequisites as `BLOCKED`. Run multi-command blocks in fail-fast Bash as shown; keep nonzero statuses visible.

## Verify prerequisites and protect local work

Inspect `git status --short`, `git diff`, and `git diff --cached` before running checks. Builds write artifacts, and clean/regeneration steps remove or replace output trees. Before those steps, inspect the relevant Makefile's `clean` rule and all affected paths, including untracked files. If they contain user work, stop that job and ask how to preserve it. Leave unrelated changes and the index intact; do not automatically stash, reset, stage, or commit.

Check the tools for the selected jobs rather than assuming they are installed:

| Job | Required tools and CI versions |
| --- | --- |
| `hlint` | HLint 3.6.1; check `command -v hlint` and `hlint --version`. |
| `build-haskell` and its dependents | Stack with GHC 9.10.3, Bash, make, and Git. After building, verify with `stack exec -- ghc --numeric-version`. |
| `test-coq-files` | Coq 8.20, `coq_makefile`, opam, MathComp 2.5.0, and `coq-equations.1.3.1+8.20` (CI image: `mathcomp/mathcomp:2.5.0-coq-8.20`). |
| `tests` | `coq.8.20.1`, `coq_makefile`, and `coq-equations.1.3.1+8.20`. This job does not require MathComp. |
| `test-rocq9` | `rocq-prover`, `rocq-core`, `rocq-runtime`, and `rocq-stdlib`, all 9.0.0; `rocq-equations.1.3.1+9.0`; `rocq` and the matching `coq_makefile`. |
| Translation jobs | No Coq/Rocq compiler required. `test-translation` also needs `lndir` and GNU sed for GHC regeneration. |

Report missing prerequisites and version mismatches alongside the affected results. Use a UTF-8 locale available on the host; CI uses `LANG=C.utf8`. On macOS, ensure GNU sed is exposed as `sed` for GHC regeneration; see `CLAUDE.md`, "GHC example".

### Per-job compiler environments

Coq 8.20 and Rocq 9.0 need separate environments. The compiler blocks below use `opam exec` so selecting one job does not change the global switch or contaminate the next job's `PATH`.

Use `opam switch list --short` to discover existing switches. Set `COQ820_SWITCH` and `ROCQ90_SWITCH` to the appropriate names in the command environment; these are not prescribed switch names. Before each compiler job, inspect `opam list --switch="$COQ820_SWITCH" --installed` or its Rocq equivalent for the packages above. Verify the selected compiler and Makefile tool:

```bash
opam exec --switch="${COQ820_SWITCH:?Select a Coq 8.20 switch}" -- coqc --version
opam exec --switch="$COQ820_SWITCH" -- sh -c 'command -v coq_makefile'
```

```bash
opam exec --switch="${ROCQ90_SWITCH:?Select a Rocq 9.0 switch}" -- rocq --version
opam exec --switch="$ROCQ90_SWITCH" -- sh -c 'command -v coq_makefile'
```

For a non-opam installation, use an equivalent isolated environment and verify both tools there. Do not use whichever `coqc` happens to be on the global `PATH`: Rocq also supplies that compatibility command. Direct local Stack commands below omit container-only flags; shared Makefiles and check scripts already include `--allow-different-user` where needed and should run unchanged.

## Test result criteria

Success is exit status 0. The test Makefiles already account for expected failures; any nonzero `make` status, including 2, is a failure to investigate.

The shared unit suites define categories in `examples/tests/test-rules.mk`, not their wrapper Makefiles. `examples/base-tests/Makefile` defines its own `PASS` and `TODO_PASS` cases.

| Category | Result target | Required outcome |
| --- | --- | --- |
| `PASS` | `TestName.pass` | Translation exits zero, produces a `.v` file, and compilation succeeds. |
| `TODO_PASS` | `TestName.fail` | Translation exits zero and produces a `.v` file, but compilation fails. |
| `TODO_TRANSLATE` | `TestName.fail_translate` | Translation fails or produces no output. Successful translation that produces a `.v` file is unexpected, regardless of compilation. |

An unexpected success is also a test failure. For targeted reruns and repairs, see `ci-fix.md`, "Unit-test failures".

## Job: hlint

After verifying the HLint version:

```bash
hlint src/lib src/exe
```

## Job: build-haskell

```bash
bash -e -o pipefail <<'BASH'
stack build
stack exec -- ghc --numeric-version
stack exec -- runghc -package=yaml examples/tests/checks/CiCatalog.hs --self-test
stack exec -- runghc -package=hs-to-rocq examples/tests/checks/RocqVersion.hs
bash examples/tests/checks/harness.sh
bash examples/tests/checks/concurrent.sh
BASH
```

The catalog check validates job coverage, prerequisites, `/ci-fix` delegation, failure propagation, and Bash syntax without running builds or regeneration. Its self-tests include the pinned old catalog and mutations. The remaining steps check direct version parsing/rewriting, harness failure propagation with fake tools, and concurrent real translations for both targets. The concurrent check also verifies the explicit GHC code-generation override. None requires a Coq/Rocq compiler; they do not replace the compiler suites.

## Job: test-coq-files

Use the Coq 8.20 environment with MathComp and Equations. This job compiles checked-in convenience copies; it does not regenerate them. Build the full graph theories target, not a hand-picked subset.

```bash
opam exec --switch="${COQ820_SWITCH:?Select a Coq 8.20 switch}" -- bash -e -o pipefail <<'BASH'
opam lint base/coq-hs-to-rocq-base.opam
opam lint base-thy/coq-hs-to-rocq-base-thy.opam
opam lint examples/containers/coq-hs-to-rocq-containers.opam

(cd base && coq_makefile -f _CoqProject -o Makefile)
make -j -C base
(cd base-thy && coq_makefile -f _CoqProject -o Makefile)
make -j -C base-thy

(cd examples/containers/lib && coq_makefile -f _CoqProject -o Makefile)
make -j -C examples/containers/lib
(cd examples/containers/theories && coq_makefile -f _CoqProject -o Makefile)
make -j -C examples/containers/theories

(cd examples/transformers/lib && coq_makefile -f _CoqProject -o Makefile)
make -j -C examples/transformers/lib

(cd examples/graph/lib && coq_makefile -f _CoqProject -o Makefile)
make -j -C examples/graph/lib
(cd examples/graph/theories && coq_makefile -f _CoqProject -o Makefile)
make -j -C examples/graph/theories

(cd examples/ghc/lib && coq_makefile -f _CoqProject -o Makefile)
make -j -C examples/ghc/lib
(cd examples/ghc/theories && coq_makefile -f _CoqProject -o Makefile)
make -j -C examples/ghc/theories

(cd examples/core-semantics/lib && coq_makefile -f _CoqProject -o Makefile)
make -j -C examples/core-semantics/lib

coqc -Q base "" examples/resources/list_monad.v
BASH
```

## Job: tests

Use the Coq 8.20 environment with Equations. The MathComp-dependent resource example belongs to `test-coq-files`, not this job.

```bash
opam exec --switch="${COQ820_SWITCH:?Select a Coq 8.20 switch}" -- bash -e -o pipefail <<'BASH'
(cd base && coq_makefile -f _CoqProject -o Makefile)
make -j -C base

make -C examples/tests
make -C examples/base-tests

(cd base-thy && coq_makefile -f _CoqProject -o Makefile)
make -j -C base-thy

make -C examples/compiler
make -C examples/rle
make -C examples/quicksort
make -C examples/dlist
make -C examples/coinduction
make -C examples/intervals
make -C examples/successors
make -C examples/lambda
make -C examples/simple
(cd examples/bag && coq_makefile -f _CoqProject -o Makefile)
make -C examples/bag
BASH
```

## Job: test-rocq9

Use the Rocq 9.0 environment with Equations. Check for local work before the submodule update and clean. The top-level `base` target must regenerate the missing base after clean; do not replace this sequence with compilation of the existing copy.

```bash
opam exec --switch="${ROCQ90_SWITCH:?Select a Rocq 9.0 switch}" -- bash -e -o pipefail <<'BASH'
git submodule update --init examples/ghc/ghc
make -C examples/rocq9.0 clean
make -j2 -C examples/rocq9.0 base
make -C examples/rocq9.0/tests
BASH
```

The test wrapper selects `--target-version 9.0` and compiles with `rocq c -w +deprecated-dirpath-Coq` through the shared rules. Keep that warning check enabled.

## Translation comparison criteria

Both translation jobs compare generated output with `HEAD`. CI stages output in its disposable checkout. Locally, the commands below compare tracked files and check for new, non-ignored files without changing the index. Both checks must succeed. On a difference, show `git diff --stat HEAD -- <output-path>` and list untracked files with `git ls-files --others --exclude-standard -- <output-path>`; leave the output available for review.

Existing uncommitted output changes also differ from `HEAD`. Do not call them a passing round trip or discard them to make the comparison pass. `/ci-fix` describes how to handle an intentional baseline update.

## Job: test-rocq9-translation

This is a translation-only job; it does not activate the Rocq compiler environment.

```bash
bash -e -o pipefail <<'BASH'
git submodule update --init examples/ghc/ghc
make -C examples/rocq9.0/base-src clean
make -C examples/rocq9.0/base-src vfiles
git diff --exit-code HEAD -- examples/rocq9.0/base
test -z "$(git ls-files --others --exclude-standard -- examples/rocq9.0/base)"
BASH
```

## Job: test-translation

Check `lndir` and GNU sed before starting. Initialize only the requested submodules, not GHC's nested submodules. Preserve the workflow's regeneration order and its plain `vfiles` invocation for containers.

```bash
bash -e -o pipefail <<'BASH'
git submodule update --init examples/ghc/ghc examples/containers/containers
git submodule update --init --depth 1 examples/graph/graph

make -C examples/base-src clean
make -C examples/base-src vfiles
git diff --exit-code HEAD -- base
test -z "$(git ls-files --others --exclude-standard -- base)"

make -C examples/containers vfiles
git diff --exit-code HEAD -- examples/containers/lib
test -z "$(git ls-files --others --exclude-standard -- examples/containers/lib)"

make -C examples/ghc clean
make -C examples/ghc vfiles
git diff --exit-code HEAD -- examples/ghc/lib
test -z "$(git ls-files --others --exclude-standard -- examples/ghc/lib)"

make -C examples/graph clean
make -C examples/graph vfiles
git diff --exit-code HEAD -- examples/graph/lib
test -z "$(git ls-files --others --exclude-standard -- examples/graph/lib)"
BASH
```

## Summary

Report each executed step, then a table with one row for each of the seven workflow job names. Use `PASS` only when every required step passed, `FAIL` for a failed check, `BLOCKED` for a missing prerequisite or unsafe regeneration, and `SKIP` for an unrequested job. Include tool versions, failed commands and statuses, blocked/skipped reasons, and any files changed by generation.

Claim that `all` passed only when all seven jobs passed. A partial run, a different toolchain, or a pending comparison with `HEAD` must remain explicit.
