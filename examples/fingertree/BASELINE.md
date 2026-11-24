# Unchanged-tool baseline: checkpoint 3

This records the baseline requested on 2026-11-01, before changing the
translator for fingertree. The branch was `fingertree`, at
`e4bc91ccc9f039deb352896dae75709c892cb03c` throughout the run. All project commands
ran inside `/Users/liyao/Workspace/hs-to-coq/.claude/worktrees/fingertree` or one
of its subdirectories. The pre-report verification timestamp was
`2026-11-02 03:01:50 UTC` (still November 1 locally).

The six non-HLint catalog jobs passed with the local toolchains described below.
The exact HLint job is **BLOCKED**: the available version is 3.5, not CI's 3.6.1.
Its supplemental 3.5 run passed. Rocq compilation passed with core/runtime 9.0.1,
not CI's pinned 9.0.0. This is therefore not an exact seven-job CI pass.

## Seven-job result

Jobs ran sequentially in the catalog's order. `build-haskell`, including the
harness and concurrent checks, passed before every job that depends on it.
Every executed catalog command exited 0; no baseline failure was repaired.

| Workflow job | Result | Exit status and evidence | Main log |
| --- | --- | --- | --- |
| `hlint` | **BLOCKED** for 3.6.1 | Selected HLint is 3.5. Supplemental `hlint src/lib src/exe`: 0, `No hints`. | `01-hlint35-supplemental.log` |
| `build-haskell` | **PASS** | All five commands: 0. GHC 9.10.3; all three Haskell suites; 225 harness checks; both concurrent targets and explicit code-generation override. | `02-build-haskell.log` |
| `test-coq-files` | **PASS** | All 24 commands: 0. All ten directory builds, all three opam lints, and the resource example passed on Coq 8.20.1. | `03-test-coq-files.log` |
| `tests` | **PASS** | All 17 commands: 0. Shared suite, base tests, base-thy, and all ten small-example builds passed on Coq 8.20.1. | `04-tests.log` |
| `test-rocq9` | **PASS**, local 9.0.1 | Clean: 0; regenerate/build/base checks: 0; shared suite: 0. CI's exact 9.0.0 compiler was not exercised. | `05-test-rocq9.log` |
| `test-rocq9-translation` | **PASS** | Clean, fresh generation, tracked comparison with `HEAD`, and non-ignored untracked-file check: all 0. | `06-test-rocq9-translation.log` |
| `test-translation` | **PASS** | All 15 commands: 0. Base, containers, GHC, and graph comparisons passed. Catalog containers generation was a no-op; an additional clean regeneration also passed. | `07-test-translation.log` |

All log basenames in this document are relative to:

```text
/var/folders/3c/qfxwcbpj7q590cwh0_scnyl80000gn/T/opencode/fingertree-baseline-20261101
```

The log parent was inspected with `ls` before logs were created.

## Toolchains and local differences from CI

| Component | Verified local value | CI relationship |
| --- | --- | --- |
| Host | macOS 14.5, build 23F79, arm64 | Native local checks, not Ubuntu/Bookworm Docker setup or cache validation. |
| Stack | 3.11.1, `/opt/homebrew/bin/stack` | Catalog's local `stack build` / `stack test` commands used. |
| Selected GHC | 9.10.3, verified by `stack exec -- ghc --numeric-version` | Matches CI. The executable was built in this worktree. |
| Bash | 5.3.20, `/opt/homebrew/bin/bash` | Shell checks used this Bash. |
| GNU Make | 3.81, `/usr/bin/make` | Every catalog unbounded `make -j` was replaced with bounded `make -j2`. Plain serial Make commands stayed plain; Rocq's existing `-j2` stayed `-j2`. |
| Git | 2.55.0 | Only read-only Git inspection/comparison commands were used. |
| HLint | 3.5, `/Users/liyao/.cabal/bin/hlint` | Does not match 3.6.1; its run is supplemental only. |
| opam | 2.5.1 | Existing switches used without changing the global switch or installing packages. |
| Coq switch | `coq820`: Coq/core/stdlib 8.20.1, OCaml 4.14.2 | Matches the `tests` compiler pin and the 8.20 compiler family in `test-coq-files`. |
| Coq plugins | `coq-equations` 1.3.1+8.20; MathComp ssreflect/boot/order 2.5.0 | Required Equations and MathComp versions present. |
| Rocq switch | `rocq9`: prover 9.0.0, core/runtime 9.0.1, stdlib 9.0.0, OCaml 4.14.2 | `rocq --version` reports 9.0.1. CI pins prover/core/runtime/stdlib all to 9.0.0. |
| Rocq plugin | `rocq-equations` 1.3.1+9.0 | Matches CI. |
| GNU sed | 4.10, `/opt/homebrew/opt/gnu-sed/libexec/gnubin/sed` | GNU sed was exposed as `sed` for generation. |
| lndir | 1.0.5, `/opt/homebrew/bin/lndir` | Available for base, containers, and GHC manual-file linking. |
| Locale | `LANG=en_US.UTF-8`, `LC_ALL=en_US.UTF-8` | Host provides this UTF-8 locale, not CI's `C.utf8`. `common.mk` exports `LANG=C.utf8`; `LC_ALL` retained the available host locale. |

Compiler jobs inherited these environment settings:

```bash
env LANG=en_US.UTF-8 LC_ALL=en_US.UTF-8 \
  PATH="/opt/homebrew/opt/gnu-sed/libexec/gnubin:$PATH" \
  opam exec --switch=coq820 -- <command>

env LANG=en_US.UTF-8 LC_ALL=en_US.UTF-8 \
  PATH="/opt/homebrew/opt/gnu-sed/libexec/gnubin:$PATH" \
  opam exec --switch=rocq9 -- <command>
```

The two translation-only jobs activated no compiler environment. No old compiler
job used the global `cs2-rocq92` environment. The shared Rocq test wrapper retained
`rocq c -w +deprecated-dirpath-Coq`.

The catalog's submodule-update commands were replaced by read-only pin checks:
the requested source submodules were already initialized correctly, and this
task prohibited Git-state changes. All four source repositories were clean,
reported `--is-shallow-repository=true`, and matched these `HEAD` gitlinks:

| Source submodule | Verified commit |
| --- | --- |
| `examples/ghc/ghc` | `3f4d7d38b9661435bdde981451ac50c4335ed090` |
| `examples/containers/containers` | `4fda06c43ea14f808748aa8988158946c3ce0caf` |
| `examples/graph/graph` | `aa50a612706761a060598a84bae450ba2a575adf` |
| `examples/core-semantics/ghc-core-smallstep` | `ba02ee8c10d82d92c9c5fa6c33806f5a72440b96` |

The initial preflight mistakenly named the core-semantics source directory
`examples/core-semantics/core-semantics`; Git rejected that pathspec and the
preflight stopped. The corrected inventory used `ghc-core-smallstep` before any
job ran. The original diagnostic remains in `00-preflight.log`.

## Preparation and clean inspection

The following worktree-local documents were read before execution:

- `test/README.md`
- `examples/tests/README.md`
- `.claude/commands/ci.md`
- `.github/workflows/hs-to-rocq.yml`
- `.github/actions/setup-hs-to-rocq/action.yml`
- `CLAUDE.md`

Before jobs, `git status --short`, `git diff`, and `git diff --cached` showed no
unstaged tracked changes. The only staged work was the requested `.gitmodules`
addition and the new fingertree gitlink at
`2f303a410c95802a2824b6dd54a0610fa5329858`. Existing untracked work under
`examples/fingertree/` comprised `README.md`, `edits`, `lib/`, `module-edits/`, and
`theories/`; those paths were preserved.

The clean rules were read in both base generators, the Rocq parent and shared
test rules, and the containers, GHC, and graph Makefiles. Before each destructive
sequence, scoped status/diff and untracked-file inventories were checked, and
`make -n ... clean` showed the affected paths. There was no user work in those
paths. Ignored files removed by later cleans were artifacts of this baseline's
own completed builds.

Fresh compilation started without pre-existing project outputs. The later
`tests` job reused the base/base-thy compilation just completed by
`test-coq-files`, as expected when running the catalog sequentially in one
checkout. Regeneration jobs actually cleaned their prescribed output trees;
they did not rely on those compiled copies.

Top-level command execution was fail-fast: Bash used `-e -o pipefail`, or a
sequential subprocess runner printed each command and exit status and stopped
on the first nonzero result. Logging pipelines retained `pipefail`. Existing
test categories and Make recipes were unchanged.

## Executed checks

### HLint and Haskell prerequisite

The supplemental lint commands were `hlint --version` and
`hlint src/lib src/exe`; both exited 0. The latter printed `No hints`.

The `build-haskell` commands ran from the worktree root in this order:

| Command | Exit | Observed result |
| --- | --- | --- |
| `stack build` | 0 | Built all 81 library modules and the local executable with GHC 9.10.3. |
| `stack exec -- ghc --numeric-version` | 0 | `9.10.3` |
| `stack test` | 0 | `edits`: 237 assertions; `rocq-version`: 805 assertions; `ci-catalog`: PASS, including 63 reported self-test cases. |
| `bash test/harness.sh` | 0 | `Passed 225 harness checks.` |
| `bash test/concurrent.sh` | 0 | 8.20 concurrent translations, 9.0 concurrent translations, and explicit GHC code-generation override all passed. |

### `test-coq-files`

All commands used `opam exec --switch=coq820`. First, these three commands each
exited 0:

```bash
opam lint base/coq-hs-to-rocq-base.opam
opam lint base-thy/coq-hs-to-rocq-base-thy.opam
opam lint examples/containers/coq-hs-to-rocq-containers.opam
```

In each directory below, `coq_makefile -f _CoqProject -o Makefile` ran first,
followed by `make -j2`, both with that directory as the process working directory.
Both commands exited 0 in every row. Rows preserve the catalog order.

| Working directory | Successful `COQC` invocations |
| --- | ---: |
| `base` | 54 |
| `base-thy` | 15 |
| `examples/containers/lib` | 14 |
| `examples/containers/theories` | 37 |
| `examples/transformers/lib` | 14 |
| `examples/graph/lib` | 6 |
| `examples/graph/theories` | 11 |
| `examples/ghc/lib` | 99 |
| `examples/ghc/theories` | 31 |
| `examples/core-semantics/lib` | 1 |

These builds compiled 282 files, including the full graph theories target and
all 31 enabled GHC theories, including `RecoveryChecks.v`. The final root command
`coqc -Q base "" examples/resources/list_monad.v` also exited 0, for 283 compiler
invocations in total. Job elapsed time: 439.40 seconds.

### `tests`

All commands used `opam exec --switch=coq820`. Unless another working directory
is shown, commands ran from the root. Every row exited 0.

| Working directory | Command | Observed result |
| --- | --- | --- |
| `base` | `coq_makefile -f _CoqProject -o Makefile` | Makefile generated. |
| root | `make -j2 -C base` | Existing completed base build up to date. |
| root | `make -C examples/tests` | 67 `PASS`, 3 expected `TODO_PASS` compiler failures; 237 edits assertions and 32 real-translator edits CLI cases. |
| root | `make -C examples/base-tests` | 18 `PASS`, 3 expected compiler failures; 26 deriving CLI cases; 14 closed traversal assumption reports. |
| `base-thy` | `coq_makefile -f _CoqProject -o Makefile` | Makefile generated. |
| root | `make -j2 -C base-thy` | Existing completed base-thy build up to date. |
| root | `make -C examples/compiler` | 8 files compiled. |
| root | `make -C examples/rle` | 2 files compiled. |
| root | `make -C examples/quicksort` | 3 files compiled. |
| root | `make -C examples/dlist` | 2 files compiled. |
| root | `make -C examples/coinduction` | 2 files compiled. |
| root | `make -C examples/intervals` | 4 files compiled. |
| root | `make -C examples/successors` | 2 files compiled. |
| root | `make -C examples/lambda` | 2 files compiled. |
| root | `make -C examples/simple` | 1 file compiled. |
| `examples/bag` | `coq_makefile -f _CoqProject -o Makefile` | Makefile generated. |
| root | `make -C examples/bag` | 8 files compiled. |

The expected shared-suite failures were `MutrecInst`, `TopBind`, and
`ExceptInDataDefinition`. The expected base-test failures were `Arrow`, `EqList`,
and `PaperExamples`. These were successful category checks, not ignored Make
errors. Job elapsed time: 95.96 seconds.

### `test-rocq9`

After verifying the GHC source pin and clean paths, these root commands ran
under `opam exec --switch=rocq9`:

| Command | Exit | Observed result |
| --- | --- | --- |
| `make -C examples/rocq9.0 clean` | 0 | Removed base and test outputs using the existing clean targets. |
| `make -j2 -C examples/rocq9.0 base` | 0 | Missing base regenerated through the parent rule: 34 translator invocations, 54 compiled files, 26 deriving cases, 14 closed traversal assumption reports. |
| `make -C examples/rocq9.0/tests` | 0 | 67 `PASS`, the same 3 expected shared-suite compiler failures, 237 edits assertions, and 32 edits CLI cases. |

Job elapsed time: 65.95 seconds. This result is specifically for the local
9.0.1 compiler with 9.0.0 stdlib/prover and the 1.3.1+9.0 Equations plugin.

### Translation-only comparisons

Both jobs compared generated tracked files with `HEAD` and separately rejected
new non-ignored files. They did not stage output. Every command below exited 0.

`test-rocq9-translation`, from the root:

```bash
make -C examples/rocq9.0/base-src clean
make -C examples/rocq9.0/base-src vfiles
git diff --exit-code HEAD -- examples/rocq9.0/base
test -z "$(git ls-files --others --exclude-standard -- examples/rocq9.0/base)"
```

The fresh serial generation invoked the translator 34 times. Job elapsed time:
16.81 seconds. This clean removed the compiled Rocq base produced by the earlier
compiler job.

`test-translation`, from the root, preserving the catalog's order and its plain
containers `vfiles` invocation:

```bash
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
```

Fresh generation invoked the translator 34 times for base, 51 times for GHC,
and 6 times for graph. The containers command reported nothing to do and invoked
no translator. All four tracked comparisons were empty, and all four untracked
checks passed. Job elapsed time: 676.75 seconds, including 656.75 seconds for GHC
generation.

#### Supplemental fresh containers comparison

Because the prescribed containers command was a no-op, the following additional
sequence checked for stale convenience copies. The containers clean rule and
affected tracked, untracked, and ignored files were inspected first. These were
root commands with the same UTF-8/GNU-sed environment and no compiler activation;
every command exited 0:

```bash
make -C examples/containers clean
make -C examples/containers vfiles
git diff --exit-code HEAD -- examples/containers/lib examples/containers/hs-spec
test -z "$(git ls-files --others --exclude-standard -- examples/containers/lib examples/containers/hs-spec)"
```

All seven generated library modules and `IntSetProperties` were translated:
8 translator invocations. Both output trees matched `HEAD`, including the
specification tree that the catalog does not compare. Elapsed time: 12.76
seconds. Log: `09-containers-clean-regenerate.log`.

Successful generation logs contain GHC's initial deriving diagnostics and some
interface-lookup notices. The unchanged translator recovered the requested
derivations and produced the checked outputs; all enclosing translator/Make
commands and comparisons returned 0. No source, edit, or expected outcome was
changed to obtain these results.

## Final state and handoff

- Generated tracked differences: **none**. Final `git diff --exit-code HEAD --`
  for `base`, `examples/containers/lib`, `examples/containers/hs-spec`,
  `examples/ghc/lib`, `examples/graph/lib`, and `examples/rocq9.0/base` exited 0.
  Their combined non-ignored untracked-file check also exited 0.
- The staged diff remained identical. SHA-256 of
  `git diff --cached --binary`, before and after execution, was
  `adef9d5c8e0c924295e496dc2da5142006a901f2488c32fba581f9649f29383a`.
  The staged changes still consisted only of `.gitmodules` and the fingertree gitlink at
  `2f303a410c95802a2824b6dd54a0610fa5329858`.
- `git diff --exit-code` found no unstaged tracked changes. This report is the
  only authored addition. Existing fingertree files were preserved. There were
  no commits, staging operations, pushes, translator/fixture edits, agent spawns,
  or changes to an `examples/rocq9.2` tree.
- The completed compiler results refer to the logged builds. Later catalog and
  supplemental cleans removed compiled outputs from base, Rocq base, GHC
  library/theories, graph library, and containers library/specification/theories.
  Their generated sources remain available and match `HEAD`.
- Checkpoint 3 is recorded with an exact-version HLint gap and the stated Rocq
  patch-version difference. Fingertree translation and its full proofs remain
  gated on the later translation checkpoint; these baseline checks concern the
  unchanged tool and existing examples.

Additional evidence logs:

| Log | Contents |
| --- | --- |
| `00-preflight.log` | Initial status, unstaged/cached diffs, staged-diff hash, branch/HEAD, and the rejected core-semantics pathspec. |
| `00-preflight-tools.log` | Correct source pins, selected executables/versions, switches, locale availability, and initial clean output-path status. |
| `03-compiler-preflight.log` | Installed package inventories, compiler versions, and switch-specific compiler/Makefile paths. |
| `05-rocq-clean-inspection.log` | Clean-path inventories, GHC pin check, and Rocq parent clean dry run. |
| `06-rocq-translation-clean-inspection.log` | No generated diff before the second Rocq clean; inventory of this run's build artifacts. |
| `07-translation-clean-inspection.log` | GNU sed/lndir checks, output/source status and pin checks, and base/GHC/graph clean dry runs. |
| `08-step-summary.log` | Extracted command/exit-status and suite summaries for the catalog run. |
| `09-containers-clean-inspection.log` | Supplemental clean dry run and full affected-artifact inventory. |
| `10-counts.log` | Compiler, fixture, CLI, closed-report, and generation counts extracted from the actual logs. |
| `11-final-verification.log` | Host/package versions, final source pin check, unchanged HEAD/index checks, and final generated-output comparisons before this report was added. |
| `12-report-state.log` | After this report was added: expected untracked report, unchanged HEAD/staged diff, no unstaged tracked changes, and successful generated-output comparisons. |
