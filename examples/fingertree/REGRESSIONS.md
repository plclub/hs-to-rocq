# Regression records: 2026-11-02

## Full catalog before the unfoldr integration

**Recorded source/test verdict: PASS for all six non-HLint catalog jobs.** Both
normal compiler suites passed all **70 positive fixtures**, versus 67 in the unchanged
[`BASELINE.md`](BASELINE.md), with the same three expected compiler failures.
The automatic constructor-tag and inline-negative checks passed on both targets.
Fresh convenience-copy generation, including supplemental clean containers
generation, matched `HEAD` and the baseline.

The exact HLint 3.6.1 job remains **BLOCKED**; supplemental HLint 3.5 passed with
no hints. Rocq compilation used local core/runtime 9.0.1 rather than CI's pinned
9.0.0, as in the baseline. This is not an exact seven-job CI pass.

**Additional check failure retained:** the supplemental containers Make
`validate` target exited **2** because `coqchk` rejected its external
`../hs-spec/IntSetProperties.vo` argument. Separate kernel checks succeeded for
all 37 containers project modules by logical name, all 11 graph theories, and
all 31 GHC theories. The failed Make invocation was not repaired or hidden.

This full-catalog record supersedes the intermediate 68-fixture report whose
evidence is in `fingertree-regressions-20261101`. The unchanged-tool baseline was
preserved. The results below apply to the frozen source hashes recorded here,
before the shared Makefile hook and isolated 9.2 `unfoldr` restoration.

At the time of that run, the queue compilation checkpoint was still blocked.
The later [targeted follow-up](#targeted-unfoldr-follow-up-2026-11-02) records its
resolution and the passing clean three-module integration. That follow-up did
not rerun the six-job catalog. The lazy-pattern fidelity gap and final
correctness proofs remain open; neither regression run establishes them.

## Run identity and protected state

- Worktree: `/Users/liyao/Workspace/hs-to-coq/.claude/worktrees/fingertree`.
  Every shell invocation used this working directory; child working directories
  remained below it. No implementation was read or copied from another worktree.
- Branch/HEAD: `fingertree`, `e4bc91ccc9f039deb352896dae75709c892cb03c`, unchanged
  from the baseline.
- Preflight: `2026-11-02 13:27:17 UTC`. Pre-report verification:
  `2026-11-02 14:01:21 UTC`.
- Frozen changes tested: functional-dependency erasure after GHC checking;
  ordered full instance-head matching; recursive method emission; typed
  constructor-tag lowering for checked local native ADTs; and well-founded
  recursion after mutual inlining with capture-safe saturated helper expansion.
  The discarded synthetic-match experiment is not part of this source state.
- Only this authored report was replaced. No translator, fixture, expected
  outcome, existing document, Git state, or new fingertree/Rocq 9.2 output tree
  was changed by this run. Old catalog clean targets remained separate from
  those new trees. No agents were spawned.

The catalog, workflow, setup action, root `CLAUDE.md`, both test guides,
`BASELINE.md`, and the current shared test rules were read before execution.
Jobs ran sequentially in catalog order. `build-haskell`, including all suites,
harness, and concurrency checks, passed before dependent jobs began. Runners
printed commands and exit statuses, stopped each job on its first failed command,
and retained `pipefail` through logging. Independent checks continued after the
supplemental Make validation failure.

All full-catalog log basenames below refer to this fresh directory. Its parent
was inspected with `ls` before directory creation:

```text
/var/folders/3c/qfxwcbpj7q590cwh0_scnyl80000gn/T/opencode/fingertree-final-regressions-20261102
```

## Seven catalog jobs against the baseline

| Workflow job | Baseline | Final result | Exit status, difference, and main log |
| --- | --- | --- | --- |
| `hlint` | BLOCKED for 3.6.1; supplemental 3.5 PASS | **BLOCKED** for 3.6.1; supplemental **PASS** | Version check and `hlint src/lib src/exe`: both 0, `No hints`. Same version gap. `01-hlint35-supplemental.log`. |
| `build-haskell` | PASS | **PASS** | All 5 commands: 0; all three suites, 225 harness checks, and 3 concurrency checks. `02-build-haskell.log`. |
| `test-coq-files` | PASS | **PASS** | All 24 commands: 0; complete library/theory targets and resource example. Incremental invocation counts below. `03-test-coq-files.log`. |
| `tests` | PASS; shared 67 / 3 | **PASS**; shared **70 / 3** | All 17 commands: 0; new fixtures and automatic negative checks included; base outcomes unchanged. `04-tests.log`. |
| `test-rocq9` | PASS, local 9.0.1; shared 67 / 3 | **PASS**, local 9.0.1; shared **70 / 3** | Clean, regenerate/build/base checks, normal suite: all 0. Same patch mismatch. `05-test-rocq9.log`. |
| `test-rocq9-translation` | PASS; no generated difference | **PASS**; no generated difference | All 4 commands: 0; clean generation and both comparison checks passed. `06-test-rocq9-translation.log`. |
| `test-translation` | PASS; no generated difference | **PASS**; no generated difference | All 15 commands: 0; generation counts match baseline. Supplemental clean containers comparison also passed. `07-test-translation.log`. |

No catalog command returned nonzero. The extra kernel-validation invocation
that failed is recorded separately below; `validate` is not a baseline catalog
step.

## Tool versions and execution differences

Versions and compiler paths were rechecked during this run.

| Component | Verified value | Relationship to baseline / CI |
| --- | --- | --- |
| Host | macOS 14.5, build 23F79, arm64 | Same native host; Docker setup/cache behavior is outside these local checks. |
| Stack / selected GHC | 3.11.1 / 9.10.3 | Same as baseline; GHC matches CI. `stack build` found the frozen local build up to date. |
| Bash / GNU Make / Git | 5.3.20 / 3.81 / 2.55.0 | Same as baseline. |
| HLint | 3.5 | Supplemental only; exact CI 3.6.1 remains unavailable. |
| opam / OCaml | 2.5.1 / 4.14.2 in both compiler switches | Same as baseline; no package or switch changes. |
| `coq820` | Coq/core/stdlib 8.20.1; Equations 1.3.1+8.20; MathComp 2.5.0 | Matching Coq 8.20 environment. |
| `rocq9` | core/runtime 9.0.1; prover/stdlib 9.0.0; Equations 1.3.1+9.0 | Same as baseline; CI pins all four Rocq packages to 9.0.0. |
| GNU sed / lndir | 4.10 / 1.0.5 | GNU sed exposed as `sed`; both available for generation. |
| Locale | `LANG=en_US.UTF-8`, `LC_ALL=en_US.UTF-8` | Same available host UTF-8 locale, instead of CI's `C.utf8`. `LC_ALL` also covers recipes exporting `LANG=C.utf8`. |

All job commands inherited:

```bash
env LANG=en_US.UTF-8 LC_ALL=en_US.UTF-8 \
  PATH="/opt/homebrew/opt/gnu-sed/libexec/gnubin:$PATH" <command>
```

Coq jobs additionally used `opam exec --switch=coq820 --`; the Rocq compiler job
used `opam exec --switch=rocq9 --`. Compiler and matching `coq_makefile` paths
were verified in each selected environment. No old check used the global
`cs2-rocq92` compiler. Translation-only jobs activated no compiler environment.
The Rocq shared suite retained `rocq c -w +deprecated-dirpath-Coq`.

As in the baseline, bounded `-j2` replaced every catalog unbounded `-j`.
Prescribed serial commands stayed serial, including plain containers `vfiles`;
the Rocq parent's prescribed `-j2` stayed unchanged. Already initialized GHC,
containers, graph, and core-semantics submodules were verified read-only, clean,
shallow, and at the four exact pins in `BASELINE.md`, replacing redundant
state-changing submodule updates.

## Actual commands and counts

Except for the explicitly failed supplemental command below, all commands in
this record exited 0. Commands ran at the worktree root unless another working
directory is stated.

### HLint and Haskell prerequisite

```bash
hlint --version
hlint src/lib src/exe

stack build
stack exec -- ghc --numeric-version
stack test
bash test/harness.sh
bash test/concurrent.sh
```

| Check | Baseline | Final |
| --- | ---: | ---: |
| Edits assertions | 237 | 237 |
| Version/rewrite assertions | 805 | 805 |
| Reported catalog self-test cases | 63 | 63 |
| Harness checks | 225 | 225 |
| Concurrent checks: 8.20, 9.0, explicit GHC code-generation override | 3 | 3 |

All three Haskell suites ran and passed. Supplemental lint: 12.31 seconds;
`build-haskell`: 65.98 seconds.

### `test-coq-files`: Coq 8.20.1

Under `opam exec --switch=coq820 --`, these root commands ran first:

```bash
opam lint base/coq-hs-to-rocq-base.opam
opam lint base-thy/coq-hs-to-rocq-base-thy.opam
opam lint examples/containers/coq-hs-to-rocq-containers.opam
```

In each directory below, the exact command
`coq_makefile -f _CoqProject -o Makefile` ran first, followed by `make -j2`, both
with that directory as the process working directory. Both exited 0 in every
row; rows preserve catalog order.

| Working directory | Baseline `COQC` invocations | Final `COQC` invocations |
| --- | ---: | ---: |
| `base` | 54 | 54 |
| `base-thy` | 15 | 15 |
| `examples/containers/lib` | 14 | 14 |
| `examples/containers/theories` | 37 | 37 |
| `examples/transformers/lib` | 14 | 13 |
| `examples/graph/lib` | 6 | 6 |
| `examples/graph/theories` | 11 | 9 |
| `examples/ghc/lib` | 99 | 99 |
| `examples/ghc/theories` | 31 | 31 |
| `examples/core-semantics/lib` | 1 | 1 |

The complete targets passed, including full graph theories and all 31 enabled
GHC theories with `RecoveryChecks.v`. This incremental checkout reused three
independent up-to-date files: 279 directory-build compiler invocations versus
282 in the fresh baseline. The final root command
`coqc -Q base "" examples/resources/list_monad.v` also passed, giving 280 compiler
invocations versus 283 in the baseline. Elapsed time: 457.36 seconds.

### `tests`: Coq 8.20.1

Every row used `opam exec --switch=coq820 --` and exited 0.

| Working directory | Command | Final result |
| --- | --- | --- |
| `base` | `coq_makefile -f _CoqProject -o Makefile` | Generated Makefile. |
| root | `make -j2 -C base` | Completed base build up to date. |
| root | `make -C examples/tests` | **70 positive / 3 expected failures**; 237 edits assertions, 32 edits CLI cases, 7 tag and 4 inline rejection cases. |
| root | `make -C examples/base-tests` | 18 positive / 3 expected failures; 26 deriving cases; 14 closed traversal assumption reports. |
| `base-thy` | `coq_makefile -f _CoqProject -o Makefile` | Generated Makefile. |
| root | `make -j2 -C base-thy` | Completed base-thy build up to date. |
| root | `make -C examples/compiler` | 8 compiler invocations. |
| root | `make -C examples/rle` | 2 compiler invocations. |
| root | `make -C examples/quicksort` | 3 compiler invocations. |
| root | `make -C examples/dlist` | 2 compiler invocations. |
| root | `make -C examples/coinduction` | 2 compiler invocations. |
| root | `make -C examples/intervals` | 3 compiler invocations; one independent file up to date (baseline: 4). |
| root | `make -C examples/successors` | 2 compiler invocations. |
| root | `make -C examples/lambda` | 2 compiler invocations. |
| root | `make -C examples/simple` | 1 compiler invocation. |
| `examples/bag` | `coq_makefile -f _CoqProject -o Makefile` | Generated Makefile. |
| root | `make -C examples/bag` | 8 compiler invocations. |

All ten small-example targets passed: 33 compiler invocations versus 34 in the
fresh baseline. Elapsed time: 94.66 seconds.

### Supplemental full-theory kernel checks

After the Coq jobs, before later cleans, this generated-Makefile invocation
failed:

```bash
opam exec --switch=coq820 -- make -j2 -C examples/containers/theories validate
```

Exit **2**, elapsed 0.16 seconds. Its `coqchk` command included the external
filename `../hs-spec/IntSetProperties.vo`, producing:

```text
Fatal Error: User error: Cannot find library ../hs-spec/IntSetProperties.vo in loadpath.
make: *** [validate] Error 1
```

The validation sequence stopped there. The baseline catalog contains no
`validate` step. This failure occurred at library-path resolution, before kernel
checking. No Makefile, source, or expected outcome was changed.

A separately recorded direct command checked all 37 logical project modules.
Working directory: `examples/containers/theories`; environment:
`opam exec --switch=coq820 --`. Exact command, exit 0, elapsed 74.25 seconds:

```bash
coqchk -silent -o -Q . "" -Q ../hs-spec "" -Q ../../../base "" \
  -Q ../../../base-thy Proofs -Q ../lib "" \
  CustomTactics OrdTactic OrdTheories SortSorted BitUtils HSUtil SortedUtil \
  SetProofs MapProofs.Common MapProofs.PairTypeclass MapProofs.Bounds \
  MapProofs.Tactics MapProofs.LookupProofs MapProofs.InsertProofs \
  MapProofs.MaxMinProofs MapProofs.DeleteUpdateProofs \
  MapProofs.UnionIntersectDifferenceProofs MapProofs.ToListProofs \
  MapProofs.FilterPartitionProofs MapProofs.ContainerFacts MapProofs.FromListProofs \
  MapProofs.MapFunctionProofs MapProofs.TypeclassProofs MapProofs.InterfaceProofs \
  MapProofs.ProofsWithSets MapProofs IntSetProofs IntSetWordProofs RevNatSlowProofs \
  IntSetUtil DyadicIntervals IntSetProperties IntSetPropertyProofs Set \
  IntMapRecursion IntMapProofs IntMapUnionProofs
```

The independent graph and GHC checks then passed, both from the root under
`opam exec --switch=coq820 --`:

| Command | Coverage | Exit | Seconds |
| --- | --- | ---: | ---: |
| `make -j2 -C examples/graph/theories validate` | All 11 graph theories | 0 | 47.81 |
| `make -j2 -C examples/ghc/theories validate` | All 31 enabled GHC theories | 0 | 65.45 |

Thus all 79 root project modules were kernel-checked with their existing
declared assumptions. All three successful context summaries reported no
type-in-type, unsafe (co)fixpoints, or assumed positivity. Existing theory
sources and convenience copies remained identical to `HEAD`. The failed
containers Make invocation remains a separate failed supplemental check.

### `test-rocq9`: local Rocq 9.0.1

After compiler/pin/clean inspection, these root commands ran under
`opam exec --switch=rocq9 --`, all exit 0:

```bash
make -C examples/rocq9.0 clean
make -j2 -C examples/rocq9.0 base
make -C examples/rocq9.0/tests
```

The missing-base rule regenerated through the parent target: 34 translator
invocations, 54 compiled files, 26 deriving cases, and 14 closed traversal
assumption reports, matching baseline counts. The normal suite passed **70 / 3**,
237 edits assertions, 32 edits CLI cases, 7 tag rejections, and 4 inline
rejections. Elapsed time: 72.99 seconds.

### Normal-suite witnesses and unchanged categories

Both normal suites regenerated and compiled `FunctionalDependencies`,
`RecursiveInstanceMethods`, `ConstructorTags`, and the extended
`InlineMutualEdits`. Each log contains exactly one successful result for each.
`FORCE` generation recreates fixture sources and helpers; `.pass` compiles
unconditionally. Rocq's preceding clean also removed old test outputs.

`ConstructorTags.pass` automatically ran these seven rejection cases:
`skipped`, `redefined`, `TagShadow`, `TagLetShadow`, `TagLambdaShadow`, `builtin`,
and `gadt`. `InlineMutualEdits.pass` automatically ran `no-inline`,
`two-remaining`, `partial`, and `root-capture`. The tag matrices, typed receiver
cases, recursive methods, and nonrelay/capture-safe well-founded computations
were compiled by the normal fixture checks. No focused-only substitute was used.

The shared expected compiler failures remained `MutrecInst`, `TopBind`, and
`ExceptInDataDefinition`; `TODO_TRANSLATE` remained empty. Base-test expected
failures remained `Arrow`, `EqList`, and `PaperExamples`. All matched their
categories; no nonzero Make result was tolerated. The new generated
`HsToRocq/Wf.v` helper was verified ignored in both wrappers and recreated by
their normal helper rule, with the appropriate target namespace rewriting.

### Clean generation and index-preserving comparisons

Before destructive sequences, current clean rules, scoped status/diffs,
non-ignored and ignored inventories, and clean dry runs were inspected. Only
old catalog outputs/build artifacts were affected. New fingertree/Rocq 9.2
trees and nonstaged translator/test inputs stayed outside these clean paths.

`test-rocq9-translation`, root commands, all exit 0:

```bash
make -C examples/rocq9.0/base-src clean
make -C examples/rocq9.0/base-src vfiles
git diff --exit-code HEAD -- examples/rocq9.0/base
test -z "$(git ls-files --others --exclude-standard -- examples/rocq9.0/base)"
```

Fresh generation: 34 translator invocations, same as baseline; elapsed 16.44
seconds. Tracked comparison was empty and the non-ignored untracked check passed.

`test-translation`, root commands, all exit 0:

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

Fresh generation invoked the translator 34 times for base, 51 for GHC, and 6
for graph, matching the baseline. Containers' prescribed plain `vfiles` was
again a no-op. All comparisons/checks passed. Elapsed time: 669.30 seconds,
including 648.92 seconds for GHC generation.

The same supplemental fresh containers check as the baseline followed a
separate safe clean inspection. Root commands, all exit 0:

```bash
make -C examples/containers clean
make -C examples/containers vfiles
git diff --exit-code HEAD -- examples/containers/lib examples/containers/hs-spec
test -z "$(git ls-files --others --exclude-standard -- examples/containers/lib examples/containers/hs-spec)"
```

Seven library modules plus `IntSetProperties` were freshly translated: 8
invocations. Both trees matched `HEAD`; elapsed 12.88 seconds. Since the unchanged
baseline recorded these outputs identical to the same `HEAD`, these checks also
establish no generated difference from the baseline without staging or discarding
output. Generation again printed recoverable GHC deriving diagnostics and some
interface notices; enclosing commands returned 0 and output comparisons passed.

## Frozen input files and preservation fingerprints

The existing unstaged changes were nine tracked production/test/doc files plus
the two wrapper ignore files:

```text
src/lib/HsToRocq/ConvertHaskell/Declarations/Class.hs
src/lib/HsToRocq/ConvertHaskell/Declarations/Instances.hs
src/lib/HsToRocq/ConvertHaskell/Expr.hs
src/lib/HsToRocq/ConvertHaskell/TypeEnv/Instances.hs
examples/tests/InlineMutualEdits.hs
examples/tests/InlineMutualEdits/edits
examples/tests/InlineMutualEdits/preamble.v
examples/tests/README.md
examples/tests/test-rules.mk
examples/tests/.gitignore
examples/rocq9.0/tests/.gitignore
```

Production file SHA-256 values before and after the run:

| File under `src/lib/HsToRocq/ConvertHaskell/` | SHA-256 |
| --- | --- |
| `Declarations/Class.hs` | `8d1bdfd33ea2edb99a9465a0af02b07ab4d57e64c336c9ec263d7b79cf9b6ce0` |
| `Declarations/Instances.hs` | `c08a03d2228e0cf7a15f6e8f765b845bd562b44770e583fab80406167b8914c0` |
| `Expr.hs` | `65fe714b700134c79eb9a952f2d296dae401294183c5eabeecf1dd00635ef891` |
| `TypeEnv/Instances.hs` | `9ff38768bb32279054ec80de9440b86b9cb4e5f535cb7294687bbeb06589efe1` |

The 24 untracked fixture inputs also remained unchanged: the three new fixture
modules and their edits/support files, plus the inline-negative sources, WF
shim source, script, and edit configurations. Complete path/hash manifests for
all tracked and untracked inputs are in `00-preflight.log` and
`11-final-verification.log`.

| Protected state | Before/after SHA-256 |
| --- | --- |
| Staged diff: `git diff --cached --binary` | `adef9d5c8e0c924295e496dc2da5142006a901f2488c32fba581f9649f29383a` |
| Frozen tracked diff: `git diff --binary -- src test examples/tests examples/rocq9.0/tests/.gitignore` | `27e99e453c7d2aec5d612374591e6a677d2339a461e3cc33e52c64f82cd24dab` |
| Untracked fixture hash manifest | `5f26680718ead0fb81685486c5f80894a737d09022bde6ef8367d2d47b780a2e` |
| Unchanged `BASELINE.md` | `48221778a42abfb68cbae498d1457bba227ddc41710a56c00eb2171224744063` |

The untracked manifest was computed with
`git ls-files --others --exclude-standard -z -- src test examples/tests | xargs -0 shasum -a 256 | shasum -a 256`.
Staged changes still consist only of the original `.gitmodules` addition and
fingertree gitlink at `2f303a410c95802a2824b6dd54a0610fa5329858`; HEAD is unchanged.
`git diff --check` passed. Final old-output and theory/small-example tracked
comparisons with `HEAD` passed, and generated-output non-ignored untracked
checks were empty. Generated tracked differences: **none**.

Later catalog/supplemental cleans in that run removed compiled outputs from old
base, Rocq base, GHC library/theories, graph library, and containers
library/specification/theories. Their regenerated sources remain available and
match `HEAD`; normal shared-suite fixture outputs remained available. That
source/test verdict covered the old targets, not the then-blocked three-module
fingertree checkpoint. The follow-up below supersedes that compilation status.

## Evidence index

| Log | Evidence |
| --- | --- |
| `00-preflight.log` | Full initial diffs/status, frozen tracked/untracked path/hash manifests, baseline/report hashes, tool versions, pins, initial output checks. |
| `01-hlint35-supplemental.log` | Supplemental HLint commands/statuses. |
| `02-build-haskell.log` | All five prerequisite commands, three suites, 225 harness checks, concurrency. |
| `03-compiler-preflight.log` | Selected Coq versions, packages/tools, checked-in output status. |
| `03-test-coq-files.log` | All 24 compiler-job commands/statuses and full theory builds. |
| `04-tests-preflight.log` | Compiler recheck, input status, helper ignore checks. |
| `04-tests.log` | All 17 commands; normal 70-fixture suite, automatic negatives, base checks, small examples. |
| `04-kernel-validation.log` | Failed containers Make `validate`, exact library-path diagnostic, exit 2. |
| `04-kernel-containers-direct.log` | Successful direct kernel check of all 37 logical project modules. |
| `04-kernel-graph-ghc.log` | Successful full graph/GHC Make kernel validation. |
| `05-rocq-preflight-clean-inspection.log` | Rocq environment/pin, safe clean dry run, stable frozen-input checks. |
| `05-test-rocq9.log` | Clean, regenerated/compiled base with checks, normal 70-fixture suite and automatic negatives. |
| `06-rocq-translation-clean-inspection.log` | Before-clean no-diff/status checks and dry run. |
| `06-test-rocq9-translation.log` | Clean generation and both passing comparison checks. |
| `07-translation-clean-inspection.log` | GNU sed, pins, frozen-input checks, scoped clean inspection/dry runs. |
| `07-test-translation.log` | All 15 commands, generation counts, no-diff comparisons. |
| `09-containers-clean-inspection.log` | Supplemental clean inspection/dry run. |
| `09-containers-clean-regenerate.log` | Fresh library/specification generation and comparisons. |
| `05-ignored-inventory.log`, `06-ignored-inventory.log`, `07-ignored-inventory.log`, `09-ignored-inventory.log` | Complete inspected ignored-artifact inventories for destructive sequences. |
| `10-counts-and-steps.log` | Actual command/status/count extraction; verified four required fixture successes and 7 tag/4 inline negative cases per normal suite; retained supplemental failure. |
| `11-final-verification.log` | Before-report unchanged input/baseline/index/HEAD checks, old-output no-diff checks, fixture artifact times, helper ignore checks. |
| `12-report-state.log` | After replacement: unchanged frozen tracked/untracked inputs, baseline, staging and HEAD; passing output comparisons; final report hash. |

## Targeted unfoldr follow-up (2026-11-02)

This follow-up integrated the user-authorized deferred source `unfoldr` and the
queue audit. **No Haskell translator code changed in this follow-up**; the four
production hashes above still match. The shared
`examples/rocq9.0/base-src/Makefile` change adds only the per-stem
`GHC_INTERNAL_EDITS` selection and uses it in the existing Data/Control recipe.
Only the new 9.2 wrapper selects the effective OldList edits. The older 8.20/9.0
outputs remain unchanged.

### Targeted old-target regressions

After inspecting the old-base clean scope, these commands ran from the worktree
root and passed:

```bash
bash test/harness.sh
make -s -C examples/rocq9.0/base-src clean && \
  make -s -j2 -C examples/rocq9.0/base-src vfiles && \
  git diff --exit-code HEAD -- examples/rocq9.0/base && \
  test -z "$(git ls-files --others --exclude-standard -- examples/rocq9.0/base)"
git diff --check
git diff --cached --check
```

- Harness: **225/225 PASS**.
- Safe clean and fresh parallel Rocq 9.0 base generation: **PASS**; tracked
  outputs were byte-identical to `HEAD`, with no non-ignored untracked output.
  Initial GHC deriving diagnostics recovered as in the baseline; the enclosing
  generation command and both output checks passed.
- Working-tree and cached whitespace checks: **PASS**.

This was not another full catalog or old-target compiler run. The prior
70-positive-fixture results retain their recorded scope. The exact HLint 3.6.1
block and local Rocq 9.0.1 versus CI 9.0.0 difference are unchanged.

### Clean Rocq 9.2 integration

A pre-clean SHA-256 manifest covered 107 foundation/example outputs and
`CoreSize.v`. Both new foundations and the example were cleaned, and explicit
absence checks passed before regeneration. The reproducible sequence is:

```bash
make -s -C examples/rocq9.2 clean
make -s -C examples/fingertree clean
opam exec --switch=cs2-rocq92 -- make -s -j2 -C examples/rocq9.2 check
opam exec --switch=cs2-rocq92 -- \
  make -s -j2 -C examples/fingertree kernel-check core-check priority-check
```

All build/check commands passed. The foundation run compiled 54 base and five
base-thy modules and checked the source `unfoldr` signature, rank-based unfolding
proof, finite countdown proof, and recursive kernels. The example run compiled
all three modules and passed recursive kernel checks, the core audit, and the
new enforced priority/unfoldr audits. All **107/107 SHA-256 comparisons passed**
for `.v`/`.h2ci` files, both foundation projects, and `CoreSize.v`.

The queue audit checks 74 declarations: 50 closed and 24 depending only on
`deferredFix`. Its extra `OldList.unfoldr` entry also depends only on
`deferredFix` (75 reports total). The four-report `Unfoldr.v` audit has one
closed report, one `deferredFix`-only report, and two depending exactly on
`deferredFix` plus `deferredFix_eq_on`. See [ASSUMPTIONS.md](ASSUMPTIONS.md) for
the individual declarations and proof premises.

Evidence is under
`/var/folders/3c/qfxwcbpj7q590cwh0_scnyl80000gn/T/opencode/`:

- `unfoldr-foundations-20261102.log`;
- `unfoldr-example-20261102.log`;
- `unfoldr-integration-20261102.sha256`.

The fingertree source remains clean at
`2f303a410c95802a2824b6dd54a0610fa5329858`; parent HEAD remains `e4bc91cc` on
branch `fingertree`, with implementation changes uncommitted. The authorized
translation/compilation milestone has passed. The hoisted lazy-pattern gap
remains; validity-preservation/decrease proofs, final functional-correctness
theorems, and complete theorem coverage are still needed. No formal pinned-review
verdict is claimed.
