# Isolated Rocq 9.2 foundations

The isolated **54-module base** and required **five-module base-thy closure**
support the completed finger-tree proofs on Rocq 9.2. The base restores
`Data.OldList.unfoldr` from existing GHC source through the user-authorized
deferred interface. The final clean local acceptance run passed on 2026-11-02:
the foundations regenerated and compiled, and supplemental recursive kernel
checks covered all 61 foundation/check module roots. See the
[final validation record](../fingertree/VALIDATION.md) for commands, byte
comparisons, source preservation, and the corrected supplemental invocation.

The finger-tree example has fifteen cleanly compiled and kernel-checked theories,
including valid-queue extraction/decrease, guarded unfolding, and generic
applicative traversal. ApplicationLaws proves generic Boolean Eq and comparator
tie-equivalence laws
without propositional reflection. Interval class laws need neither
`EndpointOrderLaws` nor data validity; queue laws retain valid operands and
`PriorityOrderLaws`. Interval operation invariants are unchanged. See the
[coverage inventory](../fingertree/COVERAGE.md) and
[1,048-entry manifest summary](../fingertree/ASSUMPTIONS.md#exact-final-theory-manifest);
all entries matched in the final clean run.
Those example proofs, not the foundation countdown check, establish the queue
contracts. The example's sole approved manually supplied algorithm body is
`Data.PriorityQueue.FingerTree.minViewWithKey`; source `unfoldr` itself has no
manual replacement. Both decisions are recorded in
[ASSUMPTIONS.md](../fingertree/ASSUMPTIONS.md).

## Build

Prerequisites are the worktree's built `hs-to-rocq`, GHC 9.10.3 source submodule,
Stack, GNU Make, Bash, Python 3.8+, and Rocq core/stdlib 9.2. Local validation
used the existing `cs2-rocq92` opam switch. Set `ROCQ92_SWITCH` to your existing
Rocq 9.2 switch. From the repository root in this worktree, run these commands
separately and in order, stopping on failure:

```bash
opam exec --switch="${ROCQ92_SWITCH:?Select a Rocq 9.2 switch}" -- \
  make -C examples/rocq9.2 clean
opam exec --switch="$ROCQ92_SWITCH" -- make -j2 -C examples/rocq9.2 check
```

Use an available UTF-8 locale; the initial local run used
`LANG=en_US.UTF-8 LC_ALL=en_US.UTF-8`. Do not clean concurrently with builds.
When rebuilding the finger-tree example too, clean it before rebuilding. Its
[README](../fingertree/README.md#build-and-check) gives the tested clean build
sequence, and [VALIDATION.md](../fingertree/VALIDATION.md) records the complete
acceptance checks. The earlier
[integrated validation record](../fingertree/REGRESSIONS.md#targeted-unfoldr-follow-up-2026-11-02)
preserves the pre-guard-repair run.

Without `check`, Make builds both foundations. Targets `base`, `base-thy`, and
`vfiles` select the full base, both compiled foundations, and source generation
respectively. The parent Makefile checks that the compiler and Makefile generator
both report 9.2, generates output Makefiles with `rocq makefile`, and passes
`COQC='rocq c'` to compilation.

`check` also compares the five proof copies, probes load paths, compiles
`checks/Unfoldr.v`, and recursively kernel-checks the proof closure, `Data.OldList`,
and `Rocq92Checks.Unfoldr`. The finger-tree `priority-check` target separately
enforces the exact assumption sets printed by `Unfoldr.v` and the queue audit.

The existing [`test-rocq9` CI job](../../.claude/commands/ci.md#job-test-rocq9)
runs its Rocq 9.0 checks before this isolated 9.2 route. Its setup action installs
Python and initializes the pinned GHC and fingertree submodules. The job creates
`rocq92` with OCaml 4.14.2 and `--no-switch`, then installs `rocq-prover.meta.1`
with `rocq-core`, `rocq-runtime`, and `rocq-stdlib` pinned to 9.2.0. Every new check
uses `opam exec --switch="$ROCQ92_SWITCH"`, leaving the global switch unchanged.
The 9.2 output directories remain separate from older compilers' objects.

That route first runs the
[real assumption-checker controls](../../test/README.md#assumption-audit-checks),
then cleans the example and foundations, runs this foundation `check`, and runs
the [full example checks](../fingertree/README.md#build-and-check). Use the shared
catalog for the exact sequence. This describes automated coverage, not a new
hosted CI result; the
[local acceptance qualifications](../fingertree/README.md#local-acceptance-and-regression-qualifications)
and dated validation records below remain separate evidence.

## Authoritative sources and adaptations

### Base

[`base-src/Makefile`](base-src/Makefile) includes the existing
[`../rocq9.0/base-src/Makefile`](../rocq9.0/base-src/Makefile). Both wrappers have
the same directory depth, so `BASE_SRC=../../base-src`, `OUT=../base`, and `deps/`
resolve to the intended authoritative inputs and local outputs.

The wrapper reuses the module inventory, Haskell sources, edits, preambles,
midambles, and manual files in [`../base-src/`](../base-src/), with only the
OldList guidance adjustment below. Sources come from this worktree's GHC
submodule at `3f4d7d38b9661435bdde981451ac50c4335ed090`. The translator's
`--target-version 9.0` supplies the Rocq-9 namespace; the compiler is Rocq 9.2.
Each clean generation translates 34 modules and copies 20 authoritative manual
modules, producing all 54 `.v` files.

The inherited manual-copy rule performs the `WfExtensionality` structural move
and import, maps `Coq.Init.*` to `Corelib.Init.*`, changes bare `From Coq` to
`From Stdlib`, and maps remaining `Coq.*` paths to `Stdlib.*`. Generated modules
receive namespace rewriting and the extra import from the translator itself.
Shared `base-rules.mk` retains dependency-directory ordering, manual constructor
interfaces (including `GHC/Tuple.h2ci`), removal of stale/failed translation
output, and atomic publication of `_CoqProject` after every source succeeds.
Dependency files and merged preamble/midamble temporaries stay here.

### Source unfoldr restoration

On 2026-11-02 the user authorized **"Agreed. Let's try deferredFix"** for source
`unfoldr`, following **"Use deferredFix"** for the queue. The 9.2 wrapper now
sets:

```make
GHC_INTERNAL_EDITS_Data/OldList = deps/OldList.edits
```

It checks that authoritative `module-edits/Data/OldList/edits` contains exactly
one `skip Data.OldList.unfoldr` line, removes only that line, and appends the
new local [`base-src/module-edits/Data/OldList/edits`](base-src/module-edits/Data/OldList/edits).
The effective file preserves every other authoritative edit and contains these
two added directives:

```text
in Data.OldList.unfoldr termination go deferred
in Data.OldList.unfoldr rewrite forall g, GHC.Base.build g = g cons nil
```

The source uses `build` around a local recursive producer. The rewrite
specializes the producer's result to a list, so the existing `default_list`
supplies the inhabitant required by deferred recursion. The local `go` worker
uses `deferredFix1`; its source step, branches, and recursive call are unchanged.
No Haskell source, other OldList edits, preamble/midamble, or generation recipe
is replaced. There is no manual unfold algorithm, fuel parameter, or `redefine`.

The only shared Makefile change is this selector and its use as the Data/Control
rule's `-e` input:

```make
GHC_INTERNAL_EDITS = $(or $(GHC_INTERNAL_EDITS_$*),$(wildcard $(BASE_SRC)/module-edits/$*/edits))
```

The key is the current rule's stem, so the OldList override cannot leak into
prerequisite modules. This works with GNU Make 3.81, which lacks `private`
target-specific variables. Without an override, the selector uses the same
authoritative edit file as before. Only 9.2 restores `unfoldr`; the 8.20 and 9.0
outputs remain byte-identical. A safe clean, fresh parallel 9.0 base generation
and no-diff comparison passed in the
[targeted regression follow-up](../fingertree/REGRESSIONS.md#targeted-unfoldr-follow-up-2026-11-02).

### Source unfoldr checks and assumptions

[`checks/Unfoldr.v`](checks/Unfoldr.v) checks this exact signature, with no
`Default` premise for the seed or element type:

```coq
forall (b a : Type), (b -> option (a * b)%type) -> b -> list a
```

`unfoldr_rank_eq` proves the source step equation given a natural-valued rank
that decreases on **every** successful step:

```coq
forall b a b', f b = Some (a, b') -> rank b' < rank b
```

The proof takes the recursion body from the generated definition and applies
`deferredFix_eq_on` with `P := fun _ => True` and `ltof B rank`.
`countdown_decreases` discharges that premise for `countdown_step`; the worked
proof `unfoldr_countdown_three` shows seed `3` emits `[2; 1; 0]`.

| Report | Exact assumptions under `HsToRocq.DeferredFix` |
| --- | --- |
| `Data.OldList.unfoldr` | `deferredFix` |
| `unfoldr_rank_eq` | `deferredFix`, `deferredFix_eq_on` |
| `countdown_decreases` | None; closed |
| `unfoldr_countdown_three` | `deferredFix`, `deferredFix_eq_on` |

These four reports add no `ClassicalChoice` or `Eqdep` dependency. The full base
still includes the separate classical `DeferredFixImpl.v`, but these definitions
and proofs use the axiomatic interface, not that realization. The
[assumption record](../fingertree/ASSUMPTIONS.md) explains the authorized scope.
The all-step theorem does not justify unfolding an arbitrary producer or an
invalid queue. The queue's valid-domain obligations are now proved separately in
[`PriorityOperations.v`](../fingertree/theories/PriorityOperations.v):
`minViewWithKey_some`/`minView_some` preserve validity and decrease `pqueue_size`,
`assocs_recurses_on`/`foldMap_recurses_on` establish the guarded dependence, and
`assocs_unfold`/`foldMap_unfold` give the equations. `unfoldr_valid_model` connects
the actual source `unfoldr` call to the independent stable full-entry model.
These results retain the two global deferred axioms; they do not replace them
with the classical realization. The queue's sole manual body exception repairs
the empty-guard ordering; see the
[decision record](../fingertree/ASSUMPTIONS.md#approved-translation-exception-minviewwithkey).

### Base-thy

[`base-thy-src/Makefile`](base-thy-src/Makefile) copies these files from
authoritative [`../../base-thy/`](../../base-thy/) through [`adapt.py`](adapt.py):

| Copied module | Imports from `Proofs.*` |
| --- | --- |
| `GHC/Base.v` | None |
| `GHC/List.v` | `Proofs.GHC.Base` |
| `Data/Foldable.v` | `Proofs.GHC.Base`, `Proofs.GHC.List` |
| `Data/Traversable.v` | `Proofs.GHC.Base`, `Proofs.GHC.List` |
| `Data/Functor/Identity.v` | `Proofs.GHC.Base` |

These imports close within the five files. Other project imports come from the
complete local base. Installed Rocq libraries provide
`From Stdlib Require ssreflect ssrbool ssrfun`; this closure does not require
MathComp.

`adapt.py` applies the same ordered namespace/import substitutions as the
manual-copy rule. It is a mechanical copier for these inputs, not a general
Rocq text parser. It preserves declarations and proofs up to those substitutions
and writes each copy atomically. `make check` compares all five outputs with a
fresh in-memory adaptation using `adapt.py --check`. The copy Makefile removes
outdated targets before copying and publishes its project completion marker
only after all five files succeed. No further 9.2 proof adaptations were needed.

Generated `.v` files are reproducible outputs. Changes belong in the
wrapper/copier, local edits, or authoritative sources according to their scope,
not in those outputs.

## Object-file and load-path isolation

The generated base project uses `-Q . ""`. The base-thy project uses exactly:

```text
-Q . Proofs
-Q ../base ""
```

Here `../base` is `examples/rocq9.2/base`, relative to the copied base-thy
directory. The parent clears `COQPATH` and `ROCQPATH` for all subcommands.
[`checks/LoadPaths.v`](checks/LoadPaths.v) prints the load path and loaded object
paths for five base libraries and the five proof libraries. All ten resolved to
this worktree's `examples/rocq9.2/` tree; the project load path contained neither
the root 8.20 foundations nor `examples/rocq9.0`. Switch libraries came from
`cs2-rocq92`.

The historical `unfoldr` integration clean removed both foundation output
directories, with absence checks before regeneration. Rocq 9.2 then compiled
all 54 base and five base-thy objects from newly generated sources.
`LoadPaths.v` and `Unfoldr.v` produce two additional objects under `checks/`.
`LoadPaths.v` is compiled as the root logical library `LoadPaths`, whereas
`Unfoldr.v` is compiled as `Rocq92Checks.Unfoldr`. Supplemental kernel commands
must preserve that distinction. Generated copies, interfaces, dependency
files, compiler products, and generated Makefiles are ignored by Git.

## Final local validation: 2026-11-02

The final clean run checked that old outputs were absent, then regenerated and
compiled all 54 base and five base-thy modules. The example's three libraries
and fifteen theories passed compilation, exact audits, and recursive kernel
checks. Supplemental commands checked all 61 foundation/check roots. All 122
files in the source/interface/project/theory/manifest comparison matched
byte-for-byte. See [VALIDATION.md](../fingertree/VALIDATION.md) for the complete
commands, inventories, preservation checks, and evidence.

The first supplemental kernel command failed because it requested
`Rocq92Checks.LoadPaths` instead of the compiled root `LoadPaths`. Its failed
log is retained. The corrected all-foundation/Unfoldr command and separate
`LoadPaths` check both passed; no production code changed. The validation report
records that correction rather than treating the failed invocation as a pass.

[FINAL-REGRESSIONS.md](../fingertree/FINAL-REGRESSIONS.md) records all six non-HLint
catalog jobs passing, with exact HLint 3.6.1 blocked (supplemental 3.5 passed) and
old Rocq core/runtime 9.0.1 differing from CI's 9.0.0. The historical containers
`validate` failure remains qualified there, not claimed fixed. Formal pinned-range
code/proof review has not been completed; no verdict or axis finding count is
claimed. The user has now requested one local commit; after that commit, a
meaningful committed scope will be available. See the
[review status](../fingertree/README.md#revision-and-review-status) for the earlier
preparation attempt that rejected the then-empty range.

## Historical validation records

All records below used worktree
`/Users/liyao/Workspace/hs-to-coq/.claude/worktrees/fingertree`, branch
`fingertree`, parent HEAD `e4bc91ccc9f039deb352896dae75709c892cb03c`. The
implementation was uncommitted at validation time.

| Tool | Recorded version |
| --- | --- |
| Rocq core/runtime/stdlib | 9.2.0; compiler and Makefile banner: 9.2 |
| OCaml | 5.4.1 |
| Stack / selected GHC | 3.11.1 / 9.10.3 |
| GNU Make | 3.81 |
| Python | 3.15.0 |

### Source unfoldr integration: 2026-11-02

After cleaning both new foundations and the example and checking absence,
`make -s -j2 -C examples/rocq9.2 check` passed in the 9.2 switch. The example's
`kernel-check core-check priority-check` also passed. The integrated manifest
matched **107/107 SHA-256 checks** across foundation/example `.v`/`.h2ci` files,
both foundation projects, and `CoreSize.v`.

This 107-file record predates the approved `minViewWithKey` repair and the original
fourteen-theory proof set. It is retained as historical reproducibility evidence,
not a clean-build result for the completed proofs. The final fifteen-theory
acceptance and qualified old-target results are recorded separately in
[VALIDATION.md](../fingertree/VALIDATION.md) and
[FINAL-REGRESSIONS.md](../fingertree/FINAL-REGRESSIONS.md).

The current foundation kernel command runs from this directory:

```bash
rocq check -silent -Q base "" -Q base-thy Proofs -Q checks Rocq92Checks \
  Proofs.GHC.Base Proofs.GHC.List Proofs.Data.Foldable \
  Proofs.Data.Traversable Proofs.Data.Functor.Identity Data.OldList Rocq92Checks.Unfoldr
```

It checks these modules and their dependencies recursively, with neither
`-admit` nor `-norec`. Kernel acceptance preserves declared assumptions. The
general unfolding theorem retains its rank premise; the countdown and queue
proofs discharge the applicable local premises, not the global deferred axioms.

Evidence is under
`/var/folders/3c/qfxwcbpj7q590cwh0_scnyl80000gn/T/opencode/`:
`unfoldr-foundations-20261102.log`, `unfoldr-example-20261102.log`, and
`unfoldr-integration-20261102.sha256`. Initial GHC deriving diagnostics recover
as in the baseline; existing Rocq deprecation/notation warnings remain. The
enclosing builds, audits, and kernel checks passed.

### Initial foundation checkpoint (before unfoldr restoration)

The 2026-11-01 local run (2026-11-02 UTC) established the isolated foundation
build before the new OldList guidance. Its first build, checks, and second clean
build passed: 54 base and five proof modules compiled, all five proof copies
matched, and recursive kernel checking passed. All 59 foundation sources and
both projects matched across regeneration (**61 checks**). Those hashes describe
the earlier state, not the restored `unfoldr` output.

Version-guard probes rejected compiler 9.0.1 and rejected a 9.0.1 Makefile
generator paired with compiler 9.2; the matching 9.2 pair passed. Evidence is
in the same approved temporary parent under
`fingertree-rocq92-checkpoint4-20261101/`, especially
`01-initial-build.log`, `02-isolation-kernel-check.log`,
`03-before-rebuild.sha256`, `04-version-guards.log`,
`05-final-clean-build-check.log`, `06-reproducibility.log`, and
`07-final-state.log`.
