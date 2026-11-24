# Verified measured finger trees

**The required functional proofs are complete, and Rocq 9.2 local acceptance
passed on 2026-11-02. Formal pinned-range review has not been completed.**
The fifteen theories cover all 27 core, 13 interval-map, and nine priority-queue
operations, plus the 46 required instances and their translated methods/defaults.
The queue's valid-domain
extraction and guarded-recursion obligations are proved, as are generic
applicative sequencing, validity, and interval Traversable laws.
`ApplicationLaws` extends application Eq/Ord coverage to general Boolean
equality and comparator tie equivalences.

The final clean run compiled all three libraries and all fifteen theories,
matched all **1,048 exact assumption reports**, and passed recursive kernel
checks. All **122 source/interface/project/theory/manifest files** matched
byte-for-byte before and after the rebuild. [VALIDATION.md](VALIDATION.md)
records the clean-absence checks, isolated foundations, full kernel coverage,
source preservation, and the corrected supplemental command. The
[final regression report](FINAL-REGRESSIONS.md) records all six non-HLint catalog
jobs passing, with the toolchain qualifications below.

Start with [COVERAGE.md](COVERAGE.md) for typed theorem names and precise premises,
[ASSUMPTIONS.md](ASSUMPTIONS.md) for logical dependencies and the approved
translation exception, and the [theory guide](theories/README.md) for module
boundaries. The claim is total functional correctness of the translated Gallina
definitions on finite, valid values under these premises and foundations. It is
not formal compiler correctness or a claim about complexity, persistency,
bottoms, strictness, or `seq`. `Show`, `Read`, `Generic`, and `NFData` are excluded.

## Source and scope

The source is Ross Paterson's `fingertree-0.1.6.3`, pinned at
`2f303a410c95802a2824b6dd54a0610fa5329858` in the public
[Git mirror](https://github.com/lastland/fingertree-mirror.git). The Haskell
source and original license are unchanged. Data and algorithm definitions come
from that source **except for the explicitly approved manual body of
`Data.PriorityQueue.FingerTree.minViewWithKey`**, described below. Required
instance bodies remain source-generated.

When reviewing translation guidance, handwritten support, or source-policy
changes, read [SOURCE-POLICY.md](SOURCE-POLICY.md) for the executable checks,
their limits, and the remaining review responsibilities.

The supplied `notes/FingerTreeSpec.md`, `notes/FingerTreeMirror.md`, and glossary
remain in the original checkout; they were not copied into this worktree.
The user-authorized deferred foundation amends the original restriction on
recursion axioms. The one-function redefinition separately amends the restriction
on manually supplied algorithm bodies. Functional extensionality was already
permitted by specification lines 283-284; no further logical principle is used
by the final theorem inventory.

## What the proofs establish

* **Core:** independent raw-constructor list models and external cache validity;
  construction, concatenation, views, maps, reversal, folds, and measurement.
  Measurement laws are explicit propositional associativity and identities,
  with no Eq/decidable-equality restriction and no commutativity requirement.
* **Search and split:** exact nonmonotonic search endpoint classifications and
  adjacent crossings; monotonicity adds uniqueness of the sequence cut.
  Monotonic split scans nonempty prefixes and cuts before the triggering element,
  without assuming `p mempty = false`. Domain certificates and parametricity
  connect the predicate domains to actual generated calls and internal errors.
* **Intervals:** full entries in lexicographic interval order, closed intervals,
  stable insertion/merge, exact ordered query filters, smallest enclosing bounds,
  extraction, and partition. Duplicate entries and payloads are retained.
* **Queues:** an independent stable ordering of the raw entry sequence, without
  requiring the raw tree to be sorted. Extraction returns the first full entry,
  preserves validity, avoids the guarded errors, and decreases `pqueue_size`.
  These facts prove `recurses_on` and guarded unfolding for source `assocs` and
  Foldable recursion.
* **Effects and instances:** all translated methods/defaults have behavioral
  specifications. Traversals quantify over arbitrary lawful applicatives and
  preserve validity inside effects using `HoldsF`. Contextual premises refer to
  original prefix/suffix occurrences. Algebraic laws use behavioral relations,
  not equality of raw tree shapes. ApplicationLaws proves general Boolean Eq
  and comparator tie-equivalence laws: interval class laws need neither
  `EndpointOrderLaws` nor data validity, while queue laws retain valid operands and
  `PriorityOrderLaws`. Stronger propositional-reflection bundles remain optional
  corollaries, not the primary generic law coverage. Interval operation
  invariants are unchanged.

## Build and check

Run from the repository root in the `fingertree` worktree, with its translator
built and its pinned fingertree and GHC source submodules initialized. Set
`ROCQ92_SWITCH` to an existing Rocq 9.2 opam switch:

```bash
opam exec --switch="${ROCQ92_SWITCH:?Select a Rocq 9.2 switch}" -- \
  make -j2 -C examples/rocq9.2 check
opam exec --switch="$ROCQ92_SWITCH" -- \
  make -j2 -C examples/fingertree kernel-check core-check interval-check priority-check
```

The translator emits Gallina with `--target-version 9.0`; **Rocq 9.2** compiles
it with `rocq c`. Historical local runs used `cs2-rocq92`; that switch name is
not a build dependency. Foundations come only from `../rocq9.2/base/` and
`../rocq9.2/base-thy/`; do not reuse older compilers' objects. See the
[foundation guide](../rocq9.2/README.md) for
prerequisites and load-path isolation.

The [Makefile](Makefile) defines these targets:

| Target | Work performed |
| --- | --- |
| `source-policy` | Check owned guidance and support against approved redefinition targets, pinned rewrites, and protected generated names; needs Stack and Python, not Rocq or generated foundations. |
| `vfiles` | Regenerate all three library source/interface pairs, automatically running `source-policy` first and source-only inventories after each translation; builds the isolated foundations. |
| default `all` | Compile all three library modules and all fifteen theories, enforcing the theory assumption manifest. |
| `proofs` | Compile every `theories/*.v` through `theories/check-assumptions.py`, including required library/theory prerequisites. |
| `kernel-check` | Compile libraries and proofs, then recursively kernel-check all three libraries and all fifteen theories. |
| `core-check` | Compile the eight core/support theories and the 131-entry generated core inventory; recursively kernel-check them. |
| `interval-check` | Compile the 31-entry interval inventory; compile and recursively kernel-check `IntervalModel`, `IntervalOperations`, `IntervalLaws`, and dependencies. |
| `priority-check` | Compile the three priority theories; enforce the generated queue, source `unfoldr`, and five-regression inventories with `check-priority-audit.py`; recursively kernel-check them. |
| `check-source` | Check the release pin and unchanged source tree, including its license. |

The shared `ApplicationLaws` module is included by `all`, `proofs`, and
`kernel-check`, not by the separate core/interval/priority group targets.

The `source-policy` prerequisite runs before this example builds foundations or
translates modules. Each translated `.v` must then pass its source-only name
inventory before compilation. These checks also run for direct targets and with
existing outputs. They detect specific guidance violations and missing or
duplicate required names; they prove neither source origin nor semantic
equivalence. `vfiles` is a translation milestone, not proof acceptance: the full
theory, assumption, and kernel checks above remain necessary.

Translation, example compilation, and theory audits are forced on each
invocation. Translation removes old `.v`/`.h2ci` outputs and discards failed,
missing, or inventory-rejected output. Theory rules remove the old `.vo` before
compilation/auditing.
The exact checker pairs each exported constant with its own report marker and
rejects missing declarations, changed counts, and changed assumption sets.
Its generated audit sources and logs go under `deps/proof-audits/`.

To reproduce the successful clean regeneration and compilation, inspect the
clean scope, then run these steps separately and in order, stopping on failure.
[VALIDATION.md](VALIDATION.md) gives the exact recorded commands, supplemental
kernel checks, and byte comparisons:

```bash
opam exec --switch="${ROCQ92_SWITCH:?Select a Rocq 9.2 switch}" -- \
  make -C examples/fingertree clean
opam exec --switch="$ROCQ92_SWITCH" -- make -C examples/rocq9.2 clean
opam exec --switch="$ROCQ92_SWITCH" -- make -j2 -C examples/rocq9.2 check
opam exec --switch="$ROCQ92_SWITCH" -- \
  make -j2 -C examples/fingertree kernel-check core-check interval-check priority-check
```

The example clean removes generated library files, dependencies/audit logs, and
compiled theory/audit products, not the authored theories or foundations. The
foundation clean removes its isolated outputs. Never clean concurrently with a
build. Reproducibility additionally requires comparison of regenerated sources
and interfaces; compilation alone does not establish it.

CI runs the [assumption-audit controls](../../test/README.md#assumption-audit-checks)
in the existing `build-haskell` job without a compiler. The existing
[`test-rocq9` job](../../.claude/commands/ci.md#job-test-rocq9) retains the Rocq 9.0
suite first, then runs the real controls in an isolated Rocq 9.2 switch, cleans
the example and its foundations, and runs the foundation `check` followed by
`kernel-check core-check interval-check priority-check`. This route enforces the
theory and queue/foundation assumption inventories and recursively kernel-checks
all three libraries and all fifteen theories. Every nonzero status fails the job.
The shared catalog defines the full sequence and pins; the
[foundation guide](../rocq9.2/README.md#build) explains compiler isolation.

The automated route does not repeat the historical 122-file byte comparison or
the supplemental checks of all 61 foundation/check roots. Those remain separate
evidence in [VALIDATION.md](VALIDATION.md), not implied CI results.

## Approved minViewWithKey redefinition

On 2026-11-02 the user explicitly approved `redefine` for
**`Data.PriorityQueue.FingerTree.minViewWithKey` only** and required a permanent
record. At the pinned
[`source lines 238-246`](fingertree/Data/PriorityQueue/FingerTree.hs#L238-L246),
`FT.null q` protects the lazy `where` binding `Prio k v = measure q`.
The previous translation matched the measure first, so a valid empty queue's
`NoPrio` reached `GHC.Err.patternFailure` instead of returning `None`.

The [single directive](module-edits/Data/PriorityQueue/FingerTree/edits#L19)
puts the empty guard outside the measure match. Its nonempty branch retains the
cached priority **and payload**, `split (below k)`, `viewl`, and reappend. The
original "can't happen" and failed-measure branches remain in their guarded
positions. The public signature has no new `Default` premise or validity
restriction. The source and license were not edited; the replacement introduces
no logical axiom. This is a scoped repair, not a proved general lazy-binding
translation correction. See the
[permanent decision record](ASSUMPTIONS.md#approved-translation-exception-minviewwithkey).

`PriorityRegression.v` proves five closed regression equations, including both
polymorphic empty views, an empty payload type, singleton extraction, and a
four-entry priority/tie/payload/reappend observation. The general extraction,
error-unreachability, validity, and decrease proofs are now in
`PriorityOperations.v`; they are not inferred from those smoke tests.

## Source recursion and foundation dependencies

The user authorized **"Use deferredFix"**, then **"Agreed. Let's try deferredFix"**
for source `unfoldr`. Queue Foldable uses `deferredFix2`; `assocs` remains
`Data.OldList.unfoldr minViewWithKey`. The isolated 9.2 base generates `unfoldr`
from existing GHC source by deferring its worker and specializing `build` to
`cons`/`nil`. It adds no public Default premise, manual unfold body, or fuel
algorithm. The one manually supplied example body remains `minViewWithKey`.

The guarded queue obligations are proved, but the global `deferredFix` and
`deferredFix_eq_on` axioms remain intentional assumptions. The exact theory
manifest and final audit agree on **947 closed reports, 38 with functional
extensionality only, five with `deferredFix` only, and 58 with both deferred
axioms**. These 1,048 reports are separate from the generated-library inventories
and the four-entry foundation audit. [ASSUMPTIONS.md](ASSUMPTIONS.md) gives the
breakdown.

The example derives `deps/base.edits` by omitting only
`skip module GHC.Classes`, retaining required native Eq/Ord derivations and the
existing renames to compiled `GHC.Base`. `TESTING` enables the release's
constructor exports without changing Haskell source.

## Local acceptance and regression qualifications

[VALIDATION.md](VALIDATION.md) is the final fifteen-theory acceptance record;
[FINAL-REGRESSIONS.md](FINAL-REGRESSIONS.md) is the final old-target regression
record. The clean run regenerated and compiled the isolated 54-module base and
five-module base-thy closure. Recursive checks covered all three example
libraries, all fifteen theories, and all 61 foundation/check module roots.
The pinned Haskell source and license, parent HEAD, and index hash were unchanged
at validation time.

All six non-HLint catalog jobs passed. Exact HLint 3.6.1 remained **blocked**;
the supplemental local 3.5 run passed. Old Rocq compiler checks used core/runtime
9.0.1 rather than CI's exact 9.0.0. These results are qualified local acceptance,
not an exact seven-job CI pass. The historical containers Make `validate`
failure below remains a separate recorded failure, not a claim that it was fixed.

Separate CI-wiring checks passed locally: the 24-case compiler-independent
assumption runner, the focused `ci-catalog` guard with its mutation tests, and
the 31-case runner with native Rocq 9.2. The workflow's Docker bootstrap was not
run locally because the Docker daemon was unavailable. These checks do not
establish a new hosted CI pass or replace the proof-acceptance records above.

## Historical evidence

The records below predate the original fourteen-theory proof set. They remain
evidence for their recorded source states, not the final acceptance result.
Old statements that functional proofs were open are superseded by
[COVERAGE.md](COVERAGE.md).

| Historical stage | Recorded evidence |
| --- | --- |
| [Core checkpoint](CORE-CHECKPOINT.md) | Expanded native-instance core and CoreSize compiled and kernel-checked; 131 core declaration and 41 size reports were closed. |
| [Interval checkpoint](INTERVAL-CHECKPOINT.md) | Generated interval library compiled and kernel-checked; 31 dictionary/operation reports closed; clean regeneration matched. |
| Source `unfoldr` integration | Clean foundations (54 base, five base-thy modules) and all three libraries passed; **107/107** source/interface/project/size-file SHA-256 comparisons matched. This was before the `minViewWithKey` redefinition and final theories. |
| [Guard repair](PRIORITY-CHECKPOINT.md#historical-guard-repair-validation) | Integrated checks passed after the approved edit; five regression equations closed. Core/interval source-interface pairs and queue interface were unchanged; queue source changed through regeneration. |
| [Baseline](BASELINE.md) and [regression follow-up](REGRESSIONS.md) | Six non-HLint catalog jobs passed for their recorded source hashes; the later targeted `unfoldr` follow-up passed 225 harness checks and byte-identical fresh old-target generation, not another full catalog. |

The historical exact HLint 3.6.1 check was blocked by local 3.5. Old Rocq
compiler checks used local core/runtime 9.0.1, not CI's exact 9.0.0. A
supplemental containers Make `validate` invocation failed at library-path
resolution; separate logical-library kernel checks passed for all 37 containers,
11 graph, and 31 GHC theory modules. The failure remains a failed historical
check, not a current regression verdict or a hidden pass.

The final reports above supersede these earlier records for current acceptance.
The older counts and failures retain their original scope.

Historical temporary evidence is under
`/var/folders/3c/qfxwcbpj7q590cwh0_scnyl80000gn/T/opencode/`, notably
`unfoldr-foundations-20261102.log`, `unfoldr-example-20261102.log`,
`unfoldr-integration-20261102.sha256`, and the `minview-*-20261102.log` files
listed in the priority checkpoint. Those artifacts are not build dependencies.

## Revision and review status

The user has now requested one local commit on branch `fingertree`. At validation
time, the implementation was uncommitted, parent HEAD was
`e4bc91ccc9f039deb352896dae75709c892cb03c`, and acceptance checks left HEAD and the
index hash unchanged.

The earlier formal code-review preparation used that commit for both base and
head. It rejected the then-empty range with `error: empty or unsupported diff`.
Proof review was blocked by the same empty range. After the requested commit,
a meaningful committed scope will be available for both reviews. Formal
code/proof review has not been completed; neither workflow has produced a formal
verdict or axis finding count. Successful builds and kernel checks do not
substitute for those reviews. See [VALIDATION.md](VALIDATION.md).

The recorded local bootstrap used Stack 3.11.1, GHC 9.10.3, GNU Make 3.81, and
Rocq core/runtime/stdlib 9.2.0 with OCaml 5.4.1. GHC source is pinned at
`3f4d7d38b9661435bdde981451ac50c4335ed090`. These version records identify earlier
runs; the final tested source state and tools are recorded in
[VALIDATION.md](VALIDATION.md) and [FINAL-REGRESSIONS.md](FINAL-REGRESSIONS.md).
