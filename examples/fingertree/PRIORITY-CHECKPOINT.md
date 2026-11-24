# Priority-queue verification and historical checkpoints

## Current status: 2026-11-02

**The queue functional contracts and guarded-recursion obligations are complete.**
The final clean Rocq 9.2 run compiled and recursively kernel-checked
PriorityModel, PriorityOperations, PriorityRegression, and the shared
ApplicationLaws module, with every exact assumption audit matching. The
[coverage inventory](COVERAGE.md#priority-queue-operations-nine) maps all nine
required operations, 11 instances, and their methods/defaults to typed theorems.
[VALIDATION.md](VALIDATION.md) records completed fifteen-theory local acceptance;
[FINAL-REGRESSIONS.md](FINAL-REGRESSIONS.md) records the qualified old-target
results. Formal pinned-range review has not been completed; no verdict or axis
finding count is claimed. The earlier passing runs below retain their historical
scope.

The user first instructed **"Use deferredFix"**, then
**"Agreed. Let's try deferredFix"** for the source `unfoldr`.
[ASSUMPTIONS.md](ASSUMPTIONS.md) records this amendment to the original
specification and the exact assumption sets. The separately approved
single-function `minViewWithKey` redefinition repairs the lazy-pattern guard
order. It is the only manually supplied example algorithm body; other algorithm
and required-instance bodies remain generated from unchanged source.

## Completed model and proof interface

`PriorityOperations.rawEntries` reads raw constructors through the independent
core model. Its public `model` stably orders full `(priority, payload)` entries
using `PriorityModel.ordered`. Validity requires lawful priority ordering and
correct caches, **not a sorted raw tree**. `PriorityOrderLaws` is only a total
preorder of the supplied Boolean `<=`; payloads need neither Eq nor Default.

| Scope | Typed proofs |
| --- | --- |
| Construction and stable ties | `empty_model`, `singleton_model`, `insert_model`, `add_model_ordered`, `union_model`, `fromList_model`, their validity results, and `insert_ties`, `add_ties`, `union_ties`, `fromList_ties` |
| Exact minimum extraction | `winner_at_cut`, `minViewWithKey_nonempty`, `minViewWithKey_correct`, `minViewWithKey_model`, `minView_correct`, `minView_model` |
| Validity and termination | `minViewWithKey_some`, `minView_some`, `extraction_well_founded` |
| Actual recursive bodies | `assocs_recurses_on`, `assocs_unfold`, `assocs_model`, `unfoldr_valid_eq`, `unfoldr_valid_model`, `foldMap_recurses_on`, `foldMap_unfold`, `foldMap_model` |
| Instances and inherited defaults | All twelve Foldable methods in extraction order; full-entry Eq/Ord method equations and explicit coherence laws; behavioral Semigroup/Monoid/Functor laws. See COVERAGE for each method. |

These names are in [PriorityOperations.v](theories/PriorityOperations.v).
[PriorityModel.v](theories/PriorityModel.v) supplies the independent stable-list
and summary proofs and Entry/Prio method contracts.
[PriorityRegression.v](theories/PriorityRegression.v) retains the five public
guard-order regression equations.

The shared [ApplicationLaws.v](theories/ApplicationLaws.v) extends Eq/Ord laws to
general Boolean equality and comparator tie equivalences. `queue_eq_reflexive`,
`queue_eq_symmetric`, and `queue_eq_transitive` need only component `EqLaws`,
`PriorityOrderLaws`, and valid queue operands. `queue_comparison` and
`queue_compare_ties` use `CoreInstances.ComparisonLaws`; `queue_order` and
`queue_minmax` also use component `EqCompare`. Antisymmetry and extrema identities
use Boolean equality, not equality of raw shapes or models. All model-based
queue laws retain the valid-input domain and `PriorityOrderLaws`. Stronger
propositional-reflection results in PriorityOperations remain optional
corollaries, not the primary generic law coverage.

The [exact manifest](theories/assumptions.json) pins 98, 136, and five exports in
the three priority-specific modules: 188 closed reports, four with `deferredFix`
only, and 47 with both
`deferredFix` and `deferredFix_eq_on`. The four deferred-only theory entries are
`assocs_definition`, `foldMap_definition`, `min_valid`, and `max_valid`.
Extraction/decrease and the `recurses_on` proofs are closed; the two global
deferred axioms remain intentional dependencies of guarded unfolding.
ApplicationLaws adds a separate 37-export inventory: 25 closed, `queue_methods`
with only `deferredFix`, and 11 queue-law exports with both deferred axioms.
The final clean run matched all 1,048 audits across the complete 15-theory
manifest; the detailed evidence is in [VALIDATION.md](VALIDATION.md).

## Minimal source guidance

### Queue recursion and support

The queue retains this edit:

```text
termination Data.PriorityQueue.FingerTree.Foldable__PQueue_foldMap deferred
```

Its generated `deferredFix2` body still matches `minView q`, returns `mempty`
for `None`, and recurses on `q'` for `Some (v, q')`. The existing scoped rename
of `GHC.Internal.Data.Foldable.foldMap` connects the self-call to the generated
method; it does not replace that method.

Other retained guidance addresses concrete translation needs:

- Constructor renames `Prio -> MkPrio`, `Entry -> MkEntry`, and
  `PQueue -> MkPQueue` avoid Rocq type/constructor name collisions.
- References to core `<|` and `|>` use the core's `consTree` and `snocTree` names.
- The midamble supplies a local `DefaultPQueue` instance with default value
  `MkPQueue Empty` for partial branches. It also defines `pqueue_size` from the
  independent `CoreSize.size`, ignoring cached measurements. These definitions
  alone are not termination proofs; PriorityOperations now supplies the
  valid-domain decrease and guarded-recursion proofs.

Public signatures are unchanged: no operation or required instance gains a
`Default` premise or a refined result type. `assocs` remains the source call
`Data.OldList.unfoldr minViewWithKey`.

### Approved single-function redefinition

The user explicitly approved `redefine` for `minViewWithKey` on 2026-11-02 and
required this exception to be documented. The pinned source at
`fingertree/Data/PriorityQueue/FingerTree.hs:238-246` protects the lazy binding
`Prio k v = measure q` with `FT.null q`. The old translation instead matched
the measure first. Its empty equation failed with
`Unable to unify "None" with "Err.patternFailure"`.

The directive in the queue's module edits makes the empty guard outermost.
Only the nonempty branch demands the cached `MkPrio`, performs the existing
split, and returns the original priority/payload and extraction/reappend result.
The `"can't happen"` and failed-measure branches remain guarded. The complete
public type is unchanged, with no new `Default` premise or validity restriction.
This function body is manually supplied through edits; it is the sole approved
exception to source-generated algorithm bodies. The Haskell source and license
remain unchanged. [ASSUMPTIONS.md](ASSUMPTIONS.md#approved-translation-exception-minviewwithkey)
contains the permanent decision record.

### Source `unfoldr`

The new 9.2 file
`../rocq9.2/base-src/module-edits/Data/OldList/edits` contains only these two
directives:

```text
in Data.OldList.unfoldr termination go deferred
in Data.OldList.unfoldr rewrite forall g, GHC.Base.build g = g cons nil
```

The first defers the source worker `go`. The second specializes the source's
fusion producer to a list result, for which `default_list` supplies the deferred
result inhabitant. The worker's step, branches, and recursive call remain
generated from the existing GHC source. There is no manual unfold algorithm,
fuel parameter, or `redefine`.

The 9.2 wrapper constructs `deps/OldList.edits` by removing **only**
`skip Data.OldList.unfoldr` from authoritative OldList guidance and appending the
two directives. It reuses the existing source, other edits, preamble/midamble,
and generation recipe. A per-stem `GHC_INTERNAL_EDITS_Data/OldList` override
selects this effective file without affecting prerequisite modules on GNU Make
3.81. The [foundation guide](../rocq9.2/README.md#source-unfoldr-restoration)
documents the shared hook; the 8.20 and 9.0 generated outputs are unchanged.

## Reproduce compilation and audits

From the worktree root:

```bash
opam exec --switch=cs2-rocq92 -- make -j2 -C examples/rocq9.2 check
opam exec --switch=cs2-rocq92 -- \
  make -j2 -C examples/fingertree kernel-check core-check priority-check
```

`kernel-check` compiles and recursively checks all three example modules and
all fifteen final theories, including ApplicationLaws, enforcing the exact
theory manifest. The separate `priority-check` group still selects the three
priority-specific modules, not the shared ApplicationLaws module.
`priority-check` runs
[`check-priority-audit.py`](module-edits/Data/PriorityQueue/FingerTree/check-priority-audit.py),
which compiles both audit files, checks the generated queue's complete
declaration inventory, and enforces the exact assumption set for each report.
The Make target then recursively kernel-checks `Data.OldList`,
`Rocq92Checks.Unfoldr`, `Data.PriorityQueue.FingerTree`,
`PriorityChecks.PriorityAudit`, and all three priority theories,
without `-admit` or `-norec`.

The checker also enforces all five theorems in `PriorityRegression.v` and their
exactly closed assumption reports: the two polymorphic empty equations, both
views at `PQueue bool Empty_set`, singleton extraction with the explicit
`k <= k = true` premise, and four concrete extractions covering priority order,
ties, payloads, and reappend. This public-boundary regression first failed on
the old generated body and passes after the approved edit.

### Queue inventory

[`PriorityAudit.v`](module-edits/Data/PriorityQueue/FingerTree/PriorityAudit.v)
explicitly checks all 74 queue declarations:

| Category | Count | Closed | Only `deferredFix` |
| --- | ---: | ---: | ---: |
| Datatypes | 3 | 3 | 0 |
| Public operations | 9 | 9 | 0 |
| Generated dictionaries | 11 | 8 | 3 |
| Local methods, including inherited defaults | 46 | 26 | 20 |
| Internal operations (`unionPrio`, `below`, `assocs`) | 3 | 2 | 1 |
| `DefaultPQueue` and `pqueue_size` | 2 | 2 | 0 |
| **Total** | **74** | **50** | **24** |

The additional `Data.OldList.unfoldr` entry depends only on `deferredFix`, giving
**75 reports**. The 24 queue dependencies are the recursive PQueue Foldable
methods and dictionary, the Eq/Ord methods and dictionaries, and `assocs`.
`Foldable__PQueue_null` is closed. All nine public operations are closed:
`empty`, `singleton`, `union`, `insert`, `add`, `fromList`, `null`, `minView`, and
`minViewWithKey`. These are declaration/dependency checks, not proofs of their
behavior.

### Foundation unfolding check

[`Unfoldr.v`](../rocq9.2/checks/Unfoldr.v) checks the exact signature:

```coq
forall (b a : Type), (b -> option (a * b)%type) -> b -> list a
```

It proves `unfoldr_rank_eq` under an all-step natural-rank decrease premise,
then proves `unfoldr_countdown_three`: seed `3` emits `[2; 1; 0]`.
Its four exact assumption sets are:

- `Data.OldList.unfoldr`: only `deferredFix`;
- `unfoldr_rank_eq`: `deferredFix` and `deferredFix_eq_on`;
- `countdown_decreases`: closed;
- `unfoldr_countdown_three`: `deferredFix` and `deferredFix_eq_on`.

No `ClassicalChoice` or `Eqdep` appears in these reports. The separate classical
`DeferredFixImpl` realization is not wired into this implementation.

### Historical clean integration before the guard repair

Both the new foundations and the example were cleaned, with explicit absence
checks before rebuilding. The following commands passed with Rocq 9.2:

```bash
opam exec --switch=cs2-rocq92 -- make -s -j2 -C examples/rocq9.2 check
opam exec --switch=cs2-rocq92 -- \
  make -s -j2 -C examples/fingertree kernel-check core-check priority-check
```

All **107/107 SHA-256 comparisons** passed for foundation/example sources and
interfaces, both foundation projects, and `CoreSize.v`. Evidence is under
`/var/folders/3c/qfxwcbpj7q590cwh0_scnyl80000gn/T/opencode/`:
`unfoldr-foundations-20261102.log`, `unfoldr-example-20261102.log`, and
`unfoldr-integration-20261102.sha256`.

At that checkpoint, the source pin was `2f303a410c95802a2824b6dd54a0610fa5329858`,
with a clean source tree. Parent HEAD was `e4bc91cc` on branch `fingertree`;
implementation changes were uncommitted.
[REGRESSIONS.md](REGRESSIONS.md#targeted-unfoldr-follow-up-2026-11-02)
records the targeted harness and old-base regeneration checks, not a new full
catalog run or a formal review verdict.

## Guard-order repair and proved unfolding obligations

The source protects a refutable lazy binding with the empty guard:

```haskell
minViewWithKey (PQueue q)
  | FT.null q = Nothing
  | otherwise = ...
  where
    Prio k v = measure q
```

The old generated function matched `measure q` before testing `null q`.
On a valid empty queue, `measure q` is `NoPrio`, so it reached the `Qed`-opaque
`GHC.Err.patternFailure`. The approved redefinition repairs that match nesting,
and both public empty equations end in `Qed` without assumptions.
`minViewWithKey_nonempty` now proves the general successful path: the measure is
`MkPrio k v`, the split right side has a view, the selected full entry is `(k,v)`,
and reappend returns a valid smaller queue. Thus neither guarded partial branch
is reached on valid calls. No proof identifies opaque error values with Empty.

`assocs_recurses_on` uses `P := valid` and `ltof _ pqueue_size`.
`foldMap_recurses_on` uses validity and that rank on the queue component of its
`(mapping function, queue)` input. `minViewWithKey_some` and `minView_some`
prove both validity preservation and decrease. `prio_right_id` discharges the
identity premise of `CoreSize.split_viewl_append_lt`. These facts justify the
guarded equations and independent-model results; they do not remove the
authorized global `deferredFix` or `deferredFix_eq_on` assumptions.

### Historical guard-repair validation

After the redefinition, the then-current `kernel-check core-check priority-check`
command passed on Rocq 9.2. The 74-declaration queue inventory remained 50 closed
and 24 depending only on `deferredFix`; `OldList.unfoldr` was report 75.
The four foundation assumption sets and five closed regression reports all
matched. Recursive kernel checking included the new regression theory.
Core/interval source-interface pairs and the queue interface matched the earlier
manifest; only the regenerated queue source differed. The earlier clean 107/107
comparison is a pre-redefinition record, not evidence for this changed source.

Evidence under the approved temporary directory:
`minview-red-20261102.log`, `minview-generation-20261102.log`,
`minview-priority-check-20261102.log`, `minview-integrated-20261102.log`, and
`minview-assumptions-20261102.log`. Parent HEAD and the staged-diff hash were
unchanged. No logical axioms or admissions were added by that repair.

## Historical diagnostics (not current blockers or implementation)

Before authorization, the plain source Foldable `fix` failed with
`Cannot guess decreasing argument of fix.` A temporary measure edit exposed
the obligation `minView q = Some (v, q') -> pqueue_size q' < pqueue_size q` on
arbitrary raw queues. Opaque `error` and `patternFailure` results prevented that
raw-domain proof; no such measure proof was retained.

The pre-authorization plain-`fix` queue source had SHA-256
`a3e1910d7dab619ff699ab75979e1824299dd827610352c615894f495647ac9d`.
That identifies the earlier diagnostic artifact, not the current output in the
integrated manifest.

Temporary copies replaced Foldable, then `assocs`, with diagnostic axioms to
expose the next failures. They showed the missing `Data.OldList.unfoldr` and
the valid-empty goal reducing to opaque `patternFailure = None`. Those copies
were not accepted outputs. The deferred Foldable edit resolved the first
compilation failure; source `unfoldr` restoration now resolves the second.

A separate temporary experiment refined only error results to carry size
bounds, while preserving public signatures. It proved decrease and empty-output
lemmas in that **modified model**, with closed reports, but required manual
replacement of the generated `patternFailure` fallthrough (and temporary
diagnostic axioms for the then-unresolved recursion dependencies). Existing
scoped/global rewrites and renames did not reach that fallthrough because it
was inserted after expression rewriting. Even the refined empty-output proof
did not establish source error unreachability or repair lazy-binding semantics.
This experiment is not integrated and is not evidence for current queue proofs.
Its retained evidence is in the approved temporary directory at
`fingertree-priority-refined-error-temp/`.

An earlier fuel-based `unfoldr_fuel`/`foldMap_fuel` replacement was rejected and
removed: it replaced source recursion and bypassed, rather than proved, the
queue decrease. Neither it nor `theories/PriorityTermination.v` is part of the
current implementation. The accepted route uses source recursive bodies, the
explicitly authorized deferred interface, and the sole manual `minViewWithKey`
exception. The validity, termination, and correctness obligations left open by
those early experiments are now proved in PriorityOperations. The historical
diagnostics are not current blockers or implementations.
