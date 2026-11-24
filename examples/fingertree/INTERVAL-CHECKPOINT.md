# Interval-map verification and historical translation checkpoint

## Completed proof interfaces: 2026-11-02

All 13 required interval-map operations and 17 required instances now have
functional contracts, including inherited methods/defaults. The final clean
Rocq 9.2 run compiled and recursively kernel-checked the three interval-specific
theories and shared ApplicationLaws module, with every exact assumption audit
matching. [VALIDATION.md](VALIDATION.md) records completed fifteen-theory local
acceptance; [FINAL-REGRESSIONS.md](FINAL-REGRESSIONS.md) records the qualified
old-target results. Formal pinned-range review has not been completed; no verdict
or axis finding count is claimed. The historical compilation evidence below remains
limited to its earlier source state.

| Theory | Completed interface |
| --- | --- |
| [IntervalModel](theories/IntervalModel.v) | Full entry-list model; endpoint laws, closedness, lexicographic sortedness, raw cache validity; summary endpoints and nonempty-prefix domains. |
| [IntervalOperations](theories/IntervalOperations.v) | All public operations, exact filters/stable merge, smallest enclosing bounds, validity, error-predicate safety, and all actual instance methods/defaults. |
| [IntervalLaws](theories/IntervalLaws.v) | Optional propositional-reflection Eq/Ord bundles; generic Traversable identity/composition/naturality for Node and IntervalMap. |
| [ApplicationLaws](theories/ApplicationLaws.v) | Generic Boolean Eq and comparator tie-equivalence laws for Interval, Node, and IntervalMap, including Ord methods and order/extrema bundles; also shared with the queue. |

The [manifest](theories/assumptions.json) pins 294 exports in the three
interval-specific modules: 54 in IntervalModel,
158 in IntervalOperations, and 82 in IntervalLaws. The final run matched its
274 closed reports and 20 with only functional extensionality (13 and seven in
the latter two modules). No deferred-recursion assumption appears in these theories.
The original specification already permitted the reported extensionality.
ApplicationLaws is counted separately: 37 exports, comprising 25 closed
interval/pair/list laws and 12 queue entries with the authorized deferred
dependencies. The complete manifest has 15 theories and 1,048 audits.

[COVERAGE.md](COVERAGE.md#interval-map-operations-13) lists every theorem and
premise. The model retains full entries, duplicates, tie order, and payloads.
`singleton_spec` requires closedness for validity; `insert_reversed` proves that
reversed intervals are a no-op. Queries are exact ordered filters, and `union_spec`
is a left-stable merge, not a membership-only statement. The retained
`NoInterval` errors are unreachable on valid calls by `interval_split_domain`,
`prefix_summary_nonempty`, and the `*_split_safe` equations linked to the actual
generated split behavior.

The traversal proofs quantify over arbitrary lawful applicatives and retain
effects through `HoldsF`. Payload-only transformations preserve interval
measurements, justifying unsafe core mapping/traversal. Map algebra and traversal
laws compare entry observations, not raw tree shapes. ApplicationLaws now
provides the primary generic Eq/Ord laws: component `EqLaws` for Eq, and
`CoreInstances.ComparisonLaws` plus `EqCompare` for Ord, with `<`/compare
coherence on endpoints for Interval and on payloads for Node. These class laws
hold on raw values without `EndpointOrderLaws`, closedness, sortedness, or cache
validity. The stronger reflection bundles remain useful optional corollaries.
Construction, queries, merge, and other interval operations retain their
existing endpoint-law and validity premises.

The interval algorithm and required-instance bodies remain source-generated.
The example's sole approved manual algorithm body is the queue's
[`minViewWithKey`](ASSUMPTIONS.md#approved-translation-exception-minviewwithkey).

## Historical translation/compilation result

The pinned `Data.IntervalMap.FingerTree` source translated and compiled
against the rebuilt core and `CoreSize`, with source-derived Eq/Ord:

- all required Eq/Ord dictionaries were emitted from the unchanged source
  deriving clauses (`Eq___Interval`, `Eq___Node`, `Ord__Interval`,
  `Ord__Node`) plus the explicit source `Eq___IntervalMap`/`Ord__IntervalMap`;
- no handmade Eq/Ord or comparison helpers remained in the midamble;
- `lib/Data/IntervalMap/FingerTree.v` and `.h2ci` were generated and nonempty;
- `rocq c -w +deprecated-dirpath-Coq` exited zero;
- `rocq check -silent Data.IntervalMap.FingerTree` exited zero;
- an explicit `Print Assumptions` audit over all 17 required dictionaries, the
  13 public operations, and internal `inRange` (31 reports) gave 31
  `Closed under the global context`.

That was a translation/compilation milestone, before functional verification.
At that stage the queue was blocked on source recursion, missing `unfoldr`, and
lazy guard ordering. Those blockers were subsequently resolved by the authorized
deferred interface, source `unfoldr` restoration, and the one-function exception.

## Historical source and core state

- Source pin: `2f303a410c95802a2824b6dd54a0610fa5329858`
- Source and `LICENSE` diff: empty; `make -s check-source` exited zero.
- Core: regenerated 03:00 with native source-derived Eq/Ord.
- `CoreSize.v` recompiled 03:00 against that core; recursive kernel check
  passed (41 closed reports as recorded in `CORE-CHECKPOINT.md`).
- Rocq 9.2 via `opam exec --switch=cs2-rocq92`.

`CORE-CHECKPOINT.md` records the repair of the earlier core omission: the expanded
core retained all six source-derived ViewL/ViewR/SearchResult Eq/Ord dictionaries
and passed the 131-report inventory audit. This interval checkpoint used that
expanded core and rebuilt CoreSize.

## Files changed by the historical checkpoint

- `module-edits/Data/IntervalMap/FingerTree/edits`
- `module-edits/Data/IntervalMap/FingerTree/midamble.v`
- `INTERVAL-CHECKPOINT.md`
- generated application outputs under `lib/Data/IntervalMap/`

No core, `CoreSize.v`, translator, Makefile, Haskell source, shared
documentation, or Git state was changed by this checkpoint.

## Minimal edit justification

1. **Four constructor renames** (`Interval`, `Node`, `IntInterval`,
   `IntervalMap` to `Mk*`): Rocq has one namespace for types and constructors.
2. **`Data.FingerTree.<|` to `consTree`**: the core translation already uses
   the renamed recursive helper; this is the smallest reference rename.
3. **Scoped `Foldable` eta-expansion**: the generated nested
   `foldMap (foldMap f) t` needs the inner element type for inference; the
   scoped rewrite adds only that binder type.
4. **`in Data.IntervalMap.FingerTree.union inline mutual merge2`**: the
   translator expands the saturated helper call site before `wfFix`, with
   capture-safe freshening (`inlined_N__` locals). The recursive call is placed
   directly under the outer `wfFix2` arguments, so the existing structural
   obligation tactic works without helper-bound obligations. The standalone
   `merge2` binding remains and its source body is retained; there is no
   copied source-helper body rewrite in the edits.
5. **`set type merge2`**: the retained nonrecursive helper binding needs its
   two argument types for inference; without it Program leaves an element type
   unresolved. The `@`/plain `FingerTree` spellings are definitionally equal and
   prevent binder consolidation from collapsing the two arguments.
6. **`set type matches` and `termination matches {measure (size xs)}`**:
   `inRange`'s local `matches` is not structurally recursive through
   `dropUntil`/`viewl`; CoreSize supplies `viewl_size_lt` and
   `dropUntil_size_le`.
7. **`merge1` termination**: `measure (size as_ + size bs)` with
   CoreSize `viewl_size_lt`/`split_size_bounds`.
8. **Two scoped identity renames**:
   `in Ord__Interval_op_zl__ rename value GHC.Base.compare = GHC.Base.compare`
   and the same for `Ord__Node_op_zl__`. This is the Writer Lazy / core
   ViewL precedent: it keeps the first-field `compare` as the class method
   instead of redirecting it to the instance-local compare helper. No
   pre-renamed module variant was needed; the compiled output uses
   `GHC.Base.compare` at the field type.
9. **Three minimal order edits**:
   `Eq___Interval` before `Eq___Node_op_zeze__`,
   `Ord__Interval` before `Ord__Node_compare`, and
   `Ord__Interval` before `Ord__Node_op_zl__`, so source-derived dictionaries
   precede their field consumers.

The interval module has no `redefine`, manual operation, required `skip`,
`Admitted`, `admit`, `Axiom`, deferred recursion, or public domain narrowing.

## Inventory

Generated required instances (17):

- `Eq`/`Ord` for `Interval`, `Node`, `IntervalMap`;
- `Semigroup`/`Monoid` for `IntInterval` and `IntervalMap`;
- `Measured (IntInterval v) (Node v a)`;
- `Functor`/`Foldable`/`Traversable` for `Node v` and `IntervalMap v`.

All methods and inherited defaults compile. Public operations (13):
`low`, `high`, `point`, `empty`, `singleton`, `insert`, `union`,
`intersections`, `dominators`, `search`, `bounds`, `leastView`, `splitAfter`.
Internal `inRange` is also proof-audited, giving 14 operation names. Internal
error predicates `atleast`/`greater` and all `NoInterval` error branches are
retained verbatim. `Show` remains source-skipped as before.

## Historical commands and results

From `examples/fingertree`, using the Makefile's module-first precedence:

```sh
make -s deps/base.edits   # asserts exactly one literal skip line

rm -f lib/Data/IntervalMap/FingerTree.{v,h2ci,vo,vok,vos,glob} \
      lib/Data/IntervalMap/.FingerTree.aux

stack --allow-different-user exec hs-to-rocq -- \
  --target-version 9.0 -N \
  --iface-dir ../rocq9.2/base --iface-dir lib \
  -i fingertree --ghc -DTESTING --dependency-dir deps -o lib \
  -e module-edits/Data/IntervalMap/FingerTree/edits \
  -e edits -e deps/base.edits \
  --midamble module-edits/Data/IntervalMap/FingerTree/midamble.v \
  fingertree/Data/IntervalMap/FingerTree.hs

opam exec --switch=cs2-rocq92 -- rocq c \
  -w +deprecated-dirpath-Coq \
  -Q ../rocq9.2/base "" -Q lib "" -Q theories FingerTreeProofs \
  lib/Data/IntervalMap/FingerTree.v

opam exec --switch=cs2-rocq92 -- rocq check -silent \
  -Q ../rocq9.2/base "" -Q lib "" -Q theories FingerTreeProofs \
  Data.IntervalMap.FingerTree
```

Results: generation 0; compile 0; kernel check 0; audit 0 with 31
`Closed under the global context` (17 dictionaries + 13 public operations +
internal `inRange`). A second clean regeneration produced a
byte-identical `.v` and recompiled.

`deps/base.edits` differs from authoritative `../base-src/edits` by exactly:

```diff
-skip module GHC.Classes
```

No other base guidance differs.

## Historical checkpoint hashes (SHA-256)

```text
c843e98cf0e958c9664b1fe226a42180df4dd32a699131752d525c7925c978ef  lib/Data/IntervalMap/FingerTree.v
b72ac8d31aef80c4d30c143fbd1eaf75ca67e12782b439e0fb762e4221880b91  lib/Data/IntervalMap/FingerTree.h2ci
e5a250e8294a5ced4a704a1c28e879742adb7324083632c39df73434be21038e  lib/Data/IntervalMap/FingerTree.vo
d582163d34307a9514711ff317422f27d6e2a027b11f70a1caf9a98a1ad10618  module-edits/Data/IntervalMap/FingerTree/edits
1f263db2ac8d748b6f753570d4419d5f1fea1f437627f4d5a003a216602dd54d  module-edits/Data/IntervalMap/FingerTree/midamble.v
3fd4707a84c705ecb60399f152daafe43f57fba678c4b2f98805397656d0ca6d  lib/Data/FingerTree.v
cd4c3576a33a86305668b98dd15ed6de9a8871c6edee7b4f032d3dcc887f0265  lib/Data/FingerTree.vo
71377bf798f0c86b557b68049cd1fe2ea78fc8da173e81dc5b5927bd760c93f1  theories/CoreSize.v
cb3e5a42ab860f7ed3765833b93dfc0c693df7f38c8bc854b70c82a9e480683d  theories/CoreSize.vo
```

## Historical translator scope

The nonstructural inline-mutual callsite expansion was exercised by this
integration. Its `merge2` had two explicit parameters and was applied
saturated, matching the supported shape; partial, implicit, and dependent
helper forms were outside that feature. No additional generic change was needed
for that interval checkpoint.

Those helper-shape limits describe the translator feature exercised by that
checkpoint, not missing interval proofs. The three-library compilation milestone
subsequently passed; current functional coverage is summarized above. The
successful final fifteen-theory clean acceptance is recorded separately in
[VALIDATION.md](VALIDATION.md).
