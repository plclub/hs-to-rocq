# Finger-tree proof interfaces

The fifteen theories implement the required functional contracts for the core,
interval map, and priority queue, including instance methods/defaults and generic
applicative traversal. The final clean Rocq 9.2 run compiled all fifteen,
matched all 1,048 exact assumption audits, and passed recursive kernel checks.
[VALIDATION.md](../VALIDATION.md) records local acceptance and reproducibility;
[FINAL-REGRESSIONS.md](../FINAL-REGRESSIONS.md) records the six passing non-HLint
catalog jobs with their toolchain qualifications. Formal pinned-range review
has not been completed; no verdict or axis finding count is claimed.

Use [COVERAGE.md](../COVERAGE.md) to find a public operation or instance and its
premises. Use [ASSUMPTIONS.md](../ASSUMPTIONS.md) for global dependencies and the
sole approved manual algorithm body, `Data.PriorityQueue.FingerTree.minViewWithKey`.
The remaining example algorithms and required dictionaries are source-generated.
The proofs concern finite values of the Gallina definitions, not a formal
compiler-correctness, complexity, or Haskell partiality theorem.

## Module guide

All logical names start with `FingerTreeProofs.`. Interpretations and validity
predicates inspect raw translated constructors; they do not define correctness
by the source operations they are meant to verify.

| Module | Purpose and entry points |
| --- | --- |
| [CoreSize](CoreSize.v) | Independent `sizeWith`/`size`; weighted views, append, split, and strict extraction decrease. Used by generated application termination proofs. |
| [CoreModel](CoreModel.v) | `contentsWith`, `contents`, `listMeasure`, `validityWith`, `validity`; source folds and measurement agree with the independent model under explicit laws. |
| [CoreOperations](CoreOperations.v) | Construction, concatenation, views, reversal, safe/unsafe maps, and split reconstruction/validity. Stronger `*With` interfaces lift leaf predicates through nonregular middle nodes. |
| [CoreSearch](CoreSearch.v) | `search_correct`, `search_classification`, `crossing_unique`, `split_correct`; actual-call domain certificates and parametricity over cuts/nonempty prefixes. |
| [CoreContext](CoreContext.v) | Independent positional/contextual list references; exact original-prefix/suffix arguments; maps, left/right folds, output validity and measurement. |
| [CoreInstances](CoreInstances.v) | All required core Eq/Ord, Measured, Foldable, algebra, and conditional view-Functor methods and law bundles. `FoldableBehavior` specifies all twelve actual fields; `foldable_null_length` links two observations. |
| [ApplicativeValidity](ApplicativeValidity.v) | Constructive `HoldsF`, its functor/applicative closure, and independent left-to-right `traverse_list`. Validity is inside the effect, not an assertion that effects disappear. |
| [CoreTraversal](CoreTraversal.v) | All four named traversals: contents/effect sequencing, rebuilt or preserved caches, and occurrencewise contextual mapping premises for arbitrary lawful applicatives. |
| [PriorityModel](PriorityModel.v) | `PriorityOrderLaws`, independent full-entry stable ordering and winning summaries; Entry and Prio method behavior. No raw-tree sortedness requirement. |
| [PriorityOperations](PriorityOperations.v) | Raw entries, public ordered `model`, `valid`, queue operation and instance-method contracts, error-safe extraction/decrease, and proved `recurses_on`/guarded unfolding for source `assocs` and Foldable. |
| [PriorityRegression](PriorityRegression.v) | Five closed equations guarding the approved empty-guard repair, including empty payload types and a nonempty tie/payload/reappend example. |
| [IntervalModel](IntervalModel.v) | `EndpointOrderLaws`, full `entries`, closedness/sortedness/cache `valid`, summary semantics, and nonempty-prefix summary domains. |
| [IntervalOperations](IntervalOperations.v) | All interval operations and method behavior; retained error-predicate safety, exact filters/stable merge, bounds, payload maps/folds/effects, and validity. |
| [IntervalLaws](IntervalLaws.v) | Optional propositional-reflection Eq/Ord bundles and generic Traversable identity, composition, and naturality for Node and IntervalMap. |
| [ApplicationLaws](ApplicationLaws.v) | Generic Boolean Eq and comparator tie-equivalence laws for Interval, Node, IntervalMap, and valid PQueue values. Reuses CoreInstances law predicates without propositional reflection; includes Ord methods, order/extrema bundles, and pair/list bridges. |

Read CoreModel before CoreOperations, then CoreSearch and CoreContext. Read
ApplicativeValidity before CoreTraversal. PriorityOperations combines the core
contracts with PriorityModel. IntervalOperations combines IntervalModel with
the core search/traversal interfaces; IntervalLaws adds reflection and traversal
laws. ApplicationLaws combines the application model equations with
CoreInstances' general Eq/comparison interfaces. It is shared by both applications,
not counted in either application's three-module group.
The [Makefile](../Makefile) records compilation dependencies, including CoreSize
before the generated applications.

## Choosing premises and equality

* Generic measurements need propositional associativity and identities where
  stated, not Eq/decidable equality or commutativity. Raw list and size equations
  often require fewer premises than cache-validity theorems.
* Contextual arguments measure the original prefix/suffix, excluding the
  current occurrence. Unsafe transformations preserve each produced leaf's
  measure in the same monoid. Rebuilt transformations may change monoids.
* Search classification does not assume monotonicity. Monotonicity gives a
  unique sequence cut, not unique returned shapes. Split's reference scans
  nonempty prefixes and cuts before the triggering element; no general
  `p mempty = false` premise is imposed.
* Priority validity includes the supplied total preorder and full winning
  cache, not raw sortedness. Interval validity includes endpoint laws, closed
  intervals, sorted full entries, and caches.
* Contents/model equality is behavioral, not raw-constructor equality.
  ApplicationLaws uses `EqLaws` and `CoreInstances.ComparisonLaws` to admit
  nontrivial Boolean and comparison equivalences. `EqCompare` relates Boolean
  equality to comparison ties, not propositional equality. Interval class laws
  do not require `EndpointOrderLaws`, closedness, sortedness, or cache validity;
  queue class laws retain `PriorityOrderLaws` and the valid-input domain.
* `IntervalLaws.ComparisonLaws` and `PriorityOperations.ComparisonLaws` require
  comparison ties iff propositional equality. Their reflection bundles remain
  optional stronger corollaries. They are not the primary generic law coverage;
  qualify the names to distinguish them from CoreInstances' predicate.

## Exact transitive-assumption audit

[assumptions.json](assumptions.json) pins every theory's export count and named
exceptions to an empty global-assumption set. The final clean audit matched all
**1,048** entries:
947 closed, 38 with functional extensionality only, five with `deferredFix`
only, and 58 with both `deferredFix` and `deferredFix_eq_on`. ApplicationLaws
contributes 37 exports: 25 closed, one deferred-only (`queue_methods`), and 11
with both deferred axioms. The inventory includes helper
definitions and record fields, not just public theorems. The
[assumption record](../ASSUMPTIONS.md#exact-final-theory-manifest) gives per-module
counts and explains why proved guarded-recursion obligations leave the two
authorized global axioms explicit.

[check-assumptions.py](check-assumptions.py) compiles each theory and a fresh,
fully qualified audit. It checks inventory completeness, golden counts, marker
pairing, and each exact transitive assumption set. Outputs and logs are under
`../deps/proof-audits/`. Normal `make` runs these checks; `kernel-check` then
recursively checks all libraries and all fifteen theories, including
ApplicationLaws. The separate core/interval/priority group targets do not select
that shared module. See the
[build commands](../README.md#build-and-check). Reading the manifest or finding
`Qed` is not a substitute for either check on later changes. The successful
run and the separate [formal-review status](../README.md#revision-and-review-status)
are recorded without treating one as a substitute for the other.
