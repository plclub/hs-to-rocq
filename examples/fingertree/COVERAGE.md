# Finger-tree verification coverage

The fifteen theories cover the required **27 core, 13 interval-map, and nine
priority-queue operations**, together with the **46 required instances** and
their translated methods/defaults. Proof development and Rocq 9.2 local
acceptance completed on 2026-11-02: all fifteen theories compiled from a clean
state, all 1,048 exact assumption audits matched, and recursive kernel checks
passed. [VALIDATION.md](VALIDATION.md) records the final run and 122 byte-identical
files; [FINAL-REGRESSIONS.md](FINAL-REGRESSIONS.md) records the six passing
non-HLint catalog jobs and remaining toolchain qualifications. Formal
pinned-range review has not been completed, as explained below.

The subject is the Gallina library translated from `fingertree-0.1.6.3`, pinned
at `2f303a410c95802a2824b6dd54a0610fa5329858`, with one explicitly approved
manual algorithm body: `Data.PriorityQueue.FingerTree.minViewWithKey`.
[ASSUMPTIONS.md](ASSUMPTIONS.md) records that exception and the authorized
deferred-recursion foundation. The claims concern finite values of these
definitions under the stated premises, not formal correctness of the compiler
or Haskell bottoms, strictness, `seq`, complexity, or persistency.

Operations: [core](#core-operations-27), [interval map](#interval-map-operations-13),
[priority queue](#priority-queue-operations-nine).
Instances: [core](#core-instances-18), [interval map](#interval-map-instances-17),
[priority queue](#priority-queue-instances-11),
[generic application laws](#generic-application-comparison-laws),
[all Foldable fields](#all-inherited-foldable-methods).

## How to read the contracts

Names such as `CoreOperations.append_contents` denote constants under
`FingerTreeProofs`. Each theory has a typed `Check`/`Print Assumptions` inventory;
the [theory guide](theories/README.md) maps the modules. Links below lead to the
actual statements, not merely to generated definitions with closed assumption
reports. The [exact manifest](theories/assumptions.json) lists 1,048 exported
constant audits, including definitions, helper lemmas, records, and record
fields. That is not a count of 1,048 public-operation theorems.

### Models and explicit premises

* **Core lists and caches.** [CoreModel.v](theories/CoreModel.v) defines
  `digitContentsWith`, `nodeContentsWith`, `contentsWith`, and `contents` by
  inspecting raw constructors, independently of source folds and measures.
  `validityWith mu P t` requires valid leaves and correct caches at every node
  level; `validity M t` uses the supplied `Measured` dictionary and the leaf
  predicate `True`. The source datatype enforces digit/node arities and balanced
  depth. `CoreSize.size` independently counts leaves and ignores caches.
* **Measurement laws.** Where a row says "monoid laws", it means the explicit
  propositional equations `mappend (mappend x y) z = mappend x (mappend y z)`,
  `mappend mempty x = x`, and `mappend x mempty = x` for the supplied dictionaries.
  They allow noncommutative monoids and require neither `Eq` nor decidable
  equality on measurements. They are not inferred from base-thy's
  Boolean-equality `MonoidLaws`. Some statements need only the subset specified
  below. All source-required dictionaries remain implicit or explicit arguments.
* **Intervals.** [IntervalModel.v](theories/IntervalModel.v) defines `entries`
  as full `(interval, payload)` entries in raw tree order. Its `valid` predicate
  includes `EndpointOrderLaws`, cache validity, closed stored intervals
  (`low <= high = true`), and `StronglySorted entryLE` in lexicographic
  `(low, high)` order. `EndpointOrderLaws` states exact Boolean/propositional
  equality, negated inequality, reflexive/transitive/antisymmetric/total `<=`,
  and coherence of `<`, `>`, `>=`, `compare`, `min`, and `max` with that order.
  Payload equality/order is not required for construction or queries.
* **Priorities.** [PriorityModel.v](theories/PriorityModel.v) defines independent
  stable ordering of full `(priority, payload)` entries. In
  [PriorityOperations.v](theories/PriorityOperations.v), `model q` is
  `ordered (rawEntries q)`. Its `valid` predicate requires `PriorityOrderLaws`
  and raw cache validity, **not sortedness of the raw tree**.
  `PriorityOrderLaws` requires only reflexivity, transitivity, and totality of
  the supplied Boolean `<=`: a total preorder suffices. Equivalent priorities
  need not be propositionally equal. A cached `Prio` stores the winning payload
  as well as its priority.

The core relation `CoreInstances.contentsEquiv`, interval equality of `entries`,
and queue relation `PriorityOperations.equivalent` compare observations, not raw
tree shapes. The core and [ApplicationLaws](theories/ApplicationLaws.v) Eq/Ord
laws admit nontrivial lawful Boolean equivalences on leaves and comparison ties.
Interval class laws need neither `EndpointOrderLaws` nor closedness, sortedness,
or cache validity; interval operation contracts still require their stated
endpoint/validity premises. Queue class laws retain the valid-input domain and
`PriorityOrderLaws` needed to interpret extraction. Stronger reflection bundles
remain optional corollaries under exact Boolean/propositional coherence, not
the primary generic law coverage. None of these laws narrows the generic
measurement domain.
In particular, equality of contents alone does not identify nonmonotonic search
behavior: different raw shapes may select different crossings.

## Core operations: 27

The source is [Data/FingerTree.hs](fingertree/Data/FingerTree.hs). The translator
names `<|` as `consTree`, `|>` as `snocTree`, and `><` as `op_zgzl__`.
In this table, "valid input" means `CoreModel.validity M` for each input tree.
Pure list equations often hold on all raw trees; their validity results are
listed separately rather than silently adding a validity premise to both.

| Operation | Typed theorem(s) | Contract and premises |
| --- | --- | --- |
| `empty` | [CoreOperations](theories/CoreOperations.v): `empty_contents`, `empty_validity` | Empty list and valid result; no monoid-law premise. |
| `singleton` | CoreOperations: `singleton_contents`, `singleton_validity` | Singleton list and valid result; no monoid-law premise. |
| `(<\|)` | CoreOperations: `consTree_contents`, `consTree_validity` | Prepend on all raw trees; validity from valid input, associativity, and right identity. |
| `(\|>)` | CoreOperations: `snocTree_contents`, `snocTree_validity` | Append one leaf on all raw trees; validity from valid input and monoid laws. |
| `(><)` | CoreOperations: `append_contents`, `append_validity` | List concatenation on raw trees; validity from both valid inputs and monoid laws. |
| `fromList` | CoreOperations: `fromList_contents`, `fromList_validity` | Exact input list; valid result under associativity and right identity. |
| `null` | CoreOperations: `null_contents`, `contents_empty_iff` | True exactly when contents are empty, equivalently the raw constructor is `Empty`; no laws or validity premise. |
| `viewl` | CoreOperations: `viewl_contentsWith`, `viewl_contract`; [CoreSize](theories/CoreSize.v): `viewl_empty_iff`, `viewl_size_lt` | Empty or head/tail decomposition; valid remainder from valid input, associativity, and right identity. Successful extraction strictly decreases raw size without cache/law premises. |
| `viewr` | CoreOperations: `viewr_contentsWith`, `viewr_contract`; CoreSize: `viewr_sizeWith` | Empty or initial-list/last-element decomposition; valid remainder from valid input and monoid laws. Weighted size reconstructs without validity/laws. |
| `search` | [CoreSearch](theories/CoreSearch.v): `search_correct`, `search_classification`, `search_empty`, `crossing_unique`, `search_domain_certificate`, `search_parametric_on_cuts` | Valid input and monoid laws give exact endpoint classification and an adjacent crossing for `Position`. Monotonicity is needed only for uniqueness of the cut; see below. |
| `split` | CoreSearch: `split_correct`, `split_empty`, `split_domain_certificate`, `split_parametric_on_nonempty_prefixes`; CoreOperations: `split_contract` | Valid input and monoid laws always give valid parts and reconstruction. `prefixMonotone` adds agreement with the nonempty-prefix reference; no `p mempty = false` premise. |
| `takeUntil` | CoreSearch: `takeUntil_correct`; CoreOperations: `takeUntil_validity`, `take_drop_contents` | Left split component; reference equality requires `prefixMonotone`, validity does not. |
| `dropUntil` | CoreSearch: `dropUntil_correct`; CoreOperations: `dropUntil_validity`, `take_drop_contents` | Right split component under the same premises as `takeUntil`. |
| `reverse` | CoreOperations: `reverse_contents`, `reverse_validity` | Reversed contents and rebuilt valid caches, even for an initially invalid raw tree; no monoid-law premise. |
| `fmap'` | CoreOperations: `fmap'_contents`, `fmap'_validity` | List map and rebuilt valid caches; element and measurement types may change. No input-validity or monoid-law premise. |
| `fmapWithPos` | [CoreContext](theories/CoreContext.v): `fmapWithPos_contents`, `fmapWithPos_validity`, `fmapWithPos_preserves`, `fmapWithPos_measure` | Original-prefix arguments from valid input and source monoid laws. Rebuilt cache validity holds independently; `preserves` uses `validityWith mu P t` and `forall l x, P x -> Q (f l x)`. Output-measure equality also needs target monoid laws. |
| `fmapWithContext` | CoreContext: `fmapWithContext_contents`, `fmapWithContext_validity`, `fmapWithContext_preserves`, `fmapWithContext_measure` | Original prefix and suffix under the same conditions; `preserves` uses `validityWith mu P t` and `forall l x r, P x -> Q (f l x r)`. |
| `unsafeFmap` | CoreOperations: `unsafeFmap_contents`, `unsafeFmap_validityWith`, `unsafeFmap_validity` | Contents are list map without laws. Cache validity requires valid input and `nu (f x) = mu x` in the **same monoid**; the generalized theorem also preserves `Q` from `P`. |
| `foldlWithPos` | CoreContext: `foldlWithPos_contents` | `positionFoldl` over original prefixes; valid input and monoid laws. No associativity premise on the callback. |
| `foldrWithPos` | CoreContext: `foldrWithPos_contents` | `positionFoldr` under the same premises; right association retained. |
| `foldlWithContext` | CoreContext: `foldlWithContext_contents`, `contextFoldl_cons` | `contextFoldl` over original prefix/suffix labels; valid input and monoid laws; left association retained. |
| `foldrWithContext` | CoreContext: `foldrWithContext_contents`, `contextFoldr_cons` | `contextFoldr` under the same premises; right association retained. |
| `traverse'` | [CoreTraversal](theories/CoreTraversal.v): `traverse'_contents`, `traverse'_validityWith` | Arbitrary lawful applicative; left-to-right list effects. Validity uses `validityWith mu P t` and `P x -> HoldsF Q (g x)`; target measure may differ. |
| `traverseWithPos` | CoreTraversal: `traverseWithPos_contents`, `traverseWithPos_validity_occurrences`, `traverse_pos_list_labels` | Lawful applicative, valid input, source monoid laws; mapping premise only at each original occurrence's prefix. |
| `traverseWithContext` | CoreTraversal: `traverseWithContext_contents`, `traverseWithContext_validity_occurrences`, `traverse_context_list_labels` | Same, with original prefix and suffix; occurrencewise mapping premise, not all possible contexts. |
| `unsafeTraverse` | CoreTraversal: `unsafeTraverse_contents`, `unsafeTraverse_measure` | Lawful applicative; list sequencing needs no measure/validity premise. Validity and unchanged cache require `validityWith mu P t` and `P x -> HoldsF (fun y => Q y /\ nu y = mu x) (g x)` in one monoid. |
| `measure` | [CoreModel](theories/CoreModel.v): `measure_contents`; [CoreInstances](theories/CoreInstances.v): `tree_measured_behavior` | Valid input and explicit monoid laws give the ordered list fold of element measures. |

### Search, split, and partial predicates

For `xs = contents t`, `CoreSearch.cutTest mu p xs i` is
`p (listMeasure mu (firstn i xs)) (listMeasure mu (skipn i xs))`. Let its endpoint
values be `b0` and `bn`. Without any monotonicity premise,
`search_classification` proves:

| `b0` | `bn` | Result |
| --- | --- | --- |
| `true` | `true` | `OnLeft` |
| `false` | `false` | `OnRight` |
| `true` | `false` | `Nowhere` |
| `false` | `true` | `Position l x r` |

For `Position`, `search_correct` proves validity of both trees,
`xs = contents l ++ x :: contents r`, and false/true tests at adjacent cuts
`length (contents l)` and its successor. `crossing_unique` requires
`cutMonotone` and bounds on both candidate cuts; it proves equality of indices,
not tree shapes. Other endpoint classifications do not exclude interior
crossings. On empty input `search_empty` permits only `OnLeft` or `OnRight`.

`splitReference` scans **nonempty prefixes**. If the first satisfying prefix has
length `k`, it cuts before element `k`, returning `take (k-1)` and `drop (k-1)`.
With no satisfying prefix it returns `(xs, [])`; on empty input it returns
`([], [])` without a predicate call. `prefixMonotone` quantifies only over
`0 < i <= j <= length xs`. Neither `split_correct` nor the domain theorem
assumes `p mempty = false` or a call at the empty prefix. A nonempty prefix may
itself measure to `mempty`, in which case that value is in the domain.
`split_trigger_contract` has an additional `p mempty = false` premise for its
particular boundary corollary, used by the queue; it is not the general split
specification.

The domain results are connected to the generated functions:

* `search_domain_certificate` includes both endpoints and `searchCalls` for
  recursive tests. `searchDigitTests_cuts` and the node/tree parametricity
  lemmas justify the helper calls. `search_parametric_on_cuts` proves that
  predicates agreeing on `cutDomain` give the same generated result.
* `split_domain_certificate` and `split_calls_on_nonempty_prefixes` account for
  the total-measure test and all internal tests. The digit/node/tree lemmas lead
  to `split_parametric_on_nonempty_prefixes`, an equality of actual split
  results for predicates agreeing on that domain.
* `searchCalls_nonempty` and `splitCalls_nonempty` rule out the internal empty
  error branches on these calls. Structural recursion and the `CoreSize`
  bounds supply termination independently of predicate monotonicity.

These are Gallina domain/parametricity results: callers with a partial source
predicate must supply its intended behavior on the stated domain. They are not
a formal semantics of arbitrary Haskell partiality. The interval proofs below
instantiate them for the retained source error predicates.

### Original contexts and generic effects

`CoreContext.contextMap_original_at` and `positionMap_original_at` identify the
label at a decomposition `xs = pre ++ x :: post` as the measures of `pre` and
`post`, excluding `x`. They preserve sequence order, including for
noncommutative measurement monoids. The fold references preserve each fold's
association; the traversal references sequence effects left to right.

[ApplicativeValidity.v](theories/ApplicativeValidity.v) defines
`HoldsF P fa` as an existential witness `z : F {a | P a}` whose projection by
`fmap proj1_sig` is `fa`. Its closure theorems `HoldsF_fmap`, `HoldsF_pure`,
`HoldsF_app`, and `HoldsF_liftA2` use the supplied `FunctorLaws` or
`ApplicativeLaws`. They do not erase effects: `HoldsF_None` is vacuous, whereas
`HoldsF_Some_iff` recovers the value predicate.

For contextual traversal, `traverseWithContext_validity_occurrences` requires
exactly `HoldsF Q (g (M pre) x (M post))` at every decomposition of the original
contents; the positional version omits the suffix argument. Both conclude
`HoldsF (validityWith nu Q)` of the result. The more general `*_validityWith`
helpers also expose a uniform `P`-preservation interface. Functional
extensionality used by sequencing and the positional occurrence proof is
explicit in [the manifest](theories/assumptions.json); the contextual occurrence
validity theorem itself has no global assumptions.

## Core instances: 18

The [generated core inventory](module-edits/Data/FingerTree/CoreAudit.v) retains
all 18 dictionaries and 83 local methods, including defaults. The following are
behavioral proofs, in addition to that declaration audit.

| Type and instance(s) | Methods and typed proofs | Premises and laws |
| --- | --- | --- |
| `Digit`: `Measured` | CoreInstances: `digit_measured_behavior` (`measure`) | Ordered leaf measure under monoid laws; no stored cache to validate. |
| `Node`: `Measured` | CoreInstances: `node_measured_behavior` (`measure`) | `nodeValidity mu P` and monoid laws. |
| `FingerTree`: `Measured` | CoreInstances: `tree_measured_behavior` (`measure`) | `validity M` and monoid laws. |
| `Digit`, `Node`, `FingerTree`: `Foldable` (three instances) | CoreInstances: `digit_foldable_behavior`, `node_foldable_behavior`, `tree_foldable_behavior` | Each proves all twelve conjuncts of `FoldableBehavior`; see the method table below. No cache-validity premise. |
| `FingerTree`: `Eq` | CoreOperations: `eq_contents` (`==`); CoreInstances: `tree_neq_default` (`/=`), `tree_EqLaws` | Behavior needs only leaf `Eq`; laws need leaf `EqLaws`, not exact propositional equality. |
| `FingerTree`: `Ord` | CoreOperations: `compare_contents`; CoreInstances: `tree_ord_methods`, `tree_ord_behavior`, `tree_OrderLaws` | `compare` is lexicographic over contents. The six other methods are covered by `OrdMethods`. Laws require leaf `ComparisonLaws` and `EqCompare` from CoreInstances. |
| `FingerTree`: `Semigroup`, `Monoid` | CoreInstances: `semigroup_contents` (`<>`), `mappend_contents`, `mempty_contents`, `mconcat_contents`; `append_congruent`, `append_associative`, `append_identities`, `mconcat_validity` | Algebra over `contentsEquiv`; validity uses monoid laws and valid operands (`Forall validity` for `mconcat`). `tree_SemigroupLaws`/`tree_MonoidLaws` additionally use leaf `EqLaws`; `append_boolean_congruent` preserves Boolean equality. |
| `ViewL`: `Eq`, `Ord` | CoreInstances: `viewL_eq_model`, `viewL_neq_default`, `viewL_EqLaws`; `viewL_compare_model`, `viewL_ord_methods`, `viewL_ord_behavior`, `viewL_OrderLaws` | Empty-first tagged model, then element and sequence. Eq laws need laws on both fields. Ord laws need comparison laws and Eq/compare coherence on both, plus `<`/compare coherence on the sequence field. |
| `ViewR`: `Eq`, `Ord` | CoreInstances: `viewR_eq_model`, `viewR_neq_default`, `viewR_EqLaws`; `viewR_compare_model`, `viewR_ord_methods`, `viewR_ord_behavior`, `viewR_OrderLaws` | Empty-first tagged model, then sequence and element. Same law premises, but `<`/compare coherence is needed on the element field. |
| `ViewL`, `ViewR`: conditional `Functor` (two instances) | CoreInstances: `viewL_fmap_behavior`, `viewR_fmap_behavior` (`fmap`); `viewL_replace_default`, `viewR_replace_default` (`<$`); `viewL_FunctorLaws`, `viewR_FunctorLaws` | A functor for the sequence parameter; its `FunctorLaws` give identity/composition. |
| `SearchResult`: `Eq`, `Ord` | CoreInstances: `search_eq_model`, `search_neq_default`, `search_EqLaws`; `search_compare_model`, `search_ord_methods`, `search_ord_behavior`, `search_OrderLaws` | Constructor-sensitive comparison, with contents comparisons for the two trees in `Position`. Eq laws need leaf `EqLaws`; Ord laws need leaf comparison laws and Eq/compare coherence. |

`CoreInstances.ComparisonLaws` states reflexivity, opposite comparison,
strict transitivity, and invariance under comparison ties. `EqCompare` equates
Boolean equality with a comparison tie; it does not equate ties with Rocq
equality. `OrdMethods` covers `<`, `<=`, `>`, `>=`, `min`, and `max`.
`OrderLaws` adds reflexivity/transitivity/totality, antisymmetry up to Boolean
equality, strict-order coherence, and greatest-lower/least-upper-bound laws.
`order_minmax_laws` derives the `MinMaxLaws` bundle (idempotence, commutativity,
associativity, absorption) for every row with `OrderLaws`.

## Interval-map operations: 13

The source is [Data/IntervalMap/FingerTree.hs](fingertree/Data/IntervalMap/FingerTree.hs).
All theorem names in this table are in
[IntervalOperations.v](theories/IntervalOperations.v). Order-dependent contracts
use `EndpointOrderLaws`; "valid" means the full interval invariant above.

| Operation | Typed theorem(s) | Contract and premises |
| --- | --- | --- |
| `low` | `low_spec` | Returns the stored lower endpoint; no laws or closedness premise. |
| `high` | `high_spec` | Returns the stored upper endpoint; no laws or closedness premise. |
| `point` | `point_spec` | Both endpoints equal the argument; closedness uses reflexivity of endpoint `<=`. |
| `empty` | `empty_spec` | Empty entry list and valid map under endpoint laws. |
| `singleton` | `singleton_spec` | Exactly one full entry; valid iff its interval is closed. The operation does not validate endpoints. |
| `insert` | `insert_spec`, `insert_reversed`, `insertEntries_before_equals` | A closed interval is inserted before existing equal intervals in a valid map; result valid. Reversed endpoints give the identical original map. |
| `union` | `union_spec`, `mergeEntries_left_equal` | Two valid inputs give a valid stable merge of full entries, with the left input first on equal intervals. |
| `search` | `search_spec` | On a valid map, exact ordered filter for `low i <= p <= high i`. |
| `intersections` | `intersections_spec` | Valid map and closed query; exact filter for `low i <= high q` and `low q <= high i`, including touching endpoints. |
| `dominators` | `dominators_spec` | Valid map and closed query; exact filter for `low i <= low q` and `high q <= high i`. |
| `bounds` | `bounds_none_iff`, `bounds_endpoints`, `bounds_enclosing` | Cache validity suffices for empty iff `None` and attained endpoints. Full validity gives a closed smallest enclosing interval. |
| `leastView` | `leastView_spec`, `leastView_none_iff` | On a valid map, removes the first full entry in interval order and preserves validity; `None` exactly when empty. |
| `splitAfter` | `splitAfter_spec` | On a valid map, valid parts are the exact filters at lower bounds `<= k` and `> k`. |

The filter and stable-merge equalities preserve complete entries, order, and
multiplicity; they are stronger than membership-only specifications.
`inRange_spec` verifies the shared query worker.
`IntervalModel.prefix_summary_nonempty` and
`IntervalOperations.interval_split_domain` prove that actual split predicates
receive `MkIntInterval`, never `NoInterval`. The equations
`atleast_split_safe`, `greater_split_safe`, `larger_split_safe`, and
`strict_larger_split_safe` connect those domains to the generated callers:
changing only the `NoInterval` branch has no effect on valid calls. The library's
original error branches remain unchanged.

`inRange_spec` and `union_spec` use proved `wfFix1_eq`/`wfFix2_eq` equations and
raw-size decrease. Their transitive functional-extensionality dependency is
reported; they introduce no deferred-recursion or operation axiom.

## Interval-map instances: 17

Abbreviations in this table are module names: `IntervalModel`,
`IntervalOperations`, [IntervalLaws](theories/IntervalLaws.v), and
[ApplicationLaws](theories/ApplicationLaws.v). Eq bundles use component `EqLaws`;
generic Ord bundles use `CoreInstances.ComparisonLaws` and `EqCompare`, not
propositional reflection.

| Type and instance(s) | Methods and typed proofs | Premises and laws |
| --- | --- | --- |
| `Interval`: `Eq`, `Ord` | IntervalOperations: `interval_equality_full`, `interval_inequality`, `interval_compare_full`, `interval_order_methods`; ApplicationLaws: `interval_EqLaws`, `interval_behavior`, `interval_order`, `interval_minmax` | Compares both endpoints, lexicographically for Ord. Eq laws need endpoint `EqLaws`. Ord bundles need endpoint comparison laws, `EqCompare`, and `<`/compare coherence. No `EndpointOrderLaws` or validity premise. |
| `Node`: `Eq`, `Ord` | IntervalOperations: `node_equality_full`, `node_inequality`, `node_compare_full`, `node_order_methods`; ApplicationLaws: `node_EqLaws`, `node_behavior`, `node_order`, `node_minmax` | Compares interval **and payload**. Eq laws need endpoint/payload `EqLaws`. Ord bundles need comparison laws and `EqCompare` on both types, plus payload `<`/compare coherence. No endpoint-validity or propositional-reflection premise. |
| `Node`: `Measured` | IntervalModel: `node_measure` | `measure (MkNode i a) = MkIntInterval i (high i)`; independent of payload. |
| `Node`: `Functor` | IntervalOperations: `node_fmap`, `node_replace`, `node_fmap_identity`, `node_fmap_composition`, `fmap_node_measure` | `fmap`/`<$` change only payloads and preserve measurements; identity/composition need no extra laws. |
| `Node`: `Foldable` | IntervalOperations: all `node_*` method equations in the small-container table below | Visits the single payload, not the interval. |
| `Node`: `Traversable` | IntervalOperations: `node_traverse`, `node_sequenceA`, `node_mapM`, `node_sequence`; IntervalLaws: `node_traversal_identity`, `node_traversal_composition`, `node_traversal_naturality`, `node_traversal_holds` | One payload effect, interval retained. Generic laws use arbitrary lawful applicatives; naturality uses `ApplicativeMorphism`. `mapM`/`sequence` also require their source Monad dictionary. |
| `IntInterval`: `Semigroup`, `Monoid` | IntervalModel: `summary_semigroup` (`<>`), `summary_mappend`, `summary_mempty`, `summary_mconcat`; `intervalUnion_assoc`, `intervalUnion_left_id`, `intervalUnion_right_id` | Propositional algebra under endpoint laws. Summary records the rightmost interval and maximum high endpoint, not a commutative set of intervals. |
| `IntervalMap`: `Eq`, `Ord` | IntervalOperations: `equality_entries`, `inequality_entries`, `compare_entries`, `map_order_methods`; ApplicationLaws: `map_EqLaws`, `map_behavior`, `map_order`, `map_minmax` | Full-entry comparisons on all raw maps. Eq laws need endpoint/payload `EqLaws`; Ord bundles need comparison laws and `EqCompare` on both types, with no extra `<` coherence. No closedness, sortedness, cache-validity, or `EndpointOrderLaws` premise. |
| `IntervalMap`: `Semigroup`, `Monoid` | IntervalOperations: `semigroup_union` (`<>`), `monoid_union`, `monoid_empty`, `monoid_concat`, `mconcat_spec`, `union_left_identity`, `union_right_identity`, `union_associative` | Stable-merge algebra over `entries` on valid inputs under endpoint laws. `mconcat_spec` requires `Forall valid`. |
| `IntervalMap`: `Functor` | IntervalOperations: `fmap_entries`, `replace_entries`, `fmap_valid`, `replace_valid`, `fmap_identity_entries`, `fmap_composition_entries` | Payload-only map; validity from valid input. Algebra is equality of entry lists. `fmap_node_measure` justifies the unsafe core map's unchanged caches. |
| `IntervalMap`: `Foldable` | IntervalOperations: the twelve `*_payloads` equations below | Visits payloads in entry order; on valid maps, this is interval order. |
| `IntervalMap`: `Traversable` | IntervalOperations: `traverse_entries`, `sequenceA_entries`, `mapM_entries`, `sequence_entries`, and their `*_valid` counterparts; IntervalLaws: `map_traverse_reference`, `map_traversal_identity`, `map_traversal_composition`, `map_traversal_naturality` | Arbitrary lawful applicatives, not just Identity/monads. Valid input gives `HoldsF valid` without an extra payload restriction. `mapM`/`sequence` additionally take a Monad dictionary. Laws compare full entries inside effects, not raw tree shapes. |

The [generic application-law interface](#generic-application-comparison-laws)
below gives the component comparison/coherence theorems and exact domains.
`IntervalLaws` retains useful optional reflection results:
`interval_order_spec`, `node_order_spec`, `map_order_spec`, and the
`interval_*_laws`, `node_*_laws`, and `map_*_laws` bundles for equality, order,
and extrema. They use `EndpointOrderLaws`; the Node/Map bundles additionally
use exact payload Eq/propositional coherence and
`IntervalLaws.ComparisonLaws`, with payload `<`/compare coherence for Node.
That comparison record requires `compare x y = Eq <-> x = y`, unlike the
generic core predicate. `OrderSpec` and `observational_*_laws` relate the
actual methods to observations without requiring an injective observation
function. These stronger results do not restrict the generic bundles above.

Traversal composition quantifies over two arbitrary lawful applicatives and
the actual `Compose` instance; `compose_functor_laws` and
`compose_applicative_laws` establish its laws. Naturality requires a polymorphic
`eta` satisfying `ApplicativeMorphism` (preserves `pure` and `liftA2`).
`morphism_fmap` is derived, not assumed. Map laws observe `entries` inside the
effect. `traverse_valid` separately proves that payload-only effects retain
intervals, sortedness, closedness, and caches.

## Priority-queue operations: nine

The source is [Data/PriorityQueue/FingerTree.hs](fingertree/Data/PriorityQueue/FingerTree.hs).
All names in this table are in
[PriorityOperations.v](theories/PriorityOperations.v). Model/validity contracts
use the supplied `PriorityOrderLaws`; no payload Eq or Default is needed.

| Operation | Typed theorem(s) | Contract and premises |
| --- | --- | --- |
| `empty` | `empty_model`, `empty_valid` | Empty model and valid queue. |
| `singleton` | `singleton_model`, `singleton_valid` | One full entry and valid queue. |
| `insert` | `insert_model`, `insert_valid`, `insert_ties` | Insert before existing equivalent priorities; validity from valid input. |
| `add` | `add_model_ordered`, `add_valid`, `add_ties` | Stable ordering after raw append; follows existing equivalent priorities. Validity from valid input. |
| `union` | `union_model`, `union_valid`, `union_ties` | Left-stable merge of models; preserves both inputs' full entries and tie order. Validity from both valid inputs. |
| `fromList` | `fromList_model`, `fromList_valid`, `fromList_ties` | Stable ordering of the entire input, retaining duplicates and tie order; always valid under priority laws. |
| `null` | `null_model` | True iff the ordered model is empty; no cache-validity premise. |
| `minViewWithKey` | `minViewWithKey_correct`, `minViewWithKey_model`, `minViewWithKey_some`, `minViewWithKey_none`, `minViewWithKey_nonempty` | Valid input: extract exactly the first full entry, preserve validity, and strictly decrease `pqueue_size`; `None` iff empty. This is the one approved manually supplied body. |
| `minView` | `minView_correct`, `minView_model`, `minView_some`, `minView_none` | Same remainder and size decrease, omitting only the extracted priority. |

`PriorityModel.ordered_permutation`, `ordered_sorted`, and `ordered_ties` prove
the independent model's multiplicity, ordering, and stability. They never
require raw-tree sortedness. `winner_at_cut` identifies the extracted **full
entry**, not just an equivalent priority. `minViewWithKey_nonempty` exhibits
the successful cached-`MkPrio`, split, `viewl`, and reappend branches; valid
inputs cannot take the failed-measure or "can't happen" branches.

### Repeated extraction and the source recursive methods

`extraction_well_founded` proves well-foundedness of successful extraction from
valid queues by `pqueue_size`. The guarded unfolding obligations are complete:

| Source recursion | Proved guard and decrease interface | Result |
| --- | --- | --- |
| `assocs = Data.OldList.unfoldr minViewWithKey` | `assocs_recurses_on` for `P := valid`, relation `ltof _ pqueue_size`; `minViewWithKey_some` supplies preserved validity and decrease | `assocs_definition`, `assocs_unfold`, `assocs_model`; equivalently `unfoldr_valid_eq`, `unfoldr_valid_model` |
| `Foldable__PQueue_foldMap` | `foldMap_recurses_on` for `P input := valid (snd input)`, rank `pqueue_size (snd input)`; `minView_some` supplies the recursive premises | `foldMap_definition`, `foldMap_unfold`, `foldMap_model` |

These proofs justify unfolding **on valid inputs**, not arbitrary malformed
queues. They retain the user-approved global `deferredFix` and
`deferredFix_eq_on` assumptions; proving the guard does not discharge those
axioms. The all-step foundation theorem `unfoldr_rank_eq` and its countdown
example are separate checks, not substitutes for this valid-domain proof.

## Priority-queue instances: 11

| Type and instance(s) | Methods and typed proofs | Premises and laws |
| --- | --- | --- |
| `Entry`: `Measured` | PriorityModel: `entry_measure_behavior` | Both priority and payload enter `MkPrio`. |
| `Entry`: `Functor` | PriorityModel: `entry_fmap_behavior`, `entry_replace_behavior`, `entry_fmap_identity`, `entry_fmap_composition` | Payload-only `fmap`/`<$`; direct laws, no equality premise. |
| `Entry`: `Foldable` | PriorityModel: the twelve `entry_*` equations below | Visits the single payload. |
| `Prio`: `Semigroup`, `Monoid` | PriorityModel: `prio_semigroup_behavior` (`<>`), `prio_monoid_append_behavior`, `prio_monoid_empty_behavior`, `prio_monoid_concat_behavior`, `prio_monoid_propositional_laws` | `unionPrio` selects the left full winner on ties. Associativity uses the priority preorder; identities are direct. No equality on summaries or payloads is required. |
| `PQueue`: `Eq` | PriorityOperations: `eq_model`, `neq_model`; ApplicationLaws: `queue_eq_reflexive`, `queue_eq_symmetric`, `queue_eq_transitive` | Full-entry comparison in extraction order. Generic laws require valid operands, `PriorityOrderLaws`, and priority/payload `EqLaws`, not propositional reflection. |
| `PQueue`: `Ord` | PriorityOperations: `compare_model`, `lt_behavior`, `le_behavior`, `gt_behavior`, `ge_behavior`, `min_model`, `max_model`, `min_valid`, `max_valid`; ApplicationLaws: `queue_methods`, `queue_comparison`, `queue_eq_compare`, `queue_order`, `queue_minmax` | All seven methods; generic comparison laws on valid operands under `PriorityOrderLaws` and component `CoreInstances.ComparisonLaws`. Order/extrema bundles also require component `EqCompare`. `queue_methods` alone needs only the source Ord dictionaries. |
| `PQueue`: `Semigroup`, `Monoid` | PriorityOperations: `semigroup_behavior` (`<>`), `monoid_append_behavior`, `monoid_empty_behavior`, `monoid_concat_model`, `monoid_concat_valid`, `union_associative`, `union_left_identity`, `union_right_identity`, `union_congruence` | Algebra over the full-entry `equivalent` relation; validity requires valid operands and priority laws. `mconcat` uses `Forall valid`. |
| `PQueue`: `Functor` | PriorityOperations: `fmap_raw`, `fmap_model`, `replace_model`, `fmap_valid`, `fmap_identity_model`, `fmap_composition_model`; PriorityModel: `summary_map_payload` | Recomputes caches through core `fmap'`, including the winning payload. `fmap_valid` needs priority laws but not an initially valid raw tree. Identity/composition are behavioral, not raw-shape equations. |
| `PQueue`: `Foldable` | PriorityOperations: the twelve equations below | Visits payloads in **extraction order**, not raw tree order. Validity and priority laws justify recursive observations. |

`PriorityOperations` retains optional reflection corollaries: `eq_equivalent`
and its Eq laws use exact Boolean/propositional equality on priorities and
payloads; `compare_equal_equivalent` and its order laws use
`PriorityOperations.ComparisonLaws`, which identifies comparison ties with
propositional equality. `compare_eq_boolean` combines those premises. They are
not needed for the generic Boolean laws, priority-summary correctness, or stable
extraction.
`PriorityModel.PriorityEqualityCoherence` is an optional stronger relationship
between the priority preorder and propositional equality, not an extraction
premise. `min_valid`/`max_valid` select an already valid operand; they need only
`deferredFix`, whereas the model-comparison proofs use guarded unfolding too.

## Generic application comparison laws

[ApplicationLaws.v](theories/ApplicationLaws.v) proves laws of the actual
translated dictionaries without assuming that Boolean equality or comparison
ties imply propositional equality. Its 37 exports extend the earlier
reflection-based coverage to general lawful equivalences. It reuses
`CoreInstances.ComparisonLaws` (reflexivity, opposite comparison, strict
transitivity, and invariance under ties) and `EqCompare` (Boolean equality
agrees with comparison ties).

| Interface | Typed theorem names in ApplicationLaws | Precise domain and premises |
| --- | --- | --- |
| Interval Eq | `interval_EqLaws` | `EqLaws K`; no Ord or endpoint-validity premise. |
| Node/Map Eq | `node_EqLaws`, `map_EqLaws` | `EqLaws K` and `EqLaws A`; all raw values. |
| Interval comparison/coherence | `interval_comparison`, `interval_eq_compare` | Respectively component `ComparisonLaws` and component `EqCompare` for endpoints. |
| Node/Map comparison/coherence | `node_comparison`, `map_comparison`, `node_eq_compare`, `map_eq_compare` | Respectively comparison laws and Eq/compare coherence for both endpoints and payloads; all raw values. |
| Interval/Node/Map methods | `interval_methods`, `node_methods`, `map_methods` | Six non-`compare` Ord fields. Interval needs endpoint comparison laws and endpoint `<`/compare coherence; Node needs endpoint/payload comparison laws and payload `<`/compare coherence; Map needs only the source Ord dictionaries. |
| Interval/Node/Map law bundles | `interval_behavior`, `interval_order`, `interval_minmax`; `node_behavior`, `node_order`, `node_minmax`; `map_behavior`, `map_order`, `map_minmax` | Combine the corresponding comparison, Eq/compare, and method premises. No `EndpointOrderLaws`, closedness, sortedness, or cache-validity requirement. |
| Queue Eq | `queue_eq_reflexive`, `queue_eq_symmetric`, `queue_eq_transitive` | `PriorityOrderLaws`, priority/payload `EqLaws`, and explicit validity of every queue operand; `neq_model` supplies the inherited negated-equality behavior. |
| Queue comparison | `queue_comparison`, `queue_compare_reflexive`, `queue_compare_opposite`, `queue_compare_transitive`, `queue_compare_ties` | `PriorityOrderLaws`, component comparison laws, and valid operands. `queue_comparison` packages the domain as `{q : PQueue K A \| valid q}`; it restricts only the comparator, not the raw datatype, dictionaries, or public signatures. |
| Queue Eq/compare bridge | `queue_eq_compare` | Valid operands, `PriorityOrderLaws`, and component `EqCompare`; concludes `(q == r) = isEQ (compare q r)`, not equality of models or raw trees. |
| Queue methods and bundles | `queue_methods`, `queue_order`, `queue_minmax` | Methods need only the source Ord dictionaries. Bundles additionally require `PriorityOrderLaws`, component comparison laws and `EqCompare`, and valid operands throughout. |

The pair/list bridges are `pair_compare_laws`, `list_compare_laws`,
`pair_eq_compare`, and `list_eq_compare`. Queue proofs apply them through
`PriorityOperations.eq_model` and `compare_model`, whose validity and
`PriorityOrderLaws` premises remain explicit. The queue order bundle includes
antisymmetry **up to Boolean equality**, strict-order coherence, and
greatest-lower/least-upper-bound laws. `queue_minmax` proves the eight Boolean
idempotence, commutativity, associativity, and absorption identities; intermediate
extrema remain valid because `min`/`max` select an operand.

These class laws do not weaken interval operation invariants or identify raw
shapes. The optional reflection bundles above remain available when callers
need propositional equality and can supply the stronger coherence premises.
ApplicationLaws adds no logical principle: 25 exports are closed,
`queue_methods` uses only `deferredFix`, and the other 11 queue-law exports use
both deferred axioms. See the [exact manifest](theories/assumptions.json).

## All inherited Foldable methods

The translated `Data.Foldable.Foldable__Dict` has twelve fields, named by adding
`__` to each method below. Coverage means behavioral equations for those fields,
not construction of the empty base-thy `FoldableLaws` class.

For the core, `xs` is `digitContents`, `nodeContents`, or `contents` as appropriate.
Each of `digit_foldable_behavior`, `node_foldable_behavior`, and
`tree_foldable_behavior` proves the numbered conjunct of
`CoreInstances.FoldableBehavior` shown below. For interval maps, `xs` is
`map snd (entries m)`; for queues it is `map snd (model q)`.

| Method (bundle conjunct) | Meaning of the actual field | IntervalOperations theorem | PriorityOperations theorem |
| --- | --- | --- | --- |
| `foldMap` (1) | Right fold of `mappend (f x)`, starting at `mempty` | `foldMap_payloads` | `foldMap_model` |
| `fold` (2) | Same ordered monoid fold, with identity mapping | `fold_payloads` | `fold_behavior` |
| `foldMap'` (3) | Left fold of `acc <> f x`, starting at `mempty` | `foldMap'_payloads` | `foldMap_strict_model` |
| `foldr` (4) | `List.fold_right f z xs` | `foldr_payloads` | `foldr_model` |
| `foldl` (5) | `List.fold_left f xs z` | `foldl_payloads` | `foldl_model` |
| `foldl'` (6) | Same left-associated value as `foldl` in the total model | `foldl'_payloads` | `foldl_strict_model` |
| `foldr'` (7) | Same right-associated value as `foldr` in the total model | `foldr'_payloads` | `foldr_strict_model` |
| `null` (8) | True exactly for `xs = []` | `null_payloads` | `foldable_null_model` |
| `length` (9) | `Z.of_nat (List.length xs)` | `length_payloads` | `length_model` |
| `product` (10) | Left fold of supplied numeric multiplication from `fromInteger 1` | `product_payloads` | `product_model` |
| `sum` (11) | Left fold of supplied numeric addition from `fromInteger 0` | `sum_payloads` | `sum_model` |
| `toList` (12) | Exactly `xs` | `toList_payloads` | `toList_model` |

Core and interval-map `foldMap`/`fold` list equations require explicit
propositional laws of the **result monoid**, because the generated fold groups
subtrees. Other field equations retain the actual association and need no
numeric or monoid laws beyond the required dictionaries. Queue `foldMap`/`fold`
already recurse in right-fold order, so their equations do not need result
monoid laws. Queue equations except `null` require valid input and priority
laws, with the declared deferred assumptions.
`CoreInstances.foldMap_strict_coherence` and
`PriorityOperations.foldMap_strict_agrees` equate strict and non-strict monoid
folds only under associativity, both identities, and `(<>) = mappend`.
`CoreInstances.foldable_null_length` proves the null/zero-length law for each
core bundle. No statement here claims Haskell strictness or `seq` equivalence.

The two application leaf containers have direct singleton behavior. No
endpoint/priority laws are needed for these equations; the listed source
Monoid/Num dictionaries suffice.

| Method | IntervalOperations theorem | PriorityModel theorem | Singleton behavior for payload `x` |
| --- | --- | --- | --- |
| `foldMap` | `node_foldMap` | `entry_foldMap_behavior` | `f x` |
| `fold` | `node_fold` | `entry_fold_behavior` | `x` |
| `foldMap'` | `node_foldMap'` | `entry_foldMap_strict_behavior` | `mempty <> f x`, not simplified without an identity law |
| `foldr` | `node_foldr` | `entry_foldr_behavior` | `f x z` |
| `foldl` | `node_foldl` | `entry_foldl_behavior` | `f z x` |
| `foldl'` | `node_foldl'` | `entry_foldl_strict_behavior` | `f z x` |
| `foldr'` | `node_foldr'` | `entry_foldr_strict_behavior` | `f x z` |
| `null` | `node_null` | `entry_null_behavior` | `false` |
| `length` | `node_length` | `entry_length_behavior` | `1` |
| `product` | `node_product` | `entry_product_behavior` | `fromInteger 1 * x` |
| `sum` | `node_sum` | `entry_sum_behavior` | `fromInteger 0 + x` |
| `toList` | `node_toList` | `entry_toList_behavior` | `[x]` |

## Scope and acceptance boundary

`Show`, `Read`, `Generic`, and `NFData` are excluded. The release has no standard
`Functor` or `Traversable` instance for the core tree, and no `Traversable`
instance for queues. The named core maps/traversals and the conditional view
functors are covered above. `deep`, `node2`, and `node3`, exposed by `TESTING`,
are additional audited helpers, not three extra required public operations.

The [README](README.md#build-and-check) gives build, exact-audit, and recursive
kernel-check commands. [ASSUMPTIONS.md](ASSUMPTIONS.md) separates theorem premises
from the permitted global assumptions. [VALIDATION.md](VALIDATION.md) records
completed local acceptance; [FINAL-REGRESSIONS.md](FINAL-REGRESSIONS.md) records
the qualified legacy results. Exact HLint 3.6.1 remains blocked despite the
supplemental 3.5 pass, and old Rocq checks used 9.0.1 rather than CI's 9.0.0.
Earlier checkpoint counts and the historical containers `validate` failure
retain their recorded scope.

The earlier formal code-review preparation was attempted with base and head both
`e4bc91ccc9f039deb352896dae75709c892cb03c` and rejected with
`error: empty or unsupported diff`. Proof review was blocked by the same empty
range. The user has now requested one local commit; after that commit,
a meaningful committed scope will be available for both reviews. Formal
code/proof review has not been completed, and there is no formal verdict or axis
finding count. Local acceptance is established by the recorded checks, not by
this table or by a review verdict.
