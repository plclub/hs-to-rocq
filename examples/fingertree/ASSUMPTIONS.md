# Assumptions and the approved translation exception

The functional proofs and valid-queue guarded-recursion obligations are complete.
Their global dependencies are limited to the explicitly permitted functional
extensionality and user-approved deferred interface below. The
[coverage inventory](COVERAGE.md) states the separate theorem premises.
The final clean Rocq 9.2 run compiled and recursively kernel-checked all fifteen
theories and matched all 1,048 exact assumption sets. The counts below describe
both the manifest and that observed audit. [VALIDATION.md](VALIDATION.md) records
the acceptance evidence; [FINAL-REGRESSIONS.md](FINAL-REGRESSIONS.md) records the
qualified old-target results. Formal pinned-range review has not been completed.

## Authorized scope

The supplied `notes/FingerTreeSpec.md` permits functional extensionality at
lines 283-284. On 2026-11-02 the user instructed **"Use deferredFix"**, then
**"Agreed. Let's try deferredFix"** for source `unfoldr`. Those decisions amend
the original restriction on recursion axioms for the queue and its dependency.
They authorize the existing `HsToRocq.DeferredFix.deferredFix` interface and
guarded `deferredFix_eq_on`, not an unrestricted recursive equation or additional
logical principles.

The separate one-function decision below amends the source-generation rule.
All other example algorithm and required-instance bodies remain generated from
unchanged source. Neither approval licenses new operation axioms, admissions,
source/license edits, or additional manually supplied algorithm bodies.

[source-policy.yaml](source-policy.yaml) records the sole approved redefinition
target with a link to the decision below, plus the separately approved pins for
current rewrite guidance. The [source-policy brief](SOURCE-POLICY.md) explains
the guard and source-only inventory checks. Those checks are separate from the
exact assumption audits below; they neither establish semantic equivalence nor
change the manifest or its functional-extensionality/deferred-recursion budget.

## Approved translation exception: minViewWithKey

On 2026-11-02 the user explicitly instructed:

> For this one function, let's use `redefine` to rewrite it to the expected one,
> but explicitly document this somewhere.

The scope is **`Data.PriorityQueue.FingerTree.minViewWithKey` only**. At source
pin `2f303a410c95802a2824b6dd54a0610fa5329858`,
[`Data/PriorityQueue/FingerTree.hs:238-246`](fingertree/Data/PriorityQueue/FingerTree.hs#L238-L246)
tests `FT.null q` before demanding the refutable lazy binding
`Prio k v = measure q`. The previous translation demanded that binding first;
a valid empty queue therefore reached opaque `GHC.Err.patternFailure`.

The [single `redefine`](module-edits/Data/PriorityQueue/FingerTree/edits#L19)
puts the empty guard outside the measure match. In the nonempty branch it keeps
the cached priority and payload, `split (below k)`, successful `viewl`, and
reappend. Both original partial branches remain: the failed `Prio` match and
the "can't happen" extraction error. The complete public signature is unchanged,
with no new `Default` premise or validity restriction. This manually supplied
body is the sole approved exception to source-generated example algorithms.
Haskell source and license remain unchanged, and the replacement adds no axiom.

The first polymorphic empty check failed against the old compiled library with
`Unable to unify "None" with "Err.patternFailure"`. After regeneration,
[PriorityRegression.v](theories/PriorityRegression.v) proved five closed public
equations: both empty views without a default-element premise, an empty payload
type, singleton extraction under `k <= k = true`, and a concrete four-entry
priority/tie/payload/reappend observation. The later general proofs in
[PriorityOperations.v](theories/PriorityOperations.v), especially
`minViewWithKey_nonempty`, `minViewWithKey_correct`, and `minView_correct`, now
establish validity preservation, error unreachability, and decrease under
`PriorityOrderLaws` and valid input. The regression equations alone did not
establish those contracts.

This record documents a repair to match nesting, not a formal compiler-fidelity
theorem or a general solution for translating lazy refutable bindings.

## Deferred recursion: proved guards, retained axioms

The queue Foldable method uses `termination ... deferred`, producing
`deferredFix2`. `assocs` remains the source call
`Data.OldList.unfoldr minViewWithKey`. The isolated Rocq 9.2 base restores
`unfoldr` from existing GHC source with two scoped edits: defer its local `go`
worker with `deferredFix1`, and specialize `GHC.Base.build` to `cons`/`nil`.
The existing list default supplies the result inhabitant; its checked type is:

```coq
forall (b a : Type), (b -> option (a * b)%type) -> b -> list a
```

There is no added seed/element Default premise, manual unfold algorithm, or fuel
replacement. This source-recursion statement does not include the separately
approved manual `minViewWithKey` body. Restoration is local to 9.2; see the
[foundation guide](../rocq9.2/README.md#source-unfoldr-restoration).

`deferredFix_eq_on` requires a well-founded relation `R`, a proof of
`recurses_on P R body`, and `P` for the current input. Those queue obligations
are now proved, not left as assumptions:

| Obligation | Proof in PriorityOperations |
| --- | --- |
| Nonempty valid extraction takes the successful measure/split/view/reappend branches | `minViewWithKey_nonempty`, `winner_at_cut` |
| Extraction preserves validity and strictly decreases `pqueue_size` | `minViewWithKey_some`, `minView_some` |
| Successful valid extraction is well founded | `extraction_well_founded` |
| `assocs` uses only smaller valid queues | `assocs_recurses_on`, with `P := valid` and `R := ltof _ pqueue_size` |
| Foldable recursion uses only smaller valid queues | `foldMap_recurses_on`, with `P input := valid (snd input)` and the same size rank on `snd input` |
| Actual source bodies unfold on the valid domain | `assocs_definition`, `assocs_unfold`, `foldMap_definition`, `foldMap_unfold` |
| Repeated extraction/folding agrees with the independent model | `assocs_model`, `unfoldr_valid_eq`, `unfoldr_valid_model`, `foldMap_model` |

The equations still depend on the two global deferred axioms. A proved guard
does not construct a general implementation of `deferredFix` or remove those
axioms. The separate classical `DeferredFixImpl.v` is built in the full base
but is **not wired into these definitions or proofs**. No `ClassicalChoice`,
`Eqdep`, or additional principle is permitted by the final theory manifest.

## Exact final-theory manifest

[theories/assumptions.json](theories/assumptions.json) pins fifteen modules and
**1,048 exported-constant audits**. These include definitions, helper lemmas,
records, and record fields, not just public-operation theorems. The final clean
audit matched every entry. Counting each export once, the required and observed
sets are:

| Theory | Exports | Closed | FE only | deferredFix only | deferredFix + eq_on |
| --- | ---: | ---: | ---: | ---: | ---: |
| CoreSize | 41 | 41 | 0 | 0 | 0 |
| CoreModel | 30 | 30 | 0 | 0 | 0 |
| CoreOperations | 82 | 82 | 0 | 0 | 0 |
| CoreSearch | 86 | 86 | 0 | 0 | 0 |
| CoreContext | 50 | 50 | 0 | 0 | 0 |
| CoreInstances | 102 | 102 | 0 | 0 | 0 |
| ApplicativeValidity | 29 | 29 | 0 | 0 | 0 |
| CoreTraversal | 58 | 40 | 18 | 0 | 0 |
| PriorityModel | 98 | 98 | 0 | 0 | 0 |
| PriorityOperations | 136 | 85 | 0 | 4 | 47 |
| PriorityRegression | 5 | 5 | 0 | 0 | 0 |
| IntervalModel | 54 | 54 | 0 | 0 | 0 |
| IntervalOperations | 158 | 145 | 13 | 0 | 0 |
| IntervalLaws | 82 | 75 | 7 | 0 | 0 |
| ApplicationLaws | 37 | 25 | 0 | 1 | 11 |
| **Total** | **1,048** | **947** | **38** | **5** | **58** |

Here FE means `FunctionalExtensionality.functional_extensionality_dep` as
printed by Rocq. The deferred names are printed as `DeferredFix.deferredFix`
and `DeferredFix.deferredFix_eq_on`, from `HsToRocq.DeferredFix`.

The manifest enumerates each exception by name and constructs its exact set,
not merely an allow-list of axioms:

* CoreTraversal's 18 FE entries cover list-effect reassociation, sequencing,
  contextual contents, the positional/contextual implementation bridge, and
  `traverseWithPos_validity_occurrences`. All other validity/cache results,
  including `traverseWithContext_validity_occurrences`, are closed.
* IntervalOperations' 13 FE entries are `inRange_spec`, `search_spec`,
  `intersections_spec`, `dominators_spec`, `union_spec`, `traverse_entries`,
  `sequenceA_entries`, `mapM_entries`, `sequence_entries`, `union_left_identity`,
  `union_right_identity`, `union_associative`, and `mconcat_spec`. The query/merge
  proofs use the proved well-founded unfolding interface; it contributes FE,
  not a new operation or recursion axiom.
* IntervalLaws' seven FE entries are `liftA2_associate`, `compose_functor_laws`,
  `compose_applicative_laws`, `map_traverse_reference`, `map_traversal_identity`,
  `map_traversal_naturality`, and `map_traversal_composition`.
* PriorityOperations has four `deferredFix`-only entries:
  `assocs_definition`, `foldMap_definition`, `min_valid`, and `max_valid`.
  Its 47 entries with both axioms are the guarded equations, model fold and
  comparison results, and their corollaries, enumerated in the manifest.
  Extraction, validity/decrease, and `recurses_on` proofs are closed.
* ApplicationLaws adds 25 closed generic interval/pair/list law exports.
  `queue_methods` depends only on `deferredFix`. Its 11 other queue exports
  depend on both deferred axioms: `queue_eq_reflexive`, `queue_eq_symmetric`,
  `queue_eq_transitive`, `queue_comparison`, `queue_eq_compare`,
  `queue_compare_reflexive`, `queue_compare_opposite`, `queue_compare_transitive`,
  `queue_compare_ties`, `queue_order`, and `queue_minmax`. This broadens the
  lawful-instance domain without adding a logical principle.

### What the checker enforces

[check-assumptions.py](theories/check-assumptions.py) checks that the module
inventory equals `theories/*.v`, that every named theorem/definition/record/
instance is in its explicit `Print Assumptions` inventory, and that the export
count equals the manifest. It compiles the theory, then creates a fresh audit
with an `AUDIT: name` marker, fully qualified `Check`, and `Print Assumptions`
for each constant. Each marker must have exactly one closed or axiom report.
All seven named assertion forms (`Theorem`, `Lemma`, `Remark`, `Fact`, `Corollary`,
`Proposition`, and `Example`) require inventory entries; an omitted assertion
fails before compilation, including when its proof ends in `Admitted`.
The checker rejects missing/duplicate reports and **any difference** from each
expected transitive assumption set, including a missing expected exception.
Record constructors/projections listed in the inventories are audited as well.

Normal `make` runs this checker; `kernel-check` separately checks all final
modules recursively, without `-admit` or `-norec`. Both passed in the
[final clean run](VALIDATION.md). A manifest is an assertion to be checked, not
itself evidence of a successful run on later changes.

## Separate generated-library and foundation audits

These inventories are distinct from the 1,048 theory exports. They remain useful
for detecting lost dictionaries/methods, but a closed operation report alone
does not prove its behavior or error unreachability.

The generated queue audit covers 74 declarations: **50 closed**, including all
nine public operations, and **24 with `deferredFix` only**:

| Declarations with deferredFix | Count |
| --- | ---: |
| `Foldable__PQueue` and its local `foldMap`, `fold`, `foldr`, `foldl'`, `foldMap'`, `foldl`, `foldr'`, `length`, `product`, `sum`, `toList` methods | 12 |
| `Eq___PQueue` and both local methods | 3 |
| `Ord__PQueue` and all seven local methods | 8 |
| Internal `assocs` | 1 |

`Foldable__PQueue_null` is closed. `Data.OldList.unfoldr` is one additional
`deferredFix`-only entry, giving 75 generated-library/foundation reports.
Declarations do not need `eq_on` merely to exist; their unfolding theorems do.
The earlier statement that no queue unfolding theorem had been proved is obsolete.

The separate [Unfoldr.v](../rocq9.2/checks/Unfoldr.v) audit has four entries:

| Entry | Exact assumptions |
| --- | --- |
| `Data.OldList.unfoldr` | `deferredFix` |
| `unfoldr_rank_eq` | `deferredFix`, `deferredFix_eq_on` |
| `countdown_decreases` | None |
| `unfoldr_countdown_three` | `deferredFix`, `deferredFix_eq_on` |

`unfoldr_rank_eq` uses `P := fun _ => True` and requires every successful
producer step to decrease a natural rank. The countdown example discharges
that premise. The queue instead uses the proved valid-domain predicates above;
it does not assume an all-raw-queues decrease theorem.

## Explicit premises are not global assumptions

"Closed under the global context" leaves quantified premises intact. Callers
must still supply the relevant monoid laws, priority/endpoint laws, cache and
application validity, monotonicity where required, lawful-applicative laws,
mapping-function conditions, and optional equality/comparison coherence.
[COVERAGE.md](COVERAGE.md) identifies them per operation and method.
`ApplicationLaws` proves generic Boolean Eq laws and comparator tie-equivalence
laws. Interval class laws require only their component Eq/comparison laws and
method coherence, not `EndpointOrderLaws` or data validity. Interval operations
still require their endpoint/validity premises. Queue class laws use
`PriorityOrderLaws` and valid operands to apply the existing Eq/compare model
theorems. Exact propositional-reflection bundles remain optional stronger
corollaries, not prerequisites for these generic laws.
Functional correctness is relative to these foundations and the approved
`minViewWithKey` body, not a formal source-fidelity theorem.

To reproduce the audits and recursive kernel checks, use the
[README commands](README.md#build-and-check). [VALIDATION.md](VALIDATION.md)
records final acceptance, including the corrected supplemental kernel command;
[FINAL-REGRESSIONS.md](FINAL-REGRESSIONS.md) retains the regression qualifications.
Earlier checkpoint records remain historical. The
[formal reviews](README.md#revision-and-review-status) have not been completed;
no verdict or axis finding count is claimed.
