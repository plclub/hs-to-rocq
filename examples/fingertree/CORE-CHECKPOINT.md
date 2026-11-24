# Core verification and historical translation checkpoint

## Completed proof interfaces: 2026-11-02

The core functional contracts are complete, including all required instance
methods and laws. The final clean Rocq 9.2 run compiled and recursively
kernel-checked the eight core/support theories as part of the full fifteen-theory
set, with every exact assumption audit matching. The
[coverage inventory](COVERAGE.md#core-operations-27) maps every required operation
and the 18 core instances to typed theorems and premises.
[VALIDATION.md](VALIDATION.md) records completed local acceptance;
[FINAL-REGRESSIONS.md](FINAL-REGRESSIONS.md) records the qualified old-target
results. The historical commands below retain their earlier scope. Formal
pinned-range review has not been completed; no verdict or axis finding count is
claimed.

| Theory | Completed interface |
| --- | --- |
| [CoreModel](theories/CoreModel.v) | Independent raw-constructor contents and external leaf/cache validity; source measurement and folds agree with the list model. |
| [CoreOperations](theories/CoreOperations.v) | Construction, concatenation, views, reversal, safe/unsafe maps, split reconstruction, and validity. |
| [CoreSearch](theories/CoreSearch.v) | Exact nonmonotonic endpoint classification and adjacent crossings; monotonic cut uniqueness; nonempty-prefix split reference; generated-call domain/parametricity proofs. |
| [CoreContext](theories/CoreContext.v) | Original prefix/suffix labels excluding the current leaf; positional/contextual maps and left/right folds. |
| [CoreInstances](theories/CoreInstances.v) | Full Measured, Eq/Ord, Semigroup/Monoid, conditional view-Functor, and twelve-field Foldable behavior/law interfaces, including `foldable_null_length`. |
| [ApplicativeValidity](theories/ApplicativeValidity.v) | Constructive `HoldsF` and lawful-applicative closure without erasing effects. |
| [CoreTraversal](theories/CoreTraversal.v) | All four named traversals: independent list sequencing, result/cache validity, and occurrencewise positional/contextual premises. |
| [CoreSize](theories/CoreSize.v) | Independent raw size and quantitative helper results used by the generated applications and their proofs. |

The final run matched all 478 [manifest](theories/assumptions.json) entries for
these eight modules: 460 closed and 18 with only functional extensionality, all in
CoreTraversal. CoreInstances has 102 closed exports; CoreSize retains its 41.
These counts include definitions and helpers, not only public theorems.

The shared [ApplicationLaws](theories/ApplicationLaws.v) module now applies
CoreInstances' general `ComparisonLaws`, `EqCompare`, `OrdMethods`, `OrderLaws`,
and `MinMaxLaws` interfaces to the applications. It adds Boolean Eq laws and
comparison tie-equivalence laws without propositional reflection. Its 37
exports are separate from the unchanged eight-module core count above; the
[complete manifest table](ASSUMPTIONS.md#exact-final-theory-manifest) now covers
15 theories and 1,048 exports.

The contracts quantify over arbitrary measurement monoids using explicit
propositional associativity and identities, without Eq/decidable equality or
commutativity. Unsafe transformations require same-monoid leaf-measure
preservation. Search needs no monotonicity for classification/reconstruction;
monotonicity gives uniqueness of a cut, not of raw tree shapes. Split scans
nonempty prefixes and cuts before the first triggering element, without a
general `p mempty = false` premise. See COVERAGE for exact premises and the
connection between domain certificates and the generated functions.

Core algorithms and dictionaries remain generated from the pinned source.
The example's sole approved manual algorithm body is the queue's
[`minViewWithKey`](ASSUMPTIONS.md#approved-translation-exception-minviewwithkey),
not a core replacement. No deferred-recursion axiom appears in the core theory
manifest. Functional extensionality was permitted by the original specification.

## Historical native-instance compilation checkpoint

The following record predates the complete functional theories. The expanded
generated `Data.FingerTree` core compiled with all 18 required dictionaries.
This superseded an earlier compilation milestone whose output
omitted the six source-derived ViewL/ViewR/SearchResult Eq/Ord dictionaries
because shared guidance skipped GHC.Classes. The integration fixed the guidance
input and added checked constructor-tag lowering in the translator. The
native-instance checkpoint retained minimal edits and ran the following command
from this worktree, exit zero:

```sh
opam exec --switch=cs2-rocq92 -- make -s -C examples/fingertree lib/Data/FingerTree.vo
```

That run also checked the expanded core with `rocq check -silent`, exit zero.
CoreAudit.v checked all 18 required dictionaries, their 83 local
methods, and all 30 exported operations including the three TESTING helpers:
131 closed assumption reports. Thus the milestone checked the required
inventory, not compilation alone.
The core algorithms and instance bodies were generated from unchanged
fingertree-0.1.6.3 at source pin
`2f303a410c95802a2824b6dd54a0610fa5329858`.

CoreSize.v recompiled unchanged against that expanded core and passed recursive
kernel checking. Its independent size function and accompanying lemmas provide
the raw-tree size facts needed
by the applications' termination arguments. The explicit assumption audit has
41 `Closed under the global context` reports: four definitions and 37 lemmas.

That run established core compilation and the size toolkit, not application
compilation or broad functional correctness. The later three-module compilation
and completed functional proofs are separate stages, described in the README
and the current interface table above.

## Least-power core guidance retained

The ordinary nonuniform generated datatype works: no index edit is needed.
There are no dependent-match rewrites, case eliminators, universe settings,
manual algorithms, or manual recursive knots.

The existing guidance consists of constructor renaming; necessary instance
ordering; the recursive `<|`/`|>` renames needed because their generated notation
comes after their bodies; `polyrec appendTree2` for the appendTree2/3/4 group;
mutual-helper inlining; and the minimal recursive Foldable call guidance now
supported by the generic emitter fix. `><` retains its original name.

For partial helpers, the source-generated `illegal_argument` body has an internal
result-default binder. The four digit error references receive an inhabitant
from the original digit input. Only internal searchTree/splitTree need a supplied
element default. Local tree/node/split defaults are constructive; public
search/split obtain evidence from their original input or an impossible Empty
branch. Public signatures gain neither a `Default a` premise nor a refinement
to valid trees; correctness theorems still state validity where needed.
The small Bool.Sumbool alias resolves the generated Program conditional path.

The earlier broad index-based experiments and diagnostic declaration-reordering
edits were removed. The retained guidance does not need the generic
synthesized-function-match rewrite hook, which the primary removed.

### Historical native Eq/Ord restoration

The Makefile derives `deps/base.edits` by omitting only
`skip module GHC.Classes` from the shared base edits. A direct diff confirmed
that this is its sole difference. Core module guidance is loaded first, followed
by the example/shared edits, so the primitive rules run before primitive-name
renaming. Shared guidance itself was not changed by this task.

Only these additions were needed in the core edits:

* `/=# x y` becomes an if on `Z.eqb x y` returning source `Int` zero or one.
* Only bool-ascribed `tagToEnum# (<# x y)` and `tagToEnum# (==# x y)` become
  `Z.ltb x y` and `Z.eqb x y`. No arbitrary tagToEnum# lowering is asserted.
* Scoped identity renames for GHC.Base.compare in Ord__ViewL_op_zl__ and
  Ord__ViewR_op_zl__ preserve field-dictionary dispatch. No redundant
  GHC.Classes overrides were added.
* Five additional ordering edges expose the implicit Foldable/Eq/Ord dictionary
  dependencies. The existing Foldable__Node ordering edge was preserved.

The generic translator supplies checked dataToTag# matches; no per-type tag
function, dictionary, method body, or algorithm was hand-written. The regenerated
core contains no remaining dataToTag#/tagToEnum# calls or targeted integer tag
primitives, and no axioms or admissions.

### Required instance inventory

CoreAudit.v resolves and audits every name below, not just an instance count:

| Family | Required dictionaries |
| --- | --- |
| Measured | Measured__Digit__5, Measured__Node__5, Measured__FingerTree__5 |
| Foldable | Foldable__Digit, Foldable__Node, Foldable__FingerTree |
| FingerTree | Eq___FingerTree, Ord__FingerTree, Semigroup__FingerTree, Monoid__FingerTree |
| ViewL | Eq___ViewL, Ord__ViewL, Functor__ViewL |
| ViewR | Eq___ViewR, Ord__ViewR, Functor__ViewR |
| SearchResult | Eq___SearchResult, Ord__SearchResult |

The generated module has exactly 18 Program Instance declarations. The audit
additionally checks all 83 local methods: 36 Foldable methods (all twelve methods
for each of Digit/Node/FingerTree), three Measured methods, thirteen FingerTree
Eq/Ord/Semigroup/Monoid methods, twenty-two ViewL/ViewR Eq/Ord/Functor methods,
and nine SearchResult Eq/Ord methods. This retains the generated defaults and
inherited Foldable methods. The audit also lists all thirty public operations
from the source export list, including TESTING's deep/node2/node3 exports.

## Independent termination interface

Import:

```coq
Require Import FingerTreeProofs.CoreSize.
```

The definitions do not use source folds, source measurements, or cached values:

```coq
digitSize : forall {a}, (a -> nat) -> Digit a -> nat
nodeSize  : forall {v a}, (a -> nat) -> Node v a -> nat
sizeWith  : forall {v a}, (a -> nat) -> FingerTree v a -> nat
size      : forall {v a}, FingerTree v a -> nat
```

`digitSize` and `nodeSize` sum the supplied weights of their leaves. `sizeWith`
recurses polymorphically into the middle tree with weight `nodeSize f`. `size`
assigns weight one to each raw element. Cached measurements have no effect.

### Laws not needed for views or append

For the following view/append lemmas, fix arbitrary types `v`, `a`, source
Semigroup/Monoid dictionaries for `v`, and `M : Measured v a`. No propositional
monoid laws, cache accuracy, validity, equality, element defaults, or predicate
properties are required.

```coq
size_zero_iff t : size t = 0 <-> t = Empty
null_size_zero t : null t = true <-> size t = 0

viewl_empty_iff M t : viewl t = EmptyL <-> size t = 0
viewl_size M t x r : viewl t = op_ZCzl__ x r -> size t = S (size r)
viewl_size_lt M t x r : viewl t = op_ZCzl__ x r -> size r < size t

append_size M l r : size (op_zgzl__ l r) = size l + size r
```

`size_zero_iff` and `null_size_zero` do not even require measurement or monoid
dictionaries. Weighted versions are `viewl_sizeWith`, `viewr_sizeWith`, and
`append_sizeWith`. The internal rotation, deepL/deepR, and append-helper size
lemmas support the proofs without replacing their source algorithms.

### Exactly one propositional identity premise for split

Define the explicit local premise (not a global axiom):

```coq
RID : forall x : v, GHC.Base.mappend x GHC.Base.mempty = x
```

Under the same dictionaries as above, the exported split interface is:

```coq
split_size RID M p t l r :
  split p t = (l, r) -> size t = size l + size r

split_size_bounds RID M p t l r :
  split p t = (l, r) -> size l <= size t /\ size r <= size t

takeUntil_size_le RID M p t : size (takeUntil p t) <= size t
dropUntil_size_le RID M p t : size (dropUntil p t) <= size t

split_viewl_append_size RID M p t l r x r' :
  split p t = (l, r) -> viewl r = op_ZCzl__ x r' ->
  size t = S (size (op_zgzl__ l r'))

split_viewl_append_lt RID M p t l r x r' :
  split p t = (l, r) -> viewl r = op_ZCzl__ x r' ->
  size (op_zgzl__ l r') < size t
```

The weighted reconstruction theorem is `split_sizeWith RID M f p t`.
`splitTree_sizeWith RID a t M D f p i` proves the corresponding pivot-inclusive
weighted equation for the internal helper, with its existing `D : Default a`
and the explicit condition `t <> Empty`. That nonempty condition is internal;
none of the public split/take/drop bounds has it or a Default premise.

Right identity is used only to prove that a selected middle recursion cannot
have an Empty middle tree: then the two relevant predicate arguments coincide,
contradicting the false/true guards. Thus the results apply to all raw trees and
arbitrary predicates, including nonmonotone predicates, without cache validity,
associativity, left identity, Eq/decEq on `v`, or order laws.

The interval merge uses `viewl_size` and `split_size_bounds`; the queue uses
`split_viewl_append_lt` for its successful extraction. CoreSize does not identify
an opaque `GHC.Err.error` result with Empty merely because a Default instance
exists. Instead, `PriorityOperations.minViewWithKey_nonempty` now proves that
valid calls take the successful branch and establishes strict decrease there.
`IntervalModel.intervalUnion_right_id` and `PriorityOperations.prio_right_id`
supply RID for the actual summary monoids. None of these application obligations
is left open.

## Historical commands and evidence

All commands ran from
`/Users/liyao/Workspace/hs-to-coq/.claude/worktrees/fingertree`.
Compiler: Rocq 9.2, OCaml 5.4.1, opam switch `cs2-rocq92`.

CoreSize recompilation and joint core/CoreSize kernel check (both exit zero, combined
120-second timeout):

```sh
opam exec --switch=cs2-rocq92 -- rocq c -Q examples/rocq9.2/base "" -Q examples/rocq9.2/base-thy Proofs -Q examples/fingertree/lib "" -Q examples/fingertree/theories FingerTreeProofs examples/fingertree/theories/CoreSize.v
opam exec --switch=cs2-rocq92 -- rocq check -silent -Q examples/rocq9.2/base "" -Q examples/rocq9.2/base-thy Proofs -Q examples/fingertree/lib "" -Q examples/fingertree/theories FingerTreeProofs Data.FingerTree FingerTreeProofs.CoreSize
```

CoreSize ends with explicit `Print Assumptions` commands for every definition
and lemma in the file. All 41 reports were closed. The
public lemma types were also checked in `rocq top` against the compiled module;
RID is an explicit theorem argument, not an assumption in the global context.

Required-inventory audit compilation and recursive kernel check (both exit zero,
combined 120-second timeout):

```sh
opam exec --switch=cs2-rocq92 -- rocq c -Q examples/rocq9.2/base "" -Q examples/fingertree/lib "" -Q examples/fingertree/module-edits/Data/FingerTree FingerTreeCoreChecks examples/fingertree/module-edits/Data/FingerTree/CoreAudit.v
opam exec --switch=cs2-rocq92 -- rocq check -silent -Q examples/rocq9.2/base "" -Q examples/fingertree/lib "" -Q examples/fingertree/module-edits/Data/FingerTree FingerTreeCoreChecks FingerTreeCoreChecks.CoreAudit
```

CoreAudit emitted 131 `Closed under the global context` reports, with no missing
references. Its command inventory contains exactly 131 Print Assumptions lines;
the regenerated core has exactly 18 Program Instance declarations. These counts
were checked with `rg -c`, in addition to auditing the individual required names.
Combined with CoreSize, this update has 172 closed assumption reports. Kernel
checks cover the expanded core and both audit/size modules; they do not claim
application compilation or new behavioral/algebraic correctness theorems.

### SHA-256 of the historical tested sources

Paths below are relative to `examples/fingertree`:

```text
3fd4707a84c705ecb60399f152daafe43f57fba678c4b2f98805397656d0ca6d  lib/Data/FingerTree.v
38ad7a5ffb8a45563a38bd8475676cd71bf7efaf3118bb86beace16e94558ee8  lib/Data/FingerTree.h2ci
c4d9999ffb5455a4e0b7a59ef66a58bce87cb83132b87576ac4ceaa28fe6cf9b  module-edits/Data/FingerTree/edits
5e2b3a25f7686aa8ed2c9f5ed489426c81656b02aaa3faa154b9995fc03dde19  module-edits/Data/FingerTree/midamble.v
098afbf07890a2a6e868128f1891cd0d51eb7a1e351e6f71a2423c7549241a2e  module-edits/Data/FingerTree/CoreAudit.v
71377bf798f0c86b557b68049cd1fe2ea78fc8da173e81dc5b5927bd760c93f1  theories/CoreSize.v
54731c4b16765da9c3424e820ed3ee42639c2d438a26bd14d077b6866b7398dc  deps/base.edits
```

That native-instance update changed only the core edits, added CoreAudit.v,
and updated this record. CoreSize.v and the core midamble were rechecked without
source changes. Generated output came from the existing Make target, not hand
edits. This task did not modify the translator, source algorithms/license,
foundations, Makefiles, or shared tests. No Git writes were performed. No
algorithms, axioms, admissions, skips, recursion assumptions, or public-domain
restrictions were introduced by that checkpoint. These hashes and commands
identify that earlier source state, not the final fifteen-theory acceptance.
