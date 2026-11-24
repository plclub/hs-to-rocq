# Finger-tree source policy: review reference

The source-policy guard rejects specific guidance and declaration violations.
It does **not** prove source origin or semantic equivalence. Review still covers
guidance semantics, public contracts, and the approved dependency budget.

## Executable scope

From the repository root, with the Stack-built translator package and Python 3:

```bash
make -C examples/fingertree source-policy
```

This check needs neither Rocq nor generated foundations. The [Makefile](Makefile)
runs it before building this example's foundations or translating its modules.
It checks the example's `edits` and the three modules' `edits`, `preamble.v`, and
`midamble.v` inputs under `module-edits/`. Inherited `deps/base.edits`, foundation
sources, and proof theories are outside this guard's input scope.

* **Edits:** [SourcePolicy.hs](SourcePolicy.hs) uses the translator's parser and
  `buildEdits`, with aliases local to each file. It checks every built `in` and
  `except in` configuration, including shadowed configurations. It rejects
  unapproved redefinitions, all owned `axiomatize` directives, and assumption
  additions.
* **Handwritten declarations:** additions and raw support cannot supply protected
  generated names, including required dictionaries and methods. Value/module
  renames conservatively extend protection across files and scopes. Constructive
  Default instances, size measures, termination tactics, and proof helpers remain
  legitimate support; they must not replace protected declarations.
* **Generated inventories:** each forced `.v` translation checks required names
  before compilation, including direct Make targets and runs with stale outputs.
  Missing/duplicate required declarations fail; failed outputs and interfaces are
  removed. [check-source-inventory.py](check-source-inventory.py) reuses the
  131-entry [CoreAudit](module-edits/Data/FingerTree/CoreAudit.v) and 74-entry
  [PriorityAudit](module-edits/Data/PriorityQueue/FingerTree/PriorityAudit.v).
  [IntervalAudit](module-edits/Data/IntervalMap/FingerTree/IntervalAudit.v) makes
  the historical 31-name interval inventory durable. Queue declarations and audit
  entries must match in both directions, using the same helper as the queue
  assumption checker; core and interval checks require their listed names, not
  equality with every declaration. The guard protects **234 names**, excluding
  the handwritten queue helpers `DefaultPQueue` and `pqueue_size` from the
  combined inventories. Both helpers remain in the full queue inventory.

The shared generated-declaration scan masks nested Rocq comments and string
literals before matching emitted declaration headers. Declaration-like text in
documentation neither adds a duplicate nor supplies a missing generated name.
Unterminated comments or strings fail with the generated source path.

Source inventories check names, not proof assumptions. The
[full build and checks](README.md#build-and-check) still compile the theories,
enforce exact transitive assumption sets, and recursively kernel-check results.
Passing the translation milestone does not replace that work.

## Approved target versus pinned rewrites

[source-policy.yaml](source-policy.yaml) is the machine record. Its sole
`approved-redefinitions` entry permits an ordinary `Definition` for
`Data.PriorityQueue.FingerTree.minViewWithKey`, linked to the
[approval and intended behavior](ASSUMPTIONS.md#approved-translation-exception-minviewwithkey).
The guard checks the target and declaration form, not the replacement body.
That approval does not permit an `add` or handwritten-support replacement.
Renaming the approved target or its module is rejected.

The user separately approved pinning the **11 existing parsed rewrite rules**.
These pins preserve guidance; they do not authorize more manual algorithm bodies.
Comparison includes file boundaries, rule order, and complete `in`/`except in`
wrappers; rewrite-bearing inputs follow lexical policy-key order. Formatting,
comments, and aliases resolving to the same parsed rule do not change a pin.
New, changed, removed, moved, or reordered rules fail.

Changing the approved target set or rewrite pins requires an explicit user policy
decision and a corresponding record update, not automatic acceptance of new
output. Review any change to the approved body against its recorded scope even
when the guard passes.

## Lexical scanner limits

Raw support uses a lexical scanner, not a Rocq parser. It recognizes these named
declaration headers at command starts:

* `Definition`, `Let`, `Instance`, `Fixpoint`, `CoFixpoint`;
* `Theorem`, `Lemma`, `Remark`, `Fact`, `Corollary`, `Proposition`, `Example`;
* `Inductive`, `CoInductive`, `Variant`, `Record`, `Structure`, `Class`;
* `Axiom`, `Parameter`, `Conjecture`, `Variable`, `Hypothesis`, and their plurals.

It handles `Program`, locality/universe prefixes, attributes, ordinary mutual
heads, constructors, and record/class fields. Nested comments and strings
(including doubled quotes) are masked; quoted strings inside comments leave
`(*` and `*)` inert, as they do in Rocq. Multiline and same-line commands work.
Unqualified names conservatively match any protected local name. Raw axioms,
parameters, and conjectures are rejected; variables and hypotheses are checked
for protected-name collisions, not banned outright.

Notation, Ltac, plugins, `Include`, module aliases, anonymous dictionaries, and
arbitrary vernacular wrappers are not expanded or generally recognized. They
require review and, before relying on automatic detection, scanner/test coverage.
Declaration bodies are not checked for behavior or transitive assumptions.

## Reviewer responsibilities

* **Guidance semantics:** compare changed guidance and generated bodies with the
  successful source branches, including guard order, payloads, tie behavior, and
  recursive calls. Review effects of other guidance too, such as `skip` and
  `set type`; a stable name or closed assumption report does not settle behavior.
* **Least-powerful mechanism:** check whether native generation, a source-preserving
  edit, or a translator fix can solve the problem before accepting a replacement.
* **Typed public contracts:** use [COVERAGE.md](COVERAGE.md) and the
  [theory guide](theories/README.md), not declaration counts alone. Preserve
  required methods/defaults and the public types and premises; an added Default
  or validity premise can restrict a contract without adding an axiom.
* **Source and inputs:** preserve the source pin and license checked by
  `make -C examples/fingertree check-source`. Confirm that Make supplies any new
  owned guidance/support inputs to the guard.
* **Dependencies:** preserve [ASSUMPTIONS.md](ASSUMPTIONS.md) and the exact
  [theory manifest](theories/assumptions.json), including the scoped functional
  extensionality and deferred-recursion permissions. New operation axioms and
   admissions are not authorized. For an opaque dependency that blocks a proof,
   use the [contract-aware proof guide](../../doc/proof-guide.md).

## Local validation: 2026-11-02

The uncommitted guard changes over `fd1a0fac12bc8cd2486d4ce4f3aee92788fd145b`
passed these checks in the `fingertree` worktree:

* `stack test`: all three suites, including 237 edits assertions and 152 policy
  invocation cases.
* `python3 test/assumptions.py`: 38 compiler-independent controls.
* `opam exec --switch=cs2-rocq92 -- python3 test/assumptions.py --rocq rocq`:
  45 controls, including real direct/transitive assumption rejection.
* `bash test/harness.sh`: all 225 existing harness checks.
* `make -C examples/fingertree source-policy`: current owner inputs accepted.
* `opam exec --switch=cs2-rocq92 -- make -j2 -C examples/fingertree kernel-check core-check interval-check priority-check`:
  all three libraries regenerated and compiled; all fifteen theories matched
  1,048 exact assumption reports; the requested inventory and recursive kernel
  checks passed, including the new interval audit.
* `shasum -a 256 -c examples/fingertree/validation.sha256`: all 122 existing
  foundation, generated-source/interface, theory, and manifest files matched.

The run used Stack 3.11.1, GHC 9.10.3, Python 3.15.0, GNU Make 3.81, and Rocq 9.2
with OCaml 5.4.1. It reused the existing isolated 9.2 foundations; it was not a
clean foundation rebuild or a hosted CI run. The source pin/license check and
whitespace checks passed. HEAD and the index remained unchanged. The formal
review skill requires committed snapshots, so no formal review verdict covers
these uncommitted changes.

### Inventory-scan correction

The later pinned review of `61329fa674bc5bea3f9fa4c285fd5ff455244a26` reported
no Standards findings and one medium Spec finding: declaration-like text in
generated comments/strings could cause duplicate failures or falsely witness a
missing dictionary. The follow-up masks that text in the shared inventory scan.
Its first CLI regression failed before the fix; both original failure cases now
have the expected result, with additional CLI/Make/shared-queue controls.

Validation passed 45 compiler-independent controls and 52 with real Rocq, all
three Haskell suites, and all 225 existing harness checks. The full Rocq 9.2
`kernel-check core-check interval-check priority-check` run passed again, matching
all 1,048 theory assumption sets; all 122 validation-manifest files stayed
byte-identical. This was not a clean foundation rebuild or hosted CI run. The
correction was uncommitted at validation time; formal pinned-range re-review is
still pending.

### Spec-guard corrections: 2026-11-03

The review of `d0aa2436d727942996bdd32c994e22f811983afa` against
`origin/master` found two medium Spec issues in the guards. Quoted comment
delimiters could hide active declarations from the handwritten-support scanner,
and the theory inventory omitted ordinary assertion forms such as `Remark` and
`Example`. The current fixes retain the enclosing comment state when scanning
quoted text and include all seven named assertion keywords in the theory gate.
They do not change algorithm bodies, proof statements, rewrite pins, or the
assumption manifest.

Regressions failed before each fix and passed afterward: the edits suite passed
237 parser/API assertions and 184 source-policy cases, while the assumption
runner passed 48 compiler-independent cases and 57 with native Rocq 9.2. The
real-compiler controls confirm that omitted assertions are genuine exports before
requiring the production CLI to reject them. These focused checks do not claim a
new full proof rebuild, hosted CI pass, or review of the uncommitted fixes.
