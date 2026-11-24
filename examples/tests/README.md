# Shared translator tests

This directory contains the compiler fixtures and shared
[test-rules.mk](test-rules.mk) for Coq 8.20 and Rocq 9.0. Tool-level Haskell
suites, CLI checks, and shell runners live in [`test/`](../../test/README.md).
Together, these tests exercise the public edits parser/builder, the real
translator CLI, and generated Gallina compiled with either target compiler.

## Run the tests

Run these commands from the repository root. Build the current translator first.
For compiler tests, use the matching Coq/Rocq environment with its Equations
plugin installed; the unit suites do not require the translated base library.

```bash
stack build
make -C examples/tests
make -C examples/rocq9.0/tests
```

Both normal Make entry points reach the shared `all` target, which includes
`edit-checks` as well as compiler tests. The `edit-checks` target runs
`stack --allow-different-user test hs-to-rocq:edits`, then `test/edits.sh` for
the selected target. The Coq wrapper compiles with `coqc`;
the Rocq wrapper uses `rocq c -w +deprecated-dirpath-Coq` to reject missed root
`Coq.*` rewrites. Existing CI jobs that invoke these Make targets therefore run
the edit checks without a workflow change.

To focus on one fixture or just the parser/API and CLI checks:

```bash
make -C examples/tests TypeEdits.pass
make -C examples/rocq9.0/tests TypeEdits.pass
make -C examples/tests edit-checks
make -C examples/rocq9.0/tests edit-checks
```

Replace `TypeEdits` with a name from `PASS` to run `NAME.pass`. A focused
`.pass` target does not also run `edit-checks`. The latter needs the built
translator, but no Coq/Rocq compiler. Each wrapper runs CLI checks for its own
target version, selected by `EDIT_CHECK_VERSION`.

The checks can also run independently:

```bash
stack test hs-to-rocq:edits
bash test/edits.sh
bash test/edits.sh --target-version 8.20
bash test/edits.sh --target-version 9.0
```

With no option, `edits.sh` checks both targets. It uses temporary directories
and removes them on exit. Other checks remain separate from `edit-checks`:

```bash
stack test hs-to-rocq:rocq-version
stack test hs-to-rocq:ci-catalog
bash test/harness.sh
bash test/concurrent.sh
```

`RocqVersion.hs` checks version parsing and namespace rewriting. `CiCatalog.hs`
checks the CI catalog and runs its complete self-tests by default. Run all three
Haskell suites with `stack test` or `cabal test all`; shell runners and compiler
fixtures remain separate. See the [tool test guide](../../test/README.md) for
dependencies and focused commands.

The fake-tool `harness.sh` checks Make recipes, failure propagation, regeneration,
helper dependencies, and cleanup, not edit semantics. Its 225 cases include eight that
restore missing manual `.h2ci` files when the corresponding `.v` files already
exist. They exercise both base generators, direct and `vfiles` targets, and
`-j1`/`-j2`, while preserving successfully generated sources. Four cases run the
real `test/identity-traversal.sh` with fake compilers and a Git stub that rejects
repository access. They cover both targets from the repository root, plus 8.20
from `examples/base-tests` and 9.0 from `examples/rocq9.0`. They verify compiler
arguments and the fixture source path and exercise the fourteen-report check.
`concurrent.sh` runs real translators with a shared Haskell dependency to check
concurrent translation and the explicit GHC code-generation override. These checks
do not replace compiler tests.

## What a passing check establishes

| Layer | Assertions |
| --- | --- |
| [Edits.hs](../../test/Edits.hs) | Currently 237 assertions through `parseEditList`, `parseTerm`, `buildEdits`, and related public APIs: exact ASTs, configuration fields, diagnostics, ordering, and precedence. |
| [edits.sh](../../test/edits.sh) | 32 real-CLI cases per target, 64 for both. Success requires nonempty `.v` and `.h2ci` output plus selected source assertions; rejection requires a nonzero exit and a diagnostic substring. This script does not compile output. |
| Shared compiler fixtures | Currently 70 `PASS` cases and 3 `TODO_PASS` cases per compiler. Generated proofs, type checks, and deliberate `Fail` commands distinguish selected edit effects from mere successful translation. |

The compiler counts include 12 edit fixtures, the reactivated `Records` and
`RecordConstruction`, `SoleCtorGuard`, `FunctionalDependencies`,
`RecursiveInstanceMethods`, and `ConstructorTags`, up from 52 `PASS` cases. The record
assertions check field update, named-field construction, and projection of the
constructed value. `SoleCtorGuard` combines `Single`, `Nested`, `Choice`, guarded
case arms, and empty-list guards with the `Box` and nested-pair cases. Computational
assertions cover each fixture case, including exhaustive guards and refutable
fallbacks. `SoleCtorGuard` counts as one `PASS` module. `FunctionalDependencies`,
`RecursiveInstanceMethods`, and `ConstructorTags` bring the previous inventory
of 67 to 70.
The lists in `test-rules.mk` determine which fixtures run; these counts describe
the inventory, not the outcome of a particular run.

| Category | Required translation result | Required compiler result |
| --- | --- | --- |
| `PASS` / `NAME.pass` | Exit zero and produce `.v` | Success |
| `TODO_PASS` / `NAME.fail` | Exit zero and produce `.v` | Failure |
| `TODO_TRANSLATE` / `NAME.fail_translate` | Failure or missing output | No output from a successful translation may pass this category |

`TODO_TRANSLATE` is currently empty. `TODO_PASS` contains `MutrecInst`, `TopBind`,
and `ExceptInDataDefinition`. Expected failures return success only when they
match their category; an unexpected result must keep Make's nonzero status.
Generation is forced on reruns, including helper dependencies, and a failed
translator's partial `.v` output is discarded rather than reused.

## Functional dependencies

The translator accepts functional dependencies when GHC-checked class information
is available. GHC performs inference, improvement, and instance consistency
checking. Translation retains all class parameters, checked method types,
superclass arguments, and ordinary dictionary passing in both class encodings.
The dependencies add no runtime dictionary fields, so translation erases them.
It generates no type-equality laws or axioms, and establishes no uniqueness
property for arbitrary Gallina dictionaries.

`FunctionalDependencies` exercises the public CLI and matching compiler without
the translated base library or local axioms/stubs. Its CPS `Measured` class uses
`a -> v`; its direct `Codec` class uses both `a -> v` and `v -> a`. Type checks
pin their parameter, superclass, method, and constructor types. Computational
proofs check inference from an element argument, superclass dispatch, inherited
defaults, explicit overrides, explicit dictionary arguments, and a parameterized
instance with a superclass constraint.

GHC resolves instances; translator lookup identifies the corresponding checked
declaration using every visible class argument in order, omitting invisible kind
arguments and retaining the existing representation-polymorphic head match.
Ambiguous matches fail translation. The fixture distinguishes instances sharing
their first or last argument, including parameterized list heads. A manual
mutation restoring first-match, any-argument lookup made both compilers reject
a method whose selected type expected `Element` but whose body matched
`OtherElement`; restoring all-argument lookup passed both focused compiler checks.

## Direct recursion in instance methods

Instance-method conversion applies the existing recursion machinery after
instantiating the method signature and supplying its quantified binders. Only a
local method's direct self-reference triggers this path. Ordinary structural
recursion emits a local `Definition` containing a typed `fix`; `polyrec` and
structural-argument edits have the same role as for ordinary bindings.
Well-founded orders use the existing Program Fixpoint emitter and obligation
tactic. Nonrecursive method emission keeps its existing representation.

`RecursiveInstanceMethods` uses an ordinary nonuniform `Nest tag a`, a Foldable-like
callback at the nested `Pair a` type, and a retained `Tag tag` instance premise.
Its scoped application rewrite identifies only the recursive Nest invocation;
component Pair calls retain dictionary dispatch. The list instance needs only
scoped method-name renames. All five methods remain present, including inherited
defaults. Compiler proofs check two nesting depths, component calls, defaults,
instance parameters, and the selected structural argument's reduction behavior.
No recursive algorithm, dictionary knot, axiom, or stub is supplied by edits.

The old emitter failed with a missing local recursive reference on both targets.
Removing `polyrec` rejects the changed element type; removing `{struct 2}` fails
the deliberate reduction guard. Fifteen existing class/instance fixtures also
compile on each target, with byte-identical generated Gallina. `MutrecInst`
retains its expected compiler failure; cross-method recursion is a separate case.

The earlier synthesized-function-match rewrite experiment was discarded after
the ordinary nonuniform datatype compiled. Its hook and fixture were removed;
this fixture replaced it at an inventory of 69. Earlier complete-catalog
records predate this method-emission change; the validation here is focused.

## Constructor tags in instance methods

The instance emitter lowers saturated `GHC.Magic.dataToTag#` and the older
`GHC.Prim.dataToTag#` spelling to constructor matches returning zero-based `Z`
ordinals. The receiver's own type comes from the instantiated method signature,
lambda argument alignment through `useTypeInBinders`, or an explicit ascription.
The pass removes shadowed bindings before descending and preserves primitive-free
bodies and binder syntax. Both ordinary and recursive method emission use it.

Support is limited to unique local, checked, native non-newtype ADTs with vanilla
constructors. GHC's `dataConTagZ` and `dataConSourceArity` supply the tags and field
counts. Renamed constructor lists and arities must agree with TypeInfo; target
list order alone is insufficient, especially for built-in Bool/Maybe layouts.
Skipped/redefined layouts, GADTs, imported/built-in operand types, unknown shadowed
operands, and unsupported binding contexts fail explicitly. No interface fields,
tag dictionaries, per-datatype tag functions, or new edit syntax are introduced.
Other primitive comparisons use existing, exact-shape expression rewrites.

`ConstructorTags` is a base-independent source-local primitive-method fixture.
Its two matrices cover 130 ordered pairs, source ordinal order, renamed
constructors, field arities, a phantom parameter, and actual min/max return values.
Separate proofs check a receiver different from the instance head, an explicit
receiver ascription, and a recursive method. The focused `.pass` target also runs seven public-CLI rejection cases for
layouts, pattern/let/lambda shadowing, built-ins, and GADTs. Full native derived
Eq/Ord integration belongs to the example's separate validation.

## Well-founded recursion after mutual inlining

`inline mutual` runs before the nonstructural-mutual-recursion check. If one
recursive member remains, its existing measure/well-founded guidance reaches
`wfFix`; the nonrecursive helper definition is retained. Multiple remaining
recursive members still produce the existing unsupported-recursion diagnostic.
For a single well-founded member, the selected helpers' converted bodies are
expanded at saturated call sites before `wfFix` creates decreasing arguments.
This puts the recursive call beneath the caller's case/split facts instead of
asking for decrease for arbitrary helper parameters. Structural groups and
groups without selected helpers bypass application expansion.

`InlineMutualEdits.localSplit` exercises the local form:

```text
in InlineMutualEdits.localSplit inline mutual merge2
in InlineMutualEdits.localSplit termination merge1 {measure (Nat.add (length as_) (length bs))}
obligations InlineMutualEdits.localSplit solve_local_split @peelOne_length
```

The stronger `localSplit` regression mirrors alternating merge helpers: the
caller extracts a tail and splits its other list; the helper cases on its own
arguments and splits again before recurring. Its typed two-argument helper needs
both the call-site bounds and its inner split facts. The old let-bound lowering
failed its decreasing obligation on both targets. `localShadow` also checks free
closure variables, parameter/match/let shadowing, an unrelated same-name local
function, and a source name colliding with the fresh-name prefix.

The application pass uses fresh lexical identities and freshens every copied
helper body before substituting actual arguments. It preserves argument/result
annotations and does not reduce unselected function applications. Root measure
parameters retain their names; local binders use fresh `inlined_N__` names, so
obligation tactics should match equations and types rather than local spellings.
Initial support requires exactly saturated positional calls to explicit helper
parameters. Partial/escaping or overapplied helpers, implicit/generalized helper
parameters, dependent binding forms, and helper-closure/root-parameter name
collisions are rejected explicitly rather than guessed.

The source helpers remain ordinary Haskell. Compiler checks cover the retained
helper's outer call and finite computations after all Program obligations are
discharged. The fixture compiles the existing production
`base/HsToRocq/Wf.v` utility in isolation through the CLI preamble path, so both
targets get normal namespace rewriting without building the translated base.
The finite proof unfolds the recursion combinator and destructs accessibility
evidence; it does not need the extensional unfolding lemma. Four CLI rejection
cases cover multiple retained members, an escaping helper, and an ambiguous root
closure. Thirteen assumption reports for the tag instances/proofs and measured functions/proofs
were closed on each compiler. These are focused checks, not a complete catalog run.

## Deriving and base integration

Issue 228 adds base-dependent checks without adding a base dependency to either
shared unit suite. After building the translator, use the matching compiler
environment and compiled base library:

```bash
# Coq 8.20: existing base tests plus deriving and traversal checks
make -C examples/base-tests

# Rocq 9.0: compile base, then run its base-checks target
make -C examples/rocq9.0 base

# Run either check independently; use --target-version 9.0 for Rocq
bash test/deriving.sh --target-version 8.20
bash test/identity-traversal.sh --target-version 8.20

# Focus on the two retained-instance/kind regressions
bash test/deriving.sh --target-version 8.20 --retained-only
```

[`deriving.sh`](../../test/deriving.sh) contains 36 cases per target and defaults to
8.20. Its successful translation cases compile generated modules and consumers
that infer dictionaries and check their computations. Rejection cases require
a nonzero exit, a relevant diagnostic, and no generated module. Coverage includes:

- Inline and standalone recovery; renamed module, class, and instance skips,
  including dependencies that occur only in a standalone instance context;
  method skips; and auxiliary bindings needed by retained instances.
- Multi-module translation of explicit instances, even with no deriving clauses.
  The runner prepares the class interface, checks the client alone, then translates
  both modules together with the client ordered before the class module. It compiles
  both outputs and a consumer that infers the dictionary and checks its computation.
- Whole-instance `redefine` excludes helpers used only by the discarded
  implementation. `whole-instance-redefine-unused-helpers` translates
  `DerivingRedefinedAux` through the real CLI, then compiles the output and
  `RedefinedAuxConsumer.v`. The consumer infers the replacement `Enum` dictionary
  and proves `inferredFromEnum B = 7` by reflexivity; stock deriving would return `1`.
- Individual method replacements and renamed `skip method` edits also exclude
  unused stock Enum helpers. These checks bootstrap class metadata from a source
  fixture rather than using the production edits that skip Enum entirely. The
  replacement case compiles against the real base Enum class and checks exactly
  one renamed `Enum__E` instance with no unused helpers. A source-generated
  primitive model also checks replacement of a renamed method and a
  surviving original method: its consumer computes `A, B` using both retained
  stock helpers. No helper bodies or instance dictionaries are replaced in that
  retention check.
- A provider-only method skip is respected through the imported class interface:
  the consumer does not repeat the skip, still infers its dictionary and computes,
  and emits neither unused Enum helper. This also holds when an empty import puts
  the unselected provider in GHC's source graph under `-N`. Two selected-provider
  checks translate the provider before the consumer, replacing stale interfaces
  that omit or retain the method; helpers follow the newly converted inventory.
- Nonzero failures in default/strict mode and warnings with partial success in
  permissive mode, including removal of a synthesized instance that fails the
  final GHC typecheck.
- The checked stock-generator bridge for the exact source modules
  `GHC.Internal.Data.Foldable` and `GHC.Internal.Data.Traversable`, including
  explicit `stock`, incompatible class APIs, invalid fields, hidden
  constructors, and missing superclasses.
- Retention of `Functor__Kleisli` and inline kind-polymorphic instances when
  compiler-added kind names from `GHC.Types` must not trigger a module skip.
  `--retained-only` selects these two cases.

[`identity-traversal.sh`](../../test/identity-traversal.sh) compiles the same
[`IdentityTraversal.v`](../base-tests/IdentityTraversal.v) on both targets in a
fresh temporary directory. The fixture uses public operations with inferred
dictionaries for `Identity`, `Solo`, and `Down`; it supplies no local replacement
instances. It checks `fmap`, `foldr`, `traverse`, and `mapAccumL`, including
effects and state/value order. The runner requires 14 closed `Print Assumptions`
reports and rejects any `Axioms:` report: six generated instances and eight
proofs/examples. These checks do not establish axiom-freedom for unrelated base
definitions or GHC proofs.

The Make entry points enable both scripts through `BASE_CHECKS`. The fake-tool
harness sets `BASE_CHECKS=` for Make recipe tests, but directly exercises the real
`identity-traversal.sh` runner with fake compilers. Keep the default checks enabled
for normal builds. Both base generators prepare manual `.h2ci` prerequisites even
for direct file targets.
In particular, `GHC/Tuple.h2ci` supplies metadata for the existing `Solo` datatype.

### Issue 228 validation

The issue 228 branch at `e41f3c37` recorded the following results before rebasing
onto PR 229 (`a038d05a`). Both production base trees were regenerated after the
retained-kind fix and compiled with Coq 8.20 and Rocq 9.0 respectively:

- Coq base-tests: 18 `PASS` fixtures, 3 expected compiler failures, 26 deriving
  cases, and 14 closed assumption reports.
- Rocq parent `base`: 26 deriving cases and 14 closed assumption reports after
  base compilation.
- Both base-independent unit suites: 67 `PASS` fixtures and 3 expected compiler
  failures, plus 237 edits assertions and 32 real-CLI cases per target.
- All 805 version/rewrite assertions, the concurrent real-translator check,
  and HLint.
- All 221 harness cases on both Bash 3.2 and Bash 5.3.20.

### Post-rebase validation

At `1ca9107f`, `stack build` and forced full base generation and compilation passed
for both Coq 8.20 and Rocq 9.0. Tracked generated outputs remained byte-identical
(`git diff --exit-code` returned zero). The following checks also passed:

- Per target: 67 `PASS` fixtures and 3 expected compiler failures, including the
  combined `SoleCtorGuard` cases and their computational proofs; 26 deriving CLI
  cases; and 14 closed production-instance/proof reports.
- Per target: 237 edits API assertions and 32 edits CLI cases.
- All 221 harness cases and 805 version/rewrite assertions, the `CiCatalog` guard,
  real-translator concurrency check, and HLint.

The [GHC validation record](../ghc/README.md#post-rebase-validation) covers the
dependency builds, kernel checks, and separate scratch Identity comparison.

## Edit coverage matrix

Each row corresponds to one of the 42 `Edit` constructors. `grammarCases` in
`test/Edits.hs` checks an exact parsed AST for every constructor; `grammarBranchCases`
checks additional syntax forms. The parser/API column describes those checks
and the additional builder assertions. Compiler names refer to active shared
fixtures and their `edits`, `preamble.v`, or `midamble.v` assertions; CLI names
refer to cases in `edits.sh`. Every family except explicit `class kinds` has a
live compiler witness. This is a coverage inventory, not a claim that every
combination of edits has been tested.

| Constructor / directive family | Parser/API assertion | Compiler or CLI witness |
| --- | --- | --- |
| `TypeSynonymTypeEdit` / `type synonym` | Preserve the result identifier and unqualified synonym key. | `TypeEdits`: `Small` retains the requested `typeEditsSort` annotation, rather than an inferred sort. |
| `DataTypeArgumentsEdit` / `data type arguments` | Preserve parameter/index lists, including omitted and empty clauses. | `TypeEdits`: `Product_rect` has a motive varying over index `b`, with `a` fixed as a parameter. |
| `TerminationEdit` / `termination` | Distinguish named/positional structure, measures with optional relation, `wf`, deferred, and corecursive requests; check `useProgram`. | `StructuralEdits` pins the decreasing argument; `RecursionEdits` computes with `wf` and a custom measure relation; `NonStructuralRec` uses a default measure; `Bits` identifies `deferredFix2`. |
| `ObligationsEdit` / `obligations` | Preserve tactic text and select Program even without a termination edit. | `RecursionEdits`: tactics discharge decreasing-call and well-foundedness goals; `InvariantEdits`: the constructed sigma value carries evidence. |
| `RedefinitionEdit` / `redefine` | Parse definition forms and key replacements by the declared name, including the first mutual body. | `AddAndReplace`: `foo false = true` requires the replacement; `ClassEditRedefine` distinguishes default, explicit, and replaced instance bodies. |
| `AddEdit` / `add`, `add type` | Separate phases and modules; retain additions in reverse source order within a phase. | `PhaseEdits` checks visibility on each side of the midamble; `RedefineAddAxiom` instantiates the added axiom. |
| `SkipEdit` / `skip` | Record the skipped name; `definitionTask` chooses skip before replacement or axiomatization. | `ClassEdits` skips a default body but retains its method field and explicit instance; CLI precedence cases reject emitted definitions/axioms for skipped names. |
| `SkipConstructorEdit` / `skip constructor` | Preserve the constructor key and reject duplicates. | `SkipConstructor`: non-positive and record constructors are removed, affected branches compile, and `Fail Check field` rejects a leftover selector. |
| `SkipClassEdit` / `skip class` | Preserve the class key and reject duplicates. | `ClassEdits`: class, dictionary, selectors, and both instances are absent; CLI rejects applying this edit to a datatype. |
| `SkipMethodEdit` / `skip method` | Keep the class and method as a pair, not a value-skip key. | `ClassEdits`: the removed method and its instance bodies disappear while retained methods compute; CLI rejects plain `skip` on an instance method. |
| `SkipEquationEdit` / `skip equation` | Preserve argument patterns, normalize nullary constructors, and detect normalized duplicates. | `SkipMatches`: redundant single/multiple-argument equations disappear and all Boolean inputs still compute to negation. |
| `SkipCasePatternEdit` / `skip case pattern` | Normalize nested/as-patterns and detect duplicate patterns. | `SkipMatches`: local wildcard removal and global variable-pattern removal preserve an unscoped, nonredundant wildcard. |
| `SkipModuleEdit` / `skip module` | Record the module name and reject duplicates. | `SkipConstructor`: generated code uses the preamble's `GHC.Skip` helper without requiring an external `GHC.Skip` library. |
| `ImportModuleEdit` / `import module` | Record the requested module. | `ModuleEdits`: `supportMarker` is unavailable in the preamble but available unqualified in the midamble after generated imports. |
| `AxiomatizeModuleEdit` / `axiomatize module` | Select general axiomatization and respect definition exceptions. | `AxiomatizeModule` accepts otherwise nonterminating values; CLI checks ordinary values become axioms and exceptions remain definitions. |
| `AxiomatizeOriginalModuleNameEdit` / `axiomatize original module name` | Preserve the original module key independently of renaming. | `ModuleEdits`: after merging `Abstract`, `opaqueOriginal` cannot unfold, `Pack` remains concrete, and the destination's identity still computes. |
| `AxiomatizeDefinitionEdit` / `axiomatize definition` | Select specific axiomatization and test its precedence. | `PhaseEdits`: `Fail unfold opaqueIdentity` contrasts with a computing transparent identity; CLI checks the emitted axiom. |
| `UnaxiomatizeDefinitionEdit` / `unaxiomatize definition` | Distinguish a module exception from a standalone specific axiom request. | `AxiomatizeModule`: `kind` and `saccharine` compute by reflexivity; CLI checks opt-out behavior with and without module axiomatization. |
| `HasManualNotationEdit` / `manual notation` | Record the module's notation request. | `ModuleEdits`: importing only `Support.Notations` exposes the manually supplied flag, which computes to `false`. |
| `AdditionalScopeEdit` / `add scope` | Keep value and constructor scope keys separate. | `TypeEdits`: the scoped value is `true` rather than `false`; scoped and unscoped constructors take `bool` and `unit`, respectively. |
| `OrderEdit` / `order` | Add adjacent prerequisite edges, union repeated edges, and leave one-name orders empty. | `RecursionEdits` and `PhaseEdits`: proof/tactic-only references require explicit order; an order edge cannot move a term addition before the midamble. |
| `RenameEdit` / `rename value`, `rename type` | Separate namespaces and preserve rewrite-pattern spelling. | `ScopedMethods` checks source/target spellings after module renaming; `TypeEdits` uses scoped type renaming; CLI rejects cycles within/across files. |
| `ClassKindEdit` / `class kinds` | Check the exact kind-list AST only. | Parser-only: explicit class kinds have no translation consumer. `ClassKinds.hs` tests inferred kinds, not this directive. |
| `DataKindEdit` / `data kinds` | Preserve the ordered kind terms and reject duplicate specifications. | `GADT` compiles indexed constructors; `PolyKind` compiles `T F G` with the specified higher-kinded arguments. |
| `PolyKindEdit` / `polykinds` | Preserve the ordered kind-variable names. | `PolyKind`: the explicit kind parameter allows a value of `T F G` and the class instances for `T` to typecheck. |
| `DeleteUnusedTypeVariablesEdit` / `delete unused type variables` | Record the selected declaration and reject duplicates. | `TypeEdits`: `MkTrimmed` loses its unused quantified variable, while `keepBoth` retains both used type binders. |
| `RewriteEdit` / `rewrite` | Check quantified substitution, flattened applications, arity, retained duplicates, and single-pass rule order. | `BitsRewrite`: `foo = bar` holds by reflexivity after rewriting, without class laws; CLI chains distinguish stopping at `sourceB` from reaching `sourceC`. |
| `CoinductiveEdit` / `coinductive` | Record the type and reject duplicates. | `RecursionEdits` observes a generated productive stream; `UniversePolymorphic` compiles a productive `CoFixpoint` over the edited type. |
| `RenameModuleEdit` / `rename module` | Preserve source-to-target module mapping. | `ScopedMethods` compiles under the renamed module with scoped overrides; `ModuleEdits` merges an original module while preserving its data declaration. |
| `AliasModuleEdit` / `alias module` | Expand following exact module aliases, allow rebinding, reset between files, and leave no builder effect. | `ModuleEdits` checks renamed values and additions using the real module name; CLI contrasts same-file expansion with file-local isolation. |
| `SimpleClassEdit` / `simple class` | Record the class and reject duplicates. | `ClassEditSimple`: check the direct `Build_Direct` signature, absence of dictionary wrappers, and default-method dispatch. |
| `InlineMutualEdit` / `inline mutual` | Record each selected function and reject duplicates. | `InlineMutualEdits`: transitively inline `forward`/`relay`; local inlining reduces a measured mutual group to one recursive function, with discharged obligations and a retained helper. |
| `SetTypeEdit` / `set type`, `no type` | Distinguish an explicit type, a cleared annotation, and no edit. | `TypeEdits` checks exact annotated/inferred types; `InlineMutualEdits` accepts `post` on Boolean lists and rejects natural-number lists. |
| `CollapseLetEdit` / `collapse let` | Record the function and reject duplicates. | `StructuralEdits`: a local recursive helper and calls to the outer function collapse into a computing list copy. |
| `InEdit` / `in` | Accumulate independent/nested scopes, preserve global fields, and reject duplicates within one scope. | `ScopedMethods` changes only one instance method; sibling methods and another instance retain their behavior. |
| `ExceptInEdit` / `except in` | Install edits globally, record exclusions, and subtract only the six supported fields. | `ExceptIn` compiles excluded functions against the restored original type; `InvariantEdits` gives selected public functions sigma types while the validator uses the raw type. |
| `PromoteEdit` / `promote` | Record promotions and diagnose duplicates. | `PhaseEdits`: the promoted leaf and its dependency are visible before the midamble; ordinary values remain unavailable there. CLI also rejects duplicates. |
| `PolyrecEdit` / `polyrec` | Record global/scoped requests and diagnose duplicates. | `StructuralEdits`: local `go` recurses at a changed element type and computes the expected result. CLI also rejects duplicates. |
| `UniversePolymorphicEdit` / `universe polymorphic` | Distinguish default monomorphic and requested polymorphic status. | `UniversePolymorphic`: explicit universe instances work for edited, redefined, coinductive, and mutual types; an unedited control rejects them. |
| `UniverseCumulativeEdit` / `universe cumulative` | Parse combined syntax and make cumulative status subsume polymorphic status. | `UniversePolymorphic`: constrained universe upcasts succeed for cumulative types and fail for a polymorphic-only list. |
| `EquationsEdit` / `equations` | Record the request and reject duplicates. | `Equations` consumes generated equation lemmas for patterns, local helpers, recursion, and measured recursion; CLI rejects conflicting edits and incompatible termination modes. |
| `InvariantEdit` / `add invariant` | Check all fields, raw-name renamings, selected exclusions, and generated predicate/sigma/notation additions for monomorphic and parameterized ASTs. | `InvariantEdits`: the raw representation admits `false`, an invalid sigma construction fails, a public value exposes validity evidence, and `keep` preserves its payload. |

## Interaction guards

These checks target interactions that a one-directive smoke test would miss.

| Interaction | Guard and observation |
| --- | --- |
| Skip/redefine/axiomatize precedence | `taskChecks` and CLI precedence cases require skip before redefine before axiomatization. A module opt-out overrides a simultaneous specific axiom; outside module axiomatization it does not cancel that axiom. |
| Per-file validation and merge | `duplicateCases`, `mergeChecks`, and CLI file-order cases distinguish duplicate errors within a file from first-file precedence across files. Sets union; a colliding map key selects the whole left entry, including additions, order sets, and scoped configurations. A malformed later file still fails. |
| Rename scopes and aliases | `scopeChecks` and `aliasChecks` test nesting/isolation; `ScopedMethods` checks both original and renamed module spellings against automatic sibling-method renaming. `ModuleEdits` checks aliases through imports, additions, and original-name axiomatization. |
| Rewrite order and renamed names | `rewriteChecks` and four CLI layouts require reverse source order within a file, then file order across files, with no fixed-point iteration. Rewrites must match the already-renamed spelling; their own patterns are not renamed. |
| Class edits and default dispatch | `ClassEdits` checks removed classes/methods and a body-only skip; `ClassEditSimple` checks direct encoding; `ClassEditRedefine` distinguishes inherited defaults, explicit methods, and one replaced instance method. |
| Redefined newtype and coerce | `NewtypeEdits` changes constructor/accessor metadata, rejects the old selector, and checks both Boolean results of the derived method after wrapping/unwrapping. |
| Termination, obligations, and ordering | `programChecks`, `StructuralEdits`, and `RecursionEdits` cover structural positions, local polyrec, custom relations, and tactic-only dependencies. CLI rejects well-founded edits on nonrecursive functions or cleared signatures and Equations with deferred/corecursive termination. |
| Mutual inlining with other edits | `InlineMutualEdits` combines transitive inlining with a scoped rewrite, notation scope, specialized helper type, and local measure/obligation edits. Finite results and rejection of multiple retained nonstructural members are checked. |
| Invariant, exclusions, and promotion | `invariantChecks` checks generated edits; `InvariantEdits` combines raw-name renaming, sigma exceptions, validator promotion, and a constructor obligation. The invalid-value control rejects `eq_refl` as evidence for a false payload. |
| Additions, promotion, and phases | `additionChecks` and `PhaseEdits` distinguish type-phase additions and promoted dependencies from ordinary terms. Midamble `Check`/`Fail Check` assertions enforce the boundary even with a cross-phase order request. |
| Universe edits with other type edits | `UniversePolymorphic` combines cumulative/polymorphic requests with redefinition, coinduction, and a mutual block; positive upcasts and negative controls distinguish their effects. |

Duplicate `promote`/`polyrec` diagnostics and rejection of incompatible
Equations termination on recursive definitions are regression tests for fixed
bugs, not remaining gaps. The CLI checks both recursive and nonrecursive cases.

## Limits and maintenance

- Explicit `class kinds` remains parser-only because no translator consumes it.
  The tests deliberately do not invent semantics for it.
- Constructor coverage does not guarantee all higher-order interactions or
  exhaustive runtime behavior. Some fixtures use axioms or local stubs; compiler
  success establishes the stated checks, not general semantic preservation.
- The invariant compiler fixture is monomorphic with one constructor. The API
  checks also inspect parameterized expansion, but do not compile that case.
- The newtype/coerce fixture is concrete and single-field. It does not cover
  coercions through lists, callbacks, or higher-kinded wrappers.
- `ExceptIn` subtraction supports only termination, skipped case patterns,
  renamings, rewrites, polyrec, and Equations requests. Excluding a data
  declaration's own name remains a known failure (`ExceptInDataDefinition`).
- `TODO_PASS` checks compiler failure, not its diagnostic. An unrelated compiler
  error can satisfy that category; use the real CLI checks when a diagnostic is
  part of the contract.
- Support directories `Expr`, `NestedRec`, `EqList`, `OpTyCon`, and
  `PartialRecordSel` remain inactive. Their presence is not test coverage.

For a new fixture, add `NAME.hs` and any `NAME/edits`, `NAME/preamble.v`, or
`NAME/midamble.v`, then register it in the shared category list. Add an assertion
that observes the intended effect, not just code that happens to compile.
For a new directive, extend `test/Edits.hs` and this matrix: its exhaustive `editKind`
match is compiled with `-Wall -Werror` so a new constructor needs an inventory
entry.

Use a manual red check when strengthening a witness: temporarily disable the
relevant edit or alter its effect and require the intended assertion to fail;
restore the edit and check both compiler targets. Check that the failure is for
the intended reason, not a missing prerequisite. These commands are not an
automated mutation harness; record any manual mutation checks separately.
