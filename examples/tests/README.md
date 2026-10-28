# Shared translator tests

These tests exercise hs-to-rocq through three interfaces: the public edits
parser/builder, the real translator CLI, and generated Gallina compiled with
Coq 8.20 or Rocq 9.0. Both compiler suites use the fixtures in this directory
and [test-rules.mk](test-rules.mk).

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
`edit-checks` as well as compiler tests. The Coq wrapper compiles with `coqc`;
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
stack exec -- runghc -package=hs-to-rocq examples/tests/checks/Edits.hs
bash examples/tests/checks/edits.sh
bash examples/tests/checks/edits.sh --target-version 8.20
bash examples/tests/checks/edits.sh --target-version 9.0
```

With no option, `edits.sh` checks both targets. It uses temporary directories
and removes them on exit. Other checks remain separate from `edit-checks`:

```bash
stack exec -- runghc -package=hs-to-rocq examples/tests/checks/RocqVersion.hs
bash examples/tests/checks/harness.sh
bash examples/tests/checks/concurrent.sh
```

`RocqVersion.hs` checks version parsing and namespace rewriting. The fake-tool
`harness.sh` checks Make recipes, failure propagation, regeneration, helper
dependencies, and cleanup, not edit semantics. `concurrent.sh` runs real
translators with a shared Haskell dependency to check concurrent translation
and the explicit GHC code-generation override. These checks do not replace
compiler tests.

## What a passing check establishes

| Layer | Assertions |
| --- | --- |
| [Edits.hs](checks/Edits.hs) | Currently 237 assertions through `parseEditList`, `parseTerm`, `buildEdits`, and related public APIs: exact ASTs, configuration fields, diagnostics, ordering, and precedence. |
| [edits.sh](checks/edits.sh) | 32 real-CLI cases per target, 64 for both. Success requires nonempty `.v` and `.h2ci` output plus selected source assertions; rejection requires a nonzero exit and a diagnostic substring. This script does not compile output. |
| Shared compiler fixtures | Currently 66 `PASS` cases and 3 `TODO_PASS` cases per compiler. Generated proofs, type checks, and deliberate `Fail` commands distinguish selected edit effects from mere successful translation. |

The compiler counts include 12 new edit fixtures and the reactivated `Records`
and `RecordConstruction`, up from 52 `PASS` cases. The record assertions check
field update, named-field construction, and projection of the constructed value.
The lists in `test-rules.mk` determine which fixtures actually run.

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

## Edit coverage matrix

Each row corresponds to one of the 42 `Edit` constructors. `grammarCases` in
`Edits.hs` checks an exact parsed AST for every constructor; `grammarBranchCases`
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
| `InlineMutualEdit` / `inline mutual` | Record each selected function and reject duplicates. | `InlineMutualEdits`: transitively inline `forward`/`relay` so `walk` and `forward` compute through the recursive cycle. |
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
| Mutual inlining with other edits | `InlineMutualEdits` combines transitive inlining with a scoped rewrite, added notation scope, and a specialized helper type; both the recursive result and rejected wrong-type call are checked. |
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
For a new directive, extend `Edits.hs` and this matrix: its exhaustive `editKind`
match is compiled with `-Wall -Werror` so a new constructor needs an inventory
entry.

Use a manual red check when strengthening a witness: temporarily disable the
relevant edit or alter its effect and require the intended assertion to fail;
restore the edit and check both compiler targets. Check that the failure is for
the intended reason, not a missing prerequisite. These commands are not an
automated mutation harness; record any manual mutation checks separately.
