Coqified GHC Core
=================

This directory contains a Coq translation of key GHC compiler modules
(core language, optimization passes, utility types), generated from
**GHC 9.10.3** using hs-to-rocq with **Coq 8.20**.

Compilation
-----------

This directory depends on GHC's `base` and `containers` libraries. Before
compiling here make sure those libraries have already been compiled.

    make -C ../../base
    make -C ../containers

Then build the generated library and theory proofs:

    make                # regenerates lib/*.v and compiles them
    cd theories && coq_makefile -f _CoqProject -o Makefile && make -j

Or from scratch:

    make clean && make  # full clean rebuild of lib/
    cd theories && coq_makefile -f _CoqProject -o Makefile && make -j

What's here
-----------

 * `ghc`: A pristine check-out of GHC (submodule, currently at 9.10.3)
 * `lib`: Generated Coq output — symlinks to `manual/` for hand-written
   modules, generated `.v` files for translated modules
 * `theories`: Hand-written proofs about the generated code
 * `Makefile`: Lists the modules to translate and their GHC 9.10 source paths
 * `edits`: Top level edit file (includes `rename module` directives)
 * `axiomatize-types.edits`: Axiomatization of mutual type ball
   (Type, Coercion, TyCon, DataCon, etc.)
 * `module-edits/*`: Per-module edits, `preamble.v` and `midamble.v`
 * `manual`: Hand-written Coq modules (~60 files) for axiomatized types,
   GHC 9.10 stubs, and modules that can't be auto-generated
 * `ghc-head`: Modified GHC source files used instead of the submodule source
 * `deps`: Per-module Makefile dependency fragments

Translated modules
------------------

**Utilities** (10): Util, SrcLoc, Unique, UniqSupply, HsSyn, BasicTypes,
DynFlags, Panic, OccName, Module

**Data structures** (11): Bag, EnumSet, BooleanFormula, UniqFM, UniqSet,
OrdList, FiniteMap, ListSetOps, Pair, Maybes, MonadUtils

**Core type ball** (12, compiled into `Core.v`): IdInfo, Class, TyCon,
DataCon, PatSyn, Var, VarSet, VarEnv, CoreSyn, Demand, Type, TyCoRep,
Coercion

**Core modules** (13): FastStringEnv, Constants, Id, CoreSubst, PrelNames,
CoreUtils, Name, NameEnv, NameSet, FV, Literal, FieldLabel, CoreFVs,
Exitify

**Extras** (15): TrieMap, CSE, CoreStats, UnVarGraph, CoreArity, CoreTidy,
CallArity, CoAxiom, TysWiredIn, MkCore, Digraph, SetLevels, CoreMonad,
OccurAnal, FloatIn, FloatOut

**Hand-written** (~60): AxiomatizedTypes, State, ConLike, Outputable,
PrimOp, RepType, GHC/Core/TyCo/Subst, GHC/Core/Multiplicity, and many
GHC 9.10 stub modules (see `HANDMOD` in Makefile)

Faithfulness overview
---------------------

The translation has several levels of faithfulness to GHC 9.10 source:

| Category | Description |
|----------|-------------|
| Faithful auto-translated | Core AST (Var, Expr, Alt, Bind), utilities (Unique, VarSet, VarEnv, UniqFM, UniqSet), substitution (CoreSubst), exitification (Exitify), containers (IntMap, Map) |
| Faithful manual | Subst type (matches GHC structure), State monad (bare function type matching GHC 9.10), JoinPointHood, idJoinPointHood, ConLike |
| Concrete with model abstractions | CSE traversal; Core-map operations remain opaque, and the existing type/coercion and Tick abstractions still apply |
| Soundly abstracted | Type/Coercion substitution (identity — types don't change structurally), TvSubstEnv/CvSubstEnv := unit |
| Axiomatized (no GHC source) | Type system (Type_, Coercion, TyCon, DataCon), I/O (CoreMonad, DynFlags, Panic), optimizations (OccurAnal, FloatIn, FloatOut, CallArity, CoreArity, SetLevels) |

### Concrete (un-axiomatized) definitions

These functions were previously axiomatized but are now concrete Coq definitions:

 * **`substExpr` / `substBind`** (CoreSubst): Mutually recursive `Fixpoint`
   in midamble. Capture-avoiding substitution for Id variables; type/coercion
   substitution is identity (soundly abstracted since Type_ is abstract).
 * **`exitifyRec`** (Exitify): Concrete with `deferredFix2` for general
   recursion. `mkExitJoinId` is now translated from source with the `ManyTy`
   builder recovered through edits.
 * **CSE traversal**: `cseExpr`, `cseBind`, `cse_bind`, `tryForCSE`,
   `try_for_cse`, and `cseCase` are generated definitions rather than axioms.
   See [Exitify and CSE proof recovery](#exitify-and-cse-proof-recovery) for
   the supporting edits and remaining assumptions.
 * **`Subst` type** (Core.v): Concrete inductive `Mk_Subst InScopeSet
   IdSubstEnv TvSubstEnv CvSubstEnv`, merged into Core.v via the CORESYN
   group. Matches GHC's `GHC.Core.TyCo.Subst.Subst` exactly.
 * **`idJoinPointHood`** (Id midamble): Concrete pattern match on `idDetails`,
   faithful to GHC 9.10.

### Still axiomatized

These functions remain `Axiom` in lib/ and cannot be unfolded in proofs:

 * **FloatOut**: `floatExpr`, `floatBind`, `floatRhs` (axiomatized module)
 * **FloatIn**: `fiExpr`, `fiBinds`, `fiRhs`, `floatIsCase` (axiomatized module)
 * **OccurAnal**: Entire module axiomatized (view patterns + mutual recursion)

### Edit-induced semantic changes

| Edit | Module | Change | Faithful? |
|------|--------|--------|-----------|
| `Panic.Plain.assert x y = y` | Global | Ignore assertions | YES (no runtime assertions in Coq) |
| `warnPprTrace a b c d = d` | Global | Ignore debug traces | YES (no side effects) |
| `DVarSet := VarSet` | Global | Deterministic sets = sets | PARTIAL (loses ordering guarantee) |
| `extendSubst ... = extendIdSubst` | CoreSubst | Ignore type/coercion vars | SOUND (TvSubstEnv = unit) |
| `substUnfolding _ _ = NoUnfolding` | CoreSubst | Ignore unfoldings | SOUND (Unfolding axiomatized) |
| `skip constructor Core.Tick` | Core | Remove Tick expressions | NOT FAITHFUL (ticks exist in GHC) |
| Key/Prefix/Mask := N | IntMap | Use Coq naturals for keys | PARTIAL (Haskell uses machine Int) |

### Termination axiomatizations

Functions using `deferredFix`/`deferredFix2` (axiomatized fixpoint combinator):

| Function | Module | Recursive structure |
|----------|--------|-------------------|
| `mergeWithKey'` | Data.IntMap.Internal | 2-arg on IntMap pair |
| `disjoint` | Data.IntMap.Internal | 2-arg on IntMap pair |
| `restrictKeys` / `withoutKeys` | Data.IntMap.Internal | 2-arg on IntMap x IntSet |
| `exitifyRec.go` | Exitify | Deferred on expression size |

These definitions preserve the translated recursion through an opaque combinator.
Proofs obtain unfolding equations from guarded `deferredFix_eq_on` after proving
well-foundedness and `recurses_on`; see [WF contract recovery](#wf-contract-recovery).

Proved theorems
---------------

### Main results (from Spector-Zabusky et al., arxiv 1910.11724)

 * **`exitifyProgram_WellScoped_JPV`** (Exitify.v, Qed): Exitification
   preserves well-scopedness and join point validity under the model
   assumptions described below
 * **`WellScoped_substExpr`** (CoreSubst.v, Qed): Substitution preserves
   well-scopedness under `WellScoped_Subst`. The 2026-10-29 recovery strengthens
   that internal premise with map invariants; the conclusion is unchanged.

### Exitify and CSE proof recovery

The first recovery, checked on **2026-10-28** relative to `1e4483ca` on
`proof-recovery`, closed the three Exitify admissions and four CSE equations.
It still relied on three inconsistent assumptions. The **2026-10-29**
[WF contract recovery](#wf-contract-recovery) removes those assumptions while
retaining the final Exitify statement and the intentional model abstractions.

#### Exitify

`exitifyRec_WellScoped`, `exitifyRec_JPI`, and `top_go_WellScoped_JPI` now end
in `Qed`. The final `exitifyProgram_WellScoped_JPV` keeps its statement and
has no remaining admitted dependency from these three targets. At the starting
commit it was already `Qed`, but directly called the admitted
`top_go_WellScoped_JPI`; the earlier paper audit's independence claim was false.

The proof extracts the local functions from the generated `exitifyRec` and
unfolds its deferred recursion with `DeferredFix.deferredFix_eq_on`.
`GoDom (deAnnotate ann_e)` restricts the equation to its valid domain, and
`CoreLT` supplies the well-founded relation. Exitify's unfolding does not use
an unconditional fixpoint equation.

`mkExitJoinId` now follows the GHC source. Its module edits map `ManyTy` to
`TysWiredIn.manyDataConTy`; `manyDataConTy` and `manyDataConTyCon` are generated
from `mkTyConTy` and `promoteDataCon`, whose type APIs remain opaque.
`manual/GHC/Builtin/Uniques.v` defines `initExitJoinUnique` as `mkUnique 's' 0`,
matching GHC rather than assuming the unique itself.

#### CSE

`cseExpr_App`, `cseExpr_Let`, `cseBind_NonRec`, and `tryForCSE_simpl` now end
in `Qed` against the native recursive translation. The five-argument
`cse_bind` retains distinct RHS and body environments. `WS_cseExpr` remains
admitted; that well-scopedness gap predates PR209 and is not one of the four
recovered control-flow equations.

The translation uses mutual inlining and the existing `zipMapAccumL` and
`collectNBinders_k` helper contracts. Scoped edits retain the established
type/coercion substitutions and remove only known-empty tick lists in the
Tick-free model. `BasicTypes.activateAfterInitial` is generated from source
with the exact scoped rewrite `nextPhase InitialPhase = Phase 2`; `nextPhase`
itself remains skipped.

All CSE-specific Identity support lives in `module-edits/CSE/edits`:

* `add CSE Local Definition` supplies `cse_identity_traverse` and the
  `cse_identity_traversable` dictionary.
* A scoped rewrite passes that dictionary explicitly to `addRecBinders` at
  singleton `Rec` calls, including their inlined copies.
* `add CSE Lemma` supplies `cse_identity_mapAccumL`, which proves the singleton
  traversal equation with the same explicit dictionary.

All three support declarations are closed under the global context.
The dictionary is a local definition, not a registered Identity instance.
`module-edits/CSE/preamble.v` retains only its original two String import
lines. Fixing the shared standalone-deriving pipeline is outside this recovery.

The translator's `guardTerm` now uses the existing refutability analysis to
omit redundant wildcard branches for irrefutable patterns. The shared
`SoleCtorGuard` PASS fixture covers sole and nested constructors, refutable
constructors, guarded case arms, and empty-list guards.

#### 2026-10-28 assumptions and validation

`Axioms.isLocalUnique_initExitJoinUnique` restores the pre-PR209 locality axiom
from `5aa659c0` at the new `GHC.Builtin.Uniques.initExitJoinUnique` path.
It is a **new axiom declaration relative to `1e4483ca`**, not a proved fact:
`Unique.isLocalUnique` remains abstract.

At that checkpoint, `Print Assumptions exitifyProgram_WellScoped_JPV` included
`All_IntMaps_WF`, `ValidVarSet_Axiom`, the existing `uniqAway` and FV/type
abstractions, and the inherited IntMap `deferredFix2_eq` axiom. Guarded
unfolding in Exitify alone did not remove the imported inconsistent assumptions.
The 2026-10-29 recovery below supersedes this assumption report. The four CSE
equations still retain opaque model APIs, including Core-map operations.

Validation for this recovery:

* Production `make vfiles` regenerated the library. The complete GHC library
  and theory builds passed with Coq 8.20.1 after the final edits and proof
  refactoring.
* Both shared unit suites passed: 53 PASS cases and 3 expected compiler
  failures each, with Coq 8.20.1 and Rocq 9.0.1. These are unit-suite results,
  not a Rocq port of the GHC theories.
* After the final change from preamble support to edits, CSE was freshly
  generated and its library and theory compiled with Coq 8.20.1.
  `coqchk -silent` passed for `Proofs.CSE` and `Proofs.Exitify`. Assumption
  checks confirmed the three closed Identity declarations and the remaining
  model dependencies. Both shared suites preceded this last edit-only
  reshaping; the full GHC builds followed it.

### WF contract recovery

**2026-10-29, relative to `bd8b4f9d` on `proof-recovery`.** This migration
removes `IntMapProofs.All_IntMaps_WF`, `Axioms.ValidVarSet_Axiom`, and
`IntMapProofs.deferredFix2_eq`, not just their uses in selected proofs. It also
removes the blanket derived lemma `StrongValidVarSet_Axiom`. No new axioms or
admissions were introduced in this migration. The locality axiom restored in
the earlier recovery was already present at this baseline.

These were invalid contracts, not harmless abstractions: raw IntMaps can be
malformed, a stored Var can disagree with its lookup key, and an unconditional
fixpoint equation for every functional yields a contradiction using boolean
negation. `ContainerContractCounterexamples.v` adds formal refutations of all
three contracts alongside the six existing malformed-tree counterexamples.

#### Explicit invariants and corrected helper contracts

The translated algorithms and exposed raw datatypes are unchanged. Structural
operation laws require trie-WF evidence. Payload-sensitive laws additionally
require validity of the stored Vars:

```coq
IntMapProofs.WF (Axioms.VarSet_IntMap s) /\ Axioms.ValidVarSet s
```

`WF` describes the IntMap structure; `ValidVarSet` relates lookup keys to the
stored Vars. Neither follows from raw membership equality. `ValidVarSet` and
`StrongValidVarSet` are proved equivalent without a WF premise; callers supply
validity rather than obtain it from a blanket assumption.

Key-only laws for emptiness, subset, and disjointness require WF, but no payload
validity. Their proofs query an arbitrary numeric key with a rekeyed Var rather
than assume that the stored Var already has that key. Filtering membership
implies original membership without validity or predicate-compatibility evidence;
relating the predicate on a stored Var to the queried Var still requires both.

The six raw IntMap contracts `non_member_lookup`, `member_lookup`, `null_member`,
`lookup_insert_neq`, `member_insert`, and `tree_elem_kv_lookup` retain explicit
WF premises. `VarSet_extensional_equal` requires WF and validity for both
sets. Forward-only membership facts such as `member_lookup_some` remain
unconditional where they hold on raw trees.

`VarSetFSet.v` no longer claims that every raw VarSet implements
`FSetInterface.WS`. It retains membership/equality definitions and supplies
premise-aware facts and tactics. It drops the default-based `elements`, `choose`,
and `partition` stubs and their admitted obligations; it does not implement those
operations. Structural congruence lemmas require invariant evidence;
unconditional structural `Proper` instances do not replace it.

`FV.Denotes` now requires WF and validity for the denoted set, scope, and input
accumulator, and proves those invariants for the output accumulator. Its old
membership-only specification admitted malformed accumulators and was false.
`CoreFVs.exprFreeVars_WF` and `exprFreeVars_valid` establish invariants of the
actual computed set. The optional `freeVarsOf_freeVars_revised` theorem now
requires explicit WF premises for the opaque type/coercion DSet functions.
Those premises do **not** enter final Exitify: the generated algorithm tests
`exprFreeVars (deAnnotate ann_e)`, not the annotation sets.

`WellScoped_Subst` now includes WF and validity of both the input scope and
the substitution's in-scope set, plus WF of its Id substitution environment.
Thus `WellScoped_substExpr` keeps its well-scopedness conclusion but has
stronger hypotheses through this internal predicate. `WellScoped` itself
has not changed.

#### Final Exitify boundary and 2026-10-29 assumptions

`exitifyProgram_WellScoped_JPV` retains its exact statement:

```coq
forall pgm,
  WellScopedProgram pgm ->
  isJoinPointsValidProgram pgm ->
  WellScopedProgram (exitifyProgram pgm) /\
  isJoinPointsValidProgram (exitifyProgram pgm).
```

The program input type, `WellScopedProgram`, and join-point-validity definitions
are unchanged. The proof discharges helper premises from `emptyVarSet` and
`getInScopeVars (ep_in_scope pgm) = mkVarSet (bindersOfBinds pgm)`, using proved
construction and preservation lemmas rather than new program hypotheses.

Actual `Print Assumptions` checks for final Exitify and `WellScoped_substExpr`
contain none of the three rejected axioms or the blanket validity alias.
At this checkpoint, final Exitify depends on:

* `uniqAway` contracts, the unique-locality axiom, and type/FV model APIs;
* abstract GHC parameters, including opaque type builders and DSet functions;
* guarded `DeferredFix.deferredFix_eq_on` and opaque `deferredFix`, functional
  extensionality, and `Eqdep.Eq_rect_eq.eq_rect_eq`.

Substitution also retains its `uniqAway` contracts and abstract model APIs.
Neither result establishes a fully concrete GHC model. `coqchk` checks proof
terms against their declared axioms; it does **not** prove those axioms
consistent.

#### Validation on 2026-10-29

* All 20 changed Coq files passed a fresh compilation gate with Coq 8.20.1,
  refreshing unchanged dependencies as needed. The full containers and enabled
  GHC theory builds passed. `coqchk -silent` passed for `IntMapUnionProofs`,
  `Proofs.UniqSetInv`, `Proofs.CSE`, and `Proofs.RecoveryChecks`, including their
  imported proof dependencies.
* Both shared compiler suites passed: 53 PASS cases and
  3 expected compiler failures each on Coq 8.20 and Rocq 9.0. This does not
  constitute a Rocq port of the GHC theories.
* `ContainerContractCounterexamples.v` and `RecoveryChecks.v` are included in
  the theory build. The latter checks the exact final Exitify type, rejects
  the removed names with `Fail Check`, and prints the assumptions of final
  Exitify and substitution. To rerun it, use
  `make -C theories -W RecoveryChecks.v RecoveryChecks.vo` with Coq 8.20 active.

#### Key-only contract refinement (2026-10-30)

Relative to `c8187b0c`, the emptiness, subset, and disjointness specifications and
their public set-algebra helpers no longer require payload validity. WF premises
remain explicit. Lookup-payload and predicate-sensitive filter laws retain their
validity requirements. `ValidVarSet_iff_StrongValidVarSet` completes the two-way
relationship between the existing predicates while preserving the original
`ValidVarSet_StrongValidVarSet` implication.

`RecoveryChecks.v` pins these contracts and conditional structural extensionality,
rejects the removed dummy FSet operations and laws, and exercises the key-only
specifications on a well-formed singleton whose stored Var has the wrong unique.
That singleton is proved invalid, so the regression cannot discharge its goals
through a hidden validity premise. The final Exitify contract and its remaining
model assumptions stay as described above.

Validation on 2026-10-30 passed the enabled GHC theory build, a per-file compile
gate with Coq 8.20.1, `coqchk -silent` for `Proofs.RecoveryChecks` and its imported
dependencies, and the shared Coq compiler suite. This refinement adds no axioms
or admissions.

#### TrieMap and Eqdep cleanup (2026-10-31)

Relative to `c14ff1f6`, the admitted `TrieMapLaws__Map`,
`TrieMapLaws__IntMap`, and `TrieMapLaws__UniqFM` instances are removed.
Their unconditional laws were false on the exposed raw map types: a fold can
visit a stored value that lookup cannot reach. The generic laws and proved
`MaybeMap` instance remain. `TrieMap.v` now has two admitted law instances,
for the opaque `ListMap` and `GenMap` APIs; their proofs are still incomplete.

The IntMap predicates `Desc`, `Desc0`, and `Sem` now take their element type as
a uniform parameter. Their constructor fields, representation invariants, and
operation contracts are preserved. Ordinary inversion replaces dependent-pair
injectivity in `IntMapProofs.v` and `IntMapUnionProofs.v`; the GHC container
proofs use the corresponding constructor patterns.

Actual before/after `Print Assumptions` checks show that final Exitify loses
only `Eqdep.Eq_rect_eq.eq_rect_eq` from the 2026-10-29 assumption list above.
Its exact program-level contract and the WF/validity boundary remain intact.
The substitution theorem's assumption list is unchanged. This cleanup adds
no axioms or admissions; the existing model, functional-extensionality, and
guarded deferred-recursion assumptions remain.

Validation with Coq 8.20.1 passed the full containers and enabled GHC theory
builds, a fresh compile gate for all five changed Coq files, and
`coqchk -silent` for `IntMapProofs`, `IntMapUnionProofs`, `Proofs.TrieMap`, and
`Proofs.RecoveryChecks` and their imported dependencies. The shared Coq compiler
suite passed all 53 PASS cases and 3 expected compiler failures.
`RecoveryChecks.v` continues to pin the final Exitify type and now also rejects
the three removed TrieMap instance names with `Fail Check`.

Theory proof scope and status
-----------------------------

This table describes the recovery's proof dependencies as of **2026-10-29**,
not a census of `Qed` markers or an axiom-free verification claim. Historical
publication evidence remains in [the paper claims audit](../../paper-claims-audit.md).

| File | Scope and status |
|------|------------------|
| `../containers/theories/IntMapRecursion.v` | New operation-specific unfolding equations for merge, disjointness, and key restriction/removal, derived from guarded recursion with proved termination obligations |
| `../containers/theories/IntMapUnionProofs.v` | New semantics and WF preservation for union, difference, and intersection; WF-conditioned disjointness specification |
| `ContainerProofs.v` | IntMap operation contracts with explicit WF premises where needed; no imported blanket WF or unguarded fixpoint equation |
| `Axioms.v` | Explicit validity definitions and conditional extensionality; `uniqAway` and locality assumptions remain |
| `VarSetInvariant.v` | New construction/preservation lemmas and operation specifications for VarSets |
| `VarSetFSet.v`, `VarSet.v` | Premise-aware set algebra and automation; no raw WS instance or admitted stub obligations |
| `VarEnv.v`, `UniqSetInv.v`, `VarSetStrong.v` | Environment, unique-set, and strong-subset clients migrated to explicit invariant evidence |
| `FV.v`, `CoreFVs.v` | Corrected accumulator specification and computed free-variable invariants; optional annotation theorem has explicit DSet WF premises |
| `ScopeInvariant.v`, `JoinPointInvariants.v` | Generic helpers carry invariant evidence; scoping and join-point-validity definitions are unchanged |
| `CoreSubst.v` | Substitution preservation under strengthened `WellScoped_Subst` |
| `Exitify.v` | Final program theorem proved with unchanged statement; remaining assumptions listed above |
| `CSE.v` | Four recovered equations retained; existing `WS_cseExpr` admission remains |
| `ContainerContractCounterexamples.v`, `RecoveryChecks.v` | Refutations of rejected contracts and regression checks for the final theorem boundary |

Unrelated admissions in `TrieMap.v` and the containers development remain.
This recovery does not claim to complete those proofs or the disabled GHC
theories; the enabled theory set is listed in `theories/_CoqProject`.

GHC 9.10 migration details
---------------------------

### Module reorganization

GHC 9.10 reorganized its module hierarchy (e.g., `CoreSyn` ->
`GHC.Core`, `Var` -> `GHC.Types.Var`). The Makefile has explicit
`SRCPATH_*` mappings for each module. The `edits` file uses
`rename module` directives to keep Coq output names unchanged.

### Key API changes

 * **Alt type**: Changed from tuple `(AltCon * list Var * Expr Var)` to
   algebraic `Mk_Alt` constructor. Theory intro patterns changed from
   `[[dc pats] rhs]` to `[dc pats rhs]`.
 * **Mk_Id fields**: 7 fields (added `varMult : Mult` as 4th). Pattern
   matches need an extra wildcard.
 * **realUnique type**: `N` -> `Unique`. Breaks proofs using `N.eqb_*`.
 * **lookupIdSubst**: No longer takes `String` doc parameter.
 * **State monad**: Bare function type `s -> (a * s)`, not newtype wrapper.
 * **Var type**: Single constructor `Mk_Id` only (no TyVar/TcTyVar).
 * **Subst type**: Moved to `GHC.Core.TyCo.Subst`. Now concrete in Core.v
   (was axiomatized; un-axiomatized in Phases 3-5).

### Makefile post-processing

The Makefile applies `sed` fixes to generated `.v` files:
 * **UniqFM.v**: Removes phantom kind parameters from `UniqFM`
 * **BasicTypes.v**: Makes all `Default__*` instances `#[global]`
 * **Core.v**: Extensive fixes for the mutual type ball (inserts ConLike
   type definition, fixes imports, removes circular dependencies).
   Uses `fix-files/` for multi-line insertions (portable across GNU/BSD sed).
 * **Var-related**: Removes redundant wildcard branches for single-constructor types
