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

These preserve recursion structure while hiding the termination argument from Coq.

Proved theorems
---------------

### Main results (from Spector-Zabusky et al., arxiv 1910.11724)

 * **`exitifyProgram_WellScoped_JPV`** (Exitify.v, Qed): Exitification
   preserves well-scopedness and join point validity under the model
   assumptions described below
 * **`WellScoped_substExpr`** (CoreSubst.v, Qed): Substitution preserves
   well-scopedness

### Exitify and CSE proof recovery

The recovery checked on **2026-10-28**, relative to `1e4483ca` on
`proof-recovery`, closes the three Exitify admissions and four CSE equations.
It does not remove the development's remaining model assumptions.

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

#### Remaining assumptions and validation

`Axioms.isLocalUnique_initExitJoinUnique` restores the pre-PR209 locality axiom
from `5aa659c0` at the new `GHC.Builtin.Uniques.initExitJoinUnique` path.
It is a **new axiom declaration relative to `1e4483ca`**, not a proved fact:
`Unique.isLocalUnique` remains abstract.

`Print Assumptions exitifyProgram_WellScoped_JPV` still includes
`All_IntMaps_WF`, `ValidVarSet_Axiom`, the existing `uniqAway` and FV/type
abstractions, and the inherited IntMap `deferredFix2_eq` axiom. The guarded
Exitify equation does not remove those imported assumptions. The four CSE
equations likewise retain existing opaque model APIs, including Core-map
operations. Keep the explicit premises documented in
[WF contract recovery](#wf-contract-recovery).

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

### Earlier mechanized results inventory

The counts in this inventory predate the recovery above and have not been
recounted. For current IntMap and VarSet premises, see
[WF contract recovery](#wf-contract-recovery).

 * **CoreFVs.v** (0 Admitted, 42 Qed): `freeVarsOf_freeVars_revised`,
   `elemVarSet_exprFreeVars_Var_false`, all exprFreeVars lemmas
 * **CoreSubst.v** (0 Admitted, 34 Qed): Full substitution theory including
   `SubstExtends`, `WellScoped_Subst`, all simplification lemmas
 * **JoinPointInvariants.v** (0 Admitted, 33 Qed): Join point validity
   preservation through all Core transformations
 * **ScopeInvariant.v** (0 Admitted, 27 Qed): Scope invariant preservation
 * **Var.v** (0 Admitted, 21 Qed): `isJoinId` lemmas, `EqLaws_Var`
 * **VarSet.v** (0 Admitted, 140 Qed): Comprehensive VarSet reasoning library
 * **ContainerProofs.v** (94 Qed, 0 Local Axioms): IntMap operation properties;
   all 20 previously-axiomatized properties now proved as Lemmas; imports
   deferredFix2_eq + All_IntMaps_WF axioms from IntMapProofs
 * **TrieMap.v** (1 Qed): `TrieMapLaws__MaybeMap` instance proved
 * **VarSetFSet.v** (31 Qed): FSet interface for VarSets including
   `equal_2`, `filter_1`/`filter_2`/`filter_3`

Theory proof inventory
----------------------

The Axioms, CSE, and Exitify rows were checked on 2026-10-28. Other rows retain
earlier counts, including counts from before the WF contract recovery; this
table is not a current census. `Qed` counts are source markers, not evidence
that the results are independent of admitted lemmas or axioms.

| File | Qed | Admitted | Notes |
|------|-----|----------|-------|
| Axioms.v | 11 | 0 | Includes the restored unique-locality axiom; see recovery assumptions above |
| Base.v | 4 | 0 | |
| ContainerProofs.v | 94 | 0 | 0 Local Axioms; imports deferredFix2_eq + All_IntMaps_WF from IntMapProofs |
| Core.v | 11 | 0 | `deAnnotate` lemmas |
| CoreFVs.v | 42 | 0 | All exprFreeVars lemmas proved |
| CoreInduct.v | 14 | 0 | |
| CoreSemantics.v | 2 | 0 | |
| CoreStats.v | 1 | 0 | |
| CoreSubst.v | 34 | 0 | Full substitution theory |
| CSE.v | 7 | 1 | Four equations recovered; inherited `WS_cseExpr` admission remains |
| Exitify.v | 70 | 0 | Three target proofs recovered; final theorem statement unchanged; model assumptions remain |
| Forall.v | 4 | 0 | |
| FV.v | 25 | 0 | |
| GhcTactics.v | 0 | 0 | Tactic library |
| GhcUtils.v | 7 | 0 | |
| JoinPointInvariants.v | 3 | 0 | |
| JoinPointInvariantsInductive.v | 3 | 0 | |
| OrdList.v | 1 | 0 | |
| ScopeInvariant.v | 27 | 0 | |
| StateLogic.v | 18 | 0 | Bare function type State monad |
| TrieMap.v | 1 | 4 | MaybeMap proved; ListMap/GenMap blocked (axiomatized types) |
| Unique.v | 6 | 0 | |
| UniqSetInv.v | 13 | 0 | |
| Util.v | 1 | 0 | |
| Var.v | 21 | 0 | |
| VarEnv.v | 25 | 0 | |
| VarSet.v | 140 | 0 | |
| VarSetFSet.v | 31 | 14 | equal_2, filter_1/2/3 proved; rest blocked by `elements`/`choose`/`partition` = default |
| VarSetStrong.v | 30 | 0 | |

### Remaining Admitted breakdown

Only the CSE entry was refreshed for this recovery. Exitify no longer has
admissions; the other entries below retain the earlier inventory.

| File | Admitted | Reason |
|------|----------|--------|
| CSE.v | 1 | Inherited `WS_cseExpr` well-scopedness admission, outside the four recovered equations |
| TrieMap.v | 4 | `TrieMapLaws__IntMap` and `TrieMapLaws__Map` need alter/fold specs; `TrieMapLaws__ListMap` and `TrieMapLaws__GenMap` blocked by axiomatized types |
| VarSetFSet.v | 14 | `elements`/`choose`/`partition` defined as `HsToRocq.Err.default`; `for_all`/`exists_` need IntMap `foldr` spec; `equal_1`/`is_empty_1`/`subset_1` need key-surjectivity |

### ContainerProofs Axioms (0 Local Axioms)

This earlier account predates the WF contract recovery below. It records the
initial removal of local operation axioms, not the current contracts or a
fresh count.

All Local Axioms have been eliminated from `ContainerProofs.v`. The two
foundational axioms are now imported from `IntMapProofs`:

| Axiom | Purpose |
|-------|---------|
| `IntMapProofs.deferredFix2_eq` | One-step unfolding for `deferredFix2` (general recursion combinator) |
| `IntMapProofs.All_IntMaps_WF` | All IntMaps satisfy the well-formedness predicate from IntMapProofs |

All 24 previously-axiomatized IntMap operation properties (delete, union,
difference, intersection, disjoint, filter, combined) are now proved as
Lemmas. The key characterization lemmas (`lookup_union_eq`,
`lookup_difference_eq`, `lookup_intersection_eq`, `disjoint_spec`) were
proved via well-founded induction on `size_nat m1 + size_nat m2` with
`deferredFix2_eq` for one-step unfolding.

### WF contract recovery

The raw IntMap contracts `non_member_lookup`, `member_lookup`, `null_member`,
`lookup_insert_neq`, `member_insert`, and `tree_elem_kv_lookup` now require
explicit `IntMapProofs.WF` evidence. Their conclusions are unchanged. The
insertion lemma takes WF before key inequality; the tree-membership lemma
takes WF before structural membership. `ContainerContractCounterexamples.v`,
included in the theory build, proves computational counterexamples to all six
unconditional versions.

`VarSet_extensional_equal` is now a proved lemma with explicit WF and
`ValidVarSet` premises for both input sets. Its proof maps stored Vars to their
unique keys, applies semantic uniqueness to the mapped trees, and recovers
boolean equality of the original trees. The generic supporting lemmas are
`IntMap_map_keys_equal` and `IntMap_equal_by_key_membership` in
`ContainerProofs.v`.

`Print Assumptions` reports no axioms for the first five IntMap contracts, the
two generic equality lemmas, or the six counterexamples. The structural
membership contract and the existing WF-conditioned routing helpers retain
only `Eqdep.Eq_rect_eq.eq_rect_eq`. The VarSet extensionality proof depends on
the existing abstract GHC type parameters, without `All_IntMaps_WF`,
`ValidVarSet_Axiom`, or an independent extensional-equality axiom.

In `Axioms.v`, `ValidVarSet_StrongValidVarSet` proves that `ValidVarSet` implies
`StrongValidVarSet`. The existing name `StrongValidVarSet_Axiom` now denotes a
proved lemma derived from `ValidVarSet_Axiom`, rather than an independent axiom.
The proof reuses the stored variable's fields and needs no default instances.

Native IntMap preservation results `delete_Sem`, `delete_WF`, `map_WF`, and
`mapWithKey_WF` are proved in `IntMapProofs.v`, with no axiom assumptions.
Deletion callers use `delete_WF` to derive result well-formedness from input
well-formedness. Forward-only membership callers use the unconditional
`member_lookup_some` lemma.

Callers without invariant evidence still instantiate `All_IntMaps_WF`
explicitly. This is a staged migration: the blanket statement is false for
raw trees and remains an assumption of the final substitution and Exitify
results. Their statements, input types, and scoping predicates are unchanged.
Further recovery needs preservation proofs for the remaining operations and
an invariant boundary for externally supplied maps; key validity alone does
not imply structural WF.

The containers and GHC theory builds and the repaired proof assumptions were
checked with Coq 8.20.1.

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
