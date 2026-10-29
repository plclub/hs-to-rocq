# Paper Claims Audit: hs-to-rocq Formal Verification

<!-- Historical audit with dated, scoped recovery updates. -->

**Original audit date**: 2026-03-16
**Original branch**: ghc910-coq820 (GHC 9.10.3, Coq 8.20, containers v0.7)
**Recovery update**: 2026-10-28, proof-recovery, starting at `1e4483ca`
**Invariant recovery update**: 2026-10-29, proof-recovery, relative to `bd8b4f9d`

This document preserves a source-search audit of claims from three publications.
The dated updates distinguish later proof recovery from that historical
evidence. Except where explicitly updated, claims, line references, and counts
remain the 2026-03-16 report, not a fresh audit of the repository. A `Qed`
marker alone does not show that a theorem is independent of admissions or
axioms, and `coqchk` validates proof terms against axioms rather than proving
their consistency.

The 2026-10-28 recovery closed three Exitify admissions and four CSE equations,
but retained inconsistent assumptions. The [2026-10-29 correction](#invariant-recovery-and-audit-correction-2026-10-29)
removes the three rejected axioms and retains the exact final Exitify statement.
Substitution retains its conclusion under a strengthened internal invariant.
Intentional model assumptions remain. See
[Exitify and CSE proof recovery](examples/ghc/README.md#exitify-and-cse-proof-recovery)
and [WF contract recovery](examples/ghc/README.md#wf-contract-recovery) for
implementation details and validation scope.

## Papers Audited

1. **"Ready, Set, Verify!" (JFP 2021)** — doi:10.1017/S0956796820000283
   Verified containers v0.5.11.0 (Data.Set, Data.IntSet, Data.Map.Strict)

2. **"Embracing a Mechanized Formalization Gap" (2019)** — arxiv:1910.11724
   Verified GHC 8.4.3 Core invariants (well-scopedness, join points)

3. **"Ready, Set, Verify!" (ICFP 2018)** — doi:10.1145/3167092
   Conference version of paper 1 (Set, IntSet only; no Map)

---

## Paper 1 & 3: "Ready, Set, Verify!" — Containers

### Claim Status (historical, 2026-03-16)

| # | Claim | Status | Evidence |
|---|-------|--------|----------|
| C1 | Data.Set fully verified, 0 Admitted | **HOLDS** | `SetProofs.v`: 0 Admitted (verified by grep) |
| C2 | Data.IntSet (N-based) fully verified, 0 Admitted | **HOLDS** | `IntSetProofs.v`: 0 Admitted (verified by grep) |
| C3 | All QuickCheck properties proved as theorems | **HOLDS** | `IntSetPropertyProofs.v`: 0 Admitted (verified by grep) |
| C4 | EqLaws/OrdLaws/MonoidLaws for Set | **HOLDS** | `SetProofs.v:5233`: `MonoidLaws_Set` — Qed (line 5272) |
| C5 | EqLaws/OrdLaws/MonoidLaws for IntSet | **HOLDS** | `IntSetProofs.v:6112`: `MonoidLaws_WFIntSet` — Qed (line 6127) |
| C6 | FSetInterface (WSfun, WS, Sfun, S) for Set and IntSet | **HOLDS** | `SetProofs.v:5333`: `Module SetFSet <: WSfun <: WS <: Sfun <: S` — End at 6100. `IntSetFSet.v`: complete |
| C7 | Type class laws for base types | **HOLDS** | `base-thy/GHC/Base.v`: EqLaws for Int/Word/bool/unit/comparison/list/option/pair, MonoidLaws for unit/comparison/option/list — all Qed |
| C8 | Rewrite rules verified (toAscList, toDescList) | **HOLDS** | `SetProofs.v:6113`: `rule_toAscList` — Qed. `IntSetProofs.v:7041`: same — Qed |
| C9 | Bounded_iff_valid for Set | **HOLDS** | `SetProofs.v:4935`: `Bounded_iff_valid` — Qed (line 4943) |
| C10 | fromAscList/fromDistinctAscList skipped for IntSet | **STILL TRUE** | Still skipped in `IntSet/Internal.v` (mutual recursion unsupported) |
| C11 | Data.Map.Strict verified (JFP only) | **HOLDS** | 0 Admitted in `FromListProofs.v` (both obligations Qed) |
| C12 | FMapInterface for Map | **HOLDS** | `InterfaceProofs.v:22`: `Module MapFMap <: WSfun <: WS <: Sfun <: S` — End at 1065 |
| C13 | MonoidLaws for Map (JFP Fig 4) | **HOLDS** | `TypeclassProofs.v:417`: `MonoidLaws_Map` — Qed (line 461). Was a gap; fixed 2026-03-16 |
| C14 | Containers v0.5.11.0 verified | **CHANGED** | Now v0.7; most proofs ported |

### Detailed Notes

**C11 — Map fromList proofs (0 Admitted, was 2)**:
- `fromList_create_Desc` obligation: **FIXED** (2026-03-16). Used `revert dependent P`
  to recover CPS structure, explicit pair destructuring, and `change` to normalize
  Z multiplication match forms.
- `fromList_go_Desc` obligation: **FIXED** (2026-03-16). Used manual CPS via
  `eapply (@fromList'_Desc) + apply showDesc'`, `Eq_le_r` for `order e` compatibility,
  `unfold SomeIf` for proper reduction, and `rewrite sem_list_app; destruct p` for
  residual oro chains.
- Both were *proof engineering* issues (Coq 8.20 `Program Fixpoint` changes), not
  logical gaps.

**C13 — MonoidLaws_Map (fixed)**:
- JFP paper Fig 4 explicitly lists "Map Instances: Eq, Eq1, Monoid, Semigroup"
- Before this audit: only EqLaws, OrdLaws, SemigroupLaws, FunctorLaws were proved
- Fix: added `MonoidLaws_Map` with helper lemma `unions_foldr_union` relating
  `foldl'`-based `unions` to `foldr`-based union chain
- Proof approach: CPS-style `union_Desc`/`empty_Desc` + `strong_eq1` for identity laws;
  `replace` + induction for mconcat law (matching Set proof pattern)

**C14 — Version change**: containers v0.5.11.0 → v0.7.
Key changes: native v0.7 `split`/`fromAscList`/`fromDescList`/`fromDistinctAscList`
definitions. Most proofs ported; Map fromList proofs regressed due to Coq 8.20.

### Improvements Over Papers (2026-03-16 report)

- Set `fromAscList`/`fromDistinctAscList`/`fromDescList` now translated (were skipped)
- IntSetWordProofs.v added (Int-based IntSet variant; 80 Admitted — work in progress)
- IntMapProofs.v added (partial; 12 Admitted, 2 Axioms)
- ContainerProofs.v: 94 proved lemmas, 0 Local Axioms (IntMap properties used by GHC)

### Admitted Summary (Containers, historical)

These are the original source-search counts. The 2026-10-29 recovery removes
the two named IntMap axioms below; it does not recount or complete the remaining
container proofs.

| File | Admitted | Axioms | Theorems Affected |
|------|----------|--------|-------------------|
| IntSetWordProofs.v | 80 | 0 | Bit-level properties; Int-based IntSet variant (new, WIP) |
| IntMapProofs.v | 12 | 2 | `deferredFix2_eq`, `All_IntMaps_WF` axioms; partial coverage (new) |
| FromListProofs.v | 0 | 0 | Both obligations Qed (was 2 Admitted; Coq 8.20 obligation regression fixed) |
| **Total** | **92** | **2** | |

---

## Paper 2: "Embracing a Mechanized Formalization Gap" — GHC

### Claim Status (historical, updated through 2026-10-28)

G2, G6, G9, and G10 were updated on 2026-10-28. Other rows report the original
2026-03-16 audit. The table is preserved as evidence of those assessments;
the [2026-10-29 correction](#invariant-recovery-and-audit-correction-2026-10-29)
below supersedes its substitution, Exitify, and VarSetFSet claims.

| # | Claim | Status | Evidence |
|---|-------|--------|----------|
| G1 | WellScoped_substExpr (Qed) | **HOLDS** | `CoreSubst.v:1431`: Lemma — Qed at line 1436 |
| G2 | exitifyProgram_WellScoped_JPV (Qed) | **RECOVERED UNDER MODEL ASSUMPTIONS** | Final statement unchanged; all three Exitify target helpers now Qed; Coq 8.20.1 compilation and kernel check pass |
| G3 | 0 Admitted in CoreSubst proofs | **HOLDS** | `CoreSubst.v`: 0 Admitted (verified by grep) |
| G4 | Well-scopedness + join point definitions | **HOLDS** | `ScopeInvariant.v`, `JoinPointInvariants.v`: both 0 Admitted |
| G5 | GHC 8.4.3 verified | **CHANGED** | Now GHC 9.10.3 |
| G6 | CSE proofs | **FOUR EQUATIONS RECOVERED** | `CSE.v`: 7 Qed markers, 1 inherited `WS_cseExpr` admission; native translation compiled and kernel-checked |
| G7 | VarSetFSet interface | **PARTIAL** | `VarSetFSet.v`: 13 Admitted (was 18; 7 lemmas proved: subset_1, is_empty_1, for_all_1/2, exists_2, equal_1, eq_dec) |
| G8 | 13K+ lines of proof | **EXPANDED** | Now 30 theory files |
| G9 | Exitify bug fix verified | **RECOVERED UNDER MODEL ASSUMPTIONS** | `exitifyProgram_WellScoped_JPV` now uses proved target helpers; see the correction and remaining assumptions below |
| G10 | Unique-generation assumptions | **BASELINE LOCALITY AXIOM RESTORED** | `isLocalUnique_initExitJoinUnique` restored at the GHC 9.10 path; new declaration relative to `1e4483ca`, inherited from the pre-PR209 model |
| G11 | Type FVs axiomatized as empty | **HOLDS** | `CoreFVs.v`: 4 axioms (`tyCoFVsOfType_is_emptyFV`, `tyCoFVsOfCo_is_emptyFV`, `tyCoVarsOfTypeDSet_empty`, `tyCoVarsOfCoDSet_empty`) |

### Detailed Notes

**G5 — GHC version change**: GHC 8.4.3 → 9.10.3. Major type changes:
`Alt` uses `Mk_Alt` constructor (not tuple); `Mk_Id` has 7 fields (`varMult : Mult`
added 4th); `Var` has single `Mk_Id` constructor (no `TyVar`). These changes
required proof adaptations. The original audit overstated G2
and G9 by overlooking the final Exitify theorem's admitted dependency; the
2026-10-28 recovery closes that proof gap, subject to the assumptions below.

**G6 - CSE recovery (2026-10-28)**:
The 2026-03-16 audit recorded five admissions while the generated CSE module was
axiomatized. Four are control-flow equations, now proved against native
translation:
1. `cseExpr_App` (original audit: line 47)
2. `cseExpr_Let` (original audit: line 53)
3. `cseBind_NonRec` (original audit: line 63)
4. `tryForCSE_simpl` (original audit: line 179)

`WS_cseExpr` (original audit: line 187) is a separate well-scopedness result,
already admitted before PR209. It remains the only admission in `theories/CSE.v`.
The earlier description of all five as unfolding lemmas was incorrect.

The recovery preserves the distinct RHS/body environments in the five-argument
`cse_bind`. CSE's Identity traversal, explicit local dictionary, and singleton
`mapAccumL` lemma are supplied entirely through edits; all three are closed
under the global context. They do not register an Identity instance or fix the
shared standalone-deriving pipeline. The four equations still depend on existing
opaque model APIs, including Core-map operations; they do not prove full CSE
well-scopedness or semantic correctness.

**G7 - VarSetFSet (2026-03-16 report: 15 Admitted, was 18)**:
This historical account predates the replacement of the raw FSet adapter on
2026-10-29. Its counts differ from the original summary table and have not been
reconciled or presented as a current inventory.

7 FSet interface lemmas newly proved using `StrongValidVarSet` axiom
(key-surjectivity) and `VarSet_extensional_equal` axiom (WF PATRICIA uniqueness):
`subset_1` (Qed), `is_empty_1` (Qed), `for_all_1` (Qed), `for_all_2` (Qed),
`exists_2` (Qed), `equal_1` (Qed), `eq_dec` (Defined).
`exists_1` Admitted (1 sub-admit: lookup→tree_elem, blocked by `eq` shadowing).
2 bridge lemmas Admitted (`foldr_andb_eq_go`, `foldr_orb_eq_go`: local fix =
standalone Fixpoint, OOM during proof).
Remaining 10 Admitted use `default` stubs (not real implementations):
`fold_1`, `cardinal_1`, `partition_1/2`, `elements_1/2`,
`choose_1/2/3`, `elements_3w`.

**Exitify recovery and audit correction (2026-10-28)**:
The 2026-03-16 audit recorded three admissions, also present at `1e4483ca`:
1. `exitifyRec_WellScoped` (original audit: line 336)
2. `exitifyRec_JPI` (original audit: line 344)
3. `top_go_WellScoped_JPI` (original audit: line 464)

That recovery reported all three as `Qed`, with 70 Qed markers and no
admissions in `theories/Exitify.v`. These are historical counts, not a new census.
The final `exitifyProgram_WellScoped_JPV` kept its statement and passed Coq
8.20.1 compilation and `coqchk`. The earlier independence claim was
false: its `Qed` proof directly used the admitted `top_go_WellScoped_JPI`.
The recovered helpers closed that dependency rather than bypassing it.

The recovery uses the `GoDom`-guarded `deferredFix_eq_on` rule and the
well-founded `CoreLT` relation to unfold Exitify's local recursion. It also
recovers native `mkExitJoinId` and the `ManyTy` builders, plus the concrete
`initExitJoinUnique` matching GHC's `mkUnique 's' 0`.

At that checkpoint, the final theorem was **not axiom-free**. Its assumptions
included `All_IntMaps_WF`, `ValidVarSet_Axiom`, existing `uniqAway` and FV/type
abstractions, and the inherited IntMap `deferredFix2_eq` axiom.
`isLocalUnique_initExitJoinUnique` is restored from the pre-PR209 model at
`5aa659c0`, now referring to `GHC.Builtin.Uniques.initExitJoinUnique`.
This is a new axiom declaration relative to `1e4483ca`, not a proof of the
abstract locality predicate. In particular, recovering the proofs does not
justify a claim of zero new assumptions relative to that starting commit.
Map-invariant migration remained unfinished at that checkpoint. The next
update records the removal of the three inconsistent assumptions; it does not
erase the earlier locality-axiom addition.

### Invariant recovery and audit correction (2026-10-29)

**Baseline: `bd8b4f9d` on `proof-recovery`.** This recovery removes three
inconsistent declarations from the containers/GHC development, rather than
merely avoiding their names in the final proof:

| Removed declaration | Why its contract is invalid |
|---------------------|-----------------------------|
| `IntMapProofs.All_IntMaps_WF` | Exposed raw trees include malformed IntMaps |
| `Axioms.ValidVarSet_Axiom` | A stored Var can disagree with its lookup key, even in a structurally well-formed singleton |
| `IntMapProofs.deferredFix2_eq` | An unguarded equation for every functional yields a contradiction via boolean negation |

The blanket derived lemma `StrongValidVarSet_Axiom` is also removed.
`ValidVarSet_StrongValidVarSet` remains a proved implication with an explicit
validity premise. `ContainerContractCounterexamples.v` retains the six earlier
malformed-tree examples and adds formal refutations of the three rejected
contracts. The 2026-10-28 compilation and kernel checks did not establish that
these assumptions were consistent.

The recovery changes internal proof contracts, not the translated algorithms
or exposed raw datatypes:

* `IntMapRecursion.v` derives operation-specific equations from guarded
  `deferredFix_eq_on`, with proved well-foundedness and recursion obligations.
  `IntMapUnionProofs.v` proves union/difference/intersection semantics and WF
  preservation, plus a WF-conditioned disjointness specification.
* `VarSetInvariant.v` proves construction and preservation of structural WF
  and key validity. `VarSetFSet.v` replaces the unconditional raw WS adapter
  with premise-aware facts and automation. It drops the admitted stub
  obligations rather than implementing the missing operations. Raw membership
  equality does not supply representation evidence.
* `FV.Denotes` is corrected to exclude malformed scopes and accumulators and
  to prove output WF and validity. `exprFreeVars_WF` and `exprFreeVars_valid`
  establish invariants of the actual computed sets. The optional
  `freeVarsOf_freeVars_revised` theorem requires explicit WF premises for opaque
  type/coercion DSet functions; those premises are not assumptions of final Exitify.
* `WellScoped_Subst` now requires WF and validity for the input and substitution
  scopes, plus WF of the Id substitution environment. **G1 keeps its conclusion
  under stronger hypotheses**, not the same effective contract as before.

For **G2 and G9**, `exitifyProgram_WellScoped_JPV` retains its exact statement,
program input type, scoping predicates, and join-point-validity definitions.
The proof discharges the new helper premises from empty sets and
`mkVarSet (bindersOfBinds pgm)`. No raw-map premise is added to the final theorem.

Actual `Print Assumptions` checks for final Exitify and `WellScoped_substExpr`
contain none of the rejected axioms or the blanket validity alias. Final Exitify
still depends on `uniqAway`/locality contracts, type/FV model APIs, abstract GHC
parameters, guarded `deferredFix_eq_on` and opaque `deferredFix`, functional
extensionality, and `Eqdep.Eq_rect_eq.eq_rect_eq`. Opaque DSet functions remain
in its dependency list, but the optional annotation theorem's DSet WF premises
do not. Substitution retains its `uniqAway` contracts and abstract model APIs.
These results are not proofs about a fully concrete GHC model.

**No new axioms or admissions were introduced relative to `bd8b4f9d`.** This
does not contradict the locality axiom's addition relative to `1e4483ca` on
2026-10-28. The existing CSE `WS_cseExpr` admission and unrelated TrieMap and
container proof debt remain; no current aggregate proof count is claimed.

Validation for this update:

* All 20 changed Coq files passed a fresh compilation gate with Coq 8.20.1,
  refreshing unchanged dependencies. The full containers and enabled GHC theory
  builds passed. `coqchk -silent` passed for `IntMapUnionProofs`,
  `Proofs.UniqSetInv`, `Proofs.CSE`, and `Proofs.RecoveryChecks` and their imported
  proof dependencies. These checks validate proofs relative to axioms, not the
  consistency of those axioms.
* Both shared compiler suites passed: 53 PASS cases and 3 expected compiler
  failures each on Coq 8.20 and Rocq 9.0. This is not a Rocq GHC-theory port.
* The counterexample file and `RecoveryChecks.v` are included in the theory
  build. The latter checks the exact final theorem type, the absence of the
  removed names, and the assumptions of final Exitify and substitution.

### Admitted Summary (GHC Theories, historical)

Only the CSE and Exitify rows were rechecked on 2026-10-28. The other rows
preserve the 2026-03-16 source-search counts; no current aggregate is claimed.
In particular, the VarSetFSet row describes the old adapter removed on 2026-10-29.

| File | Admitted | In Comments | Actual | Theorems |
|------|----------|-------------|--------|----------|
| VarSetFSet.v | 13 | 0 | 13 | 7 proved (subset_1, is_empty_1, for_all_1/2, exists_2, equal_1, eq_dec); 2 bridge + 1 sub-Admitted; 10 default-stub Admitted |
| CSE.v | 1 | 0 | 1 | Inherited `WS_cseExpr`; four equations recovered (2026-10-28) |
| TrieMap.v | 5 | 0 | 5 | `TrieMapLaws` instances for Map/IntMap/ListMap/UniqFM/GenMap |
| Exitify.v | 0 | 0 | 0 | Three target proofs recovered; model assumptions remain (2026-10-28) |
| UniqSetInv.v | 1 | 1 | 0 | (only occurrence is inside `(* ... *)` comment) |

### Axiom Summary (GHC Theories, historical)

The Axioms.v row was rechecked on 2026-10-28. The other rows retain the original
audit counts. These declaration counts are not a theorem-dependency audit.
`ValidVarSet_Axiom` was removed on 2026-10-29; the row below records the earlier state.

| File | Count | Axioms |
|------|-------|--------|
| Axioms.v | 8 | 6 `uniqAway` properties, `ValidVarSet_Axiom`, and the restored `isLocalUnique_initExitJoinUnique` |
| CoreFVs.v | 4 | Type FVs are empty (types axiomatized) |
| JoinPointInvariantsInductive.v | 3 | `isJoinId_eq`, `delVarList_singleton`, `extendVarList_singleton` (in unused code) |

### Zero-Admitted Theory Files (historical source search, 2026-03-16)

CoreInduct, CoreFVs, CoreSemantics, JoinPointInvariants, CoreSubst,
ScopeInvariant, Var, VarSet, VarSetStrong, UniqSetInv, StateLogic, FV, VarEnv

Additional zero-Admitted files:
Axioms, Base, ContainerProofs, Core, CoreStats, Forall, GhcTactics, GhcUtils,
JoinPointInvariantsInductive, OrdList, Unique, Util

### New Since Papers (2026-03-16 inventory)

- TrieMap.v: 5 Admitted (TrieMap axiomatized in GHC 9.10)
- ContainerProofs.v: 94 proved lemmas for IntMap (used by GHC proofs), 0 Admitted
- VarSetStrong.v, UniqSetInv.v, StateLogic.v: new proof modules (all 0 Admitted)
- 30 theory files total (up from ~15 in the paper)

### Translation Blockers Identified in the Original Audit

1. **CSE.v**: The four equation regressions were resolved on 2026-10-28 with
   native translation, edits, and a translator pattern-guard fix. The inherited
   `WS_cseExpr` admission remains.
2. **TrieMap.v** (5 Admitted): TrieMap types axiomatized in GHC 9.10

### Proof Work Identified in the Original Audit

3. **Exitify.v**: All three target admissions were closed on 2026-10-28 using
   guarded unfolding and state-invariant proofs. The 2026-10-29 recovery removes
   the three inconsistent assumptions; intentional model assumptions remain.
4. **VarSetFSet.v** (historical report: 15 Admitted): 5 key-surjectivity lemmas
   proved (was 18); 10 default-stub obligations, 2 bridge lemmas, and 1 sub-admit
   reported as remaining. The 2026-10-29 recovery replaces this raw adapter
   rather than completing its unsupported WS contract.

---

## Summary

The GHC entries below include the dated recoveries through 2026-10-29. Other
entries retain the original audit's findings and have not been re-audited here.

### What Holds
- `WellScoped_substExpr`: preserved conclusion under strengthened
  `WellScoped_Subst` hypotheses (2026-10-29)
- `exitifyProgram_WellScoped_JPV`: exact statement retained without the three
  inconsistent axioms; disclosed model and logical assumptions remain (2026-10-29)
- Complete FSetInterface for Set, IntSet; FMapInterface for Map
- All type class laws (Eq, Ord, Semigroup, Monoid, Functor) for Set, IntSet, Map
- QuickCheck property proofs for IntSet (0 Admitted)
- Rewrite rules verified (toAscList, toDescList)
- `Bounded_iff_valid` for Set

### What Changed
- GHC version: 8.4.3 → 9.10.3 (substantial source code changes)
- Containers version: 0.5.11.0 → 0.7
- Coq version: 8.10 → 8.20 (proof engineering changes)

### Regressions and Recoveries
- CSE: four equation regressions recovered on 2026-10-28; one inherited
  `WS_cseExpr` admission remains
- Exitify: all three internal admissions recovered on 2026-10-28; the final
  statement retained through the invariant recovery on 2026-10-29
- IntMap/VarSet: blanket WF, blanket key validity, and unguarded fixpoint
  assumptions removed on 2026-10-29, with no new axioms or admissions relative
  to `bd8b4f9d`
- Map fromList proofs: 0 Admitted (both Coq 8.20 `Program Fixpoint` regressions fixed)

### What Improved
- MonoidLaws for Map proved (was missing vs JFP Fig 4 claim)
- More translated functions (fromAscList/fromDescList for Set)
- New proof modules (ContainerProofs, VarSetStrong, StateLogic, etc.)
- IntMap proofs added (partial)
- VarSetFSet (2026-03-16 report): 7 lemmas proved via `StrongValidVarSet` +
  `VarSet_extensional_equal` axioms (was 18 Admitted, then 13). On 2026-10-29,
  premise-aware algebra replaces the raw WS adapter and its admitted stub
  obligations; this is not a claim of a complete raw-carrier FSet interface.
