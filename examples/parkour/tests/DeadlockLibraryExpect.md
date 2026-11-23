# Independent library contract freeze

The expectation is `tests/DeadlockLibraryExpect.v`, module
`DeadlockLibraryExpect.DeadlockContract`. Its SHA-256 is
`70c70585f06d6446cbdbdeab2f2238a8615bf7c0a7154ac22f0d7642987a6288`.
The adjacent SHA-256 manifest freezes the spec, actual machine definitions,
source well-formedness, shared-state model, and generated syntax/projection
inputs used for this check. `make -C examples/parkour check-required` verifies
the historical source entry against the frozen Git blob and verifies the
revised occurrence-based source against its separate amendment. A direct
checksum of the *current* source against the historical entry should differ.
Do not refresh these expectations to accommodate a failing library proof.

## Signatures

All four proposition definitions take, in order:

```
M E : Type -> Type
Store Input : Type
model : local_model M E Symbol (Store * Input)
stores : Symbol -> Store
input : Input
R : list Symbol
A : Symbol -> Type
c : forall p, Choreo M p (A p)
```

The last three additionally take `matches`, with exactly this interface:

```
list (source_action E ((Symbol -> Store) * Input)) ->
configuration_C M E ((Symbol -> Store) * Input) A ->
list (action_N E ((Symbol -> Store) * Input)) ->
configuration_N M E ((Symbol -> Store) * Input) -> Prop
```

This parameter abstracts only the future relation, not a proof of simulation.
It may later be instantiated with the real relation closed over the common
inputs. The headline expectation does not take this parameter.

Each proposition requires only `DeadlockWellFormed.well_formed R M A c`,
plus the antecedents intrinsic to its claim:

- `epp_preserves_deadlock_freedom`: every finite source run ends final or
  enabled implies every finite network run ends final or enabled.
- `network_run_has_source`: every finite network run has a source run and
  matching histories/current states.
- `matched_ready`: any reachable matching pair transfers final-or-enabled
  source readiness to final-or-enabled network readiness. No source DF premise.
- `deadlock_reflection`: any reachable nonfinal network without a step has a
  matching reachable nonfinal source without a step.

The file expands both run quantifiers, both readiness disjunctions, and both
negative stuckness conditions. `source_initial` uses actual `c`, empty source
deliveries and `(stores,input)`. `network_initial` uses actual `initialize R`
and `runReaderT (unEpp (epp (c p) (@MkSSymbol p))) Root`, empty queues and the
same state. Both machines use `DeadlockState.shared_model model`.

## Validation and provenance

Created independently before importing or proving any final library exports.
Repository HEAD at validation: `cd185d574200bca191dd5be2d5cf65de5ac58025`.
Parkour upstream HEAD: `872bb12fe1698c8a791b8f64df7b8249f7463367`.
Uncommitted machine sources are identified by the frozen manifest, not HEAD.

Validation used `opam exec --switch=rocq9`, verified Rocq 9.0.1 and the private
ITree pins through `itree_pins.verify_prefix`, then compiled fresh copies in
`build/deadlock-library-expect-independent`, in this order:

1. `DeadlockLocal`
2. `DeadlockRuns`
3. `DeadlockSource`
4. `DeadlockNetwork`
5. `DeadlockState`
6. `DeadlockWellFormed`
7. `DeadlockLibraryExpect`

Every compiler invocation went through `parkour_rocq.py`
(`rocq c -q -w +all`, warning detection, unchanged nonzero status) with a
120-second per-file subprocess timeout. All seven exited zero without warnings.
The load paths were `examples/rocq9.0/base`, Parkour's existing
`build/run/{transformers,manual,local}`, `lib`, and the fresh output directory.
The generated dependencies were existing production objects, not regenerated
by this independent check; the six machine modules were freshly compiled.

Four separate fresh single-query `Print Assumptions` files each produced
exactly `Closed under the global context`. These audit the proposition
definitions, NOT inhabitants proving the propositions. The original isolated
queries used `Require DeadlockLibraryExpect.` and the fully qualified nested
name. The standard `make check-required` gate now issues the same queries
through `check-assumptions.py --library DeadlockLibraryExpect` and verifies
the manifest against its own freshly generated library.

## Public proof gate

`make -C examples/parkour check-final SCRATCH=1` compiles the separate
[direct witness file](../theories/DeadlockContract.v). It applies these
unchanged expectations to the actual inputs and `DeadlockMatch.matches`.
Missing or mistyped exports fail this gate. When the witnesses compile,
each actual theorem receives its own assumption audit.
