# Local acceptance freeze

`deadlock-local.sha256` records the first pre-proof expectation draft.
That draft did not elaborate: the `Vis` lambda needed a Boolean annotation,
and the fixture reply function placed its role before its type argument.
The draft also needed an explicit template-universe declaration to meet the
all-warnings policy. These are elaboration corrections, not changed literal
outcomes or propositions. The original digest remains as an audit record.

`deadlock-local-v1.sha256` freezes the corrected, successfully compiled
expectations before any acceptance proof bodies were written. Reruns check
this fixed manifest; they must not regenerate it from the working copy.
The old manifest is historical and intentionally does not match v1.

The local component does not import generated source/network syntax. It is
an independently checked shared primitive, not an integrated preservation
proof. Source `Locally` and target `Exec` must use the same `local_model`,
and each branch must receive the current shared store, not a private copy.

The additive `deadlock-local-exact.sha256` freezes two further generic
contracts before their proofs: return is exactly the independent finite
view ending in `RetF`; a step is exactly a finite view ending in `VisF`
with an enabled reply, the real typed event/reply trace entry, and the
continuation resumed at that reply. `DeadlockLocalExactCases.v` proves
both directions. The expectation files contain no proof bodies.

## Standalone gate

From the repository root, with a private installation made by
`examples/parkour/install-itree-pins`:

```sh
opam exec --switch rocq9 -- python3 examples/parkour/tests/check-deadlock-local.py \
  --itree-prefix "$ITREE_PREFIX" --output "$NEW_EVIDENCE_DIRECTORY"
```

The gate requires Rocq 9.0.1, checks all three source revisions, checks that
installed `.vo` bytes match those pinned builds, checks both active digest
manifests, copies five modules into a fresh directory, and compiles them
through production `parkour_rocq.compile_file`. Thus every acceptance compile
uses `rocq c -q -w +all`. Each compiler/checker invocation has a 120-second timeout.
Each of the 20 independently named exports, including helpers, receives its
own fresh assumption query through `check-assumptions.py`;
the entire output must be exactly `Closed under the global context`.
The output directory retains the copied inputs and full compiler/query logs.

**Standalone validation, 2026-11-22:** exit 0, five modules, no diagnostics,
20 individual closed assumption reports. ExtLib, Paco and ITree were the
three pins listed in the specification, using the fresh private installation
already documented in `ITREE-INSTALL.md`.

## Integration handoff

`theories/DeadlockLocal.v` needs only `From ITree Require Import ITree`.
Its public definitions are `local_model` (interpretation and reply relation
only), `local_view`, `local_return`, `local_event`/`LocalEvent`, and
`local_step`/`LocalStep`. `local_step_typed_trace` exposes the actual
existential event type, event, typed reply, continuation, and stores.
`ViewNow` and `ViewTau` describe finite observation derivations.

The fixed cases use role 7, store 3, `Get : request bool`, reply `true`,
new store 4, and returned value 11 (not 22). They reject store 0, role 8,
and an invented `false` reply. `twice` leaves its second event suspended
after one action. Arbitrarily many finite Taus preserve returns/actions;
visible events are not returns, returns are not actions, and the infinite
Tau tree has neither. The independent exactness contracts prevent extra
step or return rules.

`check-required` now compiles the production theory, expectations and cases
in `build/run/local` and checks all 20 exports before compiling dependents
with the same load path. `check-deadlock-local` runs the local gate without
the translation build. Its success alone does not establish source or
network readiness.
