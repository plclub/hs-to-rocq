# Parkour: projecting a Choreo2 choreography

This example targets the upstream `explicit-parallel` choreography library
and its quorum-voting protocol. The [translation specification](SPEC.md)
defines what the port must preserve. The [deadlock-freedom contracts](DEADLOCK-FREEDOM-SPEC.md)
are checked against the repaired projection, in which the `Cond` owner broadcasts
before its continuation can send. The [original-projection counterexample](counterexample/UPSTREAM.md)
exercises the opposite ordering on the same FIFO.

With the dependencies below installed, run these commands from the repository root:

```sh
make -C examples/parkour        # Translate the library and compile its theories
make -C examples/parkour check  # Run the tests and audit theorem assumptions
```

`make check` works from clean outputs. It rebuilds the library with edit and
origin checks before compiling the fixtures and querying the resulting proofs.

### Theory source layout and `_CoqProject` workflow

[`theories/_CoqProject`](theories/_CoqProject) maps the 83 modules under
[`theories/`](theories/) to the `ParkourTheories` logical root, and
[`tests/_CoqProject`](tests/_CoqProject) maps the 51 positive fixtures and
contracts under [`tests/`](tests/) to `ParkourTheories.Tests` while importing
`ParkourTheories` from `../theories`. Both project files pass
`-arg -q -arg -w -arg +all` and map the Rocq 9 base, generated `transformers`
modules, manual support models, and translated HasChor library with `-Q`.
They do not map switch packages with `-Q`: `rocq` loads `ExtLib`, `Paco`, and
`ITree` from the active opam switch.

The 83 `.v` sources under [`theories/`](theories/) are organized by domain:

- [`Semantics/`](theories/Semantics/): local ITree effects (`LocalEffects`),
  decidable role equality (`Roles`), abstract finite runs and readiness
  (`Runs`), and shared role stores (`SharedState`).
- [`Choreography/`](theories/Choreography/): occurrences (`Occurrences`),
  typed pending deliveries (`PendingDeliveries`), structural precedence
  (`Precedence`), receive sites (`ReceiveSites`), per-role steps (`RoleSteps`),
  choreography execution (`Execution`), silent/live observations
  (`Observations`), well-formedness (`WellFormedness`), cursor histories,
  labelled steps, log decomposition, and replay archives
  ([`Histories/`](theories/Choreography/Histories/): `CursorHistories`,
  `LabelledSteps`, `LogDecomposition`, `PureBindDescent`, `RoleChronology`,
  `SyntaxDecomposition`, `TransitionArchive`), and cut-family results
  ([`Results/`](theories/Choreography/Results/): `CutFamilySoundness`,
  `FiniteSelection`, `OperandObservations`, `SilentReturns`).
- [`Network/`](theories/Network/): wire mailboxes (`Mailboxes`), endpoint
  control trees (`Endpoints`), network execution (`Execution`), enabledness
  (`Enabledness`), step inversion (`StepInversion`), and roster scheduling
  (`Scheduling`).
- [`Projection/`](theories/Projection/): the endpoint runner (`EndpointRunner`),
  constructor unfolding equations (`ConstructorEquations`), session-ID paths
  (`SessionPaths`), run correspondence (`RunCorrespondence`), readiness and
  deadlock-freedom preservation (`Progress`), [`Matching/`](theories/Projection/Matching/),
  [`FIFO/`](theories/Projection/FIFO/) (and [`FIFO/Heads/`](theories/Projection/FIFO/Heads/)),
  [`Occurrences/`](theories/Projection/Occurrences/),
  [`Payloads/`](theories/Projection/Payloads/),
  [`CommunicationTree/`](theories/Projection/CommunicationTree/), and
  [`RoleLogs/`](theories/Projection/RoleLogs/) (`ArchiveOrder`,
  `ChoiceExecution`, `OccurrenceScope`, `PrimitiveObservations`, and
  [`RoleLogs/Families/`](theories/Projection/RoleLogs/Families/)).
- [`Protocols/`](theories/Protocols/): well-formedness and deadlock freedom for
  `Main.quorumVoting` (`QuorumVoting`).

The 51 positive fixtures under [`tests/`](tests/) mirror these domains under
`ParkourTheories.Tests` ([`Choreography/`](tests/Choreography/),
[`FIFO/`](tests/FIFO/), [`Network/`](tests/Network/),
[`Projection/`](tests/Projection/), [`Protocols/`](tests/Protocols/),
[`Semantics/`](tests/Semantics/), and [`Translation/`](tests/Translation/)).
Modules import library theories and test contracts with `From ParkourTheories`
headers:

```coq
From ParkourTheories Require Import Semantics.LocalEffects Semantics.SharedState
  Projection.Matching.PrefixRelation Network.Scheduling.
From ParkourTheories Require Projection.RunCorrespondence Projection.Progress
  Protocols.QuorumVoting.
From ParkourTheories Require Tests.Projection.RunCorrespondenceTypes
  Tests.Protocols.QuorumProgress.
```

The default build compiles `theories/` in place through `rocq makefile`;
`make check` also compiles `tests/`. For a standalone `_CoqProject` build
or editor session, `deps` prepares the generated libraries and support models.
From the repository root, build the theories first, then the fixtures if
needed:

```sh
make -C examples/parkour deps
make -j2 -C examples/parkour/theories
cd examples/parkour/tests && rocq makefile -f _CoqProject -o Makefile.coq && make -f Makefile.coq
```

Run `make -C examples/parkour check-layout` ([`scripts/check_layout.py`](scripts/check_layout.py))
from the repository root to check `theories/`. Each directory may hold up to 10
`.v` files, no two `.v` filenames in the same directory may share their first
four characters, and each `.v` file may contain up to 1,000 physical lines
(including comments and blank lines) with up to 80 characters per line
excluding the newline. Compiler outputs do not count. The check also verifies
that [`theories/_CoqProject`](theories/_CoqProject) declares
`-Q . ParkourTheories`, lists every `.v` source under `theories/` exactly once,
and uses capitalized Rocq identifiers for all directory and module names.

Use the original Rocq names in Parkour sources: import the particular names
you need (for example, `Import Choreography.Choreo2 (At, Choreo).`) or write
the term directly. `make -C examples/parkour check-no-local-notation` rejects
explicitly local `Notation` and `Infix` declarations, including `#[local]`
and `Reserved` forms. It checks Parkour-authored `.v` files, including
fixtures and translation preambles, and reports each violation by path and
line. The check needs only Python and runs as part of `check-layout`.

[`scripts/frozen_inputs.py`](scripts/frozen_inputs.py) checks the independent
contracts against pinned manifests and maps their source digests to current
modules through [`tests/namespace-migration.tsv`](tests/namespace-migration.tsv).
The [control manifest](tests/slice1.sha256) pins the deadlock-freedom spec at
SHA-256 `688b31eb14f43ccf3b557a3d86aee532eb4aaf2e4e6ce9497c15fc422c326327`.
The [network cases](tests/DEADLOCK-NETWORK-FREEZE.md) and
[source-ordering cases](tests/deadlock-source-ordering-v1.md) are also checked
byte for byte. For the source receive rule, the checker uses the
[occurrence amendment](tests/DeadlockSourceOccurrenceAmendment.md).

The [HasChor submodule](upstream) includes an unpublished, one-commit fix:
the choice owner binds its broadcast before running the continuation.
[`cond-order.bundle`](cond-order.bundle) carries just that commit on top of
the public `explicit-parallel` revision. From the repository root:

```sh
p=examples/parkour/upstream
git submodule init "$p"
if [ ! -e "$p/.git" ]; then
  git clone --no-checkout "$(git config --get submodule.examples/parkour/upstream.url)" "$p"
fi
git -C "$p" fetch ../cond-order.bundle refs/heads/sequence-cond-announcement
git submodule update --init "$p"
make -C examples/parkour verify-source
```

The gitlink pins local revision `872bb12fe1698c8a791b8f64df7b8249f7463367`,
whose parent is `8ff9fadc480ddbd0397db6c3a12240c39fd9b5fb`.
`verify-source` compares working-tree bytes against the pinned Git blobs and
rejects extra files in the source directories. The checkout also supplies the
`mkLoc` Template Haskell splices used by the upstream protocol.

Use GHC 9.10.3 and an opam switch with Rocq 9.0.1 or 9.2. Install the
[pinned ITree dependencies](ITREE-INSTALL.md) in that switch and prepare
the Haskell sources:

```sh
switch=cs2-rocq92  # use rocq9 for the Rocq 9.0.1 switch
opam install --switch="$switch" --deps-only ./examples/parkour/parkour-deps.opam
git submodule update --init examples/ghc/ghc
git -C examples/ghc/ghc submodule update --init libraries/transformers
stack build
examples/parkour/scripts/check-ghc
```

With **Rocq 9.0.1**, first run `opam exec --switch="$switch" -- make -C examples/rocq9.0 base`.
Rocq 9.2 builds those sources under `build/run/base`, leaving the 9.0.1 objects
untouched. Then, with either compiler:

```sh
opam exec --switch="$switch" --set-switch -- make -C examples/parkour
opam exec --switch="$switch" --set-switch -- make -C examples/parkour check
```

Both compilers use the translator's `9.0` output format. Rebuild the
generated modules and proofs after switching compilers. `make check` also
runs `check-layout`, `lint`, the Haskell comparison, and the harness controls
before `check-required`.

The Parkour compiler driver enables all warnings on both versions. On 9.0.1
every warning is fatal. On 9.2 exactly three diagnostic categories remain
visible but nonfatal: `notation-for-abbreviation`, `bad-template-constraint`,
and `register-all`. This lets both versions compile the same frozen sources.
The theorem assumptions, dependency checks and negative controls are the same
on both versions. The shared base and pinned external libraries use their own
upstream build flags.

`scripts/check-ghc` installs the snapshot packages in `upstream-packages.txt`,
typechecks the pinned `Main.hs` with GHC 9.10.3, and checks the four singleton
signatures expanded by `mkLoc`. It does not modify HasChor's Cabal bounds.
When translating `Main`, the build runs those splices with GHC's external
interpreter. On arm64 macOS it also passes `-dynamic` to select `ghc-iserv-dyn`:
the static interpreter can segfault at the first `mkLoc` splice or report a
`PAGE21` relocation out of range while loading the HTTP package dependencies.
Both commands pass `Main.hs` explicitly and reset GHC's home-module search
path to `upstream/src`, so a file in the working directory cannot shadow a
pinned import when GHC expands a splice.

The runtime boundary covers backend transport (including HTTP), primitive
I/O, and STM. The projection, session-ID assignment, and protocol are on the
translated side of that boundary. Checking projected network terms does not
require a running web server or an STM scheduler.

The build translates `Control.Monad.Signatures`, `Control.Monad.Trans.Class`,
and `Control.Monad.Trans.Reader` from the GHC tree's `transformers` submodule
(`ba3503905dec072acc6515323c884706efd4dbb4`), using that package's declared
`Haskell2010` language. It retains the quantified `MonadTrans` superclass.
Reader needs two classes outside the Rocq base: the build translates
`Control.Monad.IO.Class` whole and extracts the `Contravariant` class and its
default method from the pinned base source (`scripts/extract-contravariant.py`).
`Parkour.Functions` supplies the standard function `Functor` dictionary and
GHC's `leftSection` helper.

The one example-owned skip is `Choreography.Location.unwrap`: its legacy
`Empty` case has no value to return. `Network` uses `LocTm` from that module.
The evidence-based `Choreography.Choreo2.unwrap` is translated without a
`Default` constraint.

[`ReaderTreeUniverses.v`](tests/Translation/ReaderTreeUniverses.v)
(`ParkourTheories.Tests.Translation.ReaderTreeUniverses`) checks the interface
between the Rocq 9 base and the generated libraries. `Tree.Bind` hides an
intermediate type, so a tree lives in a larger universe than its result index.
This check applies the generated `ReaderT` and `Tree` dictionaries explicitly:
a universe error here cannot be fixed by increasing typeclass search depth.
The Rocq 9 base generator makes the bind selector (`GHC.Base.op_zgzgze__`)
universe-polymorphic so `Tree` and `ReaderT` can instantiate it independently.
The example's `universe template` edits name only declarations for which
Rocq 9.0.1 reports `auto-template`, including the generated `Tree` inductive
and `ReaderT` inductive. `ChoreoSig` has no such edit.

`make -C examples/parkour check-deadlock-local`
([`scripts/check-deadlock-local.py`](scripts/check-deadlock-local.py)) runs the
local semantics gate on its own with either supported compiler.
[`scripts/itree_pins.py`](scripts/itree_pins.py) verifies the active switch
against [`parkour-deps.opam`](parkour-deps.opam).
Each run checks the [frozen local resumption contracts](tests/DEADLOCK-LOCAL-FREEZE.md),
compiles [`theories/Semantics/LocalEffects.v`](theories/Semantics/LocalEffects.v)
and the four local test modules in [`tests/Semantics/`](tests/Semantics/) under
their canonical `ParkourTheories` / `ParkourTheories.Tests` roots, and checks
all 20 named assumption reports. Focused compiler and assumption logs are under
`build/deadlock-local/`.

`check-required` (and thus `check`) compiles `theories/` and `tests/` through
their `_CoqProject` files and runs the same frozen local contract and 20-export
assumption checks under `build/run/local/`. `check-edits` does not require the
Rocq switch packages.

## Checking deadlock freedom

`check-required` also builds the run, shared-state, source, source-order,
well-formedness, and network contracts. It checks the repaired four-action
network run and the initial well-formedness of generated `Main.quorumVoting`
against its independently typed client contract. Single-export assumption
reports, declarative dependency queries, and the disabled-left/right network
controls are in `build/run/semantics/`.

The same gate checks generated projection equations, network enabledness
and step views, and literal typed-message/FIFO cases. A single-message
fixture checks the correct generated endpoints and two broken variants:
wrong session and omitted sender. The four frozen library propositions
are compiled and audited as *types*; that check supplies no inhabitants.
For the matching relation, the cases accept the initial states and reject
an inserted target event, an invented delivery, and a receive that skips
an earlier choice on the same queue. A fresh dependency query checks that
matching uses the generated projection and the ghost queue relation without
depending on readiness.

The slice gate also checks finite role-value selection, endpoint scheduling,
conditional alignment and matching steps, and a nonempty matched prefix for
a generated send. [`ParallelAndChoiceMatches.v`](tests/Projection/ParallelAndChoiceMatches.v)
(`ParkourTheories.Tests.Projection.ParallelAndChoiceMatches`)
checks either projected `App` branch sending first, self-communication, and
single- and multi-peer choices, including a peer still waiting to hear.
The [independent wire-run expectations](tests/FIFO/ScheduledTraceContracts.v)
(`ParkourTheories.Tests.FIFO.ScheduledTraceContracts`)
cover schedules where a single peer holds both the announcement and data on
`Root`, or where self-communication and a real exchange occur in different `App`
branches. One candidate negative in that file changes only the value inside a
source `HearAction`, leaving the observed bytes and receiver state unchanged.
The action hides its payload type. In
[`InvalidSourceTraces.v`](tests/FIFO/InvalidSourceTraces.v)
(`ParkourTheories.Tests.FIFO.InvalidSourceTraces`),
`invented_value_transport_obstruction` shows that a type equality transporting
`true` to `false` would make that candidate incompatible with the positive run.
The [wire-value control](tests/FIFO/WrongAnnouncementValue.v)
(`ParkourTheories.Tests.FIFO.WrongAnnouncementValue`) tests the peer actually
receiving `"False"` after `"True"` was announced. The original candidate remains
in the frozen contract; the checker requires the observable rejection and the
transport result separately.

Two proofs explain how matching handles value-dependent code. In
[`ReturnedValues.v`](theories/Projection/Matching/ReturnedValues.v)
(`ParkourTheories.Projection.Matching.ReturnedValues`),
`matched_partial_results` recovers the return values of the roles that
finished a prefix; a blocked peer need not supply a value. In
[`ReceiverCodec.v`](theories/Projection/Payloads/ReceiverCodec.v)
(`ParkourTheories.Projection.Payloads.ReceiverCodec`),
`matched_receiver_packet_codec` connects an exposed receiver to the typed
packet its sender actually produced, even inside nested continuations. It
applies to packets at that occurrence. The
[frontier proof](theories/Projection/Matching/MatchedReceiveSafety.v)
(`ParkourTheories.Projection.Matching.MatchedReceiveSafety`) shows that the
**first** packet on the FIFO has that occurrence.

Three modules contain the public theorems:

- [`RunCorrespondence.v`](theories/Projection/RunCorrespondence.v) proves
  `network_run_has_source`: every finite run of the generated endpoints
  has a matching source run.
- [`Progress.v`](theories/Projection/Progress.v) proves `matched_ready` for
  each reachable matched pair, `epp_preserves_deadlock_freedom`, and
  `deadlock_reflection`.
- [`QuorumVoting.v`](theories/Protocols/QuorumVoting.v) proves `quorum_well_formed`
  for the generated four-role program. Its `quorum_deadlock_freedom` corollary
  requires source deadlock freedom for the given local model, stores, and
  input; the client's STM actions can block.

`check-required` compiles the [public witnesses](tests/Projection/RunAndProgressTypes.v)
against the independent [library types](tests/Projection/RunCorrespondenceTypes.v)
and [quorum type](tests/Protocols/QuorumProgress.v). Generated
`Choreography.Choreo2.epp` and the four library theorems must each report
`Closed under the global context`. The two quorum proofs may use only the
14 [permitted runtime constants](tests/slice1/client-allowlist). The individual
reports are under `build/run/semantics/` and `build/run/final/`.

For clean outputs while another process uses the generated libraries, pass
`SCRATCH=1` to the build or check target. Each run prints its fresh directory
under `build/`. `make -C examples/parkour SCRATCH=1` builds `lib/`, `build/run/`
and `theories/` there; `make -C examples/parkour check SCRATCH=1` also builds
`tests/` and writes the assumption reports.

## Checking the translation

The translation assertions live under [`tests/Translation/`](tests/Translation/)
in the `ParkourTheories.Tests.Translation` namespace:
[`ReaderTreeUniverses.v`](tests/Translation/ReaderTreeUniverses.v) (universe
polymorphism across `ReaderT` and `Tree`),
[`GeneratedBindingTypes.v`](tests/Translation/GeneratedBindingTypes.v) (expected
types of the required generated bindings),
[`EndpointTraces.v`](tests/Translation/EndpointTraces.v) (projected `Comm`,
`App`, `par`, `Bind`, and `Cond` behavior),
[`ChoiceBroadcastOrder.v`](tests/Translation/ChoiceBroadcastOrder.v) (the
repaired `Cond` owner's `Bind` root and session-ID nesting, with closed
assumption checks on all five theorems), and
[`QuorumEndpoints.v`](tests/Translation/QuorumEndpoints.v) (projected
`Main.quorumVoting` endpoints at `candidate`, `voter1`, `voter2`, and `voter3`).

`check` includes `make -C examples/parkour lint`, which runs strict mypy,
Ruff, and ShellCheck on [`scripts/`](scripts/). Install `uv` and `shellcheck`
for the default commands, or use `MYPY=mypy RUFF=ruff` with locally installed
Python tools. The typed scripts require Python 3.10 or later.

`make -C examples/parkour test-checks` runs the Python scanner unit tests
([`scripts/test_layout.py`](scripts/test_layout.py) and
[`scripts/test_local_notation.py`](scripts/test_local_notation.py)) and the
shell controls in [`scripts/test-checks.sh`](scripts/test-checks.sh) (including
[`scripts/test-vc1`](scripts/test-vc1)) without generating the library. For
example, it compiles a handwritten replacement that computes the right answer,
then checks that the translator refuses to credit it as a source definition.
Another control typechecks an alias to an axiom and checks that the assumptions
test rejects it.

Both build targets verify the pinned source bytes, regenerate the HasChor
modules in an empty `lib/`, and compile the support models and `transformers`
dependencies on separate load paths under `build/run/`. Edit external models
in [`manual/Parkour/`](manual/Parkour/).

`check-edits` audits the exact translator arguments used by `check-required`.
[`scripts/CheckEdits.hs`](scripts/CheckEdits.hs) parses each input before
merging edits and checks the SHA-256 of the shared base edits. The translator's
`--require-origin` option checks the source and emitted names listed in
[`required.tsv`](required.tsv) during checked translation.

`make clean` removes the compiled theories and fixtures, their generated
Makefiles, and the `lib/` and `build/` directories.
