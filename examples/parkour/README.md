# Parkour: projecting a Choreo2 choreography

This example targets the upstream `explicit-parallel` choreography library
and its quorum-voting protocol. The [specification](SPEC.md) lists the
bindings, type contracts, and projection behavior that the port must preserve.

The [deadlock-freedom investigation](DEADLOCK-HANDOFF.md) found a
counterexample in the original upstream revision: the choice owner's
continuation could send on `Root` before the announcement on the same FIFO.
The receiver expected the announcement first. The handoff records both
this checked counterexample and the matching run after the fix.

### Theory source layout and `_CoqProject` workflow

[`theories/_CoqProject`](theories/_CoqProject) maps the 83 modules under
[`theories/`](theories/) to the `ParkourTheories` logical root, and
[`tests/_CoqProject`](tests/_CoqProject) maps the 51 positive fixtures and
contracts under [`tests/`](tests/) to `ParkourTheories.Tests` while importing
`ParkourTheories` from `../theories`. Both project files pass
`-arg -q -arg -w -arg +all` and bind the Rocq 9 base, generated `transformers`
modules, manual support models, translated HasChor library, and pinned
`ExtLib`, `Paco`, and `ITree` installations.

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

The build compiles `theories/` and `tests/` in place through `rocq makefile`
with no flat file staging. To prepare the generated libraries, support models,
and verified `build/run/pins` links for standalone `_CoqProject` builds or
editor sessions, run `make -C examples/parkour deps` from the repository root,
then build the theories and, optionally, the test fixtures:

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

Frozen `.sha256` manifests under `tests/` and the immutable specifications
([`SPEC.md`](SPEC.md) and [`DEADLOCK-FREEDOM-SPEC.md`](DEADLOCK-FREEDOM-SPEC.md))
retain their historical `Deadlock*` filenames and digests.
[`tests/namespace-migration.tsv`](tests/namespace-migration.tsv) records 42
tab-separated rows of `(historical input SHA-256, reviewed canonical file SHA-256,
project-relative filename)`. When a historical input was split across multiple
modules (compared with `git show fe8a2152:examples/parkour/theory_sources.py`),
multiple rows with that historical SHA-256 explicitly identify every split
piece. [`scripts/frozen_inputs.py`](scripts/frozen_inputs.py) verifies the
migration table's own pinned digest and compares each file's exact bytes against
its reviewed SHA-256; it never derives an expected digest from the working copy.

An independent migration review comparing the current frozen fixtures and split
modules against `fe8a2152` in Rocq 9.0.1 confirmed all 42 digest triples in
[`tests/namespace-migration.tsv`](tests/namespace-migration.tsv): all 818
historical exports matched with the same normalized elaborated types, and all
467 mutually unfoldable definitions matched their normalized bodies. The
remaining 54 definition entries did not unfold on either side; the comparison
does not claim proof-term identity.

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

Use the repository's Stack build (GHC 9.10.3) and put Rocq 9.0.1 or Rocq 9.2
on `PATH`. Initialize the GHC and `transformers` submodules:

```sh
git submodule update --init examples/ghc/ghc
git -C examples/ghc/ghc submodule update --init libraries/transformers
stack build
examples/parkour/scripts/check-ghc
make -C examples/rocq9.0 base    # only with Rocq 9.0.1
make -C examples/parkour
```

Rocq 9.2 dependency setup skips the `examples/rocq9.0 base` command. Parkour
compiles the same base sources under `build/run/base`, leaving the 9.0.1
objects untouched. Both compilers use the translator's `9.0` output format.
Run `make -C examples/parkour` after switching compilers to rebuild the
generated modules and proofs. `make -C examples/parkour check` also runs lint,
the Haskell comparison, and the harness controls.

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
local semantics gate on its own with either supported compiler. The first run uses
[`scripts/install-itree-pins`](ITREE-INSTALL.md) to build ExtLib, Paco, and
Interaction Trees under `.itree-cache/` in a compiler-specific directory;
these installations survive `make clean`.
To reuse a prepared installation, set `ITREE_PREFIX` to the installer’s output
directory. Each run verifies the source revisions, installed objects, and
[frozen local contracts](tests/DEADLOCK-LOCAL-FREEZE.md) before compiling
[`theories/Semantics/LocalEffects.v`](theories/Semantics/LocalEffects.v) and
the four local test modules in [`tests/Semantics/`](tests/Semantics/) under
their canonical `ParkourTheories` / `ParkourTheories.Tests` roots and checking
20 named exports. Focused compiler and assumption logs are under
`build/deadlock-local/`.

`check-required` (and thus `check`) symlinks the verified private `user-contrib`
tree at `build/run/pins`, compiles `theories/` and `tests/` through their
`_CoqProject` files, and runs the local assumption checks under
`build/run/local/`. `test-checks` and `check-edits` do not require the private
installation.

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
were frozen in `60653fa8` before their witnesses. One schedule leaves a
single peer with both the announcement and data on `Root`; another puts
self-communication and a real exchange in different `App` branches.
One candidate negative in that file changed only the value inside a
source `HearAction`, leaving the observed bytes and receiver state unchanged.
The action hides its payload type. In
[`InvalidSourceTraces.v`](tests/FIFO/InvalidSourceTraces.v)
(`ParkourTheories.Tests.FIFO.InvalidSourceTraces`),
`invented_value_transport_obstruction` shows that a type equality transporting
`true` to `false` would make that candidate incompatible with the positive run.
The [wire-value control](tests/FIFO/WrongAnnouncementValue.v)
(`ParkourTheories.Tests.FIFO.WrongAnnouncementValue`), frozen separately in
`a85f7c51`, tests the peer actually receiving `"False"` after `"True"` was
announced. The original candidate remains in the frozen file; the checker
requires the observable rejection and the transport result separately.

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
**first** packet on the FIFO has that occurrence. The [handoff](DEADLOCK-HANDOFF.md)
traces these two results through to preservation, scheduling, readiness,
deadlock reflection, and their quorum client.

`make -C examples/parkour check-required` compiles the
[public witnesses](tests/Projection/RunAndProgressTypes.v)
(`ParkourTheories.Tests.Projection.RunAndProgressTypes`) against the
independent [library types](tests/Projection/RunCorrespondenceTypes.v) and
[quorum type](tests/Protocols/QuorumProgress.v), then audits the actual
exports (`ParkourTheories.Projection.Progress`,
`ParkourTheories.Projection.RunCorrespondence`, and
`ParkourTheories.Protocols.QuorumVoting`) under `build/run/final/`. A missing
proof makes this target fail. `check-final` is an alias for the same checks.
Normal `make check` runs `check-required` once after `check-layout`, `lint`,
the Haskell comparison, and harness controls.

For an isolated clean run while another process uses the generated libraries,
run `make -C examples/parkour check-required SCRATCH=1`. The command prints
a fresh directory under `build/` containing its own `parkour/` tree (`lib/`,
`build/run/`, and clean copies of `theories/` and `tests/` from their
`_CoqProject` files).

## Checking the translation

The translation assertions live under [`tests/Translation/`](tests/Translation/)
in the `ParkourTheories.Tests.Translation` namespace:
[`ReaderTreeUniverses.v`](tests/Translation/ReaderTreeUniverses.v),
[`GeneratedBindingTypes.v`](tests/Translation/GeneratedBindingTypes.v),
[`EndpointTraces.v`](tests/Translation/EndpointTraces.v),
[`ChoiceBroadcastOrder.v`](tests/Translation/ChoiceBroadcastOrder.v), and
[`QuorumEndpoints.v`](tests/Translation/QuorumEndpoints.v).

**Native project validation (2026-11-22).** On Rocq 9.0.1 and GHC 9.10.3,
`make clean` followed by `make check` passed in this example. The standalone
`_CoqProject` builds compiled 83 library modules and 51 fixtures without
warnings. Both native builds also rejected the `arguments-assert` and
`disj-pattern-notation` controls. Make tracked `Semantics/LocalEffects.v`
as a transitive dependency of `Projection/Progress.vo` and left the unrelated
`Semantics/Roles.vo` current. The [handoff](DEADLOCK-HANDOFF.md) lists the
public theorem assumption reports.

**Historical strict generator check (2026-11-22, pre-migration names):** At
upstream `872bb12f`, `build-example.py` regenerated the dependencies and the
HasChor modules into empty scratch output directories. With the updated Rocq 9
base, all compiled on Rocq 9.0.1 under `rocq c -q -w +all`. The `epp`
assumption check passed, as did `ReaderTree`, `Required`, `Behavior`,
`OwnerCond`, `Integration` (now under `ParkourTheories.Tests.Translation.*`),
and the five individual `OwnerCond` closure checks. Both shared compiler suites
and the VC1 edit-policy controls also passed.

**Historical translation baseline (`3e36e582`, before the all-warnings gate):**
The clean `check` above exited 0 on GHC 9.10.3 and Rocq 9.0.1 at upstream
`8ff9fadc480ddbd0397db6c3a12240c39fd9b5fb`. Rocq reported
`Choreography.Choreo2.epp` **Closed under the global context**, compiled all
eight behavior assertions, and typechecked the generated `Main.quorumVoting`
projections at `candidate`, `voter1`, `voter2`, and `voter3`. The validation
used an isolated `STACK_WORK` directory for the in-tree translator.

`check` includes `make -C examples/parkour lint`, which runs strict mypy,
Ruff, and ShellCheck on [`scripts/`](scripts/). Install `uv` and `shellcheck`
for the default commands, or use `MYPY=mypy RUFF=ruff` with locally installed
Python tools. The typed scripts require Python 3.10 or later.

`make -C examples/parkour test-checks` runs [`scripts/test_layout.py`](scripts/test_layout.py)
and [`scripts/test-checks.sh`](scripts/test-checks.sh) without generating the
library. For example, it compiles a handwritten replacement that computes the
right answer, then checks that the translator refuses to credit it as a source
definition. Another control typechecks an alias to an axiom and checks that the
assumptions test rejects it.

`check-edits` audits the exact translator arguments used by `check-required`.
[`scripts/CheckEdits.hs`](scripts/CheckEdits.hs) parses each input before
merging edits and checks the SHA-256 of the shared base edits. The translator's
`--require-origin` option checks the source and emitted names listed in
[`required.tsv`](required.tsv). Plain `make -C examples/parkour` runs
`check-required` ([`scripts/build-example.py`](scripts/build-example.py)). It
verifies the source bytes, runs the checked Stack-built translator, regenerates
the HasChor modules in an empty `lib/`, and compiles the independent Rocq
projects in [`theories/`](theories/) and [`tests/`](tests/). Edit external
models in [`manual/Parkour/`](manual/Parkour/). The build compiles copies of
those models and the `transformers` dependencies on separate load paths under
`build/run/`. `clean` cleans the generated `Makefile.coq` files in `theories/`
and `tests/` and removes `lib/` and `build/`, preserving the pinned source,
models, theories, and tests.
