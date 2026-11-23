# Parkour: projecting a Choreo2 choreography

This example targets the upstream `explicit-parallel` choreography library
and its quorum-voting protocol. The [specification](SPEC.md) lists the
bindings, type contracts, and projection behavior that the port must preserve.

The separate [deadlock-freedom investigation](DEADLOCK-HANDOFF.md) found
a well-formed two-role `Cond` whose generated endpoints can deadlock under
the specified parallel `App` and FIFO rules. See the handoff for the Rocq
counterexample and the results of the stricter warning gate.

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

The target toolchain is the repository's Stack build (GHC 9.10.3) and
Rocq 9.0.1. Activate the Rocq switch before running the checks. Build the
Rocq 9 base and initialize the GHC submodule for the `transformers` sources:

```sh
git submodule update --init examples/ghc/ghc
git -C examples/ghc/ghc submodule update --init libraries/transformers
stack build
examples/parkour/check-ghc
make -C examples/rocq9.0 base
make -C examples/parkour clean
make -C examples/parkour check
```

`check-ghc` installs the snapshot packages in `upstream-packages.txt`,
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
default method from the pinned base source (`extract-contravariant.py`).
`Parkour.Functions` supplies the standard function `Functor` dictionary and
GHC's `leftSection` helper.

The one example-owned skip is `Choreography.Location.unwrap`: its legacy
`Empty` case has no value to return. `Network` uses `LocTm` from that module.
The evidence-based `Choreography.Choreo2.unwrap` is translated without a
`Default` constraint.

[`ReaderTree.v`](theories/ReaderTree.v) checks the interface between the
Rocq 9 base and the generated libraries. `Tree.Bind` hides an intermediate
type, so a tree lives in a larger universe than its result index. This check
applies the generated `ReaderT` and `Tree` dictionaries explicitly: a universe
error here cannot be fixed by increasing typeclass search depth.
The Rocq 9 base generator makes the bind selector (`GHC.Base.op_zgzgze__`)
universe-polymorphic so `Tree` and `ReaderT` can instantiate it independently.
The example's `universe template` edits name only declarations for which
Rocq 9.0.1 reports `auto-template`, including the generated `Tree` inductive
and `ReaderT` inductive. `ChoreoSig` has no such edit.

`make -C examples/parkour check-deadlock-local` runs the local semantics gate
on its own with Rocq 9.0.1. The first run uses [`install-itree-pins`](ITREE-INSTALL.md)
to build ExtLib, Paco and Interaction Trees under `.itree-cache/pins`; this
cache survives `make clean`. To reuse a prepared installation, set `ITREE_PREFIX`
to the installer’s output directory. Each run verifies the source revisions
and installed objects before compiling the [frozen contracts](tests/DEADLOCK-LOCAL-FREEZE.md)
and checking 20 named exports. Focused compiler and assumption logs are under
`build/deadlock-local/`.

`check-required` (and thus `check`) runs the same gate under `build/run/local/`
and uses that directory and private installation for subsequent compilations.
`test-checks` and `check-edits` do not require the private installation.

`check-required` also builds the run, shared-state, source, source-order,
well-formedness and network contracts. It checks the repaired four-action
network run and the initial well-formedness of generated `Main.quorumVoting`
against its independently typed client contract. Single-export assumption
reports, declarative dependency queries and the disabled-left/right network
controls are in `build/run/semantics/`. These checks do not prove a general
source/network simulation or quorum deadlock freedom.

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
a generated send. `DeadlockFreedom` contributes partial lemmas on empty runs,
final states and readiness under an input-availability premise.

`make -C examples/parkour check-final SCRATCH=1` additionally compiles the
[public witnesses](theories/DeadlockContract.v) against the independent
library and quorum types, then audits the actual exports. A missing proof
makes this target fail. `check-required` checks the slices separately.
Normal `make check` runs `check-final` once after lint, the Haskell
comparison, and harness controls. A green slice check alone cannot make
`check` pass.

For an isolated clean run while another process uses the generated libraries,
run `make -C examples/parkour check-required SCRATCH=1`. The command prints
a fresh directory under `build/` containing its own `lib/` and `run/`.

## Checking the translation

**Strict generator check (2026-11-22):** At upstream `872bb12f`,
`build-example.py` regenerated the dependencies and the HasChor modules into
empty scratch output directories. With the updated Rocq 9 base, all compiled
on Rocq 9.0.1 under `rocq c -q -w +all`. The `epp` assumption check passed,
as did `ReaderTree`, `Required`, `Behavior`, `OwnerCond`, `Integration`, and
the five individual `OwnerCond` closure checks. Both shared compiler suites
and the VC1 edit-policy controls also passed.

**Translation baseline (`3e36e582`, before the all-warnings gate):** The clean
`check` above exited 0 on GHC 9.10.3 and Rocq
9.0.1 at upstream `8ff9fadc480ddbd0397db6c3a12240c39fd9b5fb`. Rocq
reported `Choreography.Choreo2.epp` **Closed under the global context**,
compiled all eight behavior assertions, and typechecked the generated
`Main.quorumVoting` projections at `candidate`, `voter1`, `voter2`, and
`voter3`. The validation used an isolated `STACK_WORK` directory for the
in-tree translator.

`check` includes `make -C examples/parkour lint`, which runs strict mypy,
Ruff, and ShellCheck on the example's scripts. Install `uv` and `shellcheck`
for the default commands, or use `MYPY=mypy RUFF=ruff` with locally installed
Python tools. The typed scripts require Python 3.10 or later.

`make -C examples/parkour test-checks` runs the controls without generating
the library. For example, it compiles a handwritten replacement that computes
the right answer, then checks that the translator refuses to credit it as a
source definition. Another control typechecks an alias to an axiom and checks
that the assumptions test rejects it.

`check-edits` audits the exact translator arguments used by `check-required`.
`CheckEdits.hs` parses each input before merging edits and checks the
SHA-256 of the shared base edits. The translator's `--require-origin` option
checks the source and emitted names listed in [`required.tsv`](required.tsv).
Plain `make -C examples/parkour` runs `check-required`. It verifies the source
bytes, runs the checked Stack-built translator, regenerates the HasChor
modules in an empty `lib/`, and compiles the independent [Rocq assertions](theories/).
Edit external models in [`manual/Parkour/`](manual/Parkour/). The build compiles
copies of those models and the `transformers` dependencies on separate load
paths under `build/run/`. `clean` removes `lib/` and `build/`, preserving the
pinned source, models, and assertions.
