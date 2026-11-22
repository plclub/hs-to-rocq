# Parkour: projecting a Choreo2 choreography

This example targets the upstream `explicit-parallel` choreography library
and its quorum-voting protocol. The [specification](SPEC.md) lists the
bindings, type contracts, and projection behavior that the port must preserve.

The separate [deadlock-freedom investigation](DEADLOCK-HANDOFF.md) found
a well-formed two-role `Cond` whose generated endpoints can deadlock under
the specified parallel `App` and FIFO rules. See the handoff for the Rocq
counterexample and the results of the stricter warning gate.

Initialize the [HasChor submodule](upstream) from the repository root:

```sh
git submodule update --init examples/parkour/upstream
make -C examples/parkour verify-source
```

The gitlink pins `8ff9fadc480ddbd0397db6c3a12240c39fd9b5fb`.
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
interpreter to avoid an in-process `PAGE21` relocation failure on arm64 macOS.
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

For the deadlock-freedom investigation, [the ITree installation guide](ITREE-INSTALL.md)
builds ExtLib, Paco and Interaction Trees from the three specified commits and
checks a resumption against their freshly installed interfaces.

## Checking the translation

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
