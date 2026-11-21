
# hs-to-rocq

[![hs-to-rocq](https://github.com/plclub/hs-to-rocq/actions/workflows/hs-to-rocq.yml/badge.svg)](https://github.com/plclub/hs-to-rocq/actions/workflows/hs-to-rocq.yml)

Join our discussion on: [![Zulip](https://img.shields.io/badge/Zulip-chat-informational.svg)](https://coq.zulipchat.com/#narrow/stream/240767-hs-to-coq-devs.20.26.20users)

This repository contains a converter from Haskell code to equivalent
Coq code, as part of the [CoreSpec] component of the [DeepSpec]
project.

CPP'18 paper ["Total Haskell is Reasonable
Coq"](https://arxiv.org/abs/1711.09286) by Antal Spector-Zabusky,
Joachim Breitner, Christine Rizkallah, and Stephanie Weirich. This
paper describes the following examples:

  * [bag](examples/bag) Multiset implementation from GHC's implemention
  * [compiler](examples/compiler) Hutton's razor
  * [base-src](examples/base-src) The sources of the `base/` directory


ICFP'18 paper ["Ready, set, verify! applying hs-to-coq to real-world
Haskell code (experience
report)"](https://dl.acm.org/citation.cfm?id=3236784) by Joachim
Breitner, Antal Spector-Zabusky, Yao Li, Christine Rizkallah, John
Wiegley, and Stephanie Weirich.  This paper describes the verification
of the [containers](examples/containers) library.

See [paper-claims-audit.md](paper-claims-audit.md) for the historical claims audit
and revision-specific recovery results for GHC 9.10.3, Coq 8.20, and containers
v0.7, including post-rebase validation at `1ca9107f`. Historical results remain
scoped to their original revisions.

[**Documentation for the `hs-to-rocq` tool is
available!**](https://hs-to-coq.readthedocs.io/en/latest/)

# Installation

**Current target: GHC 9.10.3; Coq 8.20 (default) or Rocq 9.0 via `--target-version`**

## Compilation

The recommended way of building `hs-to-rocq` is to use `stack`. If you have not
setup stack before, run:

    stack setup

To build `hs-to-rocq`, then run

    stack build

Run the Haskell test suites with `stack test` or `cabal test all`. They do not
require a Coq/Rocq compiler or a generated base library. See the
[tool test guide](test/README.md) for focused suites, dependencies, and the
separate shell integration and compiler checks.

## Building the `base` library

This repository comes with a version of (parts of the) Haskell base library
converted to Coq, which you will likely need if you want to verify Haskell
code.

You must have Coq 8.20 and MathComp (with Hierarchy Builder) to build
the base library and containers proofs. To install these tools:

  1. `opam repo add coq-released https://coq.inria.fr/opam/released` (for
     SSReflect and MathComp)
  2. `opam update`
  3. `opam install coq.8.20.1 coq-mathcomp-ssreflect coq-hierarchy-builder`

Once installed, you can build the base library with

    cd base && coq_makefile -f _CoqProject -o Makefile && make -j && cd ..

The directory `base-thy/` contains auxiliary definitions and lemmas, such as
lawful type-class instances. You can build these with

    cd base-thy && coq_makefile -f _CoqProject -o Makefile && make -j && cd ..

## Regenerating the `base` library

The `base/` directory contains a convenience copy of the generated Coq files.
To regenerate from Haskell source (requires the `ghc-internal` submodule):

    git submodule update --init --recursive
    make -C examples/base-src clean
    make -C examples/base-src

This runs hs-to-rocq on the GHC 9.10 base/ghc-internal sources and
compiles the resulting Coq files. Set `LANG=C.utf8` if you encounter
encoding errors (generated files contain Unicode characters like `∘`).

# Using the tool

To use the tool, run it (using `stack`), passing the Haskell file to be
translated and an output directory to write to:

    stack exec hs-to-rocq -- -o output-directory/ Input/File.hs

Very likely you want to make use of the `base/` library. In that case, make
sure you pass `-e base/edits`.

Have a look at the example directories, e.g. `examples/successors`, for a
convenient `Makefile` based setup.

## Derived instances (GHC 9.10)

Deriving recovery retains successful inline and standalone requests. An
unskipped derivation failure exits nonzero in the default `--strict` mode.
With `--permissive`, the translator warns, removes only the failed request,
and keeps successful derivations if the remaining module passes GHC's full
typecheck. Class, module, and instance skips respect the configured renamings.

When regenerating `ghc-internal`, a checked bridge to GHC's stock generators
supports the source-defined classes in `GHC.Internal.Data.Foldable` and
`GHC.Internal.Data.Traversable`. The bridge checks class compatibility and GHC's
deriving conditions, then typechecks ordinary generated instances without
changing the source classes' identity or the Coq class encoding.

Both target libraries now generate `Functor Solo`, `Foldable Solo`,
`Foldable Down`, and `Traversable` for `Identity`, `Solo`, and `Down`.
Consumers use these shared instances through normal typeclass inference,
without a local `Identity` dictionary. `Solo` was already defined in the manual
`GHC.Tuple` module; the new `GHC/Tuple.h2ci` supplies its constructor metadata.
See the
[deriving and base integration checks](examples/tests/README.md#deriving-and-base-integration)
for commands and the scope of the assumption checks.

## Edits

The `edits` file contains directives to `hs-to-rocq` for ignoring or
transforming some Haskell constructs into proper Coq.

For example, it is common in Haskell to have the following code:

```
module Foo where
...
newtype SomeType = SomeType { someFiled :: Integer }
```

Coq has a single namespace for types and values hence the type name
will conflict with constructor name. One can pass `-e edit` file
containing custom directives to ensure correctness of generated code
with the following directive:

```
rename value Foo.SomeType = Foo.MkSomeType
```


See the [manual](https://hs-to-coq.readthedocs.io/en/latest/) for documentation
for the edits files.


# Examples Status

All examples target **GHC 9.10.3**. Large examples use **Coq 8.20**;
`examples/rocq9.0/` mirrors `base/` and `examples/tests/` for **Rocq 9.0**.
The [Parkour example](examples/parkour/README.md) targets the Choreo2
projection and upstream quorum-voting protocol on Rocq 9.0.1.
The table below records earlier example builds, not post-rebase validation.

## Dependency Chain

```
base → base-thy → containers/lib → containers/theories
                 → transformers/lib
                 → ghc/lib → ghc/theories
                           → core-semantics/lib
                 → graph/lib → graph/theories (needs coq-equations)
                 → wc/lib (needs coq-itree)
                 → shuffle/lib (depends on transformers)
                 → compiler, rle, quicksort, dlist, coinduction,
                   intervals, successors, lambda, simple
```

## Build Status

**Post-rebase checks passed at `1ca9107f`.** The combined source retains PR 229's
Exitify, VarSet, and IntMap recovery from `a038d05a`, including the key-only
contract refinement and TrieMap/Eqdep cleanup, together with issue 228's deriving
recovery from `e41f3c37`. CSE uses the shared `Traversable Identity` instance,
not PR 229's local dictionary. The exact final Exitify contract and the explicit
WF/validity requirements are preserved; intentional model assumptions and the
CSE `WS_cseExpr` admission remain. See the
[GHC proof and validation record](examples/ghc/README.md#exitify-and-cse-proof-recovery).

At that revision, `stack build`, forced generation and compilation of both base
targets, both shared suites, and the deriving/traversal and fast checks passed.
Full base generation left tracked generated outputs byte-identical.
`base-thy`, containers library/theories, and the regenerated GHC library and
all **31 enabled theories** also compiled. See the
[test results](examples/tests/README.md#post-rebase-validation) and
[kernel and assumption checks](examples/ghc/README.md#post-rebase-validation).

On the original issue 228 branch (`e41f3c37`), both production base trees were
regenerated after the retained-kind fix and compiled with their matching
compilers. Both shared unit suites and the base integration checks passed.
That branch also recorded successful builds of `base-thy`, containers
library/theories, and the regenerated GHC library and all 29 theory files then
enabled, including CSE. These results predate the combination with PR 229.

The table preserves those results and earlier records for other examples.
Its file counts are historical, not an inventory of the combined tree.

| Example | Type | Recorded status | Recorded files | Notes |
|---------|------|--------|-------|-------|
| **Core libraries** | | | | |
| `base/` | Generated lib | **PASS** | 57/57 .v | GHC 9.10 base library |
| `base-thy/` | Hand-written proofs | **PASS** | 15/15 .v | Lawful instances |
| `rocq9.0/base` | Generated lib (Rocq 9) | **PASS** | 54/54 .v | `--target-version 9.0` mirror of `base/` |
| **Major verified examples** | | | | |
| `containers/lib` | Generated lib | **PASS** | 16/16 .v | Containers v0.7 |
| `containers/theories` | Proofs | **PASS** | 34/34 .v | Verified Set/IntSet/Map |
| `ghc/lib` | Generated lib | **PASS** | 99 .v | Issue 228: regenerated and compiled with native CSE |
| `ghc/theories` | Proofs | **PASS** | 29/29 .v | At `e41f3c37`: CSE compiled with 8 Qed, 1 Admitted (`WS_cseExpr`); see the GHC README for PR 229's separate results |
| `transformers/lib` | Generated lib | **PASS** | 14/14 .v | Regenerated for GHC 9.10 |
| `graph/lib` | Generated lib + proofs | **PASS** | 6/6 .v | Omega→Lia fixed |
| `graph/theories` | Proofs | **PARTIAL** | 8/11 .v | 3 files need `coq-equations` |
| **hs-to-rocq generation examples** | | | | |
| `bag/` | Hand-written proofs | **PASS** | 8/8 .v | Multiset from GHC |
| `compiler/` | Generate + verify | **PASS** | 8/8 .v | Hutton's razor |
| `coinduction/` | Generate + verify | **PASS** | 2/2 .v | Infinite data structures |
| `dlist/` | Generate + verify | **PASS** | 2/2 .v | Difference lists |
| `intervals/` | Generate + verify | **PASS** | 4/4 .v | Interval library |
| `successors/` | Generate + verify | **PASS** | 2/2 .v | Successors Monad |
| `rle/` | Generate + verify | **PASS** | 2/2 .v | Run-length encoding |
| `quicksort/` | Generate + verify | **PASS** | 3/3 .v | Quicksort |
| `lambda/` | Generate + verify | **PASS** | 2/2 .v | Lambda calculus |
| `simple/` | Generate + verify | **PASS** | 1/1 .v | Simple example |
| **Test suites** | | | | |
| `tests/` | Unit tests | **PASS** | 67 `PASS`, 3 expected-fail | Base-independent; includes `SoleCtorGuard` |
| `base-tests/` | Integration tests | **PASS** | 18 `PASS`, 3 expected-fail | Also passed 26 deriving cases and 14 closed assumption reports |
| `rocq9.0/tests` | Unit tests (Rocq 9) | **PASS** | 67 `PASS`, 3 expected-fail | Reuses `examples/tests/` `.hs` with `rocq c` |
| **Examples with external dependencies** | | | | |
| `wc/lib` | Generated lib | **BLOCKED** | 0/14 .v | Needs `coq-itree` package |
| `wc/theories` | Proofs | **BLOCKED** | 0/2 .v | Depends on wc/lib |
| `shuffle/lib` | Generated lib | **PARTIAL** | 2/5 .v | Needs `Random Int` instance |
| `shuffle/theories` | Proofs | **BLOCKED** | 0/1 .v | Depends on shuffle/lib |
| `core-semantics/lib` | Generated lib | **PASS** | 1/1 .v | Manually updated for GHC 9.10 |
| **Document-only** | | | | |
| `resources/` | Standalone | **PASS** | 1/1 .v | Uses MathComp ssreflect |
| `tip/` | Benchmark framework | N/A | 0 .v in git | Needs `benchmarks` submodule |
| `locks/` | Skeleton | N/A | 0 .v files | _CoqProject only, no sources |
| `base-src/` | Generation source | N/A | — | Source for regenerating `base/` |

## Build Commands

```bash
# Build everything that works
make                                    # base + base-thy + containers + ghc

# Individual examples (generate + compile)
make -C examples/compiler
make -C examples/dlist
make -C examples/rle
make -C examples/quicksort
make -C examples/coinduction
make -C examples/intervals
make -C examples/successors
make -C examples/lambda
make -C examples/simple

# Graph (lib compiles, theories needs coq-equations for 3 proof files)
cd examples/graph/lib && coq_makefile -f _CoqProject -o Makefile && make -j
cd examples/graph/theories && coq_makefile -f _CoqProject -o Makefile && make -j

# Transformers
cd examples/transformers && make

# Haskell suites (no Coq/Rocq compiler or generated base required)
stack test

# Explicit shell integration checks (after stack build; no Coq/Rocq compiler)
bash test/harness.sh
bash test/concurrent.sh
bash test/edits.sh

# Coq 8.20 tests (base-tests requires a compiled base)
make -C examples/tests
make -C examples/base-tests

# Rocq 9.0 base, base checks, and unit tests (use a Rocq 9.0 environment)
make -C examples/rocq9.0

# Rocq 9.0 clean rebuild, including parallel base regeneration
git submodule update --init examples/ghc/ghc
make -C examples/rocq9.0 clean
make -j2 -C examples/rocq9.0 base
make -C examples/rocq9.0/tests
```

The local `/ci` and `/ci-fix` commands share the seven-job catalog in
`.claude/commands/ci.md`. The `ci-catalog` suite uses the existing Haskell YAML
dependency to compare workflow jobs and prerequisites with the catalog, check
`/ci-fix` delegation, reject failure masking, and parse shell snippets with
`bash -n` (including heredoc bodies). Its regressions cover a pinned old catalog,
missing/duplicate jobs, and blocked prerequisites using stubbed tools. The suite
runs its complete self-tests by default, including through `stack test` in
`build-haskell`; it does not execute the documented builds or regeneration.

The Haskell suites and shell runners live in `test/`; compiler fixtures remain
in `examples/tests/`. Shell integration and compiler checks are not part of
`stack test` or `cabal test all`.

The `rocq-version` suite runs 805 direct Haskell assertions about CLI version selection
and rewrite definitions, including proof and obligation tactics, root and module
boundaries, Unicode identifier and notation boundaries, user-name preservation, quoted string
literals (including doubled quote escapes), comments, qualified paths split by
whitespace/comments, relative `From` imports,
unrelated AST text, header imports, and Coq 8.20 identity.
`test/harness.sh` runs 225 checks with fake tools. These exercise both production
test wrappers, nested helper compilation, clean rebuilds, concurrent tool logging,
and serial and parallel base-generation retries through the `base` and `vfiles`
entry points, plus fresh Coq builds with manual modules. Eight cases check that
both base generators restore missing manual interfaces even when the `.v` files
already exist, through direct and `vfiles` targets with `-j1` and `-j2`.
Forced and outdated regeneration must reject stale output, remove failed output
even when its timestamp is unchanged, and retry without regenerating successful
sources.
Four cases run the real `test/identity-traversal.sh` with fake compilers and a
Git stub that rejects repository access. They cover 8.20 and 9.0 from the repository
root and each target's Make caller directory. They verify compiler arguments and
the `IdentityTraversal.v` source path and exercise the fourteen-report check.
The fake translator
writes interfaces and dependency files, so a missing dependency directory fails
the check. These checks do not replace real
compiler tests.
The issue 228 branch at `e41f3c37` recorded all 221 harness cases passing with
macOS Bash 3.2 and Bash 5.3.20. All 221 also passed at `1ca9107f`.

`test/concurrent.sh` runs two modules with a shared source dependency
concurrently on each target. It requires both `.v` and `.h2ci` outputs and checks
that default translation creates no shared GHC object cache, so scheduling cannot
hide the object-file race. GHC only typechecks by default (`-fno-code`); the check
also verifies that an explicit `--ghc -fobject-code` still enables native code
generation.

Both shared unit suites run the `edits` Cabal suite (237 parser/API assertions)
and `test/edits.sh` (32 real-translator CLI cases for their target), alongside
67 `PASS` compiler fixtures and three expected compiler failures. The combined
`SoleCtorGuard` fixture retains both
branches' cases and the computational assertions, but still counts as one
module. The edit checks cover all 42 constructors at the grammar boundary,
file precedence, scoped edits, rewrite ordering, and rejection diagnostics.
Compiler assertions distinguish edit effects for class methods,
recursion, declaration phases, and invariants. Explicit `class kinds` remains
parser-only because it has no translation consumer. See the
[test coverage matrix](examples/tests/README.md) for witnesses and limitations.

Base-dependent checks run separately: `make -C examples/base-tests` includes
`test/deriving.sh` and `test/identity-traversal.sh` for Coq 8.20; the Rocq parent
`make -C examples/rocq9.0 base` runs both after compiling its base. The shared
unit suites remain base-independent. `IdentityTraversal.v` checks public,
inferred instances and requires 14 closed assumption reports: six generated
instances and eight proofs/examples. This is a focused check, not an
axiom-freedom claim for the whole base library or GHC theory.

The shared unit suites compile fixtures on both targets for nested Corelib
references and moved theorems in generated definitions, raw proofs, `Program`
obligations, and preamble/midamble text. They also check that user-qualified names
remain unchanged, including names with combining marks and non-breaking spaces,
that root paths after symbolic notation, pattern apostrophes, and adjacent
numerals rewrite, and that the unqualified `Import WfExtensionality.` succeeds.
Notation coverage includes superscripts, subscripts, and punctuation ending in
dots. User identifiers containing subscripts, apostrophes, or digits remain
unchanged.
The string-literal fixture compares raw preamble, midamble, and proof values
against unchanged AST string literals. Moved theorem references after the literals
also check that rewriting resumes after each closing quote.
The `From`-import fixture loads a generated user library at
`Other.Coq.Init.Decimal` and checks its contents, so a relative operand cannot be
mistaken for a root `Coq.*` reference.
The Rocq suite treats `deprecated-dirpath-Coq` warnings as errors, so compatibility
aliases cannot hide missed namespace rewrites. Helper libraries are recompiled
on every test run, including immediate reruns with identical file timestamps.
The three expected failures in each suite are compiler failures after successful
translation.

The Rocq 9.0 `clean` target deletes the `examples/rocq9.0/base/` convenience copy
as well as test outputs. A subsequent plain `make -C examples/rocq9.0` regenerates
the missing base before compiling it; no separate `vfiles` step is needed.
Regeneration requires the GHC submodule and a built `hs-to-rocq` executable.
If regeneration fails, rerun the same build command after fixing the cause.
The build discards the failed target and retries generation before compiling,
while keeping sources that were generated successfully.
The shared base-generation rules invalidate `_CoqProject` before checking sources
and publish it only after all sources succeed, including direct `vfiles` requests.
Each translating recipe removes its old target first and deletes partial output
on failure, so a zero-exit translation with no output cannot reuse a stale file.
Both targets also prepare manual `.h2ci` files before generation, including
direct file targets, so an existing `GHC/Tuple.v` cannot hide missing `Solo`
constructor metadata.

  Some examples use git submodules, so run

      git submodule update --init --recursive

  once.

* `structural-isomorphism-plugin`: (In progress.)  A GHC plugin that connects
   the re-extracted converted code back into GHC, allowing us to run Haskell
   programs against verified/verifiable code.  Currently does not work.


[CoreSpec]: https://deepspec.org/entry/Project/Haskell+CoreSpec
[DeepSpec]: http://www.deepspec.org/
