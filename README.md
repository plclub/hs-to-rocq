
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

See [paper-claims-audit.md](paper-claims-audit.md) for a detailed audit of which
paper claims still hold on the current codebase (GHC 9.10.3, Coq 8.20,
containers v0.7).

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
The table below shows the build status of every example directory.

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

| Example | Type | Status | Files | Notes |
|---------|------|--------|-------|-------|
| **Core libraries** | | | | |
| `base/` | Generated lib | **PASS** | 57/57 .v | GHC 9.10 base library |
| `base-thy/` | Hand-written proofs | **PASS** | 15/15 .v | Lawful instances |
| `rocq9.0/base` | Generated lib (Rocq 9) | **PASS** | 54/54 .v | `--target-version 9.0` mirror of `base/` |
| **Major verified examples** | | | | |
| `containers/lib` | Generated lib | **PASS** | 16/16 .v | Containers v0.7 |
| `containers/theories` | Proofs | **PASS** | 34/34 .v | Verified Set/IntSet/Map |
| `ghc/lib` | Generated lib | **PASS** | 99/99 .v | GHC 9.10.3 core |
| `ghc/theories` | Proofs | **PASS** | 29/29 .v | 25 files 0 Admitted; 26 actual Admitted across 4 files |
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
| `tests/` | Unit tests | **PASS** | 52 pass, 3 expected-fail | Translation + type-check |
| `base-tests/` | Integration tests | **PASS** | 18 pass, 3 expected-fail | Requires `base/` |
| `rocq9.0/tests` | Unit tests (Rocq 9) | **PASS** | 52 pass, 3 expected-fail | Reuses `examples/tests/` `.hs` with `rocq c` |
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

# Fast checks (after stack build; no Coq/Rocq compiler required)
stack --allow-different-user exec -- runghc -package=hs-to-rocq examples/tests/checks/RocqVersion.hs
bash examples/tests/checks/harness.sh

# Coq 8.20 tests
make -C examples/tests
make -C examples/base-tests

# Rocq 9.0 base and shared unit tests (use a Rocq 9.0 environment)
make -C examples/rocq9.0

# Rocq 9.0 clean rebuild, including parallel base regeneration
git submodule update --init examples/ghc/ghc
make -C examples/rocq9.0 clean
make -j2 -C examples/rocq9.0 base
make -C examples/rocq9.0/tests
```

The fast checks run 649 direct Haskell assertions about CLI version selection
and rewrite definitions, including proof and obligation tactics, root and module
boundaries, Unicode identifier and notation boundaries, user-name preservation, quoted string
literals (including doubled quote escapes), comments, relative `From` imports,
unrelated AST text, header imports, and Coq 8.20 identity.
They also run 109 harness checks with fake tools. These exercise both production
test wrappers, nested helper compilation, clean rebuilds, concurrent tool logging,
and serial and parallel base-generation retries through the `base` and `vfiles`
entry points, plus fresh Coq builds with manual modules. The fake translator
writes interfaces and dependency files, so a missing dependency directory fails
the check. These checks do not replace real
compiler tests.

The shared unit suites compile fixtures on both targets for nested Corelib
references and moved theorems in generated definitions, raw proofs, `Program`
obligations, and preamble/midamble text. They also check that user-qualified names
remain unchanged, including names with combining marks and non-breaking spaces,
that root paths after superscript notation rewrite, and that the unqualified
`Import WfExtensionality.` succeeds.
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

  Some examples use git submodules, so run

      git submodule update --init --recursive

  once.

* `structural-isomorphism-plugin`: (In progress.)  A GHC plugin that connects
   the re-extracted converted code back into GHC, allowing us to run Haskell
   programs against verified/verifiable code.  Currently does not work.


[CoreSpec]: https://deepspec.org/entry/Project/Haskell+CoreSpec
[DeepSpec]: http://www.deepspec.org/
