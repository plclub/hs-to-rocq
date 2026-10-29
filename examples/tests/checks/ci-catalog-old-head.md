---
description: Run CI checks locally (mirrors GitHub Actions)
allowed-tools: Bash, Read, Glob, Grep
argument-hint: "[job-name] (build|test-coq|tests|test-translation|all)"
---

Run CI checks locally, mirroring the GitHub Actions workflow in `.github/workflows/hs-to-rocq.yml`. Assume all tools (stack, coqc, coq_makefile) are already installed — no Docker or opam setup needed. Do NOT use `--allow-different-user` (that's only for CI containers).

All commands must be run from the workspace root using relative paths.

The argument is: $ARGUMENTS

If the argument is empty or "all", run ALL four jobs in order. Otherwise run only the specified job.

Report pass/fail for each step. At the end, print a summary table of all steps and their results.

## Job: build

```bash
stack build
```

## Job: test-coq

Build all Coq targets in dependency order. For each directory, generate the Makefile from `_CoqProject` first:

```bash
# base
(cd base; coq_makefile -f _CoqProject -o Makefile) && make -j -C base

# base-thy
(cd base-thy; coq_makefile -f _CoqProject -o Makefile) && make -j -C base-thy

# containers
(cd examples/containers/lib; coq_makefile -f _CoqProject -o Makefile) && make -j -C examples/containers/lib
(cd examples/containers/theories; coq_makefile -f _CoqProject -o Makefile) && make -j -C examples/containers/theories

# transformers
(cd examples/transformers/lib; coq_makefile -f _CoqProject -o Makefile) && make -j -C examples/transformers/lib

# graph
(cd examples/graph/lib; coq_makefile -f _CoqProject -o Makefile) && make -j -C examples/graph/lib
(cd examples/graph/theories; coq_makefile -f _CoqProject -o Makefile) && make -j -C examples/graph/theories HeapEquiv.vo Crush.vo Helper.vo NicerQueue.vo RealRing.vo Path.vo Lex.vo WeightedGraphs.vo

# ghc
(cd examples/ghc/lib; coq_makefile -f _CoqProject -o Makefile) && make -j -C examples/ghc/lib
(cd examples/ghc/theories; coq_makefile -f _CoqProject -o Makefile) && make -j -C examples/ghc/theories

# core-semantics
(cd examples/core-semantics/lib; coq_makefile -f _CoqProject -o Makefile) && make -j -C examples/core-semantics/lib

# resources
coqc -Q base "" examples/resources/list_monad.v
```

Run each group sequentially (they depend on each other in order). Report pass/fail after each group.

## Job: tests

Build base first, then run unit tests and small examples:

```bash
# Build base (needed for tests)
(cd base; coq_makefile -f _CoqProject -o Makefile) && make -j -C base

# Unit tests (exit code 2 is OK — means TODO_PASS tests failed as expected)
make -C examples/tests || test $? -eq 2

# Base tests (exit code 2 is OK)
make -C examples/base-tests || test $? -eq 2

# Build base-thy (needed for some examples)
(cd base-thy; coq_makefile -f _CoqProject -o Makefile) && make -j -C base-thy

# Small examples
make -C examples/compiler
make -C examples/rle
make -C examples/quicksort
make -C examples/dlist
make -C examples/coinduction
make -C examples/intervals
make -C examples/successors
make -C examples/lambda
make -C examples/simple
(cd examples/bag; coq_makefile -f _CoqProject -o Makefile) && make -C examples/bag
coqc -Q base "" examples/resources/list_monad.v
```

Run each command sequentially. Report pass/fail for each step.

## Job: test-translation

Regenerate base, containers, and ghc, then verify the convenience copies match what's committed. This requires the git submodules to be initialized:

```bash
# Check submodules are initialized
git submodule update --init examples/ghc/ghc
git submodule update --init examples/containers/containers
```

Then for each target, regenerate and compare:

```bash
# Build hs-to-rocq first
stack build

# Translate base
make -C examples/base-src clean
make -C examples/base-src vfiles
# Check for differences
git add base
git diff-index --cached --quiet HEAD -- base
# Clean up staging
git reset HEAD base

# Translate containers
make -C examples/containers vfiles
git add examples/containers/lib
git diff-index --cached --quiet HEAD -- examples/containers/lib
git reset HEAD examples/containers/lib

# Translate GHC
make -C examples/ghc clean
make -C examples/ghc vfiles
git add examples/ghc/lib
git diff-index --cached --quiet HEAD -- examples/ghc/lib
git reset HEAD examples/ghc/lib
```

If `git diff-index` exits non-zero, the convenience copy is out of date. Show `git diff --cached --stat` before resetting to help the user see what changed. Always run `git reset HEAD <path>` afterward so staging is cleaned up even on failure.

## Summary

After all requested jobs complete, print a summary table like:

```
| Job              | Status |
|------------------|--------|
| build            | PASS   |
| test-coq         | PASS   |
| tests            | FAIL   |
| test-translation | SKIP   |
```

Use PASS, FAIL, or SKIP (if not requested).
