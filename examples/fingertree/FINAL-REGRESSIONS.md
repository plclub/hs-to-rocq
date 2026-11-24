# Completed-proof regression run: 2026-11-02

**All six non-HLint catalog jobs passed.** Both shared compiler suites passed
70 positive fixtures and their unchanged three expected compiler failures.
All old-target convenience-copy comparisons were empty. The exact HLint 3.6.1
job remains **blocked** by the local 3.5 installation; its supplemental run
passed. Rocq compiler checks used local core/runtime 9.0.1 rather than CI's exact
9.0.0. This is not an exact seven-job CI pass.

[VALIDATION.md](VALIDATION.md) records the separate clean Rocq 9.2
fifteen-theory acceptance. [BASELINE.md](BASELINE.md) is the unchanged-tool
baseline; [REGRESSIONS.md](REGRESSIONS.md) preserves earlier source-state runs.

## Scope and protected state

Every recorded command ran in the `fingertree` worktree or a selected directory
below it:

```text
/Users/liyao/Workspace/hs-to-coq/.claude/worktrees/fingertree
```

The authoritative `.claude/commands/ci.md`, workflow, setup action, test guides,
baseline, and clean rules were inspected before execution. The catalog jobs ran
sequentially. The Haskell prerequisite passed before dependent jobs; each job
stopped at its first failed command. Every required executed command returned
zero. Existing expected-failure categories and nonzero statuses were preserved.

The continuation changed no Haskell translator or shared fixture input after
the prerequisite passed. The later `ApplicationLaws.v` addition and documentation
updates affect only the new proof tree; its final checks are recorded separately.
The tested production hashes remain the same as the earlier full-catalog record:

| File under `src/lib/HsToRocq/ConvertHaskell/` | SHA-256 |
| --- | --- |
| `Declarations/Class.hs` | `8d1bdfd33ea2edb99a9465a0af02b07ab4d57e64c336c9ec263d7b79cf9b6ce0` |
| `Declarations/Instances.hs` | `c08a03d2228e0cf7a15f6e8f765b845bd562b44770e583fab80406167b8914c0` |
| `Expr.hs` | `65fe714b700134c79eb9a952f2d296dae401294183c5eabeecf1dd00635ef891` |
| `TypeEnv/Instances.hs` | `9ff38768bb32279054ec80de9440b86b9cb4e5f535cb7294687bbeb06589efe1` |

The per-stem guidance hook in `examples/rocq9.0/base-src/Makefile`, already
present before this continuation, had SHA-256
`51e5fa950ea6b3f1de3e6d6fa6f0a839af8868091ce2007b3f7d227a17f8554e`.
Tracked production/test changes and untracked fixture inputs were fingerprinted
before and after this run and matched. At validation time, HEAD stayed
`e4bc91ccc9f039deb352896dae75709c892cb03c`; the staged-diff hash stayed
`adef9d5c8e0c924295e496dc2da5142006a901f2488c32fba581f9649f29383a`.
No staging, commit, push, issue, or PR operation occurred during the recorded run.

## Job results

| Catalog job | Result | Actual checks |
| --- | --- | --- |
| `hlint` | **BLOCKED** for 3.6.1; supplemental 3.5 **PASS** | `hlint src/lib src/exe` returned zero with the available 3.5 tool. |
| `build-haskell` | **PASS** | `stack build`; selected GHC 9.10.3; all three Cabal suites; 225 harness checks; both concurrent target checks and explicit code-generation override. |
| `test-coq-files` | **PASS** | All 24 catalog commands: three opam lints, all ten library/theory directory builds, and the resource example, with Coq 8.20.1. |
| `tests` | **PASS** | All 17 commands: shared suite, base tests/checks, base-thy, and all ten small examples. Shared suite 70 positive/3 expected failures; base suite 18/3. |
| `test-rocq9` | **PASS**, local 9.0.1 | Clean, regenerate/build base with checks, normal shared suite: all three commands zero; 70 positive/3 expected failures. |
| `test-rocq9-translation` | **PASS** | All four commands: clean, fresh generation, tracked no-diff comparison, and non-ignored untracked-file check. |
| `test-translation` | **PASS** | All 15 commands for base, containers, GHC, and graph, preserving catalog ordering and its plain containers `vfiles` invocation. |

The normal shared suites each ran the 32 real-translator edits cases, seven
constructor-tag rejections, and four mutual-inlining rejections. The Coq base
tests and Rocq base target each ran all 26 deriving cases and required fourteen
closed Identity traversal reports. These were normal production entry points,
not focused substitutes.

The expected shared compiler failures stayed `MutrecInst`, `TopBind`, and
`ExceptInDataDefinition`; the base failures stayed `Arrow`, `EqList`, and
`PaperExamples`. `TODO_TRANSLATE` remained empty. All matched their categories.
No unexpected success or nonzero Make result was accepted.

## Commands and environments

The Haskell prerequisite ran from the worktree root:

```bash
stack build
stack exec -- ghc --numeric-version
stack test
bash test/harness.sh
bash test/concurrent.sh
```

The suites reported 237 edits assertions and 805 version/rewrite assertions;
the catalog suite passed its complete default self-tests. Harness output ended
with `Passed 225 harness checks.`; all three concurrent/code-generation checks
reported success.

Compiler jobs selected existing opam switches without changing the global one:

| Tool/environment | Verified local version |
| --- | --- |
| `coq820` | Coq/core/stdlib 8.20.1; OCaml 4.14.2; Equations 1.3.1+8.20; MathComp 2.5.0 |
| `rocq9` | Core/runtime 9.0.1; prover/stdlib 9.0.0; OCaml 4.14.2; Equations 1.3.1+9.0 |
| Stack / selected GHC | 3.11.1 / 9.10.3 |
| GNU Make / GNU sed / lndir | 3.81 / 4.10 / 1.0.5 |
| HLint | 3.5, supplemental only |

All catalog commands inherited:

```bash
LANG=en_US.UTF-8 LC_ALL=en_US.UTF-8
PATH="/opt/homebrew/opt/gnu-sed/libexec/gnubin:$PATH"
```

Coq jobs used `opam exec --switch=coq820 --`; the Rocq compiler job used
`opam exec --switch=rocq9 --`. Translation-only jobs activated no compiler.
Bounded `make -j2` replaced unbounded catalog `make -j`; prescribed serial
commands stayed serial. Rocq tests retained `-w +deprecated-dirpath-Coq`.
The native run validates project commands, not Docker setup, permissions,
caches, or the exact CI image environment.

Already initialized source submodules were checked read-only at the same clean
pins as the baseline instead of issuing redundant state-changing updates:
GHC `3f4d7d38...`, containers `4fda06c4...`, graph `aa50a612...`, and
core-semantics `ba02ee8c...`. The new fingertree submodule stayed clean at
`2f303a41...` throughout.

The compiler directory builds followed the catalog: regenerate each
`Makefile` with `coq_makefile -f _CoqProject -o Makefile`, then build the entire
target in its matching environment. Complete graph and GHC theories were
included. Incremental up-to-date objects were permitted by that catalog;
fixture generation/compilation was forced by the normal rules. The Rocq base
and its suite began with the prescribed clean. Neither job used Rocq 9.2
objects.

## Output comparisons and clean scope

Before destructive steps, scoped tracked/untracked inventories, clean recipes,
and clean dry runs showed only the prescribed old generated outputs and build
products. Source fixtures and new `fingertree`/`rocq9.2` trees stayed outside
those clean paths. The initial old-target generated-source comparisons with
`HEAD` were empty.

Each translation comparison used both:

```bash
git diff --exit-code HEAD -- <output-path>
test -z "$(git ls-files --others --exclude-standard -- <output-path>)"
```

Both checks passed for root base, Rocq 9.0 base, containers library, GHC library,
and graph library. The prescribed containers generation was followed by an
additional safely inspected clean/regeneration. Its library **and** `hs-spec`
comparisons passed: six supplemental commands, all zero. No generated output
was staged, discarded, or accepted as a baseline update during the recorded run.

Later generation cleans removed some compiled old-target outputs, as in the
baseline. Their recorded compiler results refer to the completed builds, and
their regenerated sources were identical to `HEAD` at validation time. The new
fifteen-theory Rocq 9.2 outputs were rebuilt and checked separately afterward.

## Qualifications and review

The prior supplemental containers Make `validate` failure at external-library
path resolution remains recorded in [REGRESSIONS.md](REGRESSIONS.md). That
command is not a catalog step and was not repeated here; its historical failure
is neither hidden nor claimed fixed. Earlier separate logical-library kernel
checks retain their recorded scope.

Formal code/proof review has not been completed. At validation time, all
implementation was uncommitted and the fixed-point-to-HEAD range was empty. The
earlier code-review preparation attempt rejected that scope. Neither review axis
has a supported verdict or finding count. No commit was authorized at validation
time merely to create a review range. The user has now requested one local
commit; after that commit, a meaningful committed scope will be available for
both reviews.

## Evidence index

Evidence directory:

```text
/var/folders/3c/qfxwcbpj7q590cwh0_scnyl80000gn/T/opencode/
  fingertree-proof-regressions-20261102/
```

`results.json` records every command, working directory, exit status, and elapsed
time. Per-job logs use the table's job names; `hlint35-supplemental.log` and
`supplemental-fresh-containers.log` identify supplemental checks.
`protected-before.json` and `protected-after.json` record matching fingerprints.
The separate prerequisite log is `fingertree-build-haskell-final-20261102.log`
in the same temporary parent. These logs are supporting evidence, not build
dependencies; the catalog and repository Make/scripts are the durable commands.
