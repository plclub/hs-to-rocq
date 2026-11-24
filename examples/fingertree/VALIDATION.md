# Completed-proof validation: 2026-11-02

**The clean Rocq 9.2 build, exact assumption audits, recursive kernel checks,
and byte-for-byte reproducibility checks passed for all fifteen theories and
all three libraries.** [FINAL-REGRESSIONS.md](FINAL-REGRESSIONS.md) records the
separate passing old-target catalog and its tool-version qualifications.
Formal pinned-range reviews have not been completed; see the review status below.

The results concern the translated Gallina definitions under the explicit
premises in [COVERAGE.md](COVERAGE.md) and foundations in
[ASSUMPTIONS.md](ASSUMPTIONS.md). The sole approved manually supplied algorithm
body is `Data.PriorityQueue.FingerTree.minViewWithKey`; its decision record and
regression proofs remain part of this validation. These checks establish no
general compiler-correctness, complexity, or Haskell partiality claim.

## Tested state

| Item | Value |
| --- | --- |
| Worktree | `/Users/liyao/Workspace/hs-to-coq/.claude/worktrees/fingertree` |
| Branch / parent HEAD at validation time | `fingertree` / `e4bc91ccc9f039deb352896dae75709c892cb03c` |
| Source release / pin | `fingertree-0.1.6.3` / `2f303a410c95802a2824b6dd54a0610fa5329858` |
| Source and license | Complete submodule diff and status empty at the pin |
| Compiler | Rocq core/runtime/stdlib 9.2.0; compiler banner 9.2; OCaml 5.4.1 |
| Local compiler switch | `cs2-rocq92` |
| Generation target / GHC | `--target-version 9.0` / 9.10.3 |
| GHC source pin | `3f4d7d38b9661435bdde981451ac50c4335ed090` |
| Stack / GNU Make | 3.11.1 / 3.81 |
| Locale | `LANG=en_US.UTF-8 LC_ALL=en_US.UTF-8` |

At validation time, the implementation was uncommitted. The index contained only
the original `.gitmodules` addition and fingertree gitlink. Its binary-diff
SHA-256 was:

```text
adef9d5c8e0c924295e496dc2da5142006a901f2488c32fba581f9649f29383a
```

No parent commit, staging operation, push, issue, or PR operation occurred during
the recorded validation run. The original checkout's specifications and unrelated
work remain outside the implementation worktree.

## Clean build and checks

The clean rules and affected paths were inspected first. The following root
commands ran sequentially, with a bounded parallel build:

```bash
make -C examples/fingertree clean
make -C examples/rocq9.2 clean
opam exec --switch=cs2-rocq92 -- make -s -j2 -C examples/rocq9.2 check
opam exec --switch=cs2-rocq92 -- \
  make -s -j2 -C examples/fingertree \
    kernel-check core-check interval-check priority-check
make -s -C examples/fingertree check-source
```

After cleaning, explicit absence checks confirmed that the foundation output
directories, example `lib/Data`, dependency/audit directory, and all theory/check
`.vo`, `.vos`, and `.vok` files were absent. Authored theories remained present.
The build then regenerated and compiled all **54 base**, **five base-thy**,
**three example library**, and **fifteen theory** modules. The foundation checks
also compiled `LoadPaths.v` and `Unfoldr.v`. Every enclosing build/check command
returned zero. Individual theory compiler/audit invocations have 180-second
timeouts; the generated queue/foundation regression checker uses 60 seconds.

`kernel-check` recursively checked all eighteen example library/theory roots.
The focused targets checked their additional declaration audits and source
`unfoldr` check. Supplemental commands recursively checked all 54 base, five
base-thy, and two foundation-check roots. No kernel invocation used `-admit` or
`-norec`.

### Corrected supplemental validation command

The first all-foundation kernel command incorrectly named the load-path probe
`Rocq92Checks.LoadPaths`. Its compilation command gives it the root name
`LoadPaths`; only `Unfoldr` is compiled with the `Rocq92Checks` prefix. The
supplemental command exited 1 at library-name resolution:

```text
LoadPaths.vo contains library LoadPaths and not library Rocq92Checks.LoadPaths
```

The failed command and log are retained. The corrected command checked the 54
base modules, five proof modules, and `Rocq92Checks.Unfoldr` with the prefixed
check path. A separate command checked `LoadPaths` with `-Q
examples/rocq9.2/checks ""`. Both returned zero. No production source or build
rule was changed to accommodate this command correction. The clean build,
theory audits, and example kernel checks had already passed and were preserved.

## Exact transitive assumptions

All **1,048/1,048** exported-constant reports matched
[`theories/assumptions.json`](theories/assumptions.json):

| Exact set | Reports |
| --- | ---: |
| Empty global-assumption set | 947 |
| Functional extensionality only | 38 |
| `deferredFix` only | 5 |
| `deferredFix` and `deferredFix_eq_on` | 58 |

These counts include definitions, helper lemmas, records, and record fields;
they are not a count of public-operation theorems. Quantified monoid, ordering,
validity, predicate-domain, and mapping premises remain in the theorem types.
The extraction/decrease and valid-domain `recurses_on` proofs are closed;
guarded unfolding intentionally retains the authorized deferred axioms.
General application Eq/Ord laws in `ApplicationLaws.v` also cover lawful
Boolean equivalences without requiring comparison ties to be propositional
equality. Stronger reflection corollaries remain available separately.

The separate generated queue audit retained all 74 declarations: 50 closed and
24 with only `deferredFix`. `OldList.unfoldr` is the 75th report, also
`deferredFix`-only. Its four-entry foundation audit and all five closed
`PriorityRegression` equations matched their exact expected sets. The generated
core inventory retained all 18 dictionaries, 83 local methods, and 30 exported
operations including three `TESTING` helpers: 131 closed reports.

The theory checker was also challenged with a real Rocq proof depending on a
temporary `rogue` axiom outside the checkout. It detected that unexpected
dependency. Controls for missing, duplicated, malformed, and ambiguous reports,
and unaudited theorem/axiom declarations, were rejected. No such axiom or test
fixture is part of the repository's proof sources.

## Reproducibility and preservation

A pre-clean manifest and a post-build manifest matched **122/122 SHA-256
comparisons**, with identical path inventories:

| Files | Count |
| --- | ---: |
| Foundation `.v`, `.h2ci`, and both `_CoqProject` files | 100 |
| Three example `.v`/`.h2ci` pairs | 6 |
| Fifteen authored theories and exact assumption manifest | 16 |
| **Total** | **122** |

The durable [`validation.sha256`](validation.sha256) manifest originally pinned
the exact 122 files tested on 2026-11-02. The standards cleanup below refreshed
only the three changed theory-source hashes after validation; the original
manifest remains available at commit `d0aa2436d727942996bdd32c994e22f811983afa`.
The other 119 entries retain the original hashes. From the worktree root, run
`shasum -a 256 -c examples/fingertree/validation.sha256` to check those files
against the manifest.

The source-pin/unchanged-tree check passed after rebuilding, including the
license. At validation time, HEAD and the staged-diff hash stayed unchanged.
Old-target convenience copies remained byte-identical to `HEAD` in the separate
regression run.
Working-tree and cached whitespace checks passed.

An earlier fourteen-theory run matched 121 files and 1,011 reports. That run
predates `ApplicationLaws.v`; the fifteen-theory record above supersedes it.
The still-earlier 107-file source/size-toolkit record remains historical.

## Review status

Both formal review flows require a nonempty committed range. At validation time,
parent HEAD equaled the supplied starting point. The earlier code-review
preparation helper was invoked with base and head both pinned to `e4bc91cc...`;
it rejected the then-empty scope with `error: empty or unsupported diff`. Proof
review was blocked by the same empty range. No unauthorized commit was made
during validation to create a review range.

The user has now requested one local commit; after that commit, a meaningful
committed scope will be available for both reviews. Formal code/proof review has
not been completed. Neither Standards nor Spec has a supported formal verdict
or finding count. Compilation, coverage inspection, and assumption audits do
not substitute for those reviews.

## Evidence

The durable interfaces, manifest, Make targets, and reports above are the
reproduction entry points. Detailed local evidence remains under:

```text
/var/folders/3c/qfxwcbpj7q590cwh0_scnyl80000gn/T/opencode/
  fingertree-proof-acceptance-final-20261102/
```

It contains `before.json`, `after.json`, `steps.json`, `summary.json`, clean and
build logs, the initial failed `05-all-foundation-kernels.log`, corrected
`05b-all-foundation-kernels.log`, `06-loadpath-kernel.log`, and `07-source.log`.
The current per-constant typed audit logs are also recreated under
`examples/fingertree/deps/proof-audits/` by normal builds. Temporary evidence is
not a build dependency.

## Standards cleanup validation: 2026-11-03

The four low-priority duplication findings from the review of
`a038d05a3f3c45952d1da650b6e8d6657b9b63fc...d0aa2436d727942996bdd32c994e22f811983afa`
were addressed without changing theorem statements or the Gallina export and
assumption inventories:

* The three `InlineMutualEdits` regressions share their accessibility tactic.
* `split_correct` shares one nonempty argument instead of separate Single/Deep copies.
* `ApplicationLaws` reuses `CoreInstances.direct_ord_methods`.
* Both Python auditors reuse `parse_assumption_block` from the theory checker;
  marker and constant association remain separate.

The other concurrent agent's Spec fixes were preserved. The shared Python
parser extraction changed only report parsing, not their declaration-inventory
changes or tests. All 57 Python controls passed with native Rocq 9.2, including
the new omitted-assertion controls and the existing direct/transitive assumption
rejection checks. The affected `InlineMutualEdits.pass` production target and
all four negative translation checks passed on both Coq 8.20.1 and Rocq 9.0.1.
All three `stack test` suites passed, including the 184 source-policy cases,
237 edits assertions, 805 Rocq-version assertions, and CI-catalog controls.

To avoid races with the concurrent agent's compiler outputs, final proof checks
ran in an isolated copy of this worktree. The copy reused only the generated
library sources and compiled Rocq 9.2 foundations; it contained no example
library, theory, or declaration-audit objects before building. From its
`examples/fingertree` directory, the command was:

```bash
opam exec --switch=cs2-rocq92 -- make -j2 \
  -o lib/Data/FingerTree.v \
  -o lib/Data/IntervalMap/FingerTree.v \
  -o lib/Data/PriorityQueue/FingerTree.v \
  kernel-check core-check interval-check priority-check
```

The command passed in 88.633 seconds. All three libraries and fifteen theories
compiled fresh, all 1,048 exact assumption sets matched the unchanged manifest,
and the requested recursive kernel checks passed. The public source-policy
invocation also passed in the isolated copy. Hashes confirmed that the relevant
source inputs did not change during those checks. This was not a clean
foundation rebuild, a translation rerun, hosted CI, or a formal pinned-range
re-review of these uncommitted changes.

The three theory-source hashes in `validation.sha256` now identify this tested
proof cleanup; no generated-library, foundation, or assumption-manifest hash
changed. Local logs, copied inputs, and `results.json` remain under
`/var/folders/3c/qfxwcbpj7q590cwh0_scnyl80000gn/T/opencode/fingertree-standards-check-d0aa2436/`.
