# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**hs-to-rocq** converts Haskell source code to Coq (Gallina) using the GHC API. It is part of the DeepSpec/CoreSpec project. The tool parses Haskell via GHC, applies user-specified "edits" to guide the translation, and pretty-prints valid Coq output.

- **Current targets**: GHC 9.10.3; Coq 8.20 (default) or Rocq 9.0 via `--target-version` (branch `ghc910-coq820`)
- **Languages**: Haskell (the tool, ~14K LOC in `src/`), Coq (generated output and proofs)

## Build Commands

```bash
stack build                                    # Build hs-to-rocq executable
stack exec hs-to-rocq -- -e edits -o output/ Input.hs  # Run on a file
make                                           # Build base + base-thy + containers
make -C examples/base-src vfiles               # Re-generate base/ from Haskell sources
make -C examples/tests                         # Unit tests (.hs → .v → coqc)
make -C examples/base-tests                    # Tests requiring base/
make -C examples/rocq9.0                       # Rocq 9.0 base + shared unit tests
make -C examples/containers                    # containers lib + theories (regenerates + builds)
make -C examples/transformers                   # transformers lib
make -C examples/ghc clean && make -C examples/ghc  # Regenerate+compile GHC lib + theories
cd examples && ./boot.sh                       # Full bootstrap (all examples)
# Individual Coq dirs: cd <dir> && coq_makefile -f _CoqProject -o Makefile && make -j
```

Use relative path instead of absolute path when `cd` to a directory.

### CI commands
- `/ci` — run CI checks locally, report pass/fail
- `/ci-fix` — run CI checks, diagnose and fix failures, commit fixes

## Architecture

### Translation Pipeline

1. **Parse & typecheck** Haskell via GHC API (`src/lib/HsToRocq/ProcessFiles.hs`)
2. **Load edits** from `.edits` files (`src/lib/HsToRocq/Edits/Parser.y`, `Types.hs`)
3. **Convert** GHC AST → Coq Gallina AST (`src/lib/HsToRocq/ConvertHaskell/`)
4. **Pretty-print** Gallina to `.v` files (`src/lib/HsToRocq/Rocq/Pretty.hs`)
5. **Output** `.h2ci` interface files for cross-module translation

### Key Source Directories

- `src/lib/HsToRocq/Rocq/Gallina.hs` — Coq AST data types (Term, Sentence, Definition, Inductive, etc.)
- `src/lib/HsToRocq/Rocq/Pretty.hs` — Pretty-printer rendering Gallina AST as Coq source
- `src/lib/HsToRocq/ConvertHaskell/` — Core conversion engine:
  - `Expr.hs` — Expression conversion (largest file, ~1700 lines)
  - `Module.hs` — Whole-module conversion
  - `Monad.hs` — Conversion monad carrying edits/renamings/state
  - `Declarations/` — Data types, classes, instances, type synonyms
  - `HsType.hs`, `Pattern.hs`, `Variables.hs` — Type/pattern/variable conversion
- `src/lib/HsToRocq/Edits/` — Edit DSL parser and types
- `src/lib/HsToRocq/CLI.hs` — Command-line interface and file processing orchestration
- `src/include/ghc-compat.h` — CPP macros for GHC version compatibility (8.4–9.10)
- `src/lib/HsToRocq/Util/GHC/` — GHC API compatibility wrappers

### The Edits System

Edits files are a plain-text DSL that guides translation of constructs that don't directly map to Coq. Key directives: `skip`, `rename`, `rewrite`, `redefine`, `add`, `order`, `termination`, `coinductive`, `axiomatize`, `manual notation`. Full documentation in `doc/source/edits.rst`.

Edits are organized per-module:
```
module-edits/<Module>/<Path>/edits       # per-module edits
module-edits/<Module>/<Path>/preamble.v  # Coq code prepended to output
module-edits/<Module>/<Path>/midamble.v  # Coq code inserted mid-file
```

### Output Directories

- `base/` — **Generated** Coq base library. **Do not edit directly** — regenerate from `examples/base-src/` instead.
- `base-thy/` — Hand-written proofs and lawful typeclass instances for `base/`
- `examples/` — Translation examples; each has `Makefile`, `edits`, `module-edits/`, `lib/` (output), `theories/` (proofs)

### Build Plumbing

- `common.mk` — Included by all example Makefiles; defines `HS_TO_ROCQ` variable (resolves to `stack exec hs-to-rocq --`)
- Each Coq directory uses `_CoqProject` + `coq_makefile` to generate its Makefile
- `.h2ci` files store interface information for cross-module translation
- `make vfiles` (base-src) skips existing `.v` files — `rm` the target file before running to force regeneration
- `examples/base-src/modules.mk` shares the base module lists; `base-rules.mk` shares dependency-directory ordering and `_CoqProject` completion rules for both targets.

### Stale .vo recovery
If you see "inconsistent assumptions over library Coq.Init.Prelude", rebuild the full chain: `base` → `base-thy` → `examples/containers` → `examples/ghc`. For coq_makefile dirs: `find <dir> \( -name '*.vo' -o -name '*.vok' -o -name '*.vos' -o -name '*.glob' -o -name '.*.aux' \) -delete && coq_makefile -f _CoqProject -o Makefile && make -j`.

### Axiomatized lib functions
When lib/*.v functions are `Axiom`, theories/*.v proofs that unfold them must be `Admitted`. Check with `grep "^Axiom" lib/Module.v` before attempting computation-based proofs. See "GHC example" section for the full list of axiomatized functions.

### False theorems
If a theorem is discovered to be false, construct a formal Coq counterexample (a proved `Lemma` showing `~ (statement)`) and `Abort` the original theorem (not `Admitted`, to prevent unsound use). Add a comment before `Abort` referencing the counterexample. Example: `mapKeys_Desc_false` in IntMapProofs.v disproves `mapKeys_Desc`.

### Coq trie proof techniques (IntMap/IntSet)
Key lemmas: `bin_Desc0` (combine Desc0), `Desc_outside` (f=None outside range), `nomatch_zero`/`nomatch_zero_smaller` (dispatch), `halfRange_inRange_testbit`, `rPrefix_halfRange_otherhalf` (left<right ordering), `sem_Desc` (sem=f). Generalize range+spec before induction for stronger IH. IntSetProofs intersection/difference/union are templates for IntMap proofs.

### Typeclass loops + unbounded N
`Require SetProofs` + IntSetProofs triggers WFSet nesting loop. Fix: `Set Typeclasses Iterative Deepening. Set Typeclasses Depth 3.` before import, `Unset` after (place after proofs needing normal depth). Coq's `N` is unbounded (Haskell `Word` is 64-bit) — bit-width properties may need explicit bounds (`k < 2^63`). Example: `thm_MaskPow2_bounded`.

## Translation Principles

**Prefer hs-to-rocq + edits over manual definitions.** Follow this priority order:

1. **Auto-generate with hs-to-rocq** — try the default translation first.
2. **Use edits** (`skip`, `rename`, `rewrite`, `order`, `termination`, `equations`, etc.) — guide the translation without replacing it.
3. **Fix hs-to-rocq itself** — if the tool can't handle a case but could be made to, fix the tool rather than working around it.
4. **`redefine`** — only when the translated output is fundamentally wrong and hs-to-rocq cannot reasonably be fixed to handle it.
5. **`midamble.v`** — only for definitions that must appear mid-file (e.g., mutual recursion helpers, termination measures) and cannot be expressed via edits.
6. **Manual files** — last resort, only when the Haskell source has no meaningful Coq translation (e.g., axiomatized types, FFI, GHC internals with no Coq equivalent).

**When unsure whether hs-to-rocq can handle a case, ask the user** rather than defaulting to `redefine` or manual definitions. Many cases that seem to require manual intervention can be solved with the right combination of edits or a targeted fix to hs-to-rocq.

## Test Structure

- `examples/tests/` and `examples/rocq9.0/tests/` share `examples/tests/test-rules.mk` and the same fixtures, compiled with `coqc` and `rocq c -w +deprecated-dirpath-Coq` respectively. Each suite has 53 `PASS` cases and 3 expected compiler failures (`TODO_PASS`). The Rocq warning flag rejects unrewritten root `Coq.*` paths while permitting user-qualified and relative `Coq` components.
- `examples/base-tests/` requires the `base/` Coq library to be built first; it has 18 `PASS` cases and 3 expected compiler failures.
- Test-specific files go in `examples/tests/<TestName>/`: `edits`, `preamble.v`, and `midamble.v`.
- `examples/tests/checks/` contains 805 direct Haskell assertions for CLI version parsing and rewrite definitions and 187 harness checks with fake tools. The harness invokes both production test wrappers, including nested helper dependency/compilation rules and clean rebuilds. It checks concurrent tool logging, dependency-directory creation, manual-file copying, fresh Coq builds with manual modules, and serial and parallel base-generation retries through the `base` and direct/top-level `vfiles` entry points. Forced and outdated regeneration must reject stale output, discard failed output even with unchanged timestamps, and preserve successful sources during retries. It supports macOS Bash 3.2 and Bash 5. See the README test commands. These fast checks do not replace compiler tests.
- `examples/tests/checks/concurrent.sh` runs real translators concurrently with a shared Haskell dependency on both targets. It requires `.v` and `.h2ci` outputs and checks that default translation creates no shared `.ghc-tmp` artifacts. GHC defaults to `-fno-code` because translation only needs typechecking; native compilation otherwise races on shared `.o.tmp` files during fresh parallel base generation. The script also checks that an explicit `--ghc -fobject-code` overrides this default.

Test categories distinguish translation from compilation:

- `PASS`: the translator must exit zero and produce a `.v` file; compilation must succeed.
- `TODO_PASS`: the translator must exit zero and produce a `.v` file; compilation must fail.
- `TODO_TRANSLATE`: failed translation or missing output is expected. Any output from a successful translation fails this category, even if compilation fails.

Both the shared rules and base-tests discard partial `.v` output when the translator exits nonzero. Unit-test generation uses `FORCE`, including the multi-source `Renamed.v` rule, so repeated runs test the current translator rather than stale output. Shared helper `.vo` targets also use `FORCE` so immediate reruns cannot reuse a stale compiled helper when timestamps match.

The shared compiler fixtures cover:

- `SoleCtorGuard`: pattern guards over sole and nested constructors, refutable constructors, guarded case arms, and empty lists.
- `RocqNestedCorelib`: nested shim references in the AST.
- `RocqMovedAst`: the moved theorem in a generated `Definition`, raw `Qed`/`Defined` proofs with whitespace/comment-separated path components, and an edits-supplied `Program` obligation tactic. The `Defined` proof also checks string-literal preservation. A local `Obligation Tactic := idtac` keeps the obligation pending, while `set type` makes `fixEqWitness` a dependent pair requiring `fixEqType`. The tactic supplies the moved theorem, and `Check (proj2_sig fixEqWitness) : fixEqType.` makes an incomplete obligation fail compilation.
- `RocqMovedText`: preamble/midamble text with `From` syntax and extra whitespace, root `Coq.*` references (including after superscript/subscript notation, punctuation ending in dots, pattern apostrophes, and adjacent numerals), and user names that must remain unchanged: identifiers containing combining U+1DC0, non-breaking U+00A0, subscripts, apostrophes, or digits, `MyCoq.add`, and paths under `UserCoq` and `Other.Coq` that resemble shim or moved-module paths.
- `RocqQuotedText`: raw preamble, midamble, and `Qed`/`Defined` proof string literals compared against unchanged AST literals. Moved theorem references after each literal require rewriting to resume after the closing quote.
- `RocqWfInnerImport`: an unqualified inner-module import.
- `RocqFromImports`: a bare `From Coq Require` prefix and relative `From Other Require` operands that resemble root `Coq.*` paths. Its dependency generates and compiles `Other.Coq.Init.Decimal`; the fixture checks a constant from that library. The shared rules compile the fixture with `-Q . ""` on both targets.

## CI (`.github/workflows/hs-to-rocq.yml`)

Seven jobs: `hlint`; `build-haskell` (haskell:9.10.3-bookworm Docker, builds the executable once and is the cache producer); `test-coq-files` (mathcomp/mathcomp:2.5.0-coq-8.20 Docker, builds base+containers+ghc lib and theories); `tests` (haskell:9.10.3-bookworm Docker + opam for Coq 8.20, runs unit + base-tests + base-thy + small examples); `test-translation` (haskell:9.10.3-bookworm Docker, verifies base/containers/ghc/graph regeneration matches); `test-rocq9` (haskell:9.10.3-bookworm Docker + opam, builds `examples/rocq9.0/base` and runs `examples/rocq9.0/tests` on Rocq 9.0); `test-rocq9-translation` (haskell:9.10.3-bookworm Docker, Rocq 9.0 round-trip no-diff). Sets `LANG=C.utf8` globally for Unicode support. All hs-to-rocq-using jobs `needs: build-haskell` and share its Stack cache.

Use the explicit Bookworm image tag: the unqualified `haskell:9.10.3` tag uses Debian 11 Bullseye, whose LTS ended in August 2026. Its security-package URLs returned 404 during compiler setup. Bookworm keeps GHC 9.10.3 while using a supported Debian package source.

After setup, `build-haskell` runs `stack --allow-different-user exec -- runghc -package=hs-to-rocq examples/tests/checks/RocqVersion.hs`, `bash examples/tests/checks/harness.sh`, and `bash examples/tests/checks/concurrent.sh`. The `test-rocq9` job runs `make -C examples/rocq9.0 clean`, then `make -j2 -C examples/rocq9.0 base`, before its unit-test step. These checks use the existing seven jobs.

**Shared setup**: `build-haskell`, `tests`, `test-rocq9`, `test-rocq9-translation`, and `test-translation` all run `actions/checkout@v7` then `.github/actions/setup-hs-to-rocq` (composite), which does fix Docker permissions → init requested submodules (`submodules` / `shallow-submodules` inputs) → install extra apt packages (`extra-apt-packages`) → restore Stack cache via `actions/cache@v6` → `stack build`. A local action is not available until after checkout, so the checkout step must precede the composite action. Per-job variation is expressed via those inputs, not duplicated steps. `hlint` (native runner) and `test-coq-files` (docker-coq-action) keep their own checkout.

**Container job gotcha**: Container jobs use `--allow-different-user` for stack commands (ownership mismatch between host-mounted workspace and container user). For docker-coq-action, use `before_script` with `sudo chown -R coq:coq .` (not `custom_script`, which bypasses permission setup). The `test-coq-files` job pre-pulls `mathcomp/mathcomp:2.5.0-coq-8.20` with retries before docker-coq-action so transient Docker Hub pull failures do not fail before project code runs. `common.mk` already includes `--allow-different-user` in the `HS_TO_ROCQ` variable. The opam-based jobs also pass `--disable-sandboxing` to `opam init` (bwrap sandboxing doesn't work in nested Docker without extra caps) and pre-install `libgmp-dev m4 pkg-config` so depext checks for zarith/conf-gmp don't fail.

**test-translation job**: Inits `examples/ghc/ghc`, `examples/containers/containers` (full) and `examples/graph/graph` (`--depth 1`, via the composite action inputs), not `submodules: recursive` — GHC has ~20 nested submodules that are not needed.

**Do not mask test failures**: the shared unit-test and base-test Makefiles return zero only when outcomes match their categories (`.pass` for `PASS`, `.fail` for `TODO_PASS`, and `.fail_translate` for the shared suite's `TODO_TRANSLATE`). Keep nonzero exits visible in CI. Do not add `|| test $? -eq 2` or similar guards; they hide unexpected outcomes.

**CI cache key**: The `stack-bookworm-ghc9.10.3-` prefix separates native build artifacts from the old Bullseye cache. Change the distribution prefix when changing the container base. Keep `src/**` in `hashFiles` so source changes invalidate the cache.

**Unicode encoding**: `src/exe/Main.hs` calls `setLocaleEncoding utf8` at startup so all file I/O uses UTF-8 regardless of system locale. Edits/midamble/preamble files may contain Unicode (e.g., `∘` in Coq identifiers). To test locally without UTF-8 locale: `LANG=C make -C examples/base-src clean && make vfiles`. Avoid Unicode in comments (smart quotes etc.) — use ASCII equivalents.

## GHC Version Compatibility

Cross-version compatibility is managed via CPP macros in `src/include/ghc-compat.h`. Key macros: `NOEXT`/`NOEXTP` (for "Trees That Grow" extension fields), `GHC_910()`, `GHC_900()` (version-gated code blocks). When updating for a new GHC version, these macros and the wrappers in `src/lib/HsToRocq/Util/GHC/` are the primary adaptation points.

## Rocq 9.0 support (`--target-version`)

`hs-to-rocq` emits code for either Coq 8.20 (default, unchanged) or Rocq 9.0, selected by `--target-version {8.20|9.0}`. The `RocqVersion` type lives in `src/lib/HsToRocq/Rocq/Gallina.hs`; it is threaded through `GlobalEnv`/`ModuleEnv`/`LocalEnv` via a `HasRocqVersion` constraint on `GlobalMonad`.

Rocq 9 split the old `Coq.*` namespace: `Stdlib.X.Y` is often a one-line `Require Export` shim whose real content is `Corelib.X.Y`, and fully-qualified names do not follow `Require Export` aliases (e.g. `Stdlib.Init.Datatypes.app` doesn't resolve; `Corelib.Init.Datatypes.app` does). Two rewriters, both in `src/lib/HsToRocq/Rocq/Gallina/Util.hs`, bridge this:

- **`coqToStdlib`**: SYB rewrite over the Gallina AST, applied to generated declarations. It visits `Qualid`s and the three `ModuleSentence` forms, and applies `rocq9RewriteText` to tactic text in `ProofQed`, `ProofDefined`, `ProofAdmitted`, and the optional obligation tactics in `ProgramSentence`. These type-specific visits leave unrelated AST strings and comments unchanged. For `Require` with a `From` prefix, only the prefix rewrites; operands remain relative to it. Use `rewriteASTFor version` rather than calling it directly. Shim matching uses whole module-component prefixes, so `Coq.Init.Decimal.Little.succ` becomes `Corelib.Init.Decimal.Little.succ` without matching longer identifiers such as `Coq.Init.DecimalX`.
- **`rocq9RewriteText`**: scans complete paths in user preamble/midamble files and raw proof/obligation tactics. It uses the shared `rocq9RenameModuleReference` and rewrites only root `Coq.*` paths. Comments and quoted string literals, including nested comments and doubled quote escapes, are copied verbatim so raw tactics and AST literal values remain consistent. `From <prefix> Require` rewrites a bare `Coq` prefix to `Stdlib`, or a dotted root `Coq.*` prefix to its target path, and preserves relative operands until the command ends. Bare `Coq` names elsewhere remain unchanged. Whole identifiers and qualified paths stay together, preserving names such as `My'Coq.add`, `My1Coq.add`, and `Other.Coq.Init.Decimal`. Root references after `@`, an unspaced `(`, symbolic notation (including punctuation ending in dots), a leading pattern apostrophe, or an adjacent numeral still rewrite. Numeric scanning follows Rocq's decimal/hexadecimal token boundaries, including fractions and exponents; `0x1Coq` has no root `Coq` token because its `C` belongs to the hexadecimal numeral. Use `rewriteTextFor version` for preamble/midamble files.

The text scanner consumes numeric and symbolic tokens separately from whole paths. Its identifier predicates follow Rocq 9.0.1's `clib/unicode.ml`: letters, underscore, and non-breaking space U+00A0 can start identifiers; numbers, non-spacing combining marks, and apostrophes can also continue them. Superscript decimal digits are symbols. Dots join identifiers only when followed by another valid identifier start, so notation such as `+.Coq.Init.Logic.I` leaves a root reference to rewrite. Whitespace/comments before a field dot remain in the path's original separator, so `Coq.Program.Wf .WfExtensionality` receives the complete structural move. A single leading dot followed by an identifier remains a field token. The shared fixtures use U+1DC0, which is accepted by both Coq 8.20 and Rocq 9.0; Rocq 9.0 accepts non-spacing marks more generally. Consuming combining marks within a path also prevents `Coq.Init.Decimal` followed by a combining-mark suffix from incorrectly matching the `Decimal` shim.

Shim and moved-module matching respect whole module-component boundaries: `Coq.Program.Wf` and `Coq.Program.Wf.X` match the shim, but `Coq.Program.WfExtensionality` does not. `corelibShimModules` is the explicit allow-list derived from the Rocq 9.2 distribution; CI exercises rewritten output on 9.0. Text rewriting still operates on plain text, not parsed Coq.

The 8.20 default path is byte-identical to the pre-Rocq-9 tool: `rewriteASTFor Rocq_8_20` and `rewriteTextFor Rocq_8_20` are both `id`, and `staticPreamble` (in `Rocq/Preamble.hs`) is parameterised by version. The cross-version surface is the unit-test tree, mirrored at `examples/rocq9.0/` (`base/`, `base-src/`, `tests/` reusing the `examples/tests/` `.hs` fixtures with `rocq c` instead of `coqc`). Large examples (`containers`, `ghc`, `transformers`) stay on Coq 8.20.

**WfExtensionality structural move** (not a namespace rename): Rocq 9 pulled `WfExtensionality` out of `Program/Wf.v` into a sibling file. Both the AST and text rewriters change references from `Coq.Program.Wf.WfExtensionality` to `Stdlib.Program.WfExtensionality.WfExtensionality`. In the AST, `Require` targets name library files, while `Import`/`Export`, module assignments, and qualified references can name inner modules.

Loading is separate from renaming. The Rocq 9 `staticPreamble` emits `Require Import Stdlib.Program.WfExtensionality.` once per generated module, before user preambles and declarations. `rocq9RewriteText` no longer inserts imports based on an exact `Require` line. Manual files copied by `examples/rocq9.0/base-src/Makefile` bypass that header, so keep their `sed` import rule. `rocq9RenameModuleReference` supplies the shared reference substitutions; the static header and manual-copy rule handle loading separately.

**Clean and rebuild**: `make -C examples/rocq9.0 clean` deletes the base convenience copy and test outputs. A subsequent plain `make -C examples/rocq9.0` regenerates the missing base automatically. The missing `base/_CoqProject` rule runs the full `base-src vfiles` submake before `coq_makefile` or compilation, including under parallel make. Shared `base-rules.mk` invalidates `_CoqProject` before checking sources and publishes it atomically after every source succeeds, so direct `vfiles` failures also force a retry. Translating targets create `deps` first and remove their old `.v` before translation, so zero-exit/no-output translation cannot reuse a stale target. Failed recipes explicitly delete partial output even when its timestamp matches the previous target; successful sources remain available for retries. `.DELETE_ON_ERROR` provides additional cleanup. Existing convenience copies do not force regeneration. Regeneration requires the `examples/ghc/ghc` submodule and a built translator. Do not run the Rocq unit suite concurrently with `clean`.

## GHC 9.10 Migration (ghc910-coq820 branch)

GHC 9.10 moved most `base` implementations to `ghc-internal`. Source files are now at `ghc-internal/src/GHC/Internal/...` instead of `base/*.hs`. The Makefile in `examples/base-src/` uses a symlink `ghc-internal -> ../ghc/ghc/libraries/ghc-internal` and `rename module` edits to map `GHC.Internal.*` names back to canonical output names.

### Modules that can't be regenerated
These must use old versions from git master with manual fixes:
- `Data/Functor/Classes` — hs-to-rocq generates valid output, but Coq can't compile it: GHC 9.10 added quantified superclass constraints to Eq2/Ord2 (`forall a. Eq a => Eq1 (f a)`) that Coq can't resolve in the CPS encoding. The manual version has the same compilation failure. Nothing downstream imports Eq2/Ord2 so this is tolerated.

- **`(->)` TyCon in GHC 9.10**: `FunTyCon` reports 0 `tyConBinders`. `Type.hs` detects `GHC.Prim.arrow` with null binders → empty args to `convertTyConApp`. `lookupInstance` uses `termHead` for flexible matching.
- `_CoqProject` ordering matters: Identity/Traversable must be listed early (EARLY_GHC_INTERNAL_MODULES in Makefile) to avoid Coq typeclass resolution stack overflow

### Deriving pipeline (GHC 9.10)
GHC's `load LoadAllTargets` processes standalone `deriving instance` declarations during typechecking — before `addDerivedInstances` runs. If any fail (e.g. types from skipped modules), `load` returns `Failed`. The fallback in `ProcessFiles.hs` strips all standalone deriving decls from the **parsed** AST, then typechecks, then uses `addDerivedInstances` to re-derive the ones we want.

### Common edit patterns for GHC 9.10
- **`skip` vs `skip method`**: Never use `skip Mod.func` for class methods — use `skip method Mod.Class func` only. Using both causes "skipping a binding" errors.
- **`SigPat` in GHC 9.10**: Now supported — `SigPat` strips the type annotation (like `ParPat`/`BangPat`). `foldl'`/`foldr'`/`foldMap'` are real class methods. Expression type annotations with free variables are stripped (would produce `forall` that changes the type); those without free variables are kept (needed for `coerce` disambiguation).
- **`envFor` cross-type method references**: `envFor` renames ALL class methods to local instance names (with pre-rename module name variants for GHC.Internal.* matching), but newtype-wrapper or parameterized instances reference methods for *component* types. `redefine` affected methods: Compose fold/null/length/product/sum, OccEnv `<$`. `in ... rename value` overrides must include BOTH post-rename and pre-rename module names (e.g., `GHC.Base.liftA2` AND `GHC.Internal.Base.liftA2`); see WriterT edits.
- **mconcat `foldl' (<>) mempty`**: GHC 9.10 generates this for non-newtype Monoids (Max, Min). Fix: `redefine` to use `foldr mappend mempty` + `order mempty mconcat`. Newtype mconcat auto-generates via expandCoerce (wraps result, maps accessor over list args)
- **`GHC.Prim.coerce` expansion** (Instances.hs `expandCoerce`): Auto-expands coerce-based instance methods into explicit newtype wrapping/unwrapping. Handles: simple newtypes, partially-applied type constructors (recursive `typeHead`), `list (Newtype)` args (via `map accessor`), and function-type args like `a -> Newtype b` (via wrapper lambdas). Requires constructor info from `storeRedefinedConstructors` (TyCl.hs) for `redefine Inductive` types. Remaining coerce cases needing `redefine`: function-composition coerce (Traversable mapAccumL/mapAccumR/fmapDefault with StateL/StateR/Identity)
- **Coq hangs on instance compilation**: Usually means expandCoerce produced type-incorrect code (e.g., missing unwrap on function-type arg). Check generated `.v` for bare `GHC.Prim.coerce` or mismatched newtype/base types in method bodies.
- **`rightSection`**: GHC 9.10 desugars `(op x)` to `rightSection op x`. Defined in `base/GHC/Prim.v`. Operators with invalid Coq chars (like `$`) are rendered as z-encoded names (e.g. `op_zd__`) instead of notation form. Proofs involving `rightSection` need `unfold GHC.Prim.rightSection` before `lia`
- **`<*` operator ambiguity**: `GHC.Base.<*` parses as `GHC.Base.<` followed by `*`. Excluded from `qualidHasValidRocqOp` in `Gallina/Util.hs` — renders as `op_zlzt__` instead. Definition added via `add` directive in base-src edits.

### Edits system gotchas
- **`skip` overrides `redefine`**: In `definitionTask` (Monad.hs), `skip` is checked first. Remove `skip` directives before adding `redefine` for the same function.
- **`redefine` type annotations**: The edits parser doesn't support `*` in product types or `%type` scope annotations. Omit the type signature (use `:=` directly) to work around parse errors.
- **`order` with `redefine`**: When `redefine` introduces definition dependencies, add explicit `order` directives to ensure correct output ordering.
- **`redefine Inductive` sorts**: The code generator's `Set` heuristic (for prop-lowerable types) doesn't apply to `redefine Inductive` — must specify `: Set` explicitly for empty/single-no-arg-constructor types.
- **Parser extensions (ghc910-coq820)**: `if/then/else`, `#n` hash-number literals, and `let fix ... in` are supported in `redefine` bodies (added in Lexer.hs/Parser.y).
- **`equations` edit directive**: Emits Coq Equations plugin syntax instead of Definition/Fixpoint. Requires `coq-equations`. Conflicts with skip/redefine/axiomatize. Test in `examples/tests/Equations/`.
- **Let binding ordering**: `convertLocalBinds` (Expr.hs) uses `foldrM` over GHC's `NValBinds` groups, so the first group becomes the outermost `Let`. Independent bindings may appear in arbitrary order.
- **Adding Gallina AST constructors**: New `Sentence` variants need cases in `Pretty.hs`, `FreeVars.hs`, `Subst.hs`. Export `(..)` for record types used across modules.

### GHC example (examples/ghc/)
Translated from GHC 9.10.3. The library and full theory build pass on Coq 8.20.1. `make clean && make` regenerates lib/ (removes dir, rebuilds via hs-to-rocq + lndir for ~48 manual files). Edit `manual/*.v` directly (not `lib/*.v` symlinks).

Key GHC 9.10 type changes: `Alt` uses `Mk_Alt` constructor (not tuple); `Mk_Id` has 7 fields (`varMult : Mult` added 4th); `realUnique` is `Unique` not `N`; `Var` has single constructor `Mk_Id` (no `TyVar`); `cse_bind` has 5 args; `lookupIdSubst` dropped `String` doc param; State monad is bare function type; `mkVarApps` uses `foldl'`. GoDom: use `alt_rhs` projection (strict positivity).

Proof bridge lemmas: `GHC.Base.foldl'` is CPS-via-`fold_right` (not `fold_left`). Use `Foldable.foldl'_is_foldl` (base-thy) to convert `foldl'` to `foldl` in proofs, or `hs_coq_foldl'_base` (base-thy/GHC/Base.v) to convert to `fold_left` directly.

**WF contract recovery**: When changing IntMap/VarSet proofs or their callers, follow the "WF contract recovery" section in `examples/ghc/README.md`. Supply explicit WF and validity evidence using `VarSetInvariant`; raw membership equality does not establish either invariant. `IntMapRecursion` derives operation equations from guarded deferred recursion, and `IntMapUnionProofs` proves semantic preservation. `RecoveryChecks.v` fixes the final Exitify contract and checks that the rejected blanket declarations remain absent.

**Exitify/CSE recovery**: When changing their translation, proofs, or assumptions, read [Exitify and CSE proof recovery](examples/ghc/README.md#exitify-and-cse-proof-recovery). It covers guarded unfolding, edit-only Identity support, the restored locality axiom, remaining theorem assumptions, and validation scope.

Un-axiomatized: `Subst` (concrete inductive in Core.v), `substExpr`/`substBind` (mutual Fixpoint in CoreSubst midamble), `exitifyRec` (concrete with `deferredFix2`), `Id.idJoinPointHood`. CoreSubst hybrid auto-generation: 4 auto-generated, 9 redefined (simplified for `TvSubstEnv=CvSubstEnv=unit`), core subst in midamble (ordering: midamble before generated code).
Key axioms: `tyCoFVsOfType_is_emptyFV`/`tyCoFVsOfCo_is_emptyFV` (types axiomatized), `tyCoVarsOfTypeDSet_empty`. Still axiomatized: `floatExpr`/`floatBind`/`floatRhs`, `fiExpr`/`fiBinds`/`fiRhs`. Locate admission markers with `rg -n Admitted examples/ghc/theories/*.v` (comments can match); use `Print Assumptions` to check a theorem's dependencies.

Build details: `manual/AxiomatizedTypes.v` instances must be `#[global]`. `axiomatize module OccurAnal` needs preamble.v + midamble.v. Midamble placed AFTER types+auto-Defaults, BEFORE values — use `skip` + midamble for custom Defaults. Makefile sed post-processing: BasicTypes/Literal (`#[global]`), UniqFM (phantom kinds), Core.v (mutual type fixes via `fix-files/`).
Core.v post-processing uses `fix-files/` for multi-line insertions (portable across GNU/BSD sed). GHC and transformers regeneration on macOS requires GNU sed: `brew install gnu-sed && PATH="/opt/homebrew/opt/gnu-sed/libexec/gnubin:$PATH" make -C examples/ghc vfiles`.

### Paper claims audit
Before reporting publication claims, read `paper-claims-audit.md` (JFP 2021, arxiv:1910.11724, ICFP 2018). It separates the historical source-search audit from dated recovery checks; a `Qed` marker alone does not establish independence from admissions or axioms.

### Containers submodule
Containers v0.7. `make clean` removes `lib/` and `hs-spec/`; `make` regenerates and builds everything. IntSet/Set/Map have native v0.7 split/fromAscList/fromDescList definitions. `hs-spec/IntSetProperties.v` auto-generated from v0.7 test sources. Full type class laws verified in TypeclassProofs.v. Check proof status: `grep -c Admitted examples/containers/theories/*.v`. IntMapProofs has formal counterexamples (Abort) for false theorems (mapKeys_Desc, isSubmapOfBy_Bin, Desc0_Desc, empty_no_elts). thm_MaskPow2 false for unbounded N; bounded version proved with `k < 2^63`.

### Transformers example (examples/transformers/)
Regenerated from GHC 9.10 transformers source via symlink `transformers -> ../ghc/ghc/libraries/transformers`. Makefile strips MonadTrans quantified superclass constraint via sed post-processing. Uses `skip class` for `Contravariant` and `Foldable1` (not in base). WriterT `<*>` has envFor cross-type override (`in ... rename value` for both GHC.Base and GHC.Internal.Base liftA2).

### Coq 8.20 compatibility
- `#[global]` required: `Program Instance` and `Program Definition` need `#[global]` prefix. Locality goes before `Program` (i.e., `#[global] Program Definition`).
- Type and constructor cannot share the same name (e.g., `StateT`)
- `omega` → `lia`; `le_lt_n_Sm` removed (use `lia` instead)
- `intuition`/`f_equal`/`auto` solve more goals — proof bullet structures may break. `auto` no longer resolves `E.eq` goals — use explicit `apply E.eq_refl`.
- Section `Variable` hypotheses generate side conditions in `rewrite`. `clear -H1 H2` clears section variables — add them to keep list (e.g., `clear -H1 H2 HEqLaws HOrdLaws`).
- `Program Fixpoint ... := _.` obligations: see "Coq 8.20 proof tactics" section below.
- Typeclass resolution may not unfold definition chains (`Key→N→Word`) — add explicit instances
- Names from `Coq.Lists.List` (like `filter`, `partition`) may shadow project names — qualify explicitly
- `eval unfold f` in sections: use `let x := constr:(@f args) in let rhs := eval unfold f in x`
- `Foldable__list_foldMap` is now `mconcat ∘ map` (not direct `foldr`) — different unfolding chains needed

### Coq 8.20 proof tactics
- **`Program Fixpoint` obligations**: Coq 8.20 pre-introduces ALL obligation variables. Use `revert dependent P` to recover CPS structure, or work with auto-named `H`/`H0`/`H1`.
- **`order e` + `==`**: `order e` can't handle `Eq_` class `==`. Convert `(x == y) = true` to `(y <= x) = true` via `Eq_le_r` first.
- **Z multiplication match form**: `2 * 2^x` reduces to `match 2^x with 0=>0|Z.pos p=>Z.pos p~0|Z.neg p=>Z.neg p~0 end`. Use `change (match ...) with (2 * 2^x)%Z in *` to normalize before `lia`/`rewrite`.
- **`applyDesc` consumes `Hsem`**: `try replace (sem s) in *` clears `Hsem`. If you need `Hsem` later, use manual CPS: `eapply lem. exact HB. intros s HB _ Hsem. apply showDesc'. split; [assumption|].`
- **`SomeIf` opacity**: `unfold SomeIf` before `destruct`/`simpl` to enable `if`-reduction.
- **`destruct_match` in Map proofs**: Picks up wrong matches (e.g. `Z.pow` in hypotheses). Use explicit `destruct p as [kx vx]; destruct (not_ordered ...) eqn:Hord` instead.
- **`++` associativity**: Coq `++` is right-associative. `A ++ nil ++ B` is `A ++ (nil ++ B)` — use `app_nil_l`, not `app_nil_r`.

## Workflow

- Every time before you commit, you should also check if other modules have been broken due to this change. For example, check `examples/test` even if you have only been working on `examples/containers`.
- After significant functional changes (e.g., replacing `redefine` with native implementations), update README files, CLAUDE.md, and any plan documents to reflect the new state before committing.
- Commit to git at each milestone with a `Co-Authored-By:` trailer crediting the coding agent that produced the work. Use the active agent and model name (e.g. `Co-Authored-By: Open Code (GLM-5.2) <noreply@opencode.ai>`), substituting whichever agent/model you are currently running.
