---
description: Run local CI checks, diagnose and fix failures, then commit the verified fixes
allowed-tools: Bash, Read, Write, Edit, Glob, Grep, Agent, mcp__rocq-mcp__rocq_get_goals, mcp__rocq-mcp__rocq_run_tactic, mcp__rocq-mcp__rocq_start_proof, mcp__rocq-mcp__rocq_get_state_at_position, mcp__rocq-mcp__rocq_search
argument-hint: "[job-name] (hlint|build-haskell|test-coq-files|tests|test-rocq9|test-rocq9-translation|test-translation|all; aliases: build, test-coq)"
---

Run local CI checks, repair failures, and commit the verified fixes. **Read `.claude/commands/ci.md` first.** It is the authoritative catalog for job selection, prerequisites, per-job compiler environments, executable steps, and result criteria. Also read the root `CLAUDE.md` for translation and proof conventions. This document adds repair guidance, not a second command catalog.

The argument is: $ARGUMENTS

Apply `ci.md`, "Select jobs", to this argument. Empty or `all` means all seven workflow jobs, including HLint, the catalog/direct/harness/concurrency checks in `build-haskell`, and both Rocq jobs. Use the exact blocks under the corresponding `Job:` headings, with their prerequisite checks and environment wrappers.

## Repair loop

1. Complete `ci.md`, "Verify prerequisites and protect local work". Record pre-existing changes so repairs do not overwrite or commit user work.
2. Run each selected job. On failure, capture the command, exit status, toolchain, and diagnostic before editing. Missing tools or unsafe regeneration are blockers, not source-code defects.
3. Find the cause using the guidance below. Fix the source of the problem rather than weakening a check. Defer design changes to the user.
4. Rerun the smallest relevant check, then the full failed job from `ci.md`. Recheck downstream jobs affected by the fix. A translator or shared-rule change requires both compiler suites as well as `build-haskell`; a base change requires its dependent libraries and proofs.
5. After the last fix, verify the selected jobs against that source state. Record failures, causes, fixes, and verification in `.claude/ci-fix-log.md`, preserving existing entries. Finish with the summary and commit steps below.

## HLint and Haskell failures

For HLint, first confirm the version from `ci.md`; do not suppress a finding merely to pass. For compilation errors, inspect the reported source under `src/`, rebuild, then rerun the remaining `build-haskell` checks.

For catalog failures, compare `ci.md` with the current workflow and inspect `examples/tests/checks/CiCatalog.hs`. Keep the job headings and selection table synchronized, retain the shared-catalog delegation here, and preserve nonzero exits. Rerun the catalog check from `ci.md` after a repair.

For direct version/rewrite assertions, inspect `examples/tests/checks/RocqVersion.hs` and the relevant CLI or Gallina rewriting code. For harness failures, inspect `examples/tests/checks/harness.sh` and the production Makefile rule it exercises. For concurrency failures, inspect `examples/tests/checks/concurrent.sh` and its translation logs; fake-tool harness success cannot substitute for this real-translator check. Rerun the failing check using its exact `build-haskell` command before rerunning the whole job.

## Coq and Rocq failures

Verify the job's compiler environment before changing code. Use the diagnostic's file and line to distinguish these cases:

- **Generated files** (`base/`, `examples/rocq9.0/base/`, and generated example `lib/` files): fix the translator or the source edits, preamble, or midamble, following `CLAUDE.md`, "Translation Principles". Both base targets share inputs under `examples/base-src/`. Regenerate through the appropriate `base-src` or example `vfiles` target; do not patch generated output. Existing `.v` files may prevent regeneration, so follow the source Makefile's rules and protect local work before removing an output or cleaning.
- **Manual files**: edit the actual source. In particular, files under `examples/ghc/manual/` are symlinked into `lib/`; check the symlink before editing. Base manual sources live in `examples/base-src/manual/`.
- **Hand-written proofs** (`theories/` and `base-thy/`): fix the proof directly. Use available proof-state and search tools with the job's compiler version. Consult `CLAUDE.md`, "Coq 8.20 compatibility" and "Coq 8.20 proof tactics", for version-specific failures.
- **Rocq namespace or loading errors**: consult `CLAUDE.md`, "Rocq 9.0 support". Check AST/text rewriting, the generated preamble, and the manual-copy rule as appropriate. Keep the unit suite's deprecated-`Coq` warning check enabled.
- **Inconsistent assumptions**: confirm a toolchain mismatch or stale compiled artifacts, then follow `CLAUDE.md`, "Stale .vo recovery", to rebuild the dependency chain with one compiler version. Cleaning only the failing leaf can leave incompatible dependencies in place.

Before changing a proof that unfolds a library function, check whether the function is axiomatized. Follow `CLAUDE.md`, "Axiomatized lib functions" and "False theorems", rather than adding assumptions or `Admitted` just to obtain a successful build. For edits conflicts, consult "Edits system gotchas"; in particular, `skip` takes precedence over `redefine`.

## Unit-test failures

Apply `ci.md`, "Test result criteria": exit status 0 already accounts for expected cases, and every nonzero status needs investigation. Read category membership in `examples/tests/test-rules.mk` for both shared suites, or `examples/base-tests/Makefile` for base-tests. A `TODO_PASS` case can fail the suite because translation failed, output is missing, or compilation unexpectedly succeeded.

Read the fixture's `.hs` file and any test-specific `edits`, `preamble.v`, or `midamble.v`. Rocq fixtures live in `examples/tests/`, not in its Rocq output directory. Fix a translation problem in its inputs or translator, not in the generated `.v` file.

Rerun the category's result target in the same compiler environment as the failing job. For example:

```bash
# PASS case, Coq 8.20
opam exec --switch="${COQ820_SWITCH:?Select a Coq 8.20 switch}" -- make -C examples/tests Simple.pass
# TODO_PASS case, Coq 8.20
opam exec --switch="$COQ820_SWITCH" -- make -C examples/tests MutrecInst.fail
# The same expected compiler failure, Rocq 9.0
opam exec --switch="${ROCQ90_SWITCH:?Select a Rocq 9.0 switch}" -- make -C examples/rocq9.0/tests MutrecInst.fail
# Base-test expected compiler failure; requires the Coq base build
opam exec --switch="$COQ820_SWITCH" -- make -C examples/base-tests Arrow.fail
```

For a `TODO_TRANSLATE` case, use `TestName.fail_translate` in the relevant shared suite. That category is currently empty; use this target only for a fixture listed there. A `.vo` target can help expose a compiler diagnostic, but it does not test the expected outcome and is not a substitute for `.pass`, `.fail`, or `.fail_translate`.

Change category membership only after confirming an unexpected success is correct. For shared fixtures, verify the new outcome on both compiler versions; base-test categories belong to their own suite. Do not move a regression into an expected-failure category to hide it. Then rerun the full affected job from `ci.md`.

## Regeneration differences

Use `ci.md`, "Translation comparison criteria", and the exact `test-translation` or `test-rocq9-translation` steps. A difference does not by itself prove that the regenerated files are correct. Inspect the diff, confirm the translator, edits, and submodule revisions, and determine whether the change is intended.

Fix unintended changes at their source and regenerate. For an intended update, review the generated files and compile the affected output with the matching `test-coq-files` or `test-rocq9` steps. Recheck dependent proofs and tests before committing.

A comparison against `HEAD` still fails while an intended baseline update is uncommitted. Report that result explicitly. Commit the reviewed source and generated changes after the other checks pass, then rerun the translation job against the new `HEAD` before calling the no-diff check passed.

## Finish

Use the seven-job summary and statuses from `ci.md`, "Summary", adding the fixes and rerun evidence for each job. List remaining failures, blockers, and uncommitted baseline differences. Claim complete success only when every selected job and prerequisite passed after the final fix; claim `all` only when all seven passed.

After the selected checks pass, commit the fixes made by this command. Before committing, inspect `git status`, `git diff`, `git diff --cached`, and `git log --oneline -10`; stage only the intended fixes and preserve unrelated staged work. Follow the repository's commit-message and co-author conventions. Report the commit and any remaining changed files.
