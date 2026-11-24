#!/usr/bin/env python3
"""Compile the audits and regressions and enforce their assumption inventories.

Requires the already compiled Rocq 9.2 foundations and queue; does not generate
or change library sources. All compiler output paths stay beside the checked
sources. Each compiler invocation has a timeout. Kernel checking remains a
separate build step.
"""

import argparse
import os
from pathlib import Path
import re
from runpy import run_path
import subprocess
import sys


DEFERRED = "DeferredFix.deferredFix"
GUARDED = "DeferredFix.deferredFix_eq_on"
REGRESSIONS = {
    "minViewWithKey_empty",
    "minView_empty",
    "empty_payload_views",
    "minViewWithKey_singleton",
    "minViewWithKey_priority_payload_ties_reappend",
}

# All other queue entries must be closed, including Foldable__PQueue_null.
RECURSIVE_QUEUE = {
    "Foldable__PQueue",
    "Foldable__PQueue_foldMap",
    "Foldable__PQueue_fold",
    "Foldable__PQueue_foldr",
    "Foldable__PQueue_foldl'",
    "Foldable__PQueue_foldMap'",
    "Foldable__PQueue_foldl",
    "Foldable__PQueue_foldr'",
    "Foldable__PQueue_length",
    "Foldable__PQueue_product",
    "Foldable__PQueue_sum",
    "Foldable__PQueue_toList",
    "assocs",
    "Eq___PQueue",
    "Eq___PQueue_op_zeze__",
    "Eq___PQueue_op_zsze__",
    "Ord__PQueue",
    "Ord__PQueue_compare",
    "Ord__PQueue_op_zl__",
    "Ord__PQueue_op_zlze__",
    "Ord__PQueue_op_zg__",
    "Ord__PQueue_op_zgze__",
    "Ord__PQueue_max",
    "Ord__PQueue_min",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def generated_declarations(generated):
    """Mask Rocq comments/strings, then match only translator-emitted named heads."""
    masked = []
    depth = 0
    quoted = False
    index = 0
    while index < len(generated):
        char = generated[index]
        pair = generated[index:index + 2]
        # Rocq also treats quoted text inside comments as strings: comment
        # delimiters there are inert, and doubled quotes do not end a string.
        if quoted and pair == '""':
            masked.append("  ")
            index += 2
        elif char == '"':
            quoted = not quoted
            masked.append(" ")
            index += 1
        elif not quoted and pair == "(*":
            depth += 1
            masked.append("  ")
            index += 2
        elif not quoted and depth and pair == "*)":
            depth -= 1
            masked.append("  ")
            index += 2
        else:
            masked.append(char if not (depth or quoted) or char == "\n" else " ")
            index += 1
    require(not quoted, "unterminated Rocq string")
    require(not depth, "unterminated Rocq comment")
    return re.findall(
        r"^(?:#\[(?:local|global)\]\s*)?(?:Program\s+)?"
        r"(?:Inductive|Definition|Instance|Fixpoint|CoFixpoint)\s+([\w']+)",
        "".join(masked),
        re.MULTILINE,
    )


def queue_inventory(audit):
    """Read the existing authoritative queue Check/Print inventory without compiling."""
    checked = re.findall(r"^Check @Queue\.([\w']+)\.$", audit, re.MULTILINE)
    printed = re.findall(
        r"^Print Assumptions Queue\.([\w']+)\.$", audit, re.MULTILINE
    )
    require(len(checked) == 74 and len(set(checked)) == 74,
            "expected exactly 74 distinct queue Check entries")
    require(checked == printed, "Check and Print Assumptions inventories differ")
    require(RECURSIVE_QUEUE <= set(checked), "expected recursive entry is missing")
    return checked


def check_inventory(generated, audit):
    declarations = generated_declarations(generated)
    checked = queue_inventory(audit)
    require(len(declarations) == 74, "queue declaration inventory changed from 74")
    require(len(set(declarations)) == 74, "duplicate generated declaration")
    require(set(checked) == set(declarations),
            "audit does not cover the entire generated queue declaration inventory; "
            f"missing {sorted(set(checked) - set(declarations))}; "
            f"unexpected {sorted(set(declarations) - set(checked))}")
    return checked


def check_report(output, expected):
    parse_assumption_block = run_path(str(
        Path(__file__).resolve().parents[4] / "theories/check-assumptions.py"
    ))["parse_assumption_block"]
    # Check prints the constant at the start of a line; all type and assumption
    # continuations are indented. The explicit module alias makes this stable
    # even though both the core and queue library files are named FingerTree.
    starts = list(re.finditer(
        r"^@?(" + "|".join(re.escape(name) for name in sorted(expected)) + r")(?=\s|$)",
        output, re.MULTILINE,
    ))
    names = [match.group(1) for match in starts]
    require(len(names) == len(set(names)), "duplicate assumption report")
    require(set(names) == set(expected), "missing or unexpected assumption report")
    for index, match in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else len(output)
        block = output[match.end():end]
        actual = parse_assumption_block(block, match.group(1))
        require(actual == expected[match.group(1)],
                f"{match.group(1)}: expected {sorted(expected[match.group(1)])}, "
                f"got {sorted(actual)}")


def compile_audit(rocq, load_paths, source, cwd, verbose):
    command = [rocq, "c", "-w", "+deprecated-dirpath-Coq", *load_paths, str(source)]
    env = dict(os.environ, COQPATH="", ROCQPATH="")
    result = subprocess.run(command, cwd=cwd, env=env, text=True, encoding="utf-8",
                            capture_output=True, timeout=60)
    if result.stderr:
        sys.stderr.write(result.stderr)
    if verbose or result.returncode:
        sys.stdout.write(result.stdout)
    require(result.returncode == 0, f"compiler failed for {source}")
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rocq", default="rocq", help="Rocq executable (not a shell command)")
    parser.add_argument("--verbose", action="store_true", help="print complete compiler reports")
    args = parser.parse_args()
    audit_dir = Path(__file__).resolve().parent
    example = audit_dir.parents[3]
    foundation = example.parent / "rocq9.2"
    audit = audit_dir / "PriorityAudit.v"
    generated = example / "lib/Data/PriorityQueue/FingerTree.v"
    try:
        checked = check_inventory(
            generated.read_text(encoding="utf-8"), audit.read_text(encoding="utf-8"),
        )
    except ValueError as error:
        raise ValueError(f"{generated} / {audit}: {error}") from error
    paths = ["-Q", str(foundation / "base"), "",
             "-Q", str(foundation / "base-thy"), "Proofs",
             "-Q", str(example / "lib"), "",
             "-Q", str(example / "theories"), "FingerTreeProofs",
             "-Q", str(audit_dir), "PriorityChecks"]
    expected = {f"Queue.{name}": {DEFERRED} if name in RECURSIVE_QUEUE else set()
                for name in checked}
    expected["OldList.unfoldr"] = {DEFERRED}
    check_report(compile_audit(args.rocq, paths, audit, example, args.verbose), expected)
    print("PriorityAudit: 74/74 queue declarations checked; "
          "50 closed, 24 depend only on deferredFix.")
    print("PriorityAudit: OldList.unfoldr depends only on deferredFix (75 reports total).")

    regression = example / "theories/PriorityRegression.v"
    text = regression.read_text(encoding="utf-8")
    lemmas = re.findall(r"^Lemma ([\w']+)", text, re.MULTILINE)
    checks = re.findall(r"^Check @?([\w']+)\.$", text, re.MULTILINE)
    reports = re.findall(r"^Print Assumptions ([\w']+)\.$", text, re.MULTILINE)
    require(len(lemmas) == len(REGRESSIONS) and set(lemmas) == REGRESSIONS,
            "regression theorem inventory changed")
    require(lemmas == checks == reports,
            "every regression theorem needs an ordered Check/Print Assumptions pair")
    check_report(compile_audit(args.rocq, paths, regression, example, args.verbose),
                 {name: set() for name in REGRESSIONS})
    print("PriorityRegression: 5/5 public behavioral equations closed; no assumptions.")

    paths = ["-Q", str(foundation / "base"), "",
             "-Q", str(foundation / "checks"), "Rocq92Checks"]
    expected = {
        "OldList.unfoldr": {DEFERRED},
        "unfoldr_rank_eq": {DEFERRED, GUARDED},
        "countdown_decreases": set(),
        "unfoldr_countdown_three": {DEFERRED, GUARDED},
    }
    check_report(compile_audit(args.rocq, paths, foundation / "checks/Unfoldr.v",
                               example, args.verbose), expected)
    print("Unfoldr: exact signature checked; 4/4 assumption sets match "
          "(one closed, one deferredFix-only, two guarded-unfolding proofs).")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.TimeoutExpired) as error:
        sys.exit(f"audit failed: {error}")
