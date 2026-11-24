#!/usr/bin/env python3
"""Compile one theory and enforce its complete transitive-assumption inventory.

The source's explicit Print Assumptions list names the exported interface.
Every named theorem/definition must occur in that inventory. A fresh audit pairs
each fully-qualified constant with a marker, so grouped source Check/Print
commands cannot misassociate reports. The checked-in manifest pins counts and
the exact exceptions to the default empty global-assumption set.
"""

import argparse
from collections import Counter
import json
import os
from pathlib import Path
import re
import subprocess
import sys


def require(ok, message):
    if not ok:
        raise ValueError(message)


def inventory(source):
    text = source.read_text(encoding="utf-8")
    names = re.findall(r"\bPrint Assumptions ([\w']+)\.", text)
    require(names and len(names) == len(set(names)),
            f"{source.name}: missing or duplicate export inventory")
    declarations = set(re.findall(
        r"^\s*(?:(?:#\[[^\]]+\]|Local|Global|Polymorphic)\s+)*"
        r"(?:Lemma|Theorem|Remark|Fact|Corollary|Proposition|Example|"
        r"Definition|Fixpoint|Record|Instance|Inductive|CoInductive|Class|Axiom|Parameter|Conjecture)\s+([\w']+)",
        text, re.MULTILINE))
    require(declarations <= set(names),
            f"{source.name}: unaudited declarations: {sorted(declarations - set(names))}")
    return names


def parse_assumption_block(block, name):
    """Read the exact assumption set from one theory or priority audit block."""
    closed = block.count("Closed under the global context")
    axioms = block.count("Axioms:")
    require((closed, axioms) in {(1, 0), (0, 1)},
            f"{name}: missing or ambiguous assumption report")
    assumptions = set()
    if axioms:
        assumptions = set(re.findall(r"^(\S+)\s*:", block.split("Axioms:", 1)[1], re.MULTILINE))
        require(bool(assumptions), f"{name}: empty axiom report")
    return assumptions


def reports(output, names):
    matches = list(re.finditer(r"^AUDIT: ([\w']+)$", output, re.MULTILINE))
    require([m.group(1) for m in matches] == names, "audit marker inventory differs")
    result = {}
    for i, match in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(output)
        block = output[match.end():end]
        result[match.group(1)] = parse_assumption_block(block, match.group(1))
    return result


def compile_file(rocq, paths, source, example, log):
    command = [rocq, "c", "-w", "+deprecated-dirpath-Coq", *paths, str(source)]
    result = subprocess.run(command, cwd=example, env=dict(os.environ, COQPATH="", ROCQPATH=""),
                            text=True, encoding="utf-8", capture_output=True, timeout=180)
    log.write_text(result.stdout + result.stderr, encoding="utf-8")
    if result.returncode:
        sys.stderr.write(result.stdout + result.stderr)
    require(result.returncode == 0, f"compiler failed for {source}; see {log}")
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module", help="unqualified theory module")
    parser.add_argument("--rocq", default="rocq")
    args = parser.parse_args()
    theory = Path(__file__).resolve().parent
    example = theory.parent
    manifest = json.loads((theory / "assumptions.json").read_text(encoding="utf-8"))
    require(set(manifest) == {p.stem for p in theory.glob("*.v")},
            "theory files and manifest module inventory differ")
    require(args.module in manifest, f"unlisted theory {args.module}")
    source = theory / f"{args.module}.v"
    names = inventory(source)
    spec = manifest[args.module]
    require(len(names) == spec["count"],
            f"{args.module}: expected {spec['count']} exports, found {len(names)}")
    expected = {name: set() for name in names}
    for assumption, exceptions in spec.get("exceptions", {}).items():
        require(set(exceptions) <= set(names), f"{args.module}: exception names missing from inventory")
        for name in exceptions:
            expected[name].add(assumption)
    out = example / "deps/proof-audits"
    out.mkdir(parents=True, exist_ok=True)
    foundation = example.parent / "rocq9.2"
    paths = ["-Q", str(foundation / "base"), "", "-Q", str(foundation / "base-thy"), "Proofs",
             "-Q", str(example / "lib"), "", "-Q", str(theory), "FingerTreeProofs",
             "-Q", str(out), "FingerTreeAudit"]
    compile_file(args.rocq, paths, source, example, out / f"{args.module}.compile.log")
    audit = out / f"Audit{args.module}.v"
    audit.write_text(f"Require FingerTreeProofs.{args.module}.\n" + "".join(
        f'Goal True. Proof. idtac "AUDIT: {name}". exact I. Qed.\n'
        f"Check @FingerTreeProofs.{args.module}.{name}.\n"
        f"Print Assumptions FingerTreeProofs.{args.module}.{name}.\n" for name in names),
        encoding="utf-8")
    output = compile_file(args.rocq, paths, audit, example, out / f"{args.module}.audit.log")
    actual = reports(output, names)
    wrong = {name: {"expected": sorted(expected[name]), "actual": sorted(found)}
             for name, found in actual.items() if found != expected[name]}
    require(not wrong, f"{args.module}: assumption mismatch: {json.dumps(wrong, indent=2)}")
    groups = Counter(tuple(sorted(found)) for found in actual.values())
    summary = "; ".join(f"{count} {','.join(key) or 'closed'}" for key, count in sorted(groups.items()))
    print(f"{args.module}: {len(names)}/{len(names)} exact assumption sets match ({summary}).")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.TimeoutExpired) as error:
        sys.exit(f"theory audit failed: {error}")
