#!/usr/bin/env python3
"""Check generated names at translation time, without compiling proofs.

CoreAudit.v and PriorityAudit.v remain authoritative. IntervalAudit.v makes the
historical 31-name interval inventory durable. Only generated declaration heads
are recognized here; handwritten support uses SourcePolicy's lexical scanner.
The exact transitive-assumption checkers remain separate and unchanged in role.
"""

import argparse
from collections import Counter
import importlib.util
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True

EXAMPLE = Path(__file__).resolve().parent
AUDITS = {
    "Data/FingerTree": ("module-edits/Data/FingerTree/CoreAudit.v", 131),
    "Data/IntervalMap/FingerTree": (
        "module-edits/Data/IntervalMap/FingerTree/IntervalAudit.v", 31),
    "Data/PriorityQueue/FingerTree": (
        "module-edits/Data/PriorityQueue/FingerTree/PriorityAudit.v", 74),
}
# These two existing audit entries are explicitly handwritten support.
SUPPORT = {"Data.PriorityQueue.FingerTree.DefaultPQueue",
           "Data.PriorityQueue.FingerTree.pqueue_size"}


def priority_checker():
    path = EXAMPLE / "module-edits/Data/PriorityQueue/FingerTree/check-priority-audit.py"
    spec = importlib.util.spec_from_file_location("priority_audit", path)
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    return checker


def inventory(module, checker):
    relative, count = AUDITS[module]
    path = EXAMPLE / relative
    text = path.read_text(encoding="utf-8")
    try:
        if module == "Data/PriorityQueue/FingerTree":
            names = checker.queue_inventory(text)
        else:
            prefix = module.replace("/", ".") + "."
            names = re.findall(r"^Print Assumptions " + re.escape(prefix) +
                               r"([\w']+)\.$", text, re.MULTILINE)
        checker.require(len(names) == count and len(set(names)) == count,
                        f"expected {count} distinct generated-name audit entries, found {len(names)}")
    except ValueError as error:
        raise ValueError(f"{path}: {error}") from error
    return names, text


def check_generated(module, checker):
    names, audit = inventory(module, checker)
    path = EXAMPLE / "lib" / (module + ".v")
    generated = path.read_text(encoding="utf-8")
    try:
        declarations = Counter(checker.generated_declarations(generated))
    except ValueError as error:
        raise ValueError(f"{path}: {error}") from error
    missing = sorted(set(names) - set(declarations))
    duplicates = sorted(name for name in names if declarations[name] > 1)
    checker.require(not missing and not duplicates,
                    f"{path}: required generated declarations missing {missing}; duplicate {duplicates}")
    if module == "Data/PriorityQueue/FingerTree":
        try:
            checker.check_inventory(generated, audit)
        except ValueError as error:
            raise ValueError(f"{path} / {EXAMPLE / AUDITS[module][0]}: {error}") from error
    print(f"{path}: {len(names)}/{len(names)} required generated declarations present.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--required", action="store_true",
                      help="print protected generated names from audits; no generated files needed")
    mode.add_argument("--module", choices=sorted(AUDITS),
                      help="check a freshly translated module before compilation")
    args = parser.parse_args()
    checker = priority_checker()
    if args.required:
        names = []
        for module in sorted(AUDITS):
            entries, _ = inventory(module, checker)
            names.extend(module.replace("/", ".") + "." + name for name in entries)
        for name in sorted(set(names) - SUPPORT):
            print(name)
    else:
        check_generated(args.module, checker)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError) as error:
        sys.exit(f"source inventory failed: {error}")
