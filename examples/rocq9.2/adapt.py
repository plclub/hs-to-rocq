#!/usr/bin/env python3
"""Mechanically copy the selected authoritative base-thy sources for Rocq 9.

These substitutions mirror the manual-copy rule in rocq9.0/base-src/Makefile.
This is a copier for this fixed source corpus, not a general Rocq text parser.
"""

import argparse
from pathlib import Path
import re


def adapt(text):
    text = text.replace(
        "Coq.Program.Wf.WfExtensionality",
        "Stdlib.Program.WfExtensionality.WfExtensionality",
    )
    text = re.sub(
        r"^Require Import Coq\.Program\.Wf\.$",
        "Require Import Coq.Program.Wf. "
        "Require Import Stdlib.Program.WfExtensionality.",
        text,
        flags=re.MULTILINE,
    )
    text = text.replace("Coq.Init.", "Corelib.Init.")
    text = re.sub(r"^(\s*From\s+)Coq(\s)", r"\1Stdlib\2", text, flags=re.MULTILINE)
    return text.replace("Coq.", "Stdlib.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare without writing")
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    expected = adapt(args.source.read_text(encoding="utf-8"))
    if args.check:
        if args.output.read_text(encoding="utf-8") != expected:
            parser.exit(1, f"outdated adapted copy: {args.output}\n")
        return
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    try:
        temporary.write_text(expected, encoding="utf-8")
        temporary.replace(args.output)
    finally:
        temporary.unlink(missing_ok=True)


if __name__ == "__main__":
    main()
