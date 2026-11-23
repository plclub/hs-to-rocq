"""Check the source layout of Parkour's Rocq theories."""

import sys
from collections import defaultdict
from pathlib import Path


def source_violations(path: Path) -> list[str]:
    errors: list[str] = []
    count = 0
    with path.open(encoding="utf-8") as source:
        for count, line in enumerate(source, start=1):
            width = len(line.removesuffix("\n"))
            if width > 80:
                errors.append(f"{path}:{count}: {width} characters (maximum 80)")
    if count > 1000:
        errors.append(f"{path}: {count} lines (maximum 1000)")
    return errors


def violations(directory: Path) -> list[str]:
    errors: list[str] = []
    entries = sorted(directory.iterdir())
    names = [p.name for p in entries if p.name.endswith(".v") and p.is_file()]
    if len(names) > 10:
        errors.append(f"{directory}: {len(names)} .v files (maximum 10)")

    groups: dict[str, list[str]] = defaultdict(list)
    for name in names:
        if len(name) >= 4:
            groups[name[:4]].append(name)
    for prefix, siblings in groups.items():
        if len(siblings) > 1:
            errors.append(f"{directory}: shared prefix {prefix!r}: {', '.join(siblings)}")
    for name in names:
        errors.extend(source_violations(directory / name))
    for child in entries:
        if not child.is_symlink() and child.is_dir():
            errors.extend(violations(child))
    return errors


if __name__ == "__main__":
    errors = violations(Path("theories"))
    for message in errors:
        print(message, file=sys.stderr)
    sys.exit(bool(errors))
