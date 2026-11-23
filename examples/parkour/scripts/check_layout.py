"""Check the source layout of Parkour's Rocq theories."""

import sys
from collections import Counter, defaultdict
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


def project_violations(directory: Path) -> list[str]:
    project = directory / "_CoqProject"
    lines = [s for line in project.read_text().splitlines() if (s := line.partition("#")[0].strip())]
    if "-Q . ParkourTheories" not in lines:
        return [f'{project}: missing "-Q . ParkourTheories"']
    entries = Counter(Path(s) for s in lines if s.endswith(".v"))
    sources = {p.relative_to(directory) for p in directory.rglob("*.v")}
    errors = []
    for path in sorted(sources | entries.keys()):
        if path not in sources or entries[path] != 1:
            errors.append(f"{project}: {path} must exist and appear exactly once")
        if any(not (name.isidentifier() and name[0].isupper()) for name in path.with_suffix("").parts):
            errors.append(f"{directory / path}: use capitalized Rocq module names")
    return errors


if __name__ == "__main__":
    source = Path(__file__).resolve().parents[1] / "theories"
    errors = violations(source) + project_violations(source)
    for message in errors:
        print(message, file=sys.stderr)
    sys.exit(bool(errors))
