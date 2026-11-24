"""Reject explicitly local Notation and Infix declarations, including reservations."""

from __future__ import annotations

import argparse
import re
import sys
from collections.abc import Iterator
from pathlib import Path


def sources(root: Path, directory: Path) -> Iterator[Path]:
    for path in directory.iterdir():
        if path.is_symlink():
            continue
        if path.is_dir():
            if directory == root and path.name in {"build", "lib", "upstream"}:
                continue
            if path.name in {".git", ".itree-cache", ".cache", ".mypy_cache",
                             ".pytest_cache", ".ruff_cache", "__pycache__"}:
                continue
            yield from sources(root, path)
        elif path.suffix == ".v" and path.is_file():
            yield path.relative_to(root)


# Strings are single tokens, even inside comments; Rocq escapes " by doubling it.
# Keep .field together so a qualified import cannot start a new command.
TOKEN = re.compile(r'''\(\*|\*\)|"(?:[^"]|"")*(?:"|\Z)|\.?[\w']+|\s+|.''')


def commands(text: str) -> Iterator[list[tuple[str, int]]]:
    command: list[tuple[str, int]] = []
    depth = 0
    line = 1
    for match in TOKEN.finditer(text):
        token = match[0]
        if token == "(*":
            depth += 1
        elif depth:
            if token == "*)":
                depth -= 1
        elif token == ".":
            yield command
            command = []
        elif not token.isspace():
            command.append((token, line))
        line += token.count("\n")
    if command:
        yield command


NATURAL = re.compile(r"(?:[0-9][0-9_]*|0[xX][0-9a-fA-F][0-9a-fA-F_]*)")


def selector_focus(first: str, tokens: Iterator[tuple[str, int]]) -> bool:
    """Try a selector followed by ': {'. On a mismatch the caller stops."""
    def take() -> str:
        return next(tokens, ("", 0))[0]

    if first in {"!", "all"}:
        return take() == ":" and take() == "{"
    while True:
        if first == "[":
            # A goal name (possibly qualified on 9.2) is an operand, not a command.
            name = []
            while (part := take()) not in {"", "]"}:
                name.append(part)
            if part != "]" or not all(s.replace("'", "_").isidentifier()
                                      for s in "".join(name).split(".")):
                return False
            sep = take()
        elif NATURAL.fullmatch(first):
            sep = take()
            if sep == "-":
                if not NATURAL.fullmatch(take()):
                    return False
                sep = take()
        else:
            return False
        if sep != ",":
            return sep == ":" and take() == "{"
        first = take()


def local_declaration(command: list[tuple[str, int]]) -> tuple[int, str] | None:
    """Inspect only the command prefix, never operands of Import, Check, etc."""
    tokens = iter(command)
    local_line = None
    for word, line in tokens:
        # Profile takes an optional string; retain the first token of its command.
        while word == "Profile":
            word, line = next(tokens, ("", 0))
            if word.startswith('"'):
                word, line = next(tokens, ("", 0))
        if word == "#" and next(tokens, ("", 0))[0] == "[":
            # Attribute names occur at the start and after top-level commas.
            at_name = True
            depth = 0
            for attr, _ in tokens:
                if attr == "]":
                    break
                if at_name and attr == "local":
                    local_line = line
                depth += (attr == "(") - (attr == ")")
                at_name = attr == "," and depth == 0
        elif word == "Local":
            local_line = line
        elif word in {"Time", "Instructions", "Fail", "Succeed"}:
            continue
        elif word in {"Timeout", "Redirect"}:
            next(tokens, None)
        elif word in {"{", "}", "-", "+", "*"} or selector_focus(word, tokens):
            # A bullet or focus brace is itself a complete command without a dot.
            local_line = None
        else:
            reserved = word == "Reserved"
            if reserved:
                word = next(tokens, ("", 0))[0]
            if local_line is not None and word in {"Notation", "Infix"}:
                return local_line, f"Reserved {word}" if reserved else word
            break
    return None


def check(root: Path) -> int:
    status = 0
    for path in sorted(sources(root, root), key=Path.as_posix):
        for command in commands((root / path).read_text(encoding="utf-8-sig")):
            violation = local_declaration(command)
            if violation:
                line, kind = violation
                print(f"{path.as_posix()}:{line}: Local {kind} is forbidden", file=sys.stderr)
                status = 1
    return status


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path, nargs="?", default=Path(__file__).resolve().parents[1],
                        help="Parkour source directory (default: the parent of scripts/)")
    root = parser.parse_args().root
    if root.is_symlink() or not root.is_dir():
        parser.error("root must be a non-symlink directory")
    sys.exit(check(root))
