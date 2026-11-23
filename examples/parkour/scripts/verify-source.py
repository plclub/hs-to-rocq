"""Verify the exact bytes GHC will read, regardless of Git index flags."""

import argparse
import subprocess
from collections.abc import Sequence
from hashlib import sha1
from pathlib import Path

PIN = "872bb12fe1698c8a791b8f64df7b8249f7463367"
UPSTREAM = Path(__file__).resolve().parents[1] / "upstream"
ROOTS = ("src", "examples/explicit-parallel/quorum-voting-choreo2")


def verify(checkout: Path, pin: str, roots: Sequence[str]) -> None:
    def git(*args: str) -> bytes:
        return subprocess.check_output(["git", "-C", checkout, *args])

    if git("rev-parse", "--show-toplevel").decode().strip() != str(checkout):
        raise SystemExit(f"missing submodule checkout: {checkout}")
    if git("rev-parse", "HEAD").decode().strip() != pin:
        raise SystemExit(f"{checkout.name} must be checked out at {pin}")

    entries = git("ls-tree", "-rz", pin, "--", *roots).split(b"\0")
    expected: set[Path] = set()
    for entry in filter(None, entries):
        meta, name = entry.decode().split("\t", 1)
        mode, kind, oid = meta.split()
        path = checkout / name
        if kind != "blob" or mode != "100644" or path.resolve() != path:
            raise SystemExit(f"unexpected source file type: {name}")
        data = path.read_bytes()
        if sha1(f"blob {len(data)}\0".encode() + data).hexdigest() != oid:
            raise SystemExit(f"{checkout.name} source differs from {pin}: {name}")
        expected.add(path)

    for root in roots:
        for path in (checkout / root).rglob("*"):
            if path.is_symlink() or (not path.is_dir() and path not in expected):
                raise SystemExit(f"unexpected {checkout.name} source input: {path}")
    print(f"verified {len(expected)} {checkout.name} files at {pin}")


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--dependencies", action="store_true")
args = parser.parse_args()
verify(UPSTREAM, PIN, ROOTS)
if args.dependencies:
    ghc = (UPSTREAM.parent / "../ghc/ghc").resolve()
    verify(ghc, "3f4d7d38b9661435bdde981451ac50c4335ed090",
           ["libraries/base/src/Control/Monad/IO/Class.hs",
            "libraries/base/src/Data/Functor/Contravariant.hs"])
    verify(ghc / "libraries/transformers", "ba3503905dec072acc6515323c884706efd4dbb4",
           ["Control", "Data"])
