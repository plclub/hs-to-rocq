"""Extract the external class used by ReaderT from GHC's pinned base source."""

import sys
from hashlib import sha256
from pathlib import Path


def extract(output: Path) -> None:
    source = Path(__file__).resolve().parent / (
        "../ghc/ghc/libraries/base/src/Data/Functor/Contravariant.hs"
    )
    data = source.read_bytes()
    if sha256(data).hexdigest() != "60ab0ef01aba6c18d3f2f8566f79352a6bb08cbc018d8f5e6988214ec6257d9c":
        raise SystemExit(f"unexpected GHC Data.Functor.Contravariant source: {source}")
    # The complete class in this revision occupies lines 99--106.
    declaration = b"".join(data.splitlines(keepends=True)[98:106])
    if not declaration.rstrip().endswith(b"(>$) = contramap . const"):
        raise SystemExit("incomplete external class declaration")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(b"module Parkour.Contravariant where\n\n" + declaration)


if __name__ == "__main__":
    extract(Path(sys.argv[1]))
