import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from check_layout import violations


class TheoryLayoutTest(unittest.TestCase):
    def test_limits_are_local_and_only_count_sources(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            child = root / "nested"
            child.mkdir()
            for name in ["Abca.v", "Abcb.v", *(f"{n:04}.v" for n in range(8))]:
                (child / name).touch()
            (root / "Abca.v").touch()
            (child / "Abca.vo").touch()
            (child / ".Abca.aux").touch()
            self.assertEqual(violations(root), [])

            (child / "AbcaExtra.v").touch()
            self.assertEqual(violations(root), [
                f"{child}: 11 .v files (maximum 10)",
                f"{child}: shared prefix 'Abca': Abca.v, AbcaExtra.v",
            ])

    def test_physical_lines_and_unicode_width(self) -> None:
        with TemporaryDirectory() as tmp:
            child = Path(tmp) / "nested"
            child.mkdir()
            source = child / "Proof.v"
            # CRLF terminates one line; a Unicode line separator is content.
            limit = ("λ" * 79 + "\u2028\r\n" + "\n" * 999).encode("utf-8")
            source.write_bytes(limit)
            for suffix in [".vo", ".vos", ".vok", ".glob", ".v.bak"]:
                source.with_suffix(suffix).write_bytes(limit + b"x" * 81)
            self.assertEqual(violations(Path(tmp)), [])

            source.write_bytes(limit + ("λ" * 81).encode("utf-8"))
            other = child / "Alpha.v"
            other.write_text("a" * 81 + "\n" + "b" * 82 + "\n", encoding="utf-8")
            self.assertEqual(violations(Path(tmp)), [
                f"{other}:1: 81 characters (maximum 80)",
                f"{other}:2: 82 characters (maximum 80)",
                f"{source}:1001: 81 characters (maximum 80)",
                f"{source}: 1001 lines (maximum 1000)",
            ])
