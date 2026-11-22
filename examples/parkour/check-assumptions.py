"""Compile a fresh single-export query; check either closure or the client ceiling."""

import re
import sys
import tempfile
from pathlib import Path

from parkour_rocq import compile_file


def main(policy: str, directory: str, export: str, *loads: str) -> None:
    ident = r"[A-Za-z_][A-Za-z_0-9']*"
    qualid = rf"{ident}(?:\.{ident})*"
    if not re.fullmatch(rf"{ident}\.{qualid}", export):
        sys.exit("expected a qualified export")
    if policy not in {"closed", "client"} or len(loads) % 3 or any(flag != "-Q" for flag in loads[::3]):
        sys.exit("invalid assumption policy or load path")
    with tempfile.TemporaryDirectory() as tmp:
        def query(command: str) -> str:
            source = Path(tmp, "ParkourAudit.v")
            source.write_text(f"Require {export.rsplit('.', 1)[0]}.\n{command}\n")
            proc = compile_file([*loads, "-Q", directory, "", str(source)])
            print(proc.stdout, end="")
            if proc.returncode:
                sys.exit(proc.returncode)
            return proc.stdout.strip()

        report = query(f"Print Assumptions {export}.")
        if report == "Closed under the global context":
            return
        failure = f"Assumption check failed for {export}"
        if policy == "closed":
            sys.exit(failure)
        lines = report.splitlines()
        if not lines or lines.pop(0) != "Axioms:":
            sys.exit(failure)
        # Rocq prints each axiom flush left; long types wrap with indentation.
        names: list[str] = []
        for line in lines:
            if line.startswith(" ") and names:
                continue
            match = re.fullmatch(rf"({qualid})(?: : .+)?", line)
            if not match or match[1] in names:
                sys.exit(failure)
            names.append(match[1])
        if not names:
            sys.exit(failure)
        allowed = set(Path(__file__).with_name("tests").joinpath("slice1/client-allowlist").read_text().splitlines())
        for name in names:
            location = query(f"Locate {name}.")
            if not location.startswith("Constant ") or location.removeprefix("Constant ") not in allowed:
                sys.exit(f"{failure}: {location}")


if __name__ == "__main__":
    main(*sys.argv[1:])
