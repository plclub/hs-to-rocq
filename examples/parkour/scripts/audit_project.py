"""Canonical load paths and fresh evidence for Parkour's Rocq audits."""

import subprocess
import sys
from functools import cache
from pathlib import Path

from itree_pins import switch_environment

SCRIPTS = Path(__file__).resolve().parent
# Standalone semantic audits share one pin check across all their queries.
audit_environment = cache(switch_environment)


def project_loads(root: Path) -> list[str]:
    return ["-Q", str(root / "theories"), "ParkourTheories",
            "-Q", str(root / "tests"), "ParkourTheories.Tests"]


def run(directory: Path, *command: str, log: str, reject: bool = False,
        env: dict[str, str] | None = None) -> str:
    if env is None:
        env = audit_environment()
    result = subprocess.run(command, cwd=directory, check=False, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=120, env=env)
    (directory / log).write_text(result.stdout)
    if (result.returncode != 0) != reject:
        raise SystemExit(f"{directory / log}: unexpected status {result.returncode}\n{result.stdout}")
    return result.stdout


def compile_v(directory: Path, loads: list[str], source: Path, *, reject: bool = False,
              env: dict[str, str] | None = None) -> str:
    return run(directory, sys.executable, str(SCRIPTS / "parkour_rocq.py"),
               *loads, str(source), log=source.stem + ".log", reject=reject, env=env)


def assumptions(directory: Path, loads: list[str], policy: str, export: str, *,
                library: str | None = None, env: dict[str, str] | None = None) -> None:
    run(directory, sys.executable, str(SCRIPTS / "check-assumptions.py"), policy, "-", export,
        *(["--library", library] if library else []), *loads, log="assumptions-" + export + ".log", env=env)
