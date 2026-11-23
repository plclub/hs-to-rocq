"""Prepare Parkour's compiler-specific base from the shared Rocq 9 sources."""

import os
import re
import shutil
import subprocess
from pathlib import Path

# The translator can read these interfaces even when checking edits without Rocq.
SOURCE_BASE = Path(__file__).resolve().parents[2] / "rocq9.0/base"


def prepare_base(version: str, destination: Path) -> None:
    """Populate a fresh destination using the active Rocq compiler."""
    if version == "9.0.1":
        destination.symlink_to(SOURCE_BASE, target_is_directory=True)
        return
    if not re.fullmatch(r"9\.2(?:\.\d+)?", version):
        raise ValueError(f"unsupported Rocq version: {version}")

    destination.mkdir()
    project = SOURCE_BASE / "_CoqProject"
    shutil.copyfile(project, destination / project.name)
    # Use the same module inventory as make; never copy compiled artifacts.
    for name in project.read_text().split():
        if name.endswith(".v"):
            target = destination / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(SOURCE_BASE / name, target)
    for interface in SOURCE_BASE.rglob("*.h2ci"):
        target = destination / interface.relative_to(SOURCE_BASE)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(interface, target)

    env = {k: v for k, v in os.environ.items() if k not in {
        "COQLIB", "ROCQLIB", "COQCORELIB", "ROCQRUNTIMELIB", "COQPATH", "ROCQPATH"}}
    subprocess.run(["rocq", "makefile", "-f", "_CoqProject", "-o", "Makefile.coq"],
                   cwd=destination, env=env, check=True)
    subprocess.run(["make", "-j2", "-f", "Makefile.coq"],
                   cwd=destination, env=env, check=True)
