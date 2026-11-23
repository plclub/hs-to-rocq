"""Use the Parkour dependencies installed in the active Rocq opam switch."""

import os
import re
import subprocess
from pathlib import Path

PARKOUR = Path(__file__).resolve().parents[1]


def rocq_environment() -> dict[str, str]:
    return {k: v for k, v in os.environ.items() if k not in {
        "COQLIB", "ROCQLIB", "COQCORELIB", "ROCQRUNTIMELIB", "COQPATH", "ROCQPATH"}}


def rocq_version() -> str:
    version = subprocess.check_output(["rocq", "c", "--print-version"], env=rocq_environment(),
                                      text=True).split()[0]
    if version != "9.0.1" and not re.fullmatch(r"9\.2(?:\.\d+)?", version):
        raise SystemExit(f"need Rocq 9.0.1 or 9.2.x; got {version}")
    return version


def switch_environment() -> dict[str, str]:
    env = rocq_environment()
    # `opam exec --switch=...` sets the prefix but need not set OPAMSWITCH
    # for nested opam commands. Local switches live in <directory>/_opam.
    if prefix := env.get("OPAM_SWITCH_PREFIX"):
        path = Path(prefix)
        env["OPAMSWITCH"] = str(path.parent) if path.name == "_opam" else path.name

    def opam(*args: str) -> str:
        return subprocess.check_output(["opam", *args, "--color=never"], env=env, text=True).strip()

    lib = Path(opam("var", "lib")).resolve()
    where = subprocess.check_output(["rocq", "c", "-where"], env=env, text=True).strip()
    if not Path(where).resolve().is_relative_to(lib):
        raise SystemExit(f"Rocq uses {where}, outside the active opam switch's {lib}")

    manifest = PARKOUR / "parkour-deps.opam"
    field = opam("show", "--just-file", "--normalise", "--field=pin-depends", str(manifest))
    pins = dict(re.findall(r'\["([^"]+)" "([^"]+)"\]', field))
    if not pins:
        raise SystemExit(f"no pin-depends in {manifest}")
    installed = {tuple(line.split(maxsplit=1)) for line in opam(
        "list", "--installed", "--pinned", "--short", "--columns=package,pin", *pins).splitlines()}
    # `opam pin --no-action` can change the URL without rebuilding an installed version.
    pending = set(opam("reinstall", "--list-pending").splitlines())
    missing = [pkg for pkg, url in pins.items() if (pkg, url) not in installed or pkg in pending]
    if missing:
        raise SystemExit(f"missing or stale Parkour pins: {', '.join(missing)}\n"
                         f"Install them in this switch with: opam install --deps-only {manifest}")
    return env


if __name__ == "__main__":
    switch_environment()
