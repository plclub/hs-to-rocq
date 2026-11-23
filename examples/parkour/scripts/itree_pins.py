"""Select and verify the private Rocq installation used by the local model."""

import os
import subprocess
import tempfile
from pathlib import Path

PARKOUR = Path(__file__).resolve().parents[1]
CACHE = PARKOUR / ".itree-cache"
PINS = (
    ("coq-ext-lib", "dd32f1c56f41d699ed2ffd4193a876c87fc44926", "theories", "ExtLib", 117),
    ("paco", "d0561bf7f0a96cac486ba3bd8ca0b72ce01fb9cf", "src", "Paco", 41),
    ("InteractionTrees", "a2bc2c38ad998dccadb932559c922139dd957c4f", "theories", "ITree", 68),
)


def prefix_path() -> Path:
    return Path(os.environ.get("ITREE_PREFIX") or CACHE / "pins").resolve()


def ensure_prefix(prefix: Path) -> None:
    if prefix.is_dir():
        return
    if prefix != CACHE / "pins" or os.environ.get("ITREE_PREFIX"):
        raise SystemExit(f"missing prepared ITree installation: {prefix}")
    CACHE.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(dir=CACHE) as tmp:
        stage = Path(tmp, "pins")
        subprocess.run([PARKOUR / "scripts/install-itree-pins", stage], check=True)
        # Publish only a complete build. A concurrent successful build wins.
        if not prefix.exists():
            try:
                stage.rename(prefix)
            except OSError:
                if not prefix.is_dir():
                    raise


def pinned_environment(prefix: Path) -> dict[str, str]:
    env = {k: v for k, v in os.environ.items() if k not in {
        "COQLIB", "ROCQLIB", "COQCORELIB", "ROCQRUNTIMELIB", "COQPATH", "ROCQPATH"}}
    config = subprocess.check_output(["rocq", "c", "-config"], env=env, text=True)
    runtime, = [line.removeprefix("COQCORELIB=") for line in config.splitlines()
                if line.startswith("COQCORELIB=")]
    if not Path(runtime).is_absolute() or not Path(runtime).is_dir():
        raise SystemExit(f"invalid Rocq runtime: {runtime!r}")
    return {**env, "ROCQLIB": str(prefix / "lib"), "ROCQRUNTIMELIB": runtime}


def verify_prefix(prefix: Path) -> None:
    version = subprocess.check_output(["rocq", "c", "--print-version"], text=True)
    if version.split()[0] != "9.0.1":
        raise SystemExit(f"need Rocq 9.0.1; got {version.strip()}")
    for repo, pin, relative, logical, count in PINS:
        source = prefix / "src" / repo
        git = ["git", "-C", str(source)]
        if subprocess.check_output([*git, "rev-parse", "HEAD"], text=True).strip() != pin:
            raise SystemExit(f"{repo}: expected revision {pin}")
        subprocess.run([*git, "diff", "--exit-code", pin, "--"], check=True)
        installed = prefix / "lib/user-contrib" / logical
        built = source / relative
        objects = {obj.relative_to(installed) for obj in installed.rglob("*.vo")}
        if len(objects) != count or objects != {obj.relative_to(built) for obj in built.rglob("*.vo")}:
            raise SystemExit(f"{logical}: installed/pinned inventories must match ({count} objects)")
        tracked = subprocess.check_output([*git, "ls-tree", "-rz", "--name-only", pin], text=True)
        inputs = set(tracked.split("\0"))
        for path in sorted(objects):
            if str(relative / path.with_suffix(".v")) not in inputs:
                raise SystemExit(f"{logical}/{path}: no source at {pin}")
            if (installed / path).read_bytes() != (built / path).read_bytes():
                raise SystemExit(f"{logical}/{path}: installed object differs from pinned build")
