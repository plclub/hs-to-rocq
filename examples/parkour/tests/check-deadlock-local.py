"""Compile the reviewed local semantics contracts and check each required export."""

import argparse
import hashlib
import shutil
import subprocess
import sys
from pathlib import Path

PARKOUR = Path(__file__).resolve().parents[1]
ROOT = PARKOUR.parents[1]
sys.path.insert(0, str(PARKOUR))
from itree_pins import ensure_prefix, pinned_environment, prefix_path, verify_prefix

MANIFESTS = {
    "deadlock-local-v1.sha256": "26cf0649672d228a135bd086088ac17727678e17585afe3281b81dbe303e6826",
    "deadlock-local-exact.sha256": "dca7c40a980377b7726e2bcc1c95ef8ef19d1d8e46d61a65795d772799d1ac60",
}
EXPORTS = {
    "DeadlockLocal": ("local_step_typed_trace",),
    "DeadlockLocalCases": (
        "finite_return", "finite_action", "one_event", "untick", "visible_view",
        "no_reply", "blocked_store", "blocked_role", "step_true_reply", "no_invented_reply",
        "visible_not_return", "return_not_action", "forever_only_tau", "infinite_not_return",
        "infinite_not_action", "typed_trace", "view_exact",
    ),
    "DeadlockLocalExactCases": ("return_exact", "step_exact"),
}


def check_digest(path: Path, expected: str) -> None:
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise SystemExit(f"digest mismatch: {path}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--itree-prefix", type=Path, help="prepared private installation")
    parser.add_argument("--output", type=Path, required=True, help="fresh evidence directory")
    args = parser.parse_args()
    for name, anchor in MANIFESTS.items():
        manifest = PARKOUR / "tests" / name
        check_digest(manifest, anchor)
        for line in manifest.read_text().splitlines():
            expected, filename = line.split("  ", 1)
            check_digest(ROOT / filename, expected)

    prefix = args.itree_prefix.resolve() if args.itree_prefix else prefix_path()
    ensure_prefix(prefix)
    verify_prefix(prefix)
    env = pinned_environment(prefix)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)

    def run(log: str, *command: str | Path) -> None:
        proc = subprocess.run(command, cwd=output, env=env, check=False, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=120)
        (output / log).write_text(proc.stdout)
        print(proc.stdout, end="")
        if proc.returncode:
            raise SystemExit(f"{log}: compiler or assumption check failed ({proc.returncode})")

    for relative in ("theories/DeadlockLocal.v", "tests/DeadlockLocalExpect.v",
                     "tests/DeadlockLocalCases.v", "tests/DeadlockLocalExactExpect.v",
                     "tests/DeadlockLocalExactCases.v"):
        target = output / Path(relative).name
        shutil.copyfile(PARKOUR / relative, target)
        run(target.stem + ".log", sys.executable, PARKOUR / "parkour_rocq.py",
            "-Q", output, "", target)

    for module, names in EXPORTS.items():
        for name in names:
            export = f"{module}.{name}"
            print(f"Checking {export}", flush=True)
            run(f"assumptions-{export}.log", sys.executable, PARKOUR / "check-assumptions.py",
                "closed", output, export)
    print("PASS: frozen local contracts, five compiled modules and 20 closed exports")


if __name__ == "__main__":
    main()
