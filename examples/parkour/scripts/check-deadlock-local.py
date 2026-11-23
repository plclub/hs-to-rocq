"""Compile the reviewed local semantics contracts and check each required export."""

import argparse
import shutil
from pathlib import Path

from audit_project import assumptions, compile_v, project_loads
from frozen_inputs import verify_local_inputs
from itree_pins import PARKOUR, switch_environment

SOURCES = ("theories/Semantics/LocalEffects.v", "tests/Semantics/LocalEffectContracts.v",
           "tests/Semantics/LocalEffectWitnesses.v", "tests/Semantics/ExactObservations.v",
           "tests/Semantics/ObservationEquivalences.v")
EXPORTS = {
    "ParkourTheories.Semantics.LocalEffects": ("local_step_typed_trace",),
    "ParkourTheories.Tests.Semantics.LocalEffectWitnesses": (
        "finite_return", "finite_action", "one_event", "untick", "visible_view",
        "no_reply", "blocked_store", "blocked_role", "step_true_reply", "no_invented_reply",
        "visible_not_return", "return_not_action", "forever_only_tau", "infinite_not_return",
        "infinite_not_action", "typed_trace", "view_exact",
    ),
    "ParkourTheories.Tests.Semantics.ObservationEquivalences": ("return_exact", "step_exact"),
}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="fresh evidence directory")
    parser.add_argument("--project-root", type=Path, help="reuse compiled canonical theories/ and tests/")
    args = parser.parse_args()
    root = args.project_root.resolve() if args.project_root else PARKOUR
    verify_local_inputs(root)

    env = switch_environment()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)

    if not args.project_root:
        root = output / "project"
        for relative in SOURCES:
            target = root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(PARKOUR / relative, target)
        for relative in SOURCES:
            compile_v(output, project_loads(root), root / relative, env=env)

    for module, names in EXPORTS.items():
        for name in names:
            export = f"{module}.{name}"
            print(f"Checking {export}", flush=True)
            assumptions(output, project_loads(root), "closed", export, env=env)
    print("PASS: frozen local contracts, five compiled modules and 20 closed exports")


if __name__ == "__main__":
    main()
