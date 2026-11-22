"""Parkour compiler policy, shared by translation checks and controls."""

import os
import subprocess
import sys
from collections.abc import Sequence


def compile_file(args: Sequence[str]) -> subprocess.CompletedProcess[str]:
    env = {k: v for k, v in os.environ.items() if k not in {"COQPATH", "ROCQPATH"}}
    result = subprocess.run(["rocq", "c", "-q", "-w", "+all", *args],
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            text=True, env=env, check=False)
    # Some diagnostics are warnings even when the compiler returns success.
    if not result.returncode and any(line.startswith("Warning:") for line in result.stdout.splitlines()):
        result.returncode = 1
    return result


if __name__ == "__main__":
    result = compile_file(sys.argv[1:])
    sys.stdout.write(result.stdout)
    sys.exit(result.returncode)
