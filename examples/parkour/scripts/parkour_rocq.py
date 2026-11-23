"""Parkour compiler policy, shared by translation checks and controls."""

import os
import re
import subprocess
import sys
from collections.abc import Sequence

from itree_pins import rocq_environment, rocq_version

COMPAT_WARNINGS = ("notation-for-abbreviation", "bad-template-constraint", "register-all")


def unexpected_warning(output: str, allowed: Sequence[str]) -> bool:
    # Rocq puts the diagnostic name first in the final bracketed tag, which
    # may be on a continuation line. An untagged warning is never exempt.
    for block in re.split(r"(?m)^(?=File \"|Error:|Warning:|\*\*\* Warning:)", output):
        if block.startswith(("Warning:", "*** Warning:")):
            tag = re.search(r"\[([\w-]+)(?:,[\w.-]+)*\]$", block, re.MULTILINE)
            if not tag or tag[1] not in allowed:
                return True
    return False


def compile_file(args: Sequence[str]) -> subprocess.CompletedProcess[str]:
    env = rocq_environment()
    allowed = COMPAT_WARNINGS if rocq_version().split(".")[:2] == ["9", "2"] else ()
    flags = ",".join(("+all", *allowed))
    result = subprocess.run(["rocq", "c", *args, "-q", "-w", flags],
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            text=True, env=env, check=False)
    # Some diagnostics are warnings even when the compiler returns success.
    if not result.returncode and unexpected_warning(result.stdout, allowed):
        result.returncode = 1
    return result


if __name__ == "__main__":
    args = sys.argv[1:]
    if args[:1] == ["--driver"]:
        if args[1:2] != ["compile"]:
            os.execvpe("rocq", ["rocq", *args[1:]], rocq_environment())
        args = args[2:]
    result = compile_file(args)
    sys.stdout.write(result.stdout)
    sys.exit(result.returncode)
