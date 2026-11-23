"""Translate the pinned modules into an empty tree and check the compiled result."""

import argparse
import os
import platform
import shutil
import subprocess
import sys
import tempfile
from collections.abc import Iterator, Mapping, Sequence
from pathlib import Path

from itree_pins import (
    ensure_prefix,
    pinned_environment,
    prefix_path,
    rocq_version,
    verify_prefix,
)
from parkour_base import SOURCE_BASE, prepare_base

SCRIPTS = Path(__file__).resolve().parent
PARKOUR = SCRIPTS.parent
os.chdir(PARKOUR)

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--check-edits", action="store_true")
parser.add_argument("--deps-only", action="store_true", help="prepare the generated libraries and verified private pins")
parser.add_argument("--final", action="store_true", help="also require the independent public theorem contract")
parser.add_argument("--scratch", action="store_true", help="use a fresh build directory and leave lib/ and build/run/ alone")
args = parser.parse_args()
project = Path(".")
if args.scratch:
    Path("build").mkdir(exist_ok=True)
    scratch = Path(tempfile.mkdtemp(dir="build", prefix="required-"))
    project = scratch / "parkour"
    project.mkdir()
    (project / "scripts").symlink_to(SCRIPTS, target_is_directory=True)
    print(f"Scratch build: {scratch}", flush=True)
out = project / "build/run"
base = out / "base"
lib = project / "lib"
deps = out / "transformers"
support = out / "manual"
transformers = Path("../ghc/ghc/libraries/transformers")
ghc_base_source = Path("../ghc/ghc/libraries/base/src")
class_source = out / "class-source"
upstream = Path("upstream/src")
protocol = Path("upstream/examples/explicit-parallel/quorum-voting-choreo2")
origins = [line.split("\t") for line in Path("required.tsv").read_text().splitlines()]
packages = Path("upstream-packages.txt").read_text().split()


Arg = str | Path
Module = tuple[str, Path, Path, Sequence[Arg]]


def modules() -> Iterator[Module]:
    cls_flags = ["--ghc=-XHaskell2010", "-e", "reader.edits"]
    yield "Parkour.Contravariant", class_source, deps, cls_flags
    yield "Control.Monad.IO.Class", ghc_base_source, deps, cls_flags
    for name in ["Control.Monad.Signatures", "Control.Monad.Trans.Class",
                 "Control.Monad.Trans.Reader"]:
        yield name, transformers, deps, [*cls_flags, "-i", transformers]
    for name in ["Control.Monad.Tree", "Choreography.Location", "Choreography.Network",
                 "Choreography.Choreo2", "Choreography2", "Main"]:
        th = ["--ghc=-fexternal-interpreter"] if name == "Main" else []
        if th and platform.system() == "Darwin" and platform.machine() == "arm64":
            # Static ghc-iserv can also crash loading Main's HTTP package closure.
            th.append("--ghc=-dynamic")
        preamble = (["-p", f"module-edits/{name.replace('.', '/')}/preamble.v"]
                    if name in {"Choreography.Location", "Choreography2"} else [])
        yield name, protocol if name == "Main" else upstream, lib, [
            "-e", "edits", "--ghc=-i", f"--ghc=-i{upstream}", "--ghc=-XGHC2021", "--ghc=-hide-all-packages",
            *["--ghc=-package=" + p for p in packages], *th, *preamble]


def invocation(name: str, root: Path, target: Path, flags: Sequence[Arg]) -> list[Arg]:
    cli = ["--strict", "--target-version", "9.0", "-N", "-e", "../../base/edits",
           *flags, "--iface-dir", SOURCE_BASE, "--iface-dir", support, "--iface-dir", deps, "--iface-dir", lib,
           "-o", target]
    for source, rocq in origins:
        if source.rpartition(".")[0] == name:
            cli.extend(["--require-origin", f"{source}={rocq}"])
    return [*cli, root / (name.replace(".", "/") + ".hs")]


def run(*command: Arg, cwd: Path | None = None, env: Mapping[str, str] | None = None) -> None:
    status = subprocess.run(command, check=False, cwd=cwd, env=env).returncode
    if status:
        raise SystemExit(status)


for module in modules():
    run(SCRIPTS / "checked-tool", "check", *invocation(*module))
if args.check_edits:
    raise SystemExit(0)

version = rocq_version()
if subprocess.check_output(["stack", "exec", "--", "ghc", "--numeric-version"],
                           text=True).strip() != "9.10.3":
    raise SystemExit("expected GHC 9.10.3")
for directory in [out, lib]:
    if directory.exists():
        shutil.rmtree(directory)
for directory in [deps, lib, support]:
    directory.mkdir(parents=True, exist_ok=True)

prepare_base(version, base)
prefix = prefix_path()
ensure_prefix(prefix)
verify_prefix(prefix)
(out / "pins").symlink_to(prefix / "lib/user-contrib", target_is_directory=True)
rocq_env = pinned_environment(prefix)
load_deps: list[Arg] = [arg for path in (base, deps, support) for arg in ("-Q", path.resolve(), "")]
rocq: list[Arg] = ["python3", SCRIPTS / "parkour_rocq.py", *load_deps, "-Q", lib.resolve(), ""]


def build_support(module: str) -> None:
    source = Path("Parkour", module + ".v")
    target = support / source
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(Path("manual") / source, target)
    interface = (Path("manual") / source).with_suffix(".h2ci")
    if interface.exists():
        shutil.copyfile(interface, target.with_suffix(".h2ci"))
    run(*rocq, target.resolve(), cwd=out, env=rocq_env)


def build_project(directory: str) -> None:
    source = Path(directory)
    target = project / directory
    if args.scratch:
        # Copy only project inputs, never checked-out .vo files or old makefiles.
        project_file = source / "_CoqProject"
        target.mkdir()
        shutil.copyfile(project_file, target / project_file.name)
        for line in project_file.read_text().splitlines():
            if line.endswith(".v"):
                (target / line).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source / line, target / line)
    run("rocq", "makefile", "-f", "_CoqProject", "-o", "Makefile.coq", cwd=target.resolve(), env=rocq_env)
    if not args.scratch:
        # Acceptance must observe diagnostics even for modules compiled earlier in an editor.
        run("make", "-f", "Makefile.coq", "clean", cwd=target.resolve(), env=rocq_env)
    # The project compiler checks warnings before parallel output is interleaved.
    log = out / f"make-{directory}.log"
    with log.open("w") as transcript, subprocess.Popen(
        ["make", "-j2", "-f", "Makefile.coq"], cwd=target.resolve(), env=rocq_env,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
    ) as make:
        dependency_warning = False
        assert make.stdout is not None
        for line in make.stdout:
            transcript.write(line)
            sys.stdout.write(line)
            sys.stdout.flush()
            dependency_warning |= line.startswith("*** Warning:")
        status = make.wait()
    if status:
        raise SystemExit(status)
    if dependency_warning:
        raise SystemExit(f"Rocq dependency warning: see {log}")


run("python3", SCRIPTS / "extract-contravariant.py", class_source / "Parkour/Contravariant.hs")
for model in ["Symbol", "Codec", "TH", "Runtime", "Functions"]:
    build_support(model)
for module in modules():
    name, target = module[0], module[2]
    run(SCRIPTS / "checked-tool", "translate", *invocation(*module))
    vfile = target / (name.replace(".", "/") + ".v")
    run(*rocq, vfile.resolve(), cwd=out, env=rocq_env)
    if name == "Control.Monad.Trans.Reader":
        build_support("Reader")
    if name == "Choreography.Network":
        build_support("Http")

if args.deps_only:
    raise SystemExit(0)

build_project("theories")
build_project("tests")
run("python3", SCRIPTS / "check-deadlock-local.py", "--output", out / "local",
    "--project-root", project.resolve())
run("bash", SCRIPTS / "test-checks.sh", "--check-closed", lib.resolve(), "Choreography.Choreo2.epp",
    *load_deps,
    cwd=out, env=rocq_env)
for theorem in ["owner_cond_sequential", "owner_cond_app", "owner_cond_false",
                "peer_cond_false", "owner_cond_then_action"]:
    run("python3", SCRIPTS / "check-assumptions.py", "closed", lib.resolve(),
        f"ParkourTheories.Tests.Translation.ChoiceBroadcastOrder.{theorem}", *load_deps,
        "-Q", (project / "theories").resolve(), "ParkourTheories",
        "-Q", (project / "tests").resolve(), "ParkourTheories.Tests", cwd=out, env=rocq_env)

run("python3", SCRIPTS / "check_semantics.py", out / "semantics", *(["--final"] if args.final else []),
    "--generated", lib, "--project-root", project.resolve(), "--", base, deps, support,
    env=rocq_env)
