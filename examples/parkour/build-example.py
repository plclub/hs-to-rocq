"""Translate the pinned modules into an empty tree and check the compiled result."""

import argparse
import shutil
import subprocess
from collections.abc import Iterator, Mapping, Sequence
from pathlib import Path

from itree_pins import pinned_environment, prefix_path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--check-edits", action="store_true")
args = parser.parse_args()
base = Path("../rocq9.0/base")
out = Path("build/run")
deps = out / "transformers"
support = out / "manual"
lib = Path("lib")
contracts = out / "theories"
local = out / "local"
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
        # Static in-process loading of the HTTP package closure overflows a
        # PAGE21 relocation on Apple Silicon when GHC runs Main's mkLoc splices.
        th = ["--ghc=-fexternal-interpreter"] if name == "Main" else []
        preamble = (["-p", f"module-edits/{name.replace('.', '/')}/preamble.v"]
                    if name in {"Choreography.Location", "Choreography2"} else [])
        yield name, protocol if name == "Main" else upstream, lib, [
            "-e", "edits", "--ghc=-i", f"--ghc=-i{upstream}", "--ghc=-XGHC2021", "--ghc=-hide-all-packages",
            *["--ghc=-package=" + p for p in packages], *th, *preamble]


def invocation(name: str, root: Path, target: Path, flags: Sequence[Arg]) -> list[Arg]:
    cli = ["--strict", "--target-version", "9.0", "-N", "-e", "../../base/edits",
           *flags, "--iface-dir", base, "--iface-dir", support, "--iface-dir", deps, "--iface-dir", lib,
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
    run("./checked-tool", "check", *invocation(*module))
if args.check_edits:
    raise SystemExit(0)

if "version 9.0.1\n" not in subprocess.check_output(["rocq", "--version"], text=True):
    raise SystemExit("activate a Rocq 9.0.1 switch")
if subprocess.check_output(["stack", "exec", "--", "ghc", "--numeric-version"],
                           text=True).strip() != "9.10.3":
    raise SystemExit("expected GHC 9.10.3")
for directory in [out, lib]:
    if directory.exists():
        shutil.rmtree(directory)
for directory in [deps, lib, support, contracts]:
    directory.mkdir(parents=True, exist_ok=True)

run("python3", "tests/check-deadlock-local.py", "--output", local)
rocq_env = pinned_environment(prefix_path())
load_deps: list[Arg] = [arg for path in (base, deps, support, local) for arg in ("-Q", path.resolve(), "")]
rocq: list[Arg] = ["python3", Path("parkour_rocq.py").resolve(), *load_deps, "-Q", lib.resolve(), ""]


def build_support(module: str) -> None:
    source = Path("Parkour", module + ".v")
    target = support / source
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(Path("manual") / source, target)
    interface = (Path("manual") / source).with_suffix(".h2ci")
    if interface.exists():
        shutil.copyfile(interface, target.with_suffix(".h2ci"))
    run(*rocq, target.resolve(), cwd=contracts, env=rocq_env)


def check_theory(name: str) -> None:
    source = Path("theories", name + ".v")
    shutil.copyfile(source, contracts / source.name)
    run(*rocq, source.name, cwd=contracts, env=rocq_env)


run("python3", "extract-contravariant.py", class_source / "Parkour/Contravariant.hs")
for model in ["Symbol", "Codec", "TH", "Runtime", "Functions"]:
    build_support(model)
for module in modules():
    name, target = module[0], module[2]
    run("./checked-tool", "translate", *invocation(*module))
    vfile = target / (name.replace(".", "/") + ".v")
    run(*rocq, vfile.resolve(), cwd=contracts, env=rocq_env)
    if name == "Control.Monad.Trans.Reader":
        build_support("Reader")
    if name == "Choreography.Network":
        check_theory("ReaderTree")
        build_support("Http")

run("bash", Path("test-checks.sh").resolve(), "--check-closed", lib.resolve(), "Choreography.Choreo2.epp",
    *load_deps,
    cwd=contracts, env=rocq_env)
for name in ["Required", "Behavior", "OwnerCond", "Integration"]:
    check_theory(name)
for theorem in ["owner_cond_sequential", "owner_cond_app", "owner_cond_false",
                "peer_cond_false", "owner_cond_then_action"]:
    run("python3", Path("check-assumptions.py").resolve(), "closed", contracts.resolve(),
        f"OwnerCond.{theorem}", *load_deps, "-Q", lib.resolve(), "",
        cwd=contracts, env=rocq_env)
