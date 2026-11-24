"""Compiler-independent controls at the source-inventory CLI and Make boundaries.

Loaded by assumptions.py. Production inventories, sources, and Makefiles run in
temporary layouts. Build tools and proof-compilation stages are faked; the real
assumption-parser controls remain in assumptions.py.
"""

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "examples/fingertree"
MODULES = ("Data/FingerTree", "Data/IntervalMap/FingerTree",
           "Data/PriorityQueue/FingerTree")
AUDITS = ("module-edits/Data/FingerTree/CoreAudit.v",
          "module-edits/Data/IntervalMap/FingerTree/IntervalAudit.v",
          "module-edits/Data/PriorityQueue/FingerTree/PriorityAudit.v")
INVENTORY = "check-source-inventory.py"
PRIORITY = "module-edits/Data/PriorityQueue/FingerTree/check-priority-audit.py"
DICTIONARIES = ("Eq___ViewR", "Traversable__IntervalMap", "Eq___PQueue")
DOCUMENTATION = (
    ("nested comment", "\n(* Documentation only:\n(* Nested example:\n"
     "Definition {name} := helper.\n*)\n*)\n"),
    ("multiline string", '\nGoal True. idtac "Documentation only:\n'
     'Definition {name} := helper.\n". Abort.\n'),
    ("doubled quotes", '\nGoal True. idtac "Documentation ""example:\n'
     'Instance {name} := helper.\n""". Abort.\n'),
    ("comment delimiters in string", '\nGoal True. idtac "(* *) *) (*\n'
     'Definition {name} := helper.\n". Abort.\n'),
    ("quotes in comment", '\n(* Documentation "quoted ""*)"" example":\n'
     'Definition {name} := helper.\n*)\n'),
    ("quoted opener in nested comment", '\n(* Documentation:\n(* "(*" example *)\n'
     'Definition {name} := helper.\n*)\n'),
)


def copy_file(source, target):
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)


def inventory_example(directory):
    example = directory / "examples/fingertree"
    example.mkdir(parents=True)
    # During red/green development the new helper/audit may not exist yet. The
    # public invocation must fail in that case, rather than silently skipping.
    for relative in (INVENTORY, PRIORITY) + AUDITS:
        if (EXAMPLE / relative).is_file():
            copy_file(EXAMPLE / relative, example / relative)
    for module in MODULES:
        relative = "lib/" + module + ".v"
        copy_file(EXAMPLE / relative, example / relative)
    return example


def assert_required(test, example, output):
    """Use the checked-in audits as witnesses, with independently pinned counts."""
    names = output.splitlines()
    test.assertEqual(len(names), 234)
    test.assertEqual(len(names), len(set(names)))
    remaining = set(names)
    for module, relative, count in zip(MODULES, AUDITS, (131, 31, 72)):
        prefix = module.replace("/", ".") + "."
        selected = {name for name in names if name.startswith(prefix)}
        test.assertEqual(len(selected), count, module)
        audit = (example / relative).read_text(encoding="utf-8")
        for name in selected:
            audited = ("Queue." + name[len(prefix):]
                       if module == MODULES[2] else name)
            test.assertIn("Print Assumptions " + audited + ".\n", audit)
        remaining -= selected
    test.assertFalse(remaining)
    for name in ("DefaultPQueue", "pqueue_size"):
        test.assertNotIn("Data.PriorityQueue.FingerTree." + name, names)
    for name in ("Data.FingerTree.Eq___ViewR", "Data.FingerTree.Eq___SearchResult",
                 "Data.IntervalMap.FingerTree.Traversable__IntervalMap",
                 "Data.PriorityQueue.FingerTree.Eq___PQueue"):
        test.assertIn(name, names)


def rename_declaration(test, path, declaration, name):
    """Lose just the declaration name, leaving references as false witnesses."""
    original = path.read_text(encoding="utf-8")
    marker = declaration + " " + name + " "
    test.assertEqual(original.count(marker), 1, str(path) + ": " + name)
    path.write_text(original.replace(marker, declaration + " omitted_" + name + " ", 1),
                    encoding="utf-8")
    return original


class SourceInventoryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="source-inventory-")
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.example = inventory_example(self.directory)

    def run_inventory(self, *args):
        # A different cwd catches accidental dependence on the Make caller.
        return subprocess.run([sys.executable, "-B", str(self.example / INVENTORY)] + list(args),
                              cwd=self.directory, text=True, encoding="utf-8",
                              capture_output=True, timeout=30)

    def assert_rejected(self, result, *diagnostics):
        output = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0, output)
        for text in diagnostics:
            self.assertIn(text, output)

    def test_current_generated_inventories_pass(self):
        for module in MODULES:
            with self.subTest(module=module):
                result = self.run_inventory("--module", module)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_declaration_text_in_nested_comment_is_ignored(self):
        for module, name in zip(MODULES, DICTIONARIES):
            with self.subTest(module=module):
                path = self.example / "lib" / (module + ".v")
                path.write_text(path.read_text(encoding="utf-8") +
                                DOCUMENTATION[0][1].format(name=name), encoding="utf-8")
                result = self.run_inventory("--module", module)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_declaration_text_in_strings_and_quoted_comments_is_ignored(self):
        for module, name in zip(MODULES, DICTIONARIES):
            path = self.example / "lib" / (module + ".v")
            original = path.read_text(encoding="utf-8")
            for label, documentation in DOCUMENTATION[1:]:
                with self.subTest(module=module, documentation=label):
                    path.write_text(original + documentation.format(name=name), encoding="utf-8")
                    result = self.run_inventory("--module", module)
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_missing_dictionaries_cannot_use_comment_or_string_witnesses(self):
        for module, name in zip(MODULES, DICTIONARIES):
            relative = "lib/" + module + ".v"
            path = self.example / relative
            rename_declaration(self, path, "Instance", name)
            omitted = path.read_text(encoding="utf-8")
            for label, documentation in DOCUMENTATION:
                with self.subTest(module=module, documentation=label):
                    path.write_text(omitted + documentation.format(name=name), encoding="utf-8")
                    self.assert_rejected(self.run_inventory("--module", module),
                                         relative, "missing ['" + name + "']")

    def test_declarations_after_documentation_still_count(self):
        for module, name in zip(MODULES, DICTIONARIES):
            relative = "lib/" + module + ".v"
            path = self.example / relative
            original = path.read_text(encoding="utf-8")
            for label, documentation in DOCUMENTATION:
                with self.subTest(module=module, documentation=label):
                    path.write_text(original + documentation.format(name=name) +
                                    "Definition " + name + " := helper.\n", encoding="utf-8")
                    self.assert_rejected(self.run_inventory("--module", module),
                                         relative, "duplicate ['" + name + "']")

    def test_unterminated_lexical_regions_fail_with_source_paths(self):
        cases = (("comment", "\n(* unfinished\n", "unterminated Rocq comment"),
                 ("nested comment", "\n(* outer (* inner *)\n", "unterminated Rocq comment"),
                 ("string", '\nGoal True. idtac "unfinished\n', "unterminated Rocq string"),
                 ("string in comment", '\n(* "unfinished *)\n', "unterminated Rocq string"))
        for module in MODULES:
            relative = "lib/" + module + ".v"
            path = self.example / relative
            original = path.read_text(encoding="utf-8")
            for label, suffix, diagnostic in cases:
                with self.subTest(module=module, region=label):
                    path.write_text(original + suffix, encoding="utf-8")
                    self.assert_rejected(self.run_inventory("--module", module),
                                         relative, diagnostic)
                    if module == MODULES[2]:
                        result = subprocess.run(
                            [sys.executable, "-B", str(self.example / PRIORITY),
                             "--rocq", str(self.directory / "missing-rocq")],
                            cwd=self.directory, text=True, encoding="utf-8",
                            capture_output=True, timeout=30)
                        self.assert_rejected(result, relative, diagnostic)

    def test_required_names_come_from_audits_without_generated_files(self):
        shutil.rmtree(self.example / "lib")
        result = self.run_inventory("--required")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        assert_required(self, self.example, result.stdout)

    def test_required_names_follow_audit_changes(self):
        audit = self.example / AUDITS[0]
        old = "Data.FingerTree.unsafeTraverse"
        new = "Data.FingerTree.source_inventory_control"
        text = audit.read_text(encoding="utf-8")
        self.assertEqual(text.count("Print Assumptions " + old + "."), 1)
        audit.write_text(text.replace("Print Assumptions " + old + ".",
                                      "Print Assumptions " + new + "."), encoding="utf-8")
        result = self.run_inventory("--required")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(new, result.stdout.splitlines())
        self.assertNotIn(old, result.stdout.splitlines())

    def test_missing_derived_core_dictionaries_fail_by_name(self):
        relative = "lib/Data/FingerTree.v"
        path = self.example / relative
        original = path.read_text(encoding="utf-8")
        for name in ("Eq___ViewR", "Eq___SearchResult"):
            with self.subTest(name=name):
                path.write_text(original, encoding="utf-8")
                rename_declaration(self, path, "Instance", name)
                result = self.run_inventory("--module", MODULES[0])
                self.assert_rejected(result, relative, name)

    def test_missing_interval_dictionary_fails_by_name(self):
        relative = "lib/Data/IntervalMap/FingerTree.v"
        name = "Traversable__IntervalMap"
        rename_declaration(self, self.example / relative, "Instance", name)
        self.assert_rejected(self.run_inventory("--module", MODULES[1]), relative, name)

    def test_missing_and_duplicate_audit_entries_fail(self):
        for module, relative, name in zip(MODULES, AUDITS,
                                         ("Data.FingerTree.Eq___ViewR",
                                          "Data.IntervalMap.FingerTree.Traversable__IntervalMap",
                                          "Queue.Eq___PQueue")):
            audit = self.example / relative
            original = audit.read_text(encoding="utf-8")
            printed = "Print Assumptions " + name + ".\n"
            checked = "Check @" + name + ".\n" if name.startswith("Queue.") else ""
            self.assertEqual(original.count(printed), 1)
            for duplicate in (False, True):
                with self.subTest(module=module, duplicate=duplicate):
                    text = original + checked + printed
                    if not duplicate:
                        text = original.replace(printed, "")
                        if checked:
                            text = text.replace(checked, "")
                    audit.write_text(text, encoding="utf-8")
                    # Both public modes must reject malformed authoritative input.
                    for args in (("--required",), ("--module", module)):
                        self.assert_rejected(self.run_inventory(*args), relative)
            audit.write_text(original, encoding="utf-8")

    def test_queue_count_and_two_way_inventory_remain_enforced(self):
        relative = "lib/Data/PriorityQueue/FingerTree.v"
        path = self.example / relative
        original = path.read_text(encoding="utf-8")
        with self.subTest(control="extra declaration"):
            path.write_text(original + "\nDefinition unaudited_queue_control := tt.\n",
                            encoding="utf-8")
            self.assert_rejected(self.run_inventory("--module", MODULES[2]), relative)
        path.write_text(original, encoding="utf-8")
        with self.subTest(control="same count, changed manual helper"):
            # --required legitimately omits this helper, but the full 74-entry
            # queue inventory must still detect its loss with the count intact.
            rename_declaration(self, path, "Instance", "DefaultPQueue")
            self.assert_rejected(self.run_inventory("--module", MODULES[2]), relative)

    def test_queue_check_and_print_inventories_must_match(self):
        relative = AUDITS[2]
        audit = self.example / relative
        text = audit.read_text(encoding="utf-8")
        audit.write_text(text.replace("Print Assumptions Queue.empty.\n", ""),
                         encoding="utf-8")
        self.assert_rejected(self.run_inventory("--module", MODULES[2]), relative)

    def test_missing_input_files_fail_with_paths(self):
        generated = "lib/Data/FingerTree.v"
        (self.example / generated).unlink()
        self.assert_rejected(self.run_inventory("--module", MODULES[0]), generated)
        (self.example / AUDITS[1]).unlink()
        self.assert_rejected(self.run_inventory("--required"), AUDITS[1])


# One append per event makes logging safe for parallel Make recipes. Unknown
# invocations fail closed so no real compiler or Git process can be reached.
TOOL_STUB = r'''
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


def record(kind, **fields):
    event = dict(kind=kind, **fields)
    fd = os.open(os.environ["SOURCE_POLICY_TEST_LOG"],
                 os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o600)
    try:
        os.write(fd, (json.dumps(event) + "\n").encode("utf-8"))
    finally:
        os.close(fd)


tool = Path(sys.argv[0]).name
args = sys.argv[1:]
if tool == "stack" and "runghc" in args:
    required = Path(args[args.index("--required") + 1])
    record("policy", args=args, required=required.read_text(encoding="utf-8"))
    status = int(os.environ.get("SOURCE_POLICY_TEST_STATUS", "0"))
    if status:
        print("source-policy-control rejected", file=sys.stderr)
    sys.exit(status)
elif tool == "stack" and "hs-to-rocq" in args:
    module = Path(args[-1]).relative_to("fingertree").with_suffix("")
    output = Path(args[args.index("-o") + 1]) / module
    output.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(Path(os.environ["SOURCE_POLICY_TEST_TEMPLATES"]) /
                    module.with_suffix(".v"), output.with_suffix(".v"))
    output.with_suffix(".h2ci").write_text("fake interface\n", encoding="utf-8")
    record("translate", module=module.as_posix())
elif tool == "git" and args[:2] == ["-C", "fingertree"]:
    if args[2:] == ["rev-parse", "HEAD"]:
        print(os.environ["SOURCE_POLICY_TEST_PIN"])
    elif args[2] not in {"diff", "status"}:
        sys.exit("unexpected fake Git invocation: " + repr(args))
elif tool == "rocq" and args[0] == "c":
    source = Path(args[-1])
    source.with_suffix(".vo").write_text("fake object\n", encoding="utf-8")
    record("compile", source=source.as_posix())
elif tool == "rocq" and args[0] == "check":
    record("kernel", args=args)
elif tool == "check-assumptions.py":
    name = args[-1]
    Path("theories", name + ".vo").write_text("fake proof\n", encoding="utf-8")
    record("theory", name=name)
elif tool == "foundation-log.py":
    record("foundations")
elif tool == "python3":
    inventory = bool(args) and Path(args[0]).name == "check-source-inventory.py"
    if inventory:
        record("inventory", args=args)
    result = subprocess.run([sys.executable, "-B"] + args)
    status = result.returncode
    # A distinctive error status verifies that cleanup preserves the checker's
    # failure instead of normalizing every failure to 1. The real CLI still runs.
    if inventory and status:
        status = int(os.environ.get("SOURCE_POLICY_TEST_INVENTORY_STATUS", "0")) or status
    if inventory:
        record("inventory-result", args=args, status=status)
    sys.exit(status)
else:
    sys.exit("unexpected fake tool invocation: " + tool + " " + repr(args))
'''


def write_tool(path):
    path.write_text("#!" + sys.executable + "\n" + TOOL_STUB, encoding="utf-8")
    path.chmod(0o755)


class MakeExample:
    def __init__(self, directory):
        self.directory = directory
        self.example = inventory_example(directory)
        self.log = directory / "events.jsonl"
        self.templates = directory / "templates"
        shutil.move(str(self.example / "lib"), str(self.templates))
        copy_file(ROOT / "common.mk", directory / "common.mk")
        copy_file(EXAMPLE / "Makefile", self.example / "Makefile")
        for relative in ("edits", "check-source-policy.hs", "SourcePolicy.hs",
                         "source-policy.yaml", "theories/assumptions.json"):
            if (EXAMPLE / relative).is_file():
                copy_file(EXAMPLE / relative, self.example / relative)
        self.owned_edits = ["edits"]
        self.owned_support = []
        for module in MODULES:
            source = self.example / "fingertree" / (module + ".hs")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("-- fake translator input\n", encoding="utf-8")
            for name in ("edits", "preamble.v", "midamble.v"):
                relative = "module-edits/" + module + "/" + name
                if (EXAMPLE / relative).is_file():
                    copy_file(EXAMPLE / relative, self.example / relative)
                else:
                    target = self.example / relative
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_text("(* fixture support *)\n", encoding="utf-8")
                (self.owned_edits if name == "edits" else
                 self.owned_support).append(relative)
        self.theories = sorted(path.stem for path in (EXAMPLE / "theories").glob("*.v"))
        for name in self.theories:
            (self.example / "theories" / (name + ".v")).write_text(
                "(* compiler-independent fixture *)\n", encoding="utf-8")
        write_tool(self.example / "theories/check-assumptions.py")
        base_edits = directory / "examples/base-src/edits"
        base_edits.parent.mkdir(parents=True)
        base_edits.write_text("skip module GHC.Classes\n", encoding="utf-8")
        foundation = directory / "examples/rocq9.2"
        foundation.mkdir()
        (foundation / "Makefile").write_text(
            "all:\n\tpython3 foundation-log.py\n.PHONY: all\n", encoding="utf-8")
        write_tool(foundation / "foundation-log.py")
        tools = directory / "bin"
        tools.mkdir()
        for name in ("stack", "git", "rocq", "python3"):
            write_tool(tools / name)
        pin = next(line.split(":=", 1)[1].strip() for line in
                   (self.example / "Makefile").read_text(encoding="utf-8").splitlines()
                   if line.startswith("SOURCE_PIN :="))
        self.env = dict(os.environ, PATH=str(tools) + os.pathsep + os.environ["PATH"],
                        PYTHONDONTWRITEBYTECODE="1", SOURCE_POLICY_TEST_LOG=str(self.log),
                        SOURCE_POLICY_TEST_TEMPLATES=str(self.templates),
                        SOURCE_POLICY_TEST_PIN=pin, SOURCE_POLICY_TEST_STATUS="0",
                        SOURCE_POLICY_TEST_INVENTORY_STATUS="0")
        # An outer Make or developer-specific compiler override must not leak in.
        for name in ("MAKEFLAGS", "MFLAGS", "MAKELEVEL", "GNUMAKEFLAGS",
                     "FOREIGN_HS_TO_ROCQ", "HS_TO_ROCQ", "HS_TO_ROCQ_DIR",
                     "COQC", "ROCQ"):
            self.env.pop(name, None)

    def seed_stale(self):
        shutil.copytree(self.templates, self.example / "lib", dirs_exist_ok=True)
        for module in MODULES:
            for suffix in (".h2ci", ".vo"):
                (self.example / "lib" / (module + suffix)).write_text(
                    "stale product\n", encoding="utf-8")
        for name in self.theories:
            (self.example / "theories" / (name + ".vo")).write_text(
                "stale proof\n", encoding="utf-8")
        (self.example / "deps").mkdir()
        (self.example / "deps/source-required.txt").write_text(
            "stale required inventory\n", encoding="utf-8")
        # A real file with the target's name must not defeat its phony recipe.
        (self.example / "source-policy").write_text("stale gate\n", encoding="utf-8")

    def run(self, *targets, jobs=1, policy_status=0, inventory_status=0):
        env = dict(self.env, SOURCE_POLICY_TEST_STATUS=str(policy_status),
                   SOURCE_POLICY_TEST_INVENTORY_STATUS=str(inventory_status))
        return subprocess.run(["make", "-j" + str(jobs)] + list(targets),
                              cwd=self.example, env=env, text=True, encoding="utf-8",
                              capture_output=True, timeout=60)

    def events(self, kind=None):
        events = ([json.loads(line) for line in self.log.read_text(encoding="utf-8").splitlines()]
                  if self.log.exists() else [])
        return [event for event in events if kind is None or event["kind"] == kind]


class SourcePolicyMakeTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="source-policy-make-")
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)

    def assert_policy_failure(self, fixture, result):
        output = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0, output)
        self.assertEqual(len(fixture.events("policy")), 1, output)
        self.assertIn("source-policy-control rejected", output)
        self.assertIn("Error 23", output)
        work = {"translate", "foundations", "compile", "theory", "kernel"}
        self.assertFalse([event for event in fixture.events()
                          if event["kind"] in work], output)

    def test_policy_failure_precedes_all_build_work(self):
        for jobs in (1, 2):
            with self.subTest(jobs=jobs):
                fixture = MakeExample(self.directory / ("j" + str(jobs)))
                if jobs == 2:
                    fixture.seed_stale()
                result = fixture.run(jobs=jobs, policy_status=23)
                self.assert_policy_failure(fixture, result)

    def test_existing_products_cannot_bypass_gate_at_public_targets(self):
        # Cover the entry points once each, rather than crossing every target
        # with both job counts. The default failure above exercises both counts.
        cases = (("vfiles", 1), ("proofs", 2), ("coq", 1),
                 ("lib/Data/FingerTree.v", 1),
                 ("lib/Data/IntervalMap/FingerTree.v", 2),
                 ("lib/Data/PriorityQueue/FingerTree.vo", 2),
                 ("core-check", 1), ("interval-check", 2),
                 ("priority-check", 1), ("kernel-check", 2), ("foundations", 2))
        for index, (target, jobs) in enumerate(cases):
            with self.subTest(target=target, jobs=jobs):
                fixture = MakeExample(self.directory / str(index))
                fixture.seed_stale()
                self.assert_policy_failure(
                    fixture, fixture.run(target, jobs=jobs, policy_status=23))

    def test_required_inventory_failure_blocks_policy_and_build_work(self):
        fixture = MakeExample(self.directory)
        audit = fixture.example / AUDITS[0]
        text = audit.read_text(encoding="utf-8")
        audit.write_text(text.replace("Print Assumptions Data.FingerTree.Eq___ViewR.\n", ""),
                         encoding="utf-8")
        result = fixture.run("vfiles", jobs=2)
        output = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0, output)
        self.assertIn(AUDITS[0], output)
        events = fixture.events()
        failures = [event for event in events if event["kind"] == "inventory-result"
                    and event["status"] != 0]
        self.assertEqual(len(failures), 1, output)
        self.assertIn("--required", failures[0]["args"])
        self.assertFalse([event for event in events if event["kind"] in
                          {"policy", "foundations", "translate", "compile", "theory", "kernel"}],
                         output)

    def test_generated_inventory_failure_removes_outputs_and_blocks_dependents(self):
        cases = ((MODULES[0], DICTIONARIES[0], 0, "proofs", 1),
                 (MODULES[0], DICTIONARIES[0], 2, "proofs", 2),
                 (MODULES[1], DICTIONARIES[1], 2, "theories/IntervalLaws.vo", 1),
                 (MODULES[1], DICTIONARIES[1], 0, "theories/IntervalLaws.vo", 2),
                 (MODULES[2], DICTIONARIES[2], 0, "theories/PriorityRegression.vo", 1),
                 (MODULES[2], DICTIONARIES[2], 2, "theories/PriorityRegression.vo", 2))
        for index, (module, name, documentation_index, target, jobs) in enumerate(cases):
            label, documentation = DOCUMENTATION[documentation_index]
            with self.subTest(module=module, jobs=jobs, documentation=label):
                fixture = MakeExample(self.directory / str(index))
                fixture.seed_stale()
                path = fixture.templates / (module + ".v")
                rename_declaration(self, path, "Instance", name)
                omitted = path.read_text(encoding="utf-8")
                if module == MODULES[2]:
                    # Balance the queue's old raw 74-head scan: only the decoy
                    # would restore the missing name and count, not a real head.
                    omitted = omitted.replace("Instance omitted_" + name + " ",
                                              "Let omitted_" + name + " ", 1)
                path.write_text(omitted + documentation.format(name=name), encoding="utf-8")
                result = fixture.run(target, jobs=jobs, inventory_status=29)
                output = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0, output)
                self.assertIn("lib/" + module + ".v", output)
                self.assertIn(name, output)
                self.assertEqual(len(fixture.events("policy")), 1, output)
                failed = [event for event in fixture.events("inventory-result")
                          if event["status"] != 0]
                self.assertEqual(len(failed), 1, output)
                self.assertEqual(failed[0]["status"], 29, output)
                self.assertIn("--module", failed[0]["args"])
                self.assertIn(module, failed[0]["args"])
                self.assertIn("Error " + str(failed[0]["status"]), output)
                for suffix in (".v", ".h2ci"):
                    self.assertFalse((fixture.example / "lib" / (module + suffix)).exists(), output)
                self.assertNotIn("lib/" + module + ".v",
                                 [event["source"] for event in fixture.events("compile")], output)
                if module == MODULES[0]:
                    downstream = set(fixture.theories)
                elif module == MODULES[1]:
                    downstream = {"IntervalModel", "IntervalOperations", "IntervalLaws", "ApplicationLaws"}
                else:
                    downstream = {"PriorityModel", "PriorityOperations", "PriorityRegression", "ApplicationLaws"}
                self.assertFalse([event for event in fixture.events("theory")
                                  if event["name"] in downstream], output)
                self.assertFalse(fixture.events("kernel"), output)

    def test_vfiles_accepts_declaration_text_in_comments_and_strings(self):
        fixture = MakeExample(self.directory)
        for module, name in zip(MODULES, DICTIONARIES):
            path = fixture.templates / (module + ".v")
            documentation = "".join(text.format(name=name) for _, text in DOCUMENTATION)
            path.write_text(path.read_text(encoding="utf-8") + documentation, encoding="utf-8")
        result = fixture.run("vfiles", jobs=2)
        output = result.stdout + result.stderr
        self.assertEqual(result.returncode, 0, output)
        self.assertCountEqual([event["module"] for event in fixture.events("translate")], MODULES)
        checked = [event for event in fixture.events("inventory-result")
                   if "--module" in event["args"]]
        self.assertEqual(len(checked), len(MODULES), output)
        self.assertTrue(all(event["status"] == 0 for event in checked), output)
        self.assertFalse(fixture.events("compile"), output)
        self.assertFalse(fixture.events("theory"), output)
        for module in MODULES:
            with self.subTest(module=module):
                self.assertEqual((fixture.example / "lib" / (module + ".v")).read_text(
                    encoding="utf-8"), (fixture.templates / (module + ".v")).read_text(
                        encoding="utf-8"))
                self.assertEqual((fixture.example / "lib" / (module + ".h2ci")).read_text(
                    encoding="utf-8"), "fake interface\n")

    def test_default_build_runs_real_inventories_and_supplies_owned_policy_inputs(self):
        fixture = MakeExample(self.directory)
        fixture.seed_stale()
        result = fixture.run(jobs=2)
        output = result.stdout + result.stderr
        self.assertEqual(result.returncode, 0, output)
        policies = fixture.events("policy")
        self.assertEqual(len(policies), 1, output)
        policy = policies[0]
        assert_required(self, fixture.example, policy["required"])
        args = policy["args"]
        for arg in ("exec", "runghc", "-package=hs-to-rocq", "-i.", "check-source-policy.hs"):
            self.assertIn(arg, args)
        self.assertEqual(args[args.index("--policy") + 1], "source-policy.yaml")
        self.assertEqual(args[args.index("--required") + 1], "deps/source-required.txt")
        for flag, expected in (("--edits", fixture.owned_edits),
                               ("--support", fixture.owned_support)):
            actual = [args[index + 1] for index, arg in enumerate(args) if arg == flag]
            self.assertCountEqual(actual, expected)

        events = fixture.events()
        policy_index = events.index(policy)
        required = [event for event in events if event["kind"] == "inventory-result"
                    and "--required" in event["args"]]
        self.assertEqual(len(required), 1, output)
        self.assertEqual(required[0]["status"], 0, output)
        self.assertLess(events.index(required[0]), policy_index)
        foundations = fixture.events("foundations")
        self.assertEqual(len(foundations), 1, output)
        self.assertLess(policy_index, events.index(foundations[0]))
        self.assertCountEqual([event["module"] for event in fixture.events("translate")], MODULES)
        checked = [event for event in fixture.events("inventory-result")
                   if "--module" in event["args"]]
        self.assertEqual(len(checked), len(MODULES), output)
        self.assertTrue(all(event["status"] == 0 for event in checked), output)
        for module in MODULES:
            with self.subTest(module=module):
                translation = next(event for event in fixture.events("translate")
                                   if event["module"] == module)
                inventory = next(event for event in checked if module in event["args"])
                compilation = next(event for event in fixture.events("compile")
                                   if event["source"] == "lib/" + module + ".v")
                self.assertLess(policy_index, events.index(translation))
                self.assertLess(events.index(translation), events.index(inventory))
                self.assertLess(events.index(inventory), events.index(compilation))
                for suffix, contents in ((".h2ci", "fake interface\n"), (".vo", "fake object\n")):
                    self.assertEqual((fixture.example / "lib" / (module + suffix)).read_text(
                        encoding="utf-8"), contents)
        self.assertCountEqual([event["name"] for event in fixture.events("theory")],
                              fixture.theories)
        for name in fixture.theories:
            self.assertEqual((fixture.example / "theories" / (name + ".vo")).read_text(
                encoding="utf-8"), "fake proof\n")
