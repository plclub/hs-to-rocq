#!/usr/bin/env python3
"""Portable controls for fingertree audit tools and source-policy build wiring.

Run with Python 3.8+ (standard library), Make, and standard Unix utilities:
    python3 test/assumptions.py
Add real compiler controls (a missing or failing compiler is an error):
    python3 test/assumptions.py --rocq rocq

All compiler inputs, manifests, logs, and products live in temporary directories.
"""

import sys

sys.dont_write_bytecode = True

import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from source_policy_checks import DOCUMENTATION, SourceInventoryTests, SourcePolicyMakeTests


ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "examples/fingertree"
THEORY_CHECKER = EXAMPLE / "theories/check-assumptions.py"
PRIORITY_CHECKER = (
    EXAMPLE / "module-edits/Data/PriorityQueue/FingerTree/check-priority-audit.py"
)
FIXTURE = Path(__file__).resolve().parent / "assumptions/AssumptionFixture.v"
PRIORITY_FIXTURE = FIXTURE.with_name("PriorityAssumptionFixture.v")
CLOSED_SOURCE = """Lemma witness : True.
Proof. exact I. Qed.
Print Assumptions witness.
"""
CLOSED_REPORT = """AUDIT: witness
witness : True
Closed under the global context
"""
AXIOM_REPORT = """AUDIT: witness
witness : True
Axioms:
rogue : True
"""
ASSERTION_FORMS = ("Lemma", "Theorem", "Remark", "Fact", "Corollary", "Proposition", "Example")
ASSERTION_PREFIXES = (
    "", "Local ", "Global ", "Polymorphic ", "#[local] ", "#[global] ",
    "#[universes(polymorphic)] ", "#[local]\nPolymorphic\n",
)


def assertion_fixture(form, admitted=False):
    names = [f"{form.lower()}_{index}" for index in range(len(ASSERTION_PREFIXES))]
    proof = ": False. Admitted.\n" if admitted else ": True. Proof. exact I. Qed.\n"
    source = "".join(f"{prefix}{form} {name} {proof}"
                     for prefix, name in zip(ASSERTION_PREFIXES, names))
    return source, names


def load_checker(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


theory = load_checker("theory_assumptions", THEORY_CHECKER)
priority = load_checker("priority_assumptions", PRIORITY_CHECKER)


def make_example(directory, source, specification):
    """Copy the production CLI into an isolated, minimal example layout."""
    example = directory / "examples/fingertree"
    theories = example / "theories"
    for path in (theories, example / "lib",
                 directory / "examples/rocq9.2/base",
                 directory / "examples/rocq9.2/base-thy"):
        path.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(THEORY_CHECKER, theories / THEORY_CHECKER.name)
    (theories / "AssumptionFixture.v").write_text(source, encoding="utf-8")
    (theories / "assumptions.json").write_text(
        json.dumps({"AssumptionFixture": specification}), encoding="utf-8"
    )
    return example


def run_checker(example, rocq):
    return subprocess.run(
        [sys.executable, "-B", str(example / "theories/check-assumptions.py"),
         "AssumptionFixture", "--rocq", str(rocq)],
        cwd=example.parent, text=True, encoding="utf-8", capture_output=True,
        timeout=180,
    )


class TemporaryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="assumptions-")
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)


class InventoryTests(TemporaryTests):
    def inventory(self, text):
        source = self.directory / "Inventory.v"
        source.write_text(text, encoding="utf-8")
        return theory.inventory(source)

    def test_complete_inventory(self):
        self.assertEqual(self.inventory(
            "Axiom premise : True.\n"
            "Theorem witness : True. Proof. exact premise. Qed.\n"
            "Print Assumptions premise.\nPrint Assumptions witness.\n"
        ), ["premise", "witness"])

    def test_missing_inventory(self):
        with self.assertRaisesRegex(ValueError, "missing or duplicate export inventory"):
            self.inventory("Lemma witness : True. Proof. exact I. Qed.\n")

    def test_duplicate_inventory(self):
        with self.assertRaisesRegex(ValueError, "missing or duplicate export inventory"):
            self.inventory(CLOSED_SOURCE + "Print Assumptions witness.\n")

    def test_complete_assertion_inventories(self):
        for form in ASSERTION_FORMS:
            with self.subTest(form=form):
                source, names = assertion_fixture(form)
                source += "".join(f"Print Assumptions {name}.\n" for name in names)
                self.assertEqual(self.inventory(source), names)

    def test_named_assertion_omitted(self):
        for form in ASSERTION_FORMS:
            for admitted in (False, True):
                with self.subTest(form=form, admitted=admitted):
                    source, names = assertion_fixture(form, admitted)
                    with self.assertRaisesRegex(ValueError, "unaudited declarations") as error:
                        self.inventory(CLOSED_SOURCE + source)
                    self.assertEqual(str(error.exception),
                                     f"Inventory.v: unaudited declarations: {sorted(names)}")

    def test_named_axiom_omitted(self):
        with self.assertRaisesRegex(ValueError, "unaudited declarations:.*rogue"):
            self.inventory("Axiom rogue : True.\n" + CLOSED_SOURCE)

    def test_priority_inventory_ignores_documentation_but_requires_real_dictionary(self):
        directory = EXAMPLE / "module-edits/Data/PriorityQueue/FingerTree"
        audit = (directory / "PriorityAudit.v").read_text(encoding="utf-8")
        generated = (EXAMPLE / "lib/Data/PriorityQueue/FingerTree.v").read_text(encoding="utf-8")
        marker = "Instance Eq___PQueue "
        self.assertEqual(generated.count(marker), 1)
        omitted = generated.replace(marker, "Instance omitted_Eq___PQueue ", 1)
        # This is the same pre-compilation API called by the full queue audit.
        for label, documentation in DOCUMENTATION:
            with self.subTest(documentation=label):
                documentation = documentation.format(name="Eq___PQueue")
                self.assertEqual(len(priority.check_inventory(generated + documentation, audit)), 74)
                with self.assertRaisesRegex(ValueError, "missing.*Eq___PQueue"):
                    priority.check_inventory(omitted + documentation, audit)


class ReportTests(unittest.TestCase):
    def accept(self, output, expected):
        self.assertEqual(theory.reports(output, list(expected)), expected)
        priority.check_report(output, expected)

    def reject(self, output, message):
        for name, check in (
            ("theory", lambda: theory.reports(output, ["witness"])),
            ("priority", lambda: priority.check_report(output, {"witness": set()})),
        ):
            with self.subTest(checker=name):
                with self.assertRaisesRegex(ValueError, message):
                    check()

    def test_closed_report(self):
        self.accept(CLOSED_REPORT, {"witness": set()})

    def test_exact_dependency_names(self):
        self.accept("""AUDIT: witness
@witness
     : True
Axioms:
Library.approved : forall A : Type,
  A -> A
Library.guarded :
  True
""", {"witness": {"Library.approved", "Library.guarded"}})

    def test_missing_markers(self):
        for output, names in (
            ("", ["witness"]),
            (CLOSED_REPORT.replace("AUDIT: witness\n", ""), ["witness"]),
            (CLOSED_REPORT, ["witness", "missing"]),
        ):
            with self.subTest(output=output, names=names):
                with self.assertRaisesRegex(ValueError, "audit marker inventory differs"):
                    theory.reports(output, names)

    def test_duplicate_markers(self):
        with self.assertRaisesRegex(ValueError, "audit marker inventory differs"):
            theory.reports(CLOSED_REPORT + CLOSED_REPORT, ["witness"])

    def test_reordered_markers(self):
        second = CLOSED_REPORT.replace("witness", "second")
        with self.assertRaisesRegex(ValueError, "audit marker inventory differs"):
            theory.reports(second + CLOSED_REPORT, ["witness", "second"])

    def test_unexpected_marker(self):
        with self.assertRaisesRegex(ValueError, "audit marker inventory differs"):
            theory.reports(CLOSED_REPORT + CLOSED_REPORT.replace("witness", "extra"),
                           ["witness"])

    def test_missing_assumption_report(self):
        self.reject("AUDIT: witness\nwitness : True\n", "missing or ambiguous")

    def test_empty_axiom_report(self):
        self.reject("AUDIT: witness\nwitness : True\nAxioms:\n", "empty axiom report")

    def test_malformed_axiom_report(self):
        self.reject("AUDIT: witness\nwitness : True\nAxioms:\nrogue True\n",
                    "empty axiom report")

    def test_ambiguous_assumption_reports(self):
        for extra in ("Axioms:\nrogue : True\n",
                      "Closed under the global context\n"):
            with self.subTest(extra=extra):
                self.reject(CLOSED_REPORT + extra, "missing or ambiguous")
        self.reject(AXIOM_REPORT + "Axioms:\nother : True\n", "missing or ambiguous")


class PriorityReportTests(unittest.TestCase):
    def test_missing_check_report(self):
        with self.assertRaisesRegex(ValueError, "missing or unexpected assumption report"):
            priority.check_report(CLOSED_REPORT, {"witness": set(), "missing": set()})

    def test_duplicate_check_report(self):
        with self.assertRaisesRegex(ValueError, "duplicate assumption report"):
            priority.check_report(CLOSED_REPORT + CLOSED_REPORT, {"witness": set()})

    def test_unexpected_axiom(self):
        with self.assertRaisesRegex(ValueError, "expected.*got.*rogue"):
            priority.check_report(AXIOM_REPORT, {"witness": set()})

    def test_extra_dependency(self):
        with self.assertRaisesRegex(ValueError, "expected.*got.*extra"):
            priority.check_report(AXIOM_REPORT + "extra : True\n", {"witness": {"rogue"}})

    def test_missing_expected_dependency(self):
        with self.assertRaisesRegex(ValueError, "expected.*required.*got"):
            priority.check_report(AXIOM_REPORT, {"witness": {"rogue", "required"}})

    def test_closed_report_does_not_satisfy_nonempty_expectation(self):
        with self.assertRaisesRegex(ValueError, "expected.*rogue.*got"):
            priority.check_report(CLOSED_REPORT, {"witness": {"rogue"}})


class CompilerFailureTests(TemporaryTests):
    def setUp(self):
        super().setUp()
        self.example = make_example(self.directory, CLOSED_SOURCE, {"count": 1})

    def test_missing_compiler_is_nonzero(self):
        missing = self.directory / "missing-rocq"
        result = run_checker(self.example, missing)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("theory audit failed:", result.stderr)
        self.assertIn(str(missing), result.stderr)

    def test_compiler_error_with_plausible_report_is_nonzero(self):
        # Python acts as the requested compiler: its `c` file ignores the Rocq
        # arguments and emits a plausible report before failing. No shell needed.
        (self.example / "c").write_text(
            "print('compiler-error-control')\nprint(" + repr(CLOSED_REPORT) + ")\n"
            "raise SystemExit(23)\n", encoding="utf-8"
        )
        result = run_checker(self.example, sys.executable)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("compiler-error-control", result.stderr)
        self.assertIn("compiler failed", result.stderr)

    def test_zero_exit_compiler_without_reports_is_nonzero(self):
        (self.example / "c").write_text("pass\n", encoding="utf-8")
        result = run_checker(self.example, sys.executable)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("audit marker inventory differs", result.stderr)


class TheoryCliInventoryTests(TemporaryTests):
    def test_cli_accepts_audited_closed_assertions(self):
        for form in ASSERTION_FORMS:
            with self.subTest(form=form):
                source, names = assertion_fixture(form)
                source += "".join(f"Print Assumptions {name}.\n" for name in names)
                example = make_example(self.directory, source, {"count": len(names)})
                output = "".join(CLOSED_REPORT.replace("witness", name) for name in names)
                (example / "c").write_text("print(" + repr(output) + ")\n", encoding="utf-8")
                result = run_checker(example, sys.executable)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn(f"{len(names)}/{len(names)} exact assumption sets match "
                              f"({len(names)} closed)", result.stdout)

    def test_cli_rejects_omitted_assertions(self):
        for form in ASSERTION_FORMS:
            for admitted in (False, True):
                with self.subTest(form=form, admitted=admitted):
                    source, names = assertion_fixture(form, admitted)
                    example = make_example(self.directory, CLOSED_SOURCE + source, {"count": 1})
                    # A successful compiler reporting only the inventoried witness
                    # must not hide any additional closed or admitted assertion.
                    (example / "c").write_text("print(" + repr(CLOSED_REPORT) + ")\n",
                                               encoding="utf-8")
                    result = run_checker(example, sys.executable)
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertIn(f"AssumptionFixture.v: unaudited declarations: {sorted(names)}",
                                  result.stderr)


class RealRocqTests(TemporaryTests):
    rocq = None
    expected = {
        "rogue": {"rogue"},
        "witness": {"rogue"},
        "dependent_witness": {"rogue"},
        "closed_control": set(),
    }
    # The priority helper consumes marker-free, qualified Check output.
    priority_expected = {
        "AssumptionFixture.witness": {"AssumptionFixture.rogue"},
        "AssumptionFixture.dependent_witness": {"AssumptionFixture.rogue"},
        "AssumptionFixture.closed_control": set(),
    }

    @classmethod
    def setUpClass(cls):
        temporary = tempfile.TemporaryDirectory(prefix="assumptions-rocq-")
        cls.addClassCleanup(temporary.cleanup)
        directory = Path(temporary.name)
        source = directory / FIXTURE.name
        shutil.copyfile(FIXTURE, source)
        cls.output = theory.compile_file(cls.rocq, [], source, directory,
                                         directory / "fixture.log")
        priority_source = directory / PRIORITY_FIXTURE.name
        shutil.copyfile(PRIORITY_FIXTURE, priority_source)
        cls.priority_output = priority.compile_audit(
            cls.rocq, ["-Q", str(directory), ""], priority_source, directory, False
        )

    def test_real_reports_have_exact_assumptions(self):
        self.assertEqual(theory.reports(self.output, list(self.expected)), self.expected)
        priority.check_report(self.priority_output, self.priority_expected)

    def test_priority_rejects_real_unexpected_axiom(self):
        expected = dict(self.priority_expected)
        expected["AssumptionFixture.witness"] = set()
        with self.assertRaisesRegex(ValueError, "witness: expected.*got.*rogue"):
            priority.check_report(self.priority_output, expected)

    def test_priority_rejects_real_transitive_dependency(self):
        expected = dict(self.priority_expected)
        expected["AssumptionFixture.dependent_witness"] = set()
        with self.assertRaisesRegex(ValueError, "dependent_witness: expected.*got.*rogue"):
            priority.check_report(self.priority_output, expected)

    def run_manifest(self, exceptions):
        example = make_example(
            self.directory, FIXTURE.read_text(encoding="utf-8"),
            {"count": 4, "exceptions": exceptions},
        )
        return run_checker(example, self.rocq)

    def test_cli_accepts_real_exact_assumption_sets(self):
        result = self.run_manifest({
            "AssumptionFixture.rogue": ["rogue", "witness", "dependent_witness"],
        })
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("4/4 exact assumption sets match", result.stdout)

    def assert_mismatch(self, result, name, expected, actual):
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("assumption mismatch: ", result.stderr)
        mismatches = json.loads(result.stderr.split("assumption mismatch: ", 1)[1])
        self.assertEqual(mismatches, {name: {"expected": expected, "actual": actual}})

    def test_cli_rejects_real_unexpected_axiom(self):
        result = self.run_manifest({
            "AssumptionFixture.rogue": ["rogue", "dependent_witness"],
        })
        self.assert_mismatch(result, "witness", [], ["AssumptionFixture.rogue"])

    def test_cli_rejects_real_transitive_dependency(self):
        result = self.run_manifest({
            "AssumptionFixture.rogue": ["rogue", "witness"],
        })
        self.assert_mismatch(result, "dependent_witness", [], ["AssumptionFixture.rogue"])

    def test_cli_rejects_nonempty_expectation_for_real_closed_proof(self):
        result = self.run_manifest({
            "AssumptionFixture.rogue": list(self.expected),
        })
        self.assert_mismatch(result, "closed_control", ["AssumptionFixture.rogue"], [])

    def test_cli_accepts_real_audited_closed_assertions(self):
        source, names = "", []
        for form in ASSERTION_FORMS:
            assertions, exports = assertion_fixture(form)
            source += assertions
            names.extend(exports)
        source += "".join(f"Print Assumptions {name}.\n" for name in names)
        example = make_example(self.directory, source, {"count": len(names)})
        result = run_checker(example, self.rocq)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(f"{len(names)}/{len(names)} exact assumption sets match "
                      f"({len(names)} closed)", result.stdout)

    def test_cli_rejects_real_omitted_assertions(self):
        for form in ASSERTION_FORMS:
            for admitted in (False, True):
                with self.subTest(form=form, admitted=admitted):
                    source, names = assertion_fixture(form, admitted)
                    example = make_example(self.directory, CLOSED_SOURCE + source, {"count": 1})
                    theories = example / "theories"
                    paths = ["-Q", str(theories), "FingerTreeProofs"]
                    theory.compile_file(self.rocq, paths, theories / FIXTURE.name,
                                        example, self.directory / "fixture.log")
                    # Compile a separate consumer first: these are genuine,
                    # qualified exports, not syntax rejected by Rocq itself.
                    consumer = self.directory / "CheckExports.v"
                    consumer.write_text("Require FingerTreeProofs.AssumptionFixture.\n" + "".join(
                        f"Check @FingerTreeProofs.AssumptionFixture.{name}.\n" for name in names
                    ), encoding="utf-8")
                    output = theory.compile_file(self.rocq, paths, consumer,
                                                 example, self.directory / "exports.log")
                    for name in names:
                        self.assertIn(name, output)
                    result = run_checker(example, self.rocq)
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertIn(f"AssumptionFixture.v: unaudited declarations: {sorted(names)}",
                                  result.stderr)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rocq", metavar="EXECUTABLE",
                        help="also run real controls with this Rocq executable (required to work)")
    args = parser.parse_args()
    classes = [InventoryTests, ReportTests, PriorityReportTests, CompilerFailureTests,
               TheoryCliInventoryTests,
               SourceInventoryTests, SourcePolicyMakeTests]
    if args.rocq is not None:
        # Preserve an explicitly relative executable path across temporary cwd's.
        RealRocqTests.rocq = (str(Path(args.rocq).resolve())
                              if Path(args.rocq).name != args.rocq else args.rocq)
        classes.append(RealRocqTests)
    suite = unittest.TestSuite(unittest.defaultTestLoader.loadTestsFromTestCase(case)
                               for case in classes)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(main())
