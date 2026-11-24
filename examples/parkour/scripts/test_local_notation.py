import os
import subprocess
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

CHECKER = Path(__file__).with_name("check_local_notation.py").resolve()


class LocalNotationTest(unittest.TestCase):
    def setUp(self) -> None:
        tmp = TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name) / "parkour"
        self.root.mkdir()

    def write(self, relative: str, text: str) -> Path:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        return path

    def check_gate(self, status: int, diagnostics: list[str]) -> None:
        result = subprocess.run(
            [sys.executable, CHECKER, self.root], cwd=self.root.parent,
            env={**os.environ, "PATH": ""}, text=True, capture_output=True, check=False,
        )
        self.assertEqual(result.returncode, status, result.stderr)
        self.assertEqual(result.stderr.splitlines(), diagnostics)
        self.assertEqual(result.stdout, "")

    def test_comments_strings_and_imports_do_not_declare_notations(self) -> None:
        self.write("theories/Allowed.v", '''\
(* "*)" (* a nested comment *) Local Notation here := False. *)
From Stdlib Require Import Lists.List.
Import ListNotations. Import Example.Local Notation.
Local Open Scope list_scope. Check [1; 2].
Definition message := "(* "". Local Infix
   ""!"" := plus. #[local] Notation ignored := True. *)".
Notation Refl := eq_refl.
Reserved Notation "'plain' x" (at level 10).
Reserved Infix "<+>" (at level 50).
#[deprecated(since="9.0", note="say ""local""")] Notation Old := unit.
#[local] Definition example := message.
''')
        self.check_gate(0, [])

    def test_goal_selector_focus_starts_a_command(self) -> None:
        self.write("Proof.v", """\
Goal True. Proof. 1: { Local Notation finished := I. exact finished. } Qed.
Goal True. Proof. refine ?[branch].
[ (* name *) branch ] (* focus *) :
  { 1 : { #[local] Notation done := I. exact done. } } Qed.
""")
        self.write("Qualified.v", """\
Set Generate Goal Names.
Goal forall n m : nat, True. Proof. intros n m. destruct n.
[O]: { destruct m.
  [O.O]: { Local Notation done := I. exact done. } [O.S]: exact I. }
[S]: exact I. Qed.
""")
        self.check_gate(1, [
            "Proof.v:1: Local Notation is forbidden",
            "Proof.v:4: Local Notation is forbidden",
            "Qualified.v:4: Local Notation is forbidden",
        ])

    def test_failed_multi_goal_focus_still_ends_before_the_declaration(self) -> None:
        # Rocq parses the brace command but only permits focusing one goal.
        self.write("Ranges.v", """\
Goal True /\\ True. Proof. split.
Fail 1 (* range *) - 2, 1 : { Local Notation done := I.
1-2: exact done. Qed.
""")
        self.check_gate(1, ["Ranges.v:2: Local Notation is forbidden"])

    def test_selectors_do_not_turn_operands_into_commands(self) -> None:
        self.write("Operands.v", """\
Definition Local (f : nat -> nat) := f.
Definition Notation (n : nat) := n.
Definition Reserved (n : nat) := n.
Definition Infix := 0.
Goal True /\\ True. Proof. split.
1-2: let t := constr:(Local Notation) in idtac.
1: Check (Local Reserved Infix).
1: { Check (forall {Local Notation : Type}, Local -> Notation).
     exact I. }
exact I. Qed.
""")
        self.check_gate(0, [])

    def test_local_reserved_declarations(self) -> None:
        self.write("Reserve.v", '''\
Local Reserved Notation "'hello' x" (at level 10).
Local (* split *)
  Reserved Infix "<+>" (at level 50).
Check nat. #[local] Reserved
  Notation "'bye' x" (at level 10).
#[
  local] (* split *) Reserved Infix "<*>" (at level 40).
''')
        self.check_gate(1, [
            "Reserve.v:1: Local Reserved Notation is forbidden",
            "Reserve.v:2: Local Reserved Infix is forbidden",
            "Reserve.v:4: Local Reserved Notation is forbidden",
            "Reserve.v:6: Local Reserved Infix is forbidden",
        ])

    def test_command_wrappers_preserve_the_declaration_head(self) -> None:
        self.write("Wrapped.v", '''\
Instructions Profile (* output *) "log ""name"""
  #[local] Notation wrapped := unit.
Profile Local Infix "<+>" := Nat.add (at level 50).
Profile "report. Local Notation ignored := nat." Check nat.
''')
        self.check_gate(1, [
            "Wrapped.v:2: Local Notation is forbidden",
            "Wrapped.v:3: Local Infix is forbidden",
        ])

    def test_reports_all_declarations_in_path_then_source_order(self) -> None:
        self.write("theories/Nested/Z.v", """\
Check nat. Local(* outer (* nested *) *)Infix "+" := plus.
Check unit.(* comment *)#[
  local (* comment *) ]
  Notation hidden := tt. Local Notation another := tt.
""")
        self.write("tests/F.v", 'Time #[deprecated(note="]"), local] Infix "!" := plus.\n')
        self.write("module-edits/Choreo/preamble.v", "\ufeffLocal (* split *)\nNotation p := unit.\n")
        self.write("manual/M.v", "#[local](* split *)Infix \"!\" := plus.\n")
        self.write("counterexample/C.v",
                   'Goal True. Proof. - { Local Infix "<+>" := Nat.add (at level 50). exact I. } Qed.\n')
        self.write("New/Unlisted.v", "#[local] Notation extra := True.\n")
        self.write("New.v", 'Check "a string with\nperiods.". #[local] Notation n := nat.\n')
        self.check_gate(1, [
            "New.v:2: Local Notation is forbidden",
            "New/Unlisted.v:1: Local Notation is forbidden",
            "counterexample/C.v:1: Local Infix is forbidden",
            "manual/M.v:1: Local Infix is forbidden",
            "module-edits/Choreo/preamble.v:1: Local Notation is forbidden",
            "tests/F.v:1: Local Infix is forbidden",
            "theories/Nested/Z.v:1: Local Infix is forbidden",
            "theories/Nested/Z.v:2: Local Notation is forbidden",
            "theories/Nested/Z.v:4: Local Notation is forbidden",
        ])

    def test_prunes_generated_vendored_and_cache_trees_and_skips_links(self) -> None:
        bad = "Local Notation hidden := unit.\n"
        for directory in ("build/run", "lib", "upstream/src", ".itree-cache",
                          ".ruff_cache", "tests/__pycache__"):
            self.write(directory + "/Ignored.v", bad)
        self.write("manual/Backup.v.bak", bad)
        (self.root / "manual/Link.v").symlink_to(self.root / "build/run/Ignored.v")
        (self.root / "tests/linked").symlink_to(self.root / "upstream", target_is_directory=True)
        self.check_gate(0, [])
