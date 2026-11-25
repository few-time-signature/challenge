import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


class GitIntakeTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.repo = Path(temp.name) / "repo"
        self.repo.mkdir()
        self.git("init", "--quiet")
        self.git("config", "user.name", "Intake test")
        self.git("config", "user.email", "test@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        self.git("commit", "--quiet", "--allow-empty", "-m", "Organizer baseline")
        self.base = self.git("rev-parse", "HEAD")

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.repo, text=True).strip()

    def copy_entry(self, name):
        entry = Path("submissions") / name
        shutil.copytree(ROOT / "examples/entries" / name, self.repo / entry)
        return entry

    def preflight(self):
        output = self.repo.parent / "outputs"
        env = dict(os.environ, BASE=self.base, HEAD=self.git("rev-parse", "HEAD"),
                   PYTHONPATH=str(ROOT), GITHUB_OUTPUT=str(output))
        return subprocess.run([sys.executable, "-B", "-m", "ci.preflight"],
                              cwd=self.repo, env=env, text=True, capture_output=True)

    def test_one_construction_can_span_two_commits(self):
        entry = self.copy_entry("construction/fors-c-2020")
        self.git("add", str(entry / "claim.json"))
        self.git("commit", "--quiet", "-m", "State the byte claim")
        self.git("add", str(entry))
        self.git("commit", "--quiet", "-m", "Supply the circuit and proof")
        result = self.preflight()
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_concurrent_organizer_changes(self):
        self.git("switch", "-qc", "entry")
        self.copy_entry("construction/fors-c-2020")
        self.git("add", "submissions")
        self.git("commit", "-qm", "Supply one entry")
        self.git("switch", "-qc", "organizer", self.base)
        (self.repo / "docs").mkdir()
        (self.repo / "docs/scores.json").write_text("{}")
        self.git("add", "docs")
        self.git("commit", "-qm", "Another result arrived")
        ledger = self.git("rev-parse", "HEAD")
        (self.repo / "RULES.md").write_text("Updated rules")
        self.git("add", "RULES.md")
        self.git("commit", "-qm", "Change organizer rules")
        rules = self.git("rev-parse", "HEAD")
        self.git("switch", "-q", "entry")
        self.base = ledger
        self.assertEqual(self.preflight().returncode, 0)
        self.base = rules
        self.assertIn("organizer rules changed", self.preflight().stderr)
        self.git("merge", "-q", "--no-edit", "organizer")
        self.assertEqual(self.preflight().returncode, 0)

    def assert_bundle_rejected(self, second):
        self.copy_entry("construction/fors-c-2020")
        self.copy_entry(second)
        self.git("add", "submissions")
        self.git("commit", "--quiet", "-m", "Submit two claims together")
        result = self.preflight()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("one entry per PR", result.stderr)

    def test_two_parameter_sets_in_one_commit(self):
        self.assert_bundle_rejected("construction/fors-c-2132")

    def test_two_tracks_in_one_commit(self):
        self.assert_bundle_rejected("lower-bound/opening-lower-bound")
