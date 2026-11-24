import contextlib
import importlib.machinery
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from judge.score import OPENING


ROOT = Path(__file__).resolve().parents[1]
loader = importlib.machinery.SourceFileLoader("fts_client", str(ROOT / "fts"))
spec = importlib.util.spec_from_loader(loader.name, loader)
client = importlib.util.module_from_spec(spec)
loader.exec_module(client)


class EntrantCliTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.upstream = self.root / "base.git"
        self.fork = self.root / "renamed-fork.git"
        for repo in (self.upstream, self.fork):
            self.git(repo.parent, "init", "--quiet", "--bare", str(repo))
        tree = self.git(self.upstream, "write-tree")
        base = self.git(self.upstream, "commit-tree", tree, "-m", "Open rehearsal")
        self.git(self.upstream, "update-ref", "refs/heads/main", base)
        self.gh_calls = []
        self.pr = None

    @staticmethod
    def git(repo, *args):
        return subprocess.check_output(["git", "-c", "user.name=Test", "-c", "user.email=test@example.com",
                                        "-c", "commit.gpgSign=false", *args], cwd=repo, text=True).strip()

    def cli(self, *args, success=True):
        result = subprocess.run([sys.executable, "-B", str(ROOT / "fts"), *args], cwd=self.root,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode == 0, success, result.stderr)
        return result

    def example(self, track):
        self.cli("init", track, "my-claim", "--team", "test-team")
        return self.root / "submissions" / track / "my-claim"

    def github_api(self, endpoint, *args):
        self.gh_calls.append((endpoint, args))
        if endpoint == "user":
            return {"login": "alice", "id": 123}
        if endpoint == f"repos/{client.REPO}/forks" and args == ("--method", "POST"):
            return {"full_name": "alice/renamed-fork"}
        self.assertEqual(endpoint, f"repos/{client.REPO}/pulls")
        if args[1] == "GET":
            self.assertIn("base=main", args)
            self.assertIn("head=alice:fts/lower-bound/my-claim", args)
            return [self.pr] if self.pr else []
        self.assertEqual(args[1], "POST")
        self.assertIsNone(self.pr)
        self.pr = {"number": 42, "state": "open", "html_url": "https://example.test/pull/42"}
        return self.pr

    def publish(self, entry):
        upstream = f"https://github.com/{client.REPO}.git"
        # Let actual Git perform transport to two distinct local bare repositories.
        cfg = {"GIT_CONFIG_COUNT": "2",
               "GIT_CONFIG_KEY_0": f"url.{self.upstream}.insteadOf", "GIT_CONFIG_VALUE_0": upstream,
               "GIT_CONFIG_KEY_1": f"url.{self.fork}.insteadOf", "GIT_CONFIG_VALUE_1": "https://github.com/alice/renamed-fork.git"}
        out = io.StringIO()
        with patch.dict(os.environ, cfg), patch.object(client, "api", self.github_api), contextlib.redirect_stdout(out):
            client.submit(*client.read_entry(entry))
        return out.getvalue()

    def judge_head(self):
        branch = "refs/heads/fts/lower-bound/my-claim"
        self.git(self.upstream, "fetch", "--quiet", str(self.fork), branch)
        head = self.git(self.upstream, "rev-parse", "FETCH_HEAD")
        base = self.git(self.upstream, "rev-parse", "refs/heads/main")
        env = dict(os.environ, BASE=base, HEAD=head, PYTHONPATH=str(ROOT), GITHUB_OUTPUT=str(self.root / "output"))
        subprocess.run([sys.executable, "-B", "-m", "ci.preflight"], cwd=self.upstream, env=env, check=True)
        return head

    def test_both_templates_and_local_validation(self):
        for track in client.TRACKS:
            entry = self.example(track)
            self.assertEqual(json.loads((entry / "claim.json").read_text())["bound_bytes"], OPENING[track])
            self.assertIn("Entry format OK", self.cli("check", str(entry)).stdout)
            self.cli("init", track, "my-claim", "--team", "test-team", success=False)
            (entry / "notes.txt").symlink_to(entry / "claim.json")
            self.assertIn("regular non-executable", self.cli("submit", str(entry), success=False).stderr)
        self.cli("init", "construction", "../other", "--team", "test-team", success=False)

    def test_submission_retry_revision_and_receipt(self):
        entry = self.example("lower-bound")
        (self.root / "unrelated.txt").write_text("Private working note")
        self.assertIn("pull/42", self.publish(entry))
        first = self.judge_head()
        self.assertEqual(self.git(self.upstream, "ls-tree", first, "--", "unrelated.txt"), "")
        self.assertIn("pull/42", self.publish(entry))
        self.assertEqual(self.judge_head(), first)
        # The official judge requires the latest main to be an ancestor of the new head.
        base = self.git(self.upstream, "rev-parse", "refs/heads/main")
        changed = self.git(self.upstream, "commit-tree", self.git(self.upstream, "write-tree"), "-p", base, "-m", "Advance main")
        self.git(self.upstream, "update-ref", "refs/heads/main", changed)
        (entry / "ARGUMENT.md").write_text("A revised argument.\n")
        self.publish(entry)
        second = self.judge_head()
        self.assertNotEqual(first, second)
        self.git(self.upstream, "merge-base", "--is-ancestor", first, second)
        self.pr["state"] = "closed"
        with self.assertRaisesRegex(ValueError, "previous PR is closed"):
            self.publish(entry)

        # Simulate the judge's accepted tree with an official score receipt.
        clone = self.root / "organizer"
        self.git(self.root, "clone", "-q", "-b", "main", str(self.upstream), str(clone))
        dest = clone / "submissions/lower-bound/my-claim"
        shutil.copytree(entry, dest)
        (clone / "docs").mkdir()
        claim = client.read_entry(entry)[2]
        (clone / "docs/scores.json").write_text(json.dumps({"history": [dict(claim, pr=42)]}))
        self.git(clone, "add", ".")
        self.git(clone, "commit", "-qm", "Accept entry")
        self.git(clone, "push", "--quiet", "origin", "main")
        self.gh_calls.clear()
        self.assertIn("Already accepted", self.publish(entry))
        self.assertFalse(any(endpoint.endswith("/forks") for endpoint, _ in self.gh_calls))
        (entry / "ARGUMENT.md").write_text("Different proof\n")
        with self.assertRaisesRegex(ValueError, "new ID"):
            self.publish(entry)
