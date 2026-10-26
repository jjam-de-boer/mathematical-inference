"""Exercise shared compiler coordination without launching Lean.

Tiny temporary Git repositories provide a real linked-worktree identity.
Short Python children test process boundaries and abrupt exit; they touch
only their fixture locks, never the live project's compiler slot or cache.
"""

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import local_check_artifacts as artifacts


class CompilerSlotTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        # Isolate even the coordination directory from actual local builds.
        temporary_path = patch.object(artifacts, "COMPILER_LOCK_ROOT", self.root)
        temporary_path.start()
        self.addCleanup(temporary_path.stop)
        self.environment = {key: value for key, value in os.environ.items()
                            if not key.startswith("GIT_")}
        self.environment.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
                                TMPDIR=str(self.root))
        self.repository = self.root / "repository"
        self.git("init", "--quiet", str(self.repository))
        tree = self.git("hash-object", "-t", "tree", "-w", "--stdin",
                        cwd=self.repository, input="")
        commit = self.git("commit-tree", tree, "-m", "compiler-slot fixture",
                          cwd=self.repository)
        self.git("update-ref", "refs/heads/main", commit, cwd=self.repository)
        self.worktree = self.root / "linked"
        self.git("worktree", "add", "--quiet", "--detach", str(self.worktree), commit,
                 cwd=self.repository)
        self.first = self.repository / "lean"
        self.second = self.worktree / "lean"
        self.first.mkdir()
        self.second.mkdir()

    def git(self, *arguments, cwd=None, input=None):
        command = ["git", "-c", "core.hooksPath=" + os.devnull,
                   "-c", "user.name=Compiler Slot Test",
                   "-c", "user.email=compiler-slot@example.invalid", *arguments]
        result = subprocess.run(command, cwd=cwd or self.root, env=self.environment,
                                text=True, input=input, capture_output=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout.strip()

    def child(self, root, body):
        tools = str(Path(artifacts.__file__).resolve().parent)
        source = ("import os, sys\nfrom pathlib import Path\n"
                  f"sys.path.insert(0, {tools!r})\n"
                  "import local_check_artifacts as artifacts\n"
                  f"artifacts.COMPILER_LOCK_ROOT = Path({str(self.root)!r})\n"
                  f"root = Path({str(root)!r})\n" + body)
        return subprocess.run([sys.executable, "-B", "-c", source], env=self.environment,
                              text=True, capture_output=True, timeout=5)

    def test_linked_worktrees_have_one_shared_slot_and_separate_artifacts(self):
        self.assertEqual(artifacts.compiler_lock_path(self.first),
                         artifacts.compiler_lock_path(self.second))
        self.assertNotEqual(artifacts.store_directory(self.first),
                            artifacts.store_directory(self.second))

    def test_other_worktree_process_is_refused_while_slot_is_held(self):
        with artifacts.exclusive_check(self.first):
            result = self.child(self.second,
                "try:\n"
                "    with artifacts.exclusive_check(root):\n"
                "        print('unexpected acquisition')\n"
                "except artifacts.ArtifactError as error:\n"
                "    print(error)\n"
                "    sys.exit(3)\n")
        self.assertEqual(result.returncode, 3, result.stderr)
        self.assertIn("compiler slot", result.stdout)
        with artifacts.exclusive_check(self.second):
            pass

    def test_process_exit_releases_both_locks_despite_stale_files(self):
        result = self.child(self.first,
            "with artifacts.exclusive_check(root):\n"
            "    os._exit(17)\n")
        self.assertEqual(result.returncode, 17, result.stderr)
        self.assertTrue(artifacts.compiler_lock_path(self.first).is_file())
        with artifacts.exclusive_check(self.second):
            pass
        with artifacts.exclusive_check(self.first):
            pass

    def test_old_same_worktree_lock_is_respected_and_shared_slot_released(self):
        local = artifacts.store_directory(self.first) / "check.lock"
        with artifacts.held_compiler_lock(local):
            with self.assertRaisesRegex(artifacts.ArtifactError, "compiler slot"):
                with artifacts.exclusive_check(self.first):
                    self.fail("an old local helper still holds this worktree")
        with artifacts.exclusive_check(self.first):
            pass

    def test_different_repositories_have_independent_keys(self):
        other = self.root / "other"
        self.git("init", "--quiet", str(other))
        self.assertNotEqual(artifacts.compiler_lock_path(self.first),
                            artifacts.compiler_lock_path(other))
        with artifacts.exclusive_check(self.first), artifacts.exclusive_check(other):
            pass

    def test_plain_archives_keep_directory_identity(self):
        archive = self.root / "archive"
        archive.mkdir()
        with patch.object(artifacts.subprocess, "run") as run:
            self.assertEqual(artifacts.compiler_repository(archive), "directory:" + str(archive))
        run.assert_not_called()

    def test_worktree_temporary_environment_cannot_split_the_slot(self):
        expected = artifacts.compiler_lock_path(self.first)
        alternate = self.root / "alternate-temporary"
        alternate.mkdir()
        with patch.dict(os.environ, {"TMPDIR": str(alternate)}), \
                patch.object(artifacts.tempfile, "tempdir", None):
            self.assertEqual(artifacts.compiler_lock_path(self.first), expected)

    def test_git_lookup_failure_is_not_treated_as_a_plain_archive(self):
        failed = subprocess.CompletedProcess([], 128, "", "fixture Git failure")
        with patch.object(artifacts.subprocess, "run", return_value=failed):
            with self.assertRaisesRegex(artifacts.ArtifactError, "shared Git compiler slot"):
                artifacts.compiler_repository(self.first)

    def test_inherited_git_overrides_cannot_change_the_repository_key(self):
        expected = artifacts.compiler_repository(self.first)
        overrides = {key: str(self.root / "unrelated") for key in
                     ("GIT_DIR", "GIT_COMMON_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE")}
        with patch.dict(os.environ, overrides):
            self.assertEqual(artifacts.compiler_repository(self.first), expected)

    def test_shared_lock_symlink_is_refused_without_touching_its_target(self):
        lock = artifacts.compiler_lock_path(self.first)
        target = self.root / "untouched"
        target.write_text("original")
        lock.symlink_to(target)
        with self.assertRaisesRegex(artifacts.ArtifactError, "symbolic-link"):
            with artifacts.exclusive_check(self.first):
                self.fail("a lock symlink must not be followed")
        self.assertEqual(target.read_text(), "original")

    def test_shared_directory_must_be_private_and_not_a_symlink(self):
        directory = artifacts.compiler_lock_path(self.first).parent
        directory.chmod(0o755)
        with self.assertRaisesRegex(artifacts.ArtifactError, "must be private"):
            artifacts.compiler_lock_path(self.first)
        directory.chmod(0o700)
        directory.rmdir()
        target = self.root / "other-directory"
        target.mkdir()
        directory.symlink_to(target, target_is_directory=True)
        with self.assertRaisesRegex(artifacts.ArtifactError, "symbolic link"):
            artifacts.compiler_lock_path(self.first)
        self.assertEqual(list(target.iterdir()), [])


if __name__ == "__main__":
    unittest.main()
