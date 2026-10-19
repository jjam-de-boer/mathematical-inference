"""Full-builder orchestration safety; no test starts Lean or Lake.

Real end-to-end evidence must come from the actual full build and audit.
These small fixtures instead guard process-group accounting, serial ordering,
configuration isolation, and refusal paths before that real work is attempted.
"""

from pathlib import Path
import subprocess
import tempfile
import tomllib
import unittest
from unittest.mock import Mock, patch

import build_local_sequential as build


class PlanningTests(unittest.TestCase):
    def test_root_facade_adapter_ignores_body_comments(self):
        self.assertEqual(build.project_imports(
            "import Thesis\nimport Thesis.Probability.Core\n/-\nimport Thesis\n-/\n"),
            ["Thesis", "Thesis.Probability.Core"])
        with self.assertRaises(build.BuildStopped):
            build.project_imports("import Thesis.__SequentialRootFacade\n")

    def test_order_is_prerequisite_first_including_main_and_facade(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Thesis").mkdir()
            (root / "Thesis/Core.lean").write_text("import Std\n")
            (root / "Thesis.lean").write_text("import Thesis.Core\n")
            (root / "Main.lean").write_text("import Thesis\n")
            ordered, graph = build.ordered_modules(root, ["Main"])
            self.assertEqual(ordered, ["Thesis.Core", "Thesis", "Main"])
            self.assertEqual(graph["Main"], ["Thesis"])
            (root / "Thesis/Core.lean").write_text("import Thesis\n")
            with self.assertRaisesRegex(build.BuildStopped, "cyclic"):
                build.ordered_modules(root, ["Main"])

    def test_weak_resource_config_preserves_reviewed_package_configuration(self):
        root = Path(__file__).resolve().parents[1]
        original = (root / "lakefile.toml").read_text()
        limits = build.Limits(memory_mb=768, rss_mb=1024)
        resource_config = tomllib.loads(build.resource_configuration(original, limits))
        self.assertEqual(resource_config.pop("weakLeanArgs"), ["-j1", "-M768", "-DmaxErrors=1"])
        self.assertEqual(resource_config, tomllib.loads(original))
        self.assertEqual((root / "lakefile.toml").read_text(), original)

    def test_process_monitor_parses_only_process_metadata(self):
        with patch.object(build.subprocess, "run", return_value=subprocess.CompletedProcess(
                [], 0, "100 10 100 2048 /pinned/bin/lake\n101 100 100 4096 /pinned/bin/lean\n", "")):
            self.assertEqual(build.group_measurement(build.processes(), 100), (6, 1))

    def test_group_counts_clang_driver_and_frontend_as_one_family(self):
        snapshot = [build.Process(100, 10, 100, 2048, "lake"),
                    build.Process(101, 100, 100, 4096, "clang"),
                    build.Process(102, 101, 100, 8192, "clang-cc1"),
                    build.Process(200, 10, 200, 999999, "unrelated-editor")]
        self.assertEqual(build.group_measurement(snapshot, 100), (14, 1))
        snapshot.append(build.Process(103, 100, 100, 4096, "lean"))
        self.assertEqual(build.group_measurement(snapshot, 100)[1], 2)


class MonitorTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.log = self.root / "check.log"
        self.child = Mock(pid=100)
        self.child.poll.return_value = None
        self.child.wait.return_value = 0

    def run_group(self, snapshot):
        with patch.object(build, "processes", side_effect=snapshot), \
             patch.object(build.subprocess, "Popen", return_value=self.child), \
             patch.object(build, "kill_group") as kill:
            try:
                return build.run_group(["not-executed"], self.root, {}, build.Limits(), self.log), kill
            except build.BuildStopped:
                kill.assert_called_once_with(self.child)
                raise

    def test_monitor_unavailable_prevents_launch(self):
        with patch.object(build, "processes", side_effect=build.BuildStopped("no monitor")), \
             patch.object(build.subprocess, "Popen") as popen:
            with self.assertRaisesRegex(build.BuildStopped, "no monitor"):
                build.run_group(["never"], self.root, {}, build.Limits(), self.log)
            popen.assert_not_called()

    def test_child_memory_is_counted_not_only_lake(self):
        snapshot = [build.Process(100, 10, 100, 50 * 1024, "lake"),
                    build.Process(101, 100, 100, 750 * 1024, "lean")]
        with self.assertRaisesRegex(build.BuildStopped, "aggregate"):
            self.run_group([[], snapshot])

    def test_independent_compilers_stop_the_owned_group(self):
        snapshot = [build.Process(100, 10, 100, 1024, "lake"),
                    build.Process(101, 100, 100, 1024, "lean"),
                    build.Process(102, 100, 100, 1024, "lean")]
        with self.assertRaisesRegex(build.BuildStopped, "multiple compiler"):
            self.run_group([[], snapshot])

    def test_wall_timeout_is_not_labelled_as_memory_exhaustion(self):
        with patch.object(build.time, "monotonic", side_effect=[0, 31]):
            with self.assertRaisesRegex(build.BuildStopped, "wall-time.*not a memory"):
                self.run_group([[]])

    def test_orphan_after_launcher_exit_is_terminated(self):
        self.child.poll.return_value = 0
        snapshot = [build.Process(101, 1, 100, 1024, "lean")]
        with self.assertRaisesRegex(build.BuildStopped, "descendants"):
            self.run_group([[], snapshot])

    def test_completed_check_can_pass_without_leaving_processes(self):
        self.child.poll.return_value = 0
        result, kill = self.run_group([[], []])
        self.assertEqual(result["exit"], 0)
        kill.assert_not_called()


if __name__ == "__main__":
    unittest.main()
