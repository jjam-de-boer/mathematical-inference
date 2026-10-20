"""Full-builder orchestration safety; no test starts Lean or Lake.

Real end-to-end evidence must come from the actual full build and audit.
These small fixtures instead guard process-group accounting, serial ordering,
configuration isolation, and refusal paths before that real work is attempted.
"""

from contextlib import redirect_stdout
import io
from pathlib import Path
import shutil
import subprocess
import tempfile
import tomllib
import unittest
from unittest.mock import Mock, patch

import build_local_sequential as build


class PlanningTests(unittest.TestCase):
    def test_extended_profile_is_explicit_and_does_not_raise_small_helper_limits(self):
        build.SequentialLimits(memory_mb=4608, rss_mb=5120).validate()
        self.assertNotIn("extended", build.SMALL_MODULE_PROFILES)
        self.assertEqual(build.RESOURCE_PROFILES["ceiling"], (1024, 1280))
        with self.assertRaises(build.PilotError):
            build.Limits(memory_mb=4608, rss_mb=5120).validate()
        with self.assertRaises(build.PilotError):
            build.SequentialLimits(memory_mb=4608, rss_mb=5120, seconds=31).validate()
        with self.assertRaises(build.PilotError):
            build.SequentialLimits(memory_mb=5120, rss_mb=5632).validate()

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
        committed_config = tomllib.loads(original)
        committed_config.pop("weakLeanArgs")
        self.assertEqual(resource_config, committed_config)
        self.assertEqual((root / "lakefile.toml").read_text(), original)

    def test_resource_config_replaces_native_ceiling_without_duplicate_keys(self):
        original = ('name = "thesis"\nweakLeanArgs = ["-j1", "-M4608", "-DmaxErrors=1"]\n'
                    '[[lean_lib]]\nname = "Thesis"\n')
        conservative = build.Limits(memory_mb=640, rss_mb=768)
        result = build.resource_configuration(original, conservative)
        self.assertEqual(tomllib.loads(result)["weakLeanArgs"],
                         ["-j1", "-M640", "-DmaxErrors=1"])
        self.assertEqual(result.count("weakLeanArgs"), 1)

    def test_resource_config_rejects_ambiguous_resource_layout(self):
        for source in ('weakLeanArgs = [\n "-j1"\n]\n[[lean_lib]]\n',
                       'weakLeanArgs = []\nweakLeanArgs = []\n[[lean_lib]]\n'):
            with self.subTest(source=source), self.assertRaises(build.BuildStopped):
                build.resource_configuration(source, build.Limits())

    def test_main_build_only_dependency_precedes_intermediate_and_full_checks(self):
        self.assertEqual(build.lean_build_roots(), ["Thesis", "Main", "Thesis.AxiomAudit"])
        self.assertEqual(build.lean_build_roots(["Main"]), ["Thesis", "Main"])
        self.assertEqual(build.lean_build_roots(["Thesis.Core"]), ["Thesis.Core"])
        self.assertEqual(build.lean_build_roots(["Main", "Thesis"]), ["Thesis", "Main"])

    def test_main_fingerprints_and_preflights_proofs_without_runtime_linkage(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Thesis").mkdir()
            (root / "Thesis/Core.lean").write_text("import Std\n")
            (root / "Thesis.lean").write_text("import Thesis.Core\n")
            (root / "Main.lean").write_text("import Init.System.IO\n")
            # An edit anywhere in the checked facade must invalidate Main's
            # intermediate fingerprint scope, not start an unchecked rebuild.
            ordered, graph = build.ordered_modules(root, ["Main"], build_dependencies=True)
            self.assertEqual(ordered, ["Thesis.Core", "Thesis", "Main"])
            self.assertEqual(graph["Main"], ["Thesis"])
            self.assertEqual(build.prerequisite_scope(graph, "Main"), set(ordered))
            # Even an explicit intermediate native Main target must not
            # compile those build-only mathematical dependencies into objects.
            self.assertEqual(build.ordered_modules(root, ["Main"]), (["Main"], {"Main": []}))

    def test_intermediate_freshness_includes_prerequisites_not_unrelated_work(self):
        graph = {"Thesis.Core": [], "Thesis.Left": ["Thesis.Core"],
                 "Thesis.Right": ["Thesis.Core"], "Thesis": ["Thesis.Left", "Thesis.Right"]}
        self.assertEqual(build.prerequisite_scope(graph, "Thesis.Left"),
                         {"Thesis.Core", "Thesis.Left"})
        self.assertEqual(build.prerequisite_scope(graph, "Thesis"), set(graph))

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
        with patch.object(build.time, "monotonic", side_effect=[0, 31, 31]):
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


class FinalGateTests(unittest.TestCase):
    def invoke(self, arguments, effect=None):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve() / "project"
            (root / "tools").mkdir(parents=True)
            (root / "Thesis").mkdir()
            repository = Path(__file__).resolve().parents[1]
            for name in ("lakefile.toml", "lean-toolchain", "lake-manifest.json"):
                shutil.copyfile(repository / name, root / name)
            (root / "Main.lean").write_text("import Thesis\n")
            (root / "Thesis.lean").write_text("import Thesis.Core\n")
            (root / "Thesis/Core.lean").write_text("import Std\n")
            (root / "Thesis/AxiomAudit.lean").write_text("import Thesis\n")
            home = root / "home"
            release = (root / "lean-toolchain").read_text().strip().replace(":", "---").replace("/", "--")
            lake = home / ".elan/toolchains" / release / "bin/lake"
            lake.parent.mkdir(parents=True)
            lake.write_text("never executed")
            with patch.object(build, "__file__", str(root / "tools/build_local_sequential.py")), \
                 patch.object(build.Path, "home", return_value=home), \
                 patch.object(build.os, "nice"), \
                 patch.dict(build.os.environ, {"LEAN_PATH": "", "LEAN_SRC_PATH": ""}), \
                 patch("sys.argv", ["builder", *arguments]), \
                 patch.object(build, "run_group", side_effect=effect,
                              return_value={"exit": 0, "seconds": 0.1, "group_rss_mib": 1.0}) as run, \
                 redirect_stdout(io.StringIO()) as output:
                result = build.main()
            return result, run.call_args_list, output.getvalue()

    def test_stale_native_prerequisites_cannot_launch_a_final_build(self):
        result, calls, output = self.invoke(["--check", "--phase", "gates"],
                                           build.BuildStopped("stale native prerequisite"))
        self.assertEqual(result, 1)
        self.assertEqual(len(calls), 1)
        command = calls[0].args[0]
        self.assertIn("--no-build", command)
        self.assertIn("+Thesis.Core:c.o", command)
        self.assertIn("+Thesis:c.o", command)
        self.assertIn("+Main:c.o", command)
        self.assertNotIn("FULL LOCAL BUILD AND AXIOM AUDIT PASSED", output)

    def test_cached_chunk_uses_one_no_build_check_and_claims_only_its_phase(self):
        result, calls, output = self.invoke(["--check", "--phase", "lean"])
        self.assertEqual(result, 0)
        self.assertEqual(len(calls), 1)
        self.assertIn("--no-build", calls[0].args[0])
        self.assertEqual(sum(arg.startswith("+") for arg in calls[0].args[0]), 4)
        self.assertIn("full build and audit NOT established", output)

    def test_extended_cli_profile_reaches_only_the_bounded_runner(self):
        result, calls, output = self.invoke(["--check", "--phase", "lean", "--profile", "extended"])
        self.assertEqual(result, 0)
        limits = calls[0].args[3]
        self.assertEqual((limits.memory_mb, limits.rss_mb, limits.seconds), (4608, 5120, 30))
        self.assertIn("full build and audit NOT established", output)

    def test_stale_chunk_falls_back_to_checks_not_a_parallel_rebuild(self):
        def only_chunk_is_stale(command, *_):
            targets = [arg for arg in command if arg.startswith("+")]
            self.assertIn("--no-build", command)
            return {"exit": 3 if len(targets) > 1 else 0, "seconds": 0.1, "group_rss_mib": 1.0}
        result, calls, _ = self.invoke(["--check", "--phase", "lean"], only_chunk_is_stale)
        self.assertEqual(result, 0)
        self.assertEqual(len(calls), 5)

    def test_compilation_after_stale_chunk_selects_only_one_module(self):
        def stale(command, *_):
            return {"exit": 3 if "--no-build" in command else 0,
                    "seconds": 0.1, "group_rss_mib": 1.0}
        result, calls, output = self.invoke(["--check", "--phase", "lean", "--max-builds", "1"], stale)
        self.assertEqual(result, 2)
        compiled = [call.args[0] for call in calls if "--no-build" not in call.args[0]]
        self.assertEqual(len(compiled), 1)
        self.assertEqual([arg for arg in compiled[0] if arg.startswith("+")], ["+Thesis.Core:olean"])
        self.assertIn("Checkpoint only", output)

    def test_final_success_requires_both_actual_original_configuration_gates(self):
        result, calls, output = self.invoke(["--check", "--phase", "gates"])
        self.assertEqual(result, 0)
        self.assertEqual(len(calls), 6)
        for call in (calls[3], calls[5]):
            self.assertNotIn("--file", call.args[0])
            self.assertNotIn("--no-build", call.args[0])
        self.assertEqual(calls[3].args[0][-1], "build")
        self.assertEqual(calls[5].args[0][-2:], ["build", "Thesis.AxiomAudit"])
        self.assertIn("FULL LOCAL BUILD AND AXIOM AUDIT PASSED", output)

    def test_failed_actual_axiom_gate_cannot_claim_success(self):
        def fail_audit(command, *_):
            if command[-2:] == ["build", "Thesis.AxiomAudit"] and "--no-build" not in command:
                raise build.BuildStopped("axiom gate failed")
            return {"exit": 0, "seconds": 0.1, "group_rss_mib": 1.0}
        result, _, output = self.invoke(["--check", "--phase", "gates"], fail_audit)
        self.assertEqual(result, 1)
        self.assertNotIn("FULL LOCAL BUILD AND AXIOM AUDIT PASSED", output)


if __name__ == "__main__":
    unittest.main()
