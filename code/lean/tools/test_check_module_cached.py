"""Safety regressions for the local helper; these tests never invoke Lean.

The fixtures use disposable source/cache trees and fake monitored children.
They check refusal paths as well as successful planning: a stale or missing
dependency, unsupported configuration, or unavailable resource monitor must
never become permission to launch an unbounded project build.
"""

import json
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

import check_module_cached as pilot


class PlanningTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def source(self, module, contents):
        path = pilot.source_path(self.root, module)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(contents)
        return path

    def test_dependency_order_and_shared_import(self):
        self.source("Thesis.Core", "import Std\nnamespace Thesis\nend Thesis\n")
        self.source("Thesis.Left", "import Thesis.Core\n")
        self.source("Thesis.Right", "import Thesis.Core\nimport Thesis.Left\n")
        self.assertEqual(pilot.closure(self.root, ["Thesis.Right"], pilot.Limits()),
                         ["Thesis.Core", "Thesis.Left", "Thesis.Right"])

    def test_reject_cycle(self):
        self.source("Thesis.Left", "import Thesis.Right\n")
        self.source("Thesis.Right", "import Thesis.Left\n")
        with self.assertRaisesRegex(pilot.PilotError, "cyclic"):
            pilot.closure(self.root, ["Thesis.Left"], pilot.Limits())

    def test_reject_large_closure_and_large_source(self):
        self.source("Thesis.Core", "import Std\n")
        source = self.source("Thesis.Client", "import Thesis.Core\n")
        with self.assertRaisesRegex(pilot.PilotError, "closure"):
            pilot.closure(self.root, ["Thesis.Client"], pilot.Limits(max_modules=1))
        source.write_text("x" * (128 * 1024 + 1))
        with self.assertRaisesRegex(pilot.PilotError, "128 KiB"):
            pilot.closure(self.root, ["Thesis.Client"], pilot.Limits())

    def test_reject_unsupported_headers_and_external_packages(self):
        for source in ("public import Thesis.Core\n", "import Mathlib\n",
                       "namespace Thesis\nimport Thesis.Core\n", "module\n"):
            with self.subTest(source=source), self.assertRaises(pilot.PilotError):
                pilot.imports(source)

    def test_comments_and_strings_cannot_masquerade_as_import_headers(self):
        source = ('/- leading /- nested -/ comment -/\nimport Thesis.Core -- dependency\n'
                  'namespace Thesis\n/-!\nmodule prose is not a module header\n'
                  'import Mathlib\n-/\ndef message := "/- not a comment"\n'
                  'def quoted := "escaped \\" quote"\nend Thesis\n')
        self.assertEqual(pilot.imports(source), ["Thesis.Core"])
        for contents in ("/- unterminated", 'def text := "unterminated'):
            with self.subTest(contents=contents), self.assertRaises(pilot.PilotError):
                pilot.imports(contents)

    def test_module_names_cannot_escape_source_tree(self):
        for name in ("../Core", "Thesis..Core", "Thesis.Core;echo", "Other.Core"):
            with self.subTest(name=name), self.assertRaises(pilot.PilotError):
                pilot.source_path(self.root, name)

    def test_source_symlinks_are_refused(self):
        target = self.source("Thesis.Core", "import Std\n")
        alias = pilot.source_path(self.root, "Thesis.Alias")
        alias.symlink_to(target)
        with self.assertRaisesRegex(pilot.PilotError, "symbolic-link"):
            pilot.closure(self.root, ["Thesis.Alias"], pilot.Limits())

    def test_limits_cannot_silently_expand(self):
        for limits in (pilot.Limits(seconds=61), pilot.Limits(memory_mb=1025),
                       pilot.Limits(rss_mb=1281), pilot.Limits(max_modules=9),
                       pilot.Limits(max_selected=4), pilot.Limits(memory_mb=768, rss_mb=768)):
            with self.subTest(limits=limits), self.assertRaises(pilot.PilotError):
                limits.validate()

    def test_explicit_memory_trial_does_not_raise_defaults_or_rss_ceiling(self):
        # Raising the hard accepted ceiling does not promote the default
        # conservative pair or permit concurrent compiler processes.
        trial = pilot.Limits(memory_mb=1024, rss_mb=1280)
        trial.validate()
        self.assertEqual(pilot.Limits().memory_mb, 640)
        self.assertEqual(pilot.Limits().rss_mb, 768)
        self.assertEqual(trial.max_selected, 1)

    def test_named_profiles_and_legacy_explicit_overrides(self):
        for name, pair in (("conservative", (640, 768)), ("pilot", (768, 1024)),
                           ("ceiling", (1024, 1280))):
            args = SimpleNamespace(profile=name, memory_mb=None, rss_mb=None,
                                   seconds=30, max_modules=6, max_selected=1)
            resolved = pilot.resolve_limits(args)
            self.assertEqual((resolved.memory_mb, resolved.rss_mb), pair)
            args.memory_mb = 512
            self.assertEqual(pilot.resolve_limits(args).memory_mb, 512)

    def test_configuration_rejects_extra_hooks(self):
        (self.root / "lakefile.toml").write_text('name = "thesis"\n')
        with self.assertRaisesRegex(pilot.PilotError, "configuration"):
            pilot.check_configuration(self.root)

    def test_missing_cache_does_not_rebuild(self):
        with self.assertRaisesRegex(pilot.PilotError, "no reusable local trace"):
            pilot.copy_dependencies(self.root, self.root / "copy", ["Thesis.Core"])

    def test_artifacts_are_copies_without_hash_sidecars(self):
        paths = pilot.cache_paths("Thesis.Core")
        for relative in paths:
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps({"synthetic": False, "outputs": {"m": False}})
                            if path.suffix == ".trace" else "original")
        destination = self.root / "copy"
        pilot.copy_dependencies(self.root, destination, ["Thesis.Core"])
        (destination / paths[0]).write_text("changed copy")
        self.assertEqual((self.root / paths[0]).read_text(), "original")
        self.assertFalse((destination / paths[0].with_suffix(".olean.hash")).exists())

    def test_synthetic_cache_is_not_accepted(self):
        trace = self.root / pilot.cache_paths("Thesis.Core")[2]
        trace.parent.mkdir(parents=True)
        trace.write_text(json.dumps({"synthetic": True, "outputs": {"m": False}}))
        with self.assertRaisesRegex(pilot.PilotError, "synthetic"):
            pilot.copy_dependencies(self.root, self.root / "copy", ["Thesis.Core"])


class MonitorTests(unittest.TestCase):
    @patch.object(pilot.subprocess, "Popen")
    @patch.object(pilot, "rss_mib", side_effect=pilot.PilotError("no monitor"))
    def test_missing_monitor_prevents_launch(self, _rss, popen):
        with self.assertRaisesRegex(pilot.PilotError, "no monitor"):
            pilot.run_capped(["never-launched"], Path("."), {}, pilot.Limits())
        popen.assert_not_called()

    @patch.object(pilot, "terminate")
    @patch.object(pilot.subprocess, "Popen")
    @patch.object(pilot, "rss_mib", side_effect=[1.0, 800.0])
    def test_rss_limit_terminates_only_pilot_child(self, _rss, popen, terminate):
        child = Mock(pid=12345)
        child.poll.return_value = None
        popen.return_value = child
        with self.assertRaisesRegex(pilot.PilotError, "RSS limit"):
            pilot.run_capped(["fake"], Path("."), {}, pilot.Limits())
        terminate.assert_called_once_with(child)

    @patch.object(pilot, "terminate")
    @patch.object(pilot.subprocess, "Popen")
    @patch.object(pilot, "rss_mib", return_value=1.0)
    @patch.object(pilot.time, "monotonic", side_effect=[0, 31])
    def test_wall_limit_terminates_child(self, _time, _rss, popen, terminate):
        child = Mock(pid=12345)
        child.poll.return_value = None
        popen.return_value = child
        with self.assertRaisesRegex(pilot.PilotError, "wall-time"):
            pilot.run_capped(["fake"], Path("."), {}, pilot.Limits())
        terminate.assert_called_once_with(child)

    @patch.object(pilot.subprocess, "Popen")
    @patch.object(pilot, "rss_mib", return_value=1.0)
    @patch("builtins.print")
    def test_failed_child_is_not_retried_at_a_larger_profile(self, _print, _rss, popen):
        child = Mock(pid=12345)
        child.poll.return_value = 1
        child.wait.return_value = 1
        popen.return_value = child
        with self.assertRaisesRegex(pilot.PilotError, "child failed"):
            pilot.run_capped(["fake", "-M640"], Path("."), {}, pilot.Limits())
        popen.assert_called_once()

    @patch.object(pilot.subprocess, "run")
    def test_sampler_fails_closed(self, run):
        run.return_value = subprocess.CompletedProcess([], 1, "", "permission denied")
        with self.assertRaisesRegex(pilot.PilotError, "unavailable"):
            pilot.rss_mib(12345)

    @patch.object(pilot.subprocess, "run")
    def test_sampler_converts_kib_to_mib(self, run):
        run.return_value = subprocess.CompletedProcess([], 0, " 10240\n", "")
        self.assertEqual(pilot.rss_mib(12345), 10)


if __name__ == "__main__":
    unittest.main()
