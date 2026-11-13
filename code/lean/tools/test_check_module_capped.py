"""Exercise the fresh checker's integration without starting a Lean process.

The fresh and cache-aware paths must share the same monitor and compiler-slot
policy. Mocked compilation here tests orchestration/refusal, not Lean proofs;
actual compiler results remain separate evidence in the build logs.
"""

from contextlib import nullcontext, redirect_stdout
import io
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import check_module_cached as cached
import check_module_capped as fresh


class FreshCheckerTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name).resolve() / "project"
        (self.root / "tools").mkdir(parents=True)
        repository = Path(__file__).resolve().parents[1]
        for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
            shutil.copyfile(repository / name, self.root / name)
        self.core = self.root / "Thesis/Core.lean"
        self.core.parent.mkdir()
        self.core.write_text("import Std\nnamespace Thesis\nend Thesis\n")
        (self.root / "Thesis/Client.lean").write_text("import Thesis.Core\n")
        self.home = Path(self.directory.name) / "home"
        release = (self.root / "lean-toolchain").read_text().strip().replace(":", "---").replace("/", "--")
        compiler = self.home / ".elan/toolchains" / release / "bin/lean"
        compiler.parent.mkdir(parents=True)
        compiler.write_text("not executed: compilation is mocked")

    def invoke(self, *options, effect=None):
        with patch.object(fresh, "__file__", str(self.root / "tools/check_module_capped.py")), \
             patch.object(fresh.Path, "home", return_value=self.home), \
             patch.dict(fresh.os.environ, {"LEAN_PATH": "", "LEAN_SRC_PATH": ""}), \
             patch("sys.argv", ["check_module_capped.py", "Thesis.Client", *options]), \
             patch.object(fresh.os, "nice"), \
             patch.object(fresh, "exclusive_check", return_value=nullcontext()) as lock, \
             patch.object(fresh, "run_capped", side_effect=effect) as run, \
             redirect_stdout(io.StringIO()) as output:
            result = fresh.main()
        return result, run, lock, output.getvalue()

    def test_resource_monitor_and_lock_are_shared(self):
        for name in ("run_capped", "exclusive_check", "resolve_limits", "RESOURCE_PROFILES"):
            self.assertIs(getattr(fresh, name), getattr(cached, name))

    def test_plan_launches_nothing_and_creates_no_cache(self):
        result, run, lock, output = self.invoke("--profile", "ceiling", "--plan")
        self.assertEqual(result, 0)
        run.assert_not_called()
        lock.assert_not_called()
        self.assertFalse((self.root / ".lake").exists())
        self.assertIn("Lean=1024 MiB; sampled RSS=1280 MiB", output)

    def test_oversized_limit_refuses_before_launch(self):
        result, run, lock, _ = self.invoke("--memory-mb", "1025")
        self.assertEqual(result, 1)
        run.assert_not_called()
        lock.assert_not_called()

    def test_fresh_closure_uses_snapshot_and_selected_profile_sequentially(self):
        result, run, lock, output = self.invoke("--profile", "pilot")
        self.assertEqual(result, 0)
        self.assertEqual(run.call_count, 2)
        lock.assert_called_once_with(self.root)
        for call in run.call_args_list:
            command, temporary, environment, limits = call.args
            self.assertIn("-j1", command)
            self.assertIn("-M768", command)
            self.assertEqual((limits.rss_mb, limits.seconds), (1024, 30))
            self.assertNotEqual(temporary, self.root)
            self.assertTrue(str(command[-1]).startswith(str(temporary)))
            self.assertNotIn(str(self.root / ".lake"), environment["LEAN_PATH"])
        self.assertIn("outputs discarded", output)
        self.assertFalse((self.root / ".lake").exists())

    def test_failed_prerequisite_stops_without_retry_or_success_claim(self):
        result, run, _, output = self.invoke(effect=cached.PilotError("child failed"))
        self.assertEqual(result, 1)
        run.assert_called_once()
        self.assertNotIn("Fresh closure checked", output)

    def test_concurrent_source_edit_invalidates_success(self):
        def mutate_source(*_):
            self.core.write_text("import Std\n-- concurrent edit\n")
        result, _, _, output = self.invoke(effect=mutate_source)
        self.assertEqual(result, 1)
        self.assertIn("sources changed", output)
        self.assertNotIn("Fresh closure checked", output)


if __name__ == "__main__":
    unittest.main()
