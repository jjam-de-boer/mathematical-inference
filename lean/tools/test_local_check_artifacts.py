"""Exercise retained-artifact integrity and invalidation without invoking Lean.

Fake artifact bytes here test cache policy, not mathematical correctness. In
particular a modified source, prerequisite, compiler profile or artifact must
never acquire the status of a reusable successful check by accident.
"""

from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import local_check_artifacts as artifacts


class ArtifactTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.store = artifacts.ArtifactStore(self.root)
        self.output = self.root / "output.olean"
        self.output.write_bytes(b"fake successful compiler output")
        self.key = "a" * 64

    def test_publish_and_importable_copy_preserve_original_output(self):
        with artifacts.exclusive_check(self.root):
            saved = self.store.publish("Thesis.Client", self.key, self.output)
            self.assertEqual(saved.read_bytes(), self.output.read_bytes())
            self.assertEqual(self.store.load("Thesis.Client", self.key), saved)
        self.assertIsNone(self.store.load("Thesis.Client", "b" * 64))
        self.assertTrue(self.output.is_file())

    def test_changed_artifact_is_not_trusted(self):
        saved = self.store.publish("Thesis.Client", self.key, self.output)
        saved.write_bytes(b"modified")
        with self.assertRaisesRegex(artifacts.ArtifactError, "changed"):
            self.store.load("Thesis.Client", self.key)

    def test_partial_publish_and_invalid_manifest_are_refused(self):
        self.store.publish("Thesis.Client", self.key, self.output)
        manifest = self.store.entry("Thesis.Client", self.key) / "checked.json"
        manifest.write_text("not json")
        with self.assertRaisesRegex(artifacts.ArtifactError, "invalid"):
            self.store.load("Thesis.Client", self.key)
        manifest.unlink()
        with self.assertRaisesRegex(artifacts.ArtifactError, "incomplete"):
            self.store.load("Thesis.Client", self.key)

    def test_successful_entry_survives_a_later_module_failure(self):
        self.store.publish("Thesis.First", self.key, self.output)
        # No publication call occurs for the failing second compiler. The
        # first result remains usable; no second result is invented.
        self.assertIsNotNone(self.store.load("Thesis.First", self.key))
        self.assertIsNone(self.store.load("Thesis.Second", self.key))

    def test_republishing_completed_output_repairs_an_interrupted_entry(self):
        saved = self.store.publish("Thesis.Client", self.key, self.output)
        saved.write_bytes(b"interrupted replacement")
        self.store.publish("Thesis.Client", self.key, self.output)
        self.assertEqual(self.store.load("Thesis.Client", self.key).read_bytes(), self.output.read_bytes())

    def test_names_and_keys_cannot_escape_store(self):
        for module, key in (("Thesis../escape", self.key), ("Thesis.Client", "../escape")):
            with self.subTest(module=module), self.assertRaises(artifacts.ArtifactError):
                self.store.load(module, key)

    def test_cache_directory_and_artifact_symlinks_are_refused(self):
        (self.store.directory / "Thesis").symlink_to(self.root, target_is_directory=True)
        with self.assertRaisesRegex(artifacts.ArtifactError, "symbolic-link"):
            self.store.publish("Thesis.Client", self.key, self.output)

    def test_artifact_symlink_is_refused(self):
        saved = self.store.publish("Thesis.Client", self.key, self.output)
        saved.unlink()
        saved.symlink_to(self.output)
        with self.assertRaisesRegex(artifacts.ArtifactError, "incomplete"):
            self.store.load("Thesis.Client", self.key)

    def test_unbounded_manifest_is_refused_before_json_parsing(self):
        self.store.publish("Thesis.Client", self.key, self.output)
        manifest = self.store.entry("Thesis.Client", self.key) / "checked.json"
        manifest.write_text(" " * 4097)
        with self.assertRaisesRegex(artifacts.ArtifactError, "bounded format"):
            self.store.load("Thesis.Client", self.key)

    @patch.object(artifacts.fcntl, "flock", side_effect=BlockingIOError)
    def test_busy_os_lock_refuses_second_check(self, _flock):
        with self.assertRaisesRegex(artifacts.ArtifactError, "compiler slot"):
            with artifacts.exclusive_check(self.root):
                self.fail("a busy compiler slot must never run work")

    def test_lock_is_released_after_failure(self):
        with self.assertRaisesRegex(RuntimeError, "fixture"):
            with artifacts.exclusive_check(self.root):
                raise RuntimeError("fixture")
        with artifacts.exclusive_check(self.root):
            pass


class KeyTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        root = Path(self.temporary.name)
        self.sources = {name: root / (name + ".lean") for name in ("Thesis.Base", "Thesis.Client", "Thesis.Other")}
        for name, source in self.sources.items():
            source.write_text(name)
        self.dependencies = {"Thesis.Base": [], "Thesis.Client": ["Thesis.Base"], "Thesis.Other": []}

    def keys(self, configuration=None, identity=None, arguments=None):
        return artifacts.module_keys(list(self.sources), self.sources, self.dependencies,
            configuration or {"config": "checked"}, identity or {"compiler": "pinned"},
            arguments or ["-j1", "-M640"])

    def test_prerequisite_edit_invalidates_dependents_not_unrelated_modules(self):
        before = self.keys()
        self.sources["Thesis.Base"].write_text("changed base")
        after = self.keys()
        self.assertNotEqual(before["Thesis.Base"], after["Thesis.Base"])
        self.assertNotEqual(before["Thesis.Client"], after["Thesis.Client"])
        self.assertEqual(before["Thesis.Other"], after["Thesis.Other"])

    def test_source_configuration_toolchain_and_arguments_are_actual_inputs(self):
        baseline = self.keys()
        for changed in (self.keys(configuration={"config": "different"}),
                        self.keys(identity={"compiler": "different"}),
                        self.keys(arguments=["-j1", "-M384"])):
            self.assertNotEqual(baseline["Thesis.Client"], changed["Thesis.Client"])
        self.sources["Thesis.Client"].write_text("changed client")
        self.assertNotEqual(baseline["Thesis.Client"], self.keys()["Thesis.Client"])

    def test_no_synthetic_lake_trace_for_retained_dependencies(self):
        self.assertEqual(artifacts.ordinary_dependencies(self.dependencies, {"Thesis.Client": "artifact"}),
                         ["Thesis.Base", "Thesis.Other"])
        with self.assertRaisesRegex(artifacts.ArtifactError, "select the cached client"):
            artifacts.ordinary_dependencies(self.dependencies, {"Thesis.Base": "artifact"})


if __name__ == "__main__":
    unittest.main()
