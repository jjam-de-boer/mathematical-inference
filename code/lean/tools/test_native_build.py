"""Keep proof checking separate from the smoke executable's runtime imports.

The executable merely prints a success message. Its explicit Lake prerequisite
must still check the complete public facade, but linking the executable must
not turn every proof-library definition and regression into a native object.
These inexpensive structural tests protect both sides of that boundary; the
actual Lake build and complete axiom audit remain the proof-verification gates.
"""

from pathlib import Path
import tomllib
import unittest

from test_example_coverage import initial_project_imports, reachable


class NativeBuildTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(__file__).resolve().parents[1]
        cls.config = tomllib.loads((cls.root / "lakefile.toml").read_text())

    def test_existing_default_command_still_checks_the_complete_facade(self):
        # A small binary alone is not a successful project build. The explicit
        # prerequisite retains the old proof closure even without an import
        # edge from Main into every example and mathematical construction.
        self.assertEqual(self.config["defaultTargets"], ["thesis"])
        self.assertEqual(self.config["lean_lib"], [{"name": "Thesis"}])
        self.assertEqual(self.config["lean_exe"], [
            {"name": "thesis", "root": "Main", "needs": ["Thesis"]}])

    def test_smoke_binary_has_no_project_runtime_imports(self):
        source = (self.root / "Main.lean").read_text()
        self.assertEqual(initial_project_imports(source), [])
        self.assertIn('IO.println "Thesis formalization compiled."', source)
        self.assertIn("import Init.System.IO", source)

    def test_native_compiler_arguments_keep_the_reviewed_memory_threshold(self):
        # These are per-compiler limits, not an aggregate watchdog or a Lake
        # scheduler setting. The documented native route also sets Lake's
        # LEAN_NUM_THREADS=1; the monitored helper remains available separately.
        self.assertEqual(self.config["weakLeanArgs"],
                         ["-j1", "-M4608", "-DmaxErrors=1"])

    def test_axiom_audit_still_reaches_the_entire_default_proof_closure(self):
        sources = [self.root / "Thesis.lean", *(self.root / "Thesis").rglob("*.lean")]
        graph = {".".join(source.relative_to(self.root).with_suffix("").parts):
                 initial_project_imports(source.read_text()) for source in sources}
        self.assertTrue(reachable(graph, "Thesis") <= reachable(graph, "Thesis.AxiomAudit"))


if __name__ == "__main__":
    unittest.main()
