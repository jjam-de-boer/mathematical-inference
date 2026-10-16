"""Protect the small graph layer from reimporting historical proof machinery.

This is a source-dependency regression, not proof verification. The complete
Lean build and transitive axiom audit still check every moved theorem. These
tests only guard the dependency boundary that motivates the extraction.
"""

from pathlib import Path
import unittest

from test_example_coverage import initial_project_imports, reachable


class IdentificationLayerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        root = Path(__file__).resolve().parents[1]
        cls.graph = {".".join(source.relative_to(root).with_suffix("").parts):
                     initial_project_imports(source.read_text())
                     for source in (root / "Thesis").rglob("*.lean")}

    def test_intrinsic_layers_do_not_import_transport_or_legacy(self):
        for module in ("Thesis.Causality.ReachabilityCorrectness", "Thesis.Causality.ComponentConnectivity",
                       "Thesis.Causality.IdentificationRank"):
            with self.subTest(module=module):
                dependencies = reachable(self.graph, module)
                forbidden = sorted(name for name in dependencies if
                                   name.startswith(("Thesis.CausalTransport.", "Thesis.Causality.Legacy.")))
                self.assertFalse(forbidden, "Intrinsic graph layer imports: " + ", ".join(forbidden))

    def test_current_clients_do_not_reimport_completeness_or_legacy(self):
        for module in ("Thesis.CausalTransport.KernelIdentification", "Thesis.CausalTransport.KernelSeparation"):
            with self.subTest(module=module):
                dependencies = reachable(self.graph, module)
                self.assertNotIn("Thesis.CausalTransport.Completeness", dependencies)
                self.assertFalse(any(name.startswith("Thesis.Causality.Legacy.") for name in dependencies))


if __name__ == "__main__":
    unittest.main()
