"""Preserve the lightweight law/support boundary and the moved declarations.

Dependency tests explain the extraction; they are not mathematical proofs.
The source hashes additionally protect the exact original declaration blocks
from baseline f298629, including proof bodies. Ordinary Lake and the complete
transitive axiom audit remain mandatory for the resulting source revision.
"""

import hashlib
from pathlib import Path
import unittest

from test_example_coverage import initial_project_imports, reachable


class ProbabilityLayerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(__file__).resolve().parents[1]
        paths = [cls.root / "Thesis.lean", *(cls.root / "Thesis").rglob("*.lean")]
        cls.graph = {".".join(path.relative_to(cls.root).with_suffix("").parts):
                     initial_project_imports(path.read_text()) for path in paths}
        cls.prefix = "Thesis.Probability.Distros."

    def test_law_basics_stays_below_specialized_distribution_results(self):
        dependencies = reachable(self.graph, self.prefix + "LawBasics")
        for name in ("Moments", "LawEquivalence", "SignedCovariance", "Concentration",
                     "SignedConcentration", "Entropy"):
            with self.subTest(name=name):
                self.assertNotIn(self.prefix + name, dependencies)

    def test_entropy_does_not_reimport_moments_or_concentration_for_support(self):
        dependencies = reachable(self.graph, self.prefix + "Entropy")
        self.assertIn(self.prefix + "LawBasics", dependencies)
        for name in ("Moments", "SignedCovariance", "Concentration", "SignedConcentration"):
            with self.subTest(name=name):
                self.assertNotIn(self.prefix + name, dependencies)

    def test_old_imports_reexport_the_existing_public_interfaces(self):
        for old in ("LawEquivalence", "SignedConcentration"):
            with self.subTest(old=old):
                self.assertIn(self.prefix + "LawBasics", reachable(self.graph, self.prefix + old))

    def test_extracted_definitions_and_proof_bodies_are_unchanged(self):
        source = (self.root / "Thesis/Probability/Distros/LawBasics.lean").read_text()
        equality = source[source.index("/-- Agreement of all Boolean"):
                          source.index("/-- Almost-sure statements")].rstrip()
        support = source[source.index("/-- Almost-sure statements"):
                         source.index("end Thesis.Probability.Distros")].rstrip()
        self.assertEqual(hashlib.sha256(equality.encode()).hexdigest(),
                         "7dc6fb1ddc57973895f61876b8d8040b466851aee523e942d90e8dc45e5fb4e0")
        self.assertEqual(hashlib.sha256(support.encode()).hexdigest(),
                         "ae724d2b7c6b8538a775adb440fc1be6096279e485e27dfe6e5d38403d6a9ec2")

    def test_new_foundations_remain_inside_the_complete_axiom_audit(self):
        self.assertIn(self.prefix + "LawBasics", reachable(self.graph, "Thesis.AxiomAudit"))


if __name__ == "__main__":
    unittest.main()
