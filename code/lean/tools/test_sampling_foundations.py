"""Protect general sampling facts below the specialized urn developments.

Exact hashes retain the original statement/proof bodies from 1ab81d2. The
positive-witness wrapper delegates to the existing general support theorem;
current clients use that theorem rather than its historical distro spelling.
Import checks deliberately allow genuine reinforced-moment mathematics used
in hypergeometric proofs. They do not ban reuse between distribution families.
"""

import hashlib
from pathlib import Path
import unittest

from test_example_coverage import initial_project_imports, reachable


class SamplingFoundationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(__file__).resolve().parents[1]
        cls.graph = {".".join(path.relative_to(cls.root).with_suffix("").parts):
                     initial_project_imports(path.read_text())
                     for path in (cls.root / "Thesis").rglob("*.lean")}
        cls.prefix = "Thesis.Probability.Distros."

    def source(self, module):
        return (self.root / (module.replace(".", "/") + ".lean")).read_text()

    def test_original_general_proofs_are_preserved(self):
        hashes = {
            "sum_modify_add": "5409665b19ee950fab8ad0fa898c7895226d23d233d9703cb0d47cb7fc73a6e5",
            "modify_add_comm": "f025274a867e33189fad7cff655bcec381ad80b27e7a93457f281606d384e9ee",
            "modify_add_zero": "9cdf25aba436ed433508f7b2f7ba8443c790e4286b2bd40504e69b02bb667933",
            "colourCounts_sum": "58030f6d1031e7ff7ec597e22c14af987e995ba9bd4a7f8aae96494d47edd96a",
            "colourCounts_perm": "9cf8a6d3cf6b80ca5d6a0644968eb5988f1096e73497d8ed7eefe1c75915398f",
            "categorical_head_select": "6999fb15166cd7ce8ef1ccfb5a7bf32f0e2ddc3ee3740d10d8193be595fdf28b",
        }
        source = self.source(self.prefix + "CategoricalSampling")
        for name, expected in hashes.items():
            with self.subTest(name=name):
                start = source.index("theorem " + name + " ")
                block = source[start:source.index("\n\n", start)]
                self.assertEqual(hashlib.sha256(block.encode()).hexdigest(), expected)
        sums = self.source("Thesis.Probability.FiniteRecordSums")
        start = sums.index("theorem eventMass_factor_sum ")
        block = sums[start:sums.index("\n\n", start)]
        self.assertEqual(hashlib.sha256(block.encode()).hexdigest(),
                         "d6525fd8eb12d582a7ee9094ad5812e5901436da0f840d85439ff4242f3e6245")
        aggregation = self.source(self.prefix + "CategoricalAggregation")
        for name, expected in {
                "aggregateCounts_zeros": "cc4e3f0dea79b16ff8fac87e1b107a524952ae7fadc8e0083b315532935360ca",
                "aggregateCounts_colourCounts": "13d08be16c3989b1a988cc4871ef520f9b83cddc588087cd764ff0094825db95"}.items():
            with self.subTest(name=name):
                start = aggregation.index("theorem " + name + " ")
                block = aggregation[start:aggregation.index("\n\n", start)]
                self.assertEqual(hashlib.sha256(block.encode()).hexdigest(), expected)

    def test_general_owners_avoid_specialized_urns_and_remain_audited(self):
        audited = reachable(self.graph, "Thesis.AxiomAudit")
        for module in (self.prefix + "CategoricalSampling", "Thesis.Probability.FiniteRecordSums"):
            with self.subTest(module=module):
                self.assertIn(module, audited)
                dependencies = reachable(self.graph, module)
                self.assertFalse(any(".Reinforced" in name or ".Depleting" in name for name in dependencies))

    def test_depleting_clients_do_not_import_reinforced_history_for_general_facts(self):
        unnecessary = {self.prefix + name for name in ("ReinforcedAggregation", "ReinforcedHistory",
                       "ReinforcedConditioning", "ReinforcedExchangeability", "ReinforcedUpdates")}
        for module in self.graph:
            if module.startswith(self.prefix + "Depleting"):
                with self.subTest(module=module):
                    self.assertFalse(reachable(self.graph, module) & unnecessary)
                    source = self.source(module)
                    self.assertNotIn("rcases eventMass_positive_witness ", source)
                    self.assertNotIn("exact eventMass_factor_sum ", source)
        # This is valid reuse of a factorial-moment theorem, not an accidental
        # path through a general positivity/count helper in an urn history.
        self.assertIn(self.prefix + "ReinforcedMoments",
                      reachable(self.graph, self.prefix + "DepletingUrn"))

    def test_original_defining_imports_reexport_the_moved_results(self):
        owner = self.prefix + "CategoricalSampling"
        for old in ("MultinomialAggregation", "CategoricalAggregation", "ReinforcedUrn", "ReinforcedUpdates",
                    "ReinforcedExchangeability"):
            self.assertIn(owner, reachable(self.graph, self.prefix + old))
        conditioning = self.source(self.prefix + "ReinforcedConditioning")
        self.assertIn("theorem eventMass_factor_sum ", conditioning)
        self.assertIn("FiniteProbRecord.eventMass_factor_sum atoms evidence factor", conditioning)
        updates = self.source(self.prefix + "ReinforcedUpdates")
        self.assertIn("theorem eventMass_positive_witness ", updates)
        self.assertIn("(FiniteProbRecord.eventMass_pos_iff_exists_atom atoms event).mp positive", updates)
        self.assertIn(self.prefix + "CategoricalAggregation",
                      reachable(self.graph, self.prefix + "ReinforcedAggregation"))


if __name__ == "__main__":
    unittest.main()
