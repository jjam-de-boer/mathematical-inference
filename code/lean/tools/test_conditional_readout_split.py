"""Keep the expensive graph checks separate without weakening the regression.

The original six-node readout fixture exceeded the 30-second local invocation
limit. Its independent graph computations now have separate module boundaries;
the original semantic/routing assertions and all finite evaluations remain.
These source guards do not replace the complete Lean build or axiom audit.
"""

import hashlib
from pathlib import Path
import re
import unittest

from test_example_coverage import initial_project_imports, reachable


class ConditionalReadoutSplitTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(__file__).resolve().parents[1]
        paths = [cls.root / "Thesis.lean", *(cls.root / "Thesis").rglob("*.lean")]
        cls.graph = {".".join(path.relative_to(cls.root).with_suffix("").parts):
                     initial_project_imports(path.read_text()) for path in paths}
        cls.prefix = "Thesis.Examples.HedgeConditionalReadout"

    def source(self, name):
        return (self.root / (name.replace(".", "/") + ".lean")).read_text()

    def test_bounded_pilots_preserve_every_fixture_assertion(self):
        # Pilot one found no speedup and was restored byte-for-byte. Pilot two
        # changes only the proof of the same literal engine assertion; in
        # particular no positive SCM, third-label or support assertion is lost.
        first = self.source("Thesis.Examples.HedgeConditionalLatentCollider")
        self.assertEqual(hashlib.sha256(first.encode()).hexdigest(),
                         "bc0af8b35774a7aefa06e5f7bccccaa0126e3534187047e9e2a4e7940f56f9e7")
        second = self.source("Thesis.Examples.HedgeConditionalCompensatedReadout")
        start = second.index("/-- The conditional program's terminal branch")
        end = second.index("\n\nend HedgeConditionalProtectedReentry", start)
        block = second[start:end]
        self.assertEqual(hashlib.sha256(block.encode()).hexdigest(),
                         "561304d2f9c8a6c2f286427161eb6c790dc3057fd6bb51b320f5258b7ce6f30a")
        original = ("theorem conditional_program_failed : failed "
                    "(identifyConditionalKernel graph query) = true := by decide +kernel")
        restored = second[:start] + original + second[end:]
        self.assertEqual(hashlib.sha256(restored.encode()).hexdigest(),
                         "fe701be89414b55c2dfda53e1aaf903b6c7fb821b592d02c352a78ae448ba5c8")

    def test_graph_checks_stay_below_semantic_transport_and_remain_audited(self):
        expected = {"Graph": ["Thesis.Causality.ConditionalIdentificationKernel"],
                    "Exchange": [self.prefix + ".Graph"],
                    "Failure": [self.prefix + ".Exchange"]}
        covered = reachable(self.graph, "Thesis.AxiomAudit")
        for part, imports in expected.items():
            module = self.prefix + "." + part
            with self.subTest(part=part):
                self.assertEqual(self.graph[module], imports)
                dependencies = reachable(self.graph, module)
                self.assertNotIn(self.prefix, dependencies)
                self.assertFalse(any(name.startswith("Thesis.CausalTransport.")
                                     for name in dependencies))
                self.assertIn(module, covered)
        self.assertIn(self.prefix + ".Failure", self.graph[self.prefix])

    def test_every_original_graph_statement_and_proof_is_retained_exactly(self):
        blocks = []
        for part, first in (
                ("Graph", "/-! ## Two confounded roots, an unconfounded merge, and a retained conditioner -/"),
                ("Exchange", "theorem no_exchange :"),
                ("Failure", "private def computedFailure")):
            source = self.source(self.prefix + "." + part)
            blocks.append(source[source.index(first):
                                 source.rindex("end HedgeConditionalMergedReadout")].rstrip())
        # Restore the original inter-declaration blank lines at file boundaries.
        original = blocks[0] + "\n" + blocks[1] + "\n\n" + blocks[2]
        self.assertEqual(hashlib.sha256(original.encode()).hexdigest(),
                         "6f5341093dda34caa0a68c900266a46be452e5026c5361790f0d081a448d19eb")

    def test_original_routing_and_countermodel_assertions_are_unchanged(self):
        source = self.source(self.prefix)
        source = source[source.index("noncomputable def extraction :="):]
        self.assertEqual(hashlib.sha256(source.encode()).hexdigest(),
                         "4e5a724ea35de0c121611a2b0db27b53ad6c4bacd8e972c02fdadd1e98b7dc68")

    def test_closed_readout_queries_have_independent_audited_engine_checks(self):
        prefix = "Thesis.Examples.HedgeConditionalClosedReadout"
        covered = reachable(self.graph, "Thesis.AxiomAudit")
        for part in ("Graph", "PrimaryEngine", "EarlierEngine"):
            module = prefix + "." + part
            with self.subTest(part=part):
                dependencies = reachable(self.graph, module)
                self.assertNotIn(prefix, dependencies)
                self.assertNotIn("Thesis.CausalTransport.HedgeConditionalCompensatedReadout", dependencies)
                self.assertFalse(any(".Historical." in name or ".Legacy." in name
                                     or ".CompletenessLegacy" in name for name in dependencies))
                self.assertIn(module, covered)
        for part in ("PrimaryEngine", "EarlierEngine"):
            self.assertEqual(self.graph[prefix + "." + part], [prefix + ".Graph"])
            self.assertIn(prefix + "." + part, self.graph[prefix])

    def test_closed_readout_data_and_all_six_engine_assertions_are_retained(self):
        prefix = "Thesis.Examples.HedgeConditionalClosedReadout."
        graph = self.source(prefix + "Graph")
        blocks = [
            (graph, "def signature :", "def earlierQuery :",
             "82e423a34290be13ac760f41e15849f8de6a8fa8860af5b8a39f7cc38c8cbf9e"),
            (graph, "def earlierQuery :", "end HedgeConditionalClosedReentry",
             "0a6d0683de2a0aebc054ad0087cadf4d5cfa7f999b17a2173cf080acfa13b4c2"),
        ]
        for part, start, expected in (
                ("PrimaryEngine", "theorem no_exchange :",
                 "b370342632d3b2eab6fca8b8a675a6d52bdea7db3d05351b3c73e2634dbb2b8d"),
                ("EarlierEngine", "theorem earlier_no_exchange :",
                 "62aa051c2c879cc0e9be929c73b058eab23f1f81df6cca7d0017aae9340dc3e3")):
            source = self.source(prefix + part)
            helper = source[source.index("private def failed (result :"):source.index(start)].rstrip()
            self.assertEqual(hashlib.sha256(helper.encode()).hexdigest(),
                             "ee96fdb626df05649cc42ff95378b56477f471cb8369d1f2ff072e32125f3544")
            blocks.append((source, start, "end HedgeConditionalClosedReentry", expected))
        for source, start, end, expected in blocks:
            with self.subTest(start=start):
                block = source[source.index(start):source.index(end, source.index(start))].rstrip()
                self.assertEqual(hashlib.sha256(block.encode()).hexdigest(), expected)

    def test_closed_readout_countermodels_and_denominator_proofs_are_unchanged(self):
        source = self.source("Thesis.Examples.HedgeConditionalClosedReadout")
        source = source[source.index("private theorem large_forest"):]
        source = re.sub(r"\n{3,}", "\n\n", source).rstrip()
        self.assertEqual(hashlib.sha256(source.encode()).hexdigest(),
                         "6af3c3d6579809cf07520a4c953f085657e5c41ee3ced9d73d30838935ecacff")


if __name__ == "__main__":
    unittest.main()
