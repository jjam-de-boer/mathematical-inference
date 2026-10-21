"""Protect causal foundations extracted without changing their mathematics.

The hashes compare exact source blocks (including proof bodies) with the
verified pre-extraction revision f7204c7 and first causal checkpoint e2eee12.
The failure-core check normalizes only extra blank lines left by extraction.
Import checks protect the smaller
current interfaces while keeping historical imports and audit reachability.
Neither check replaces Lean elaboration or the transitive axiom audit.
"""

import hashlib
from pathlib import Path
import re
import unittest

from test_example_coverage import initial_project_imports, reachable


class CausalFoundationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(__file__).resolve().parents[1]
        paths = [cls.root / "Thesis.lean", *(cls.root / "Thesis").rglob("*.lean")]
        cls.graph = {".".join(path.relative_to(cls.root).with_suffix("").parts):
                     initial_project_imports(path.read_text()) for path in paths}

    def source(self, module):
        return (self.root / (module.replace(".", "/") + ".lean")).read_text()

    def test_current_foundations_and_selected_clients_avoid_legacy_completeness(self):
        for module in ("Causality.TermSupport", "Causality.InterventionalCounterexample",
                       "Causality.IdentificationOutcomeTraces", "Causality.CForestConstruction",
                       "CausalTransport.ActionDeletion",
                       "CausalTransport.Hedge.ReadoutGeometry", "CausalTransport.Hedge.Models",
                       "CausalTransport.Hedge.Parity", "CausalTransport.HedgePartialIncidence",
                       "CausalTransport.HedgeChannelCounterexample",
                       "CausalTransport.HedgeChannelEnvironmentIncidence",
                       "CausalTransport.ConditionalBayes", "CausalTransport.CompletenessAssembly",
                       "CausalTransport.ConditionalFailureCore", "CausalTransport.Hedge.WitnessSearch",
                       "CausalTransport.HedgeChannelCompleteness",
                       "CausalTransport.HiddenDAGCorrespondence",
                       "CausalTransport.HiddenDAGSupportedCorrespondence",
                       "CausalTransport.PositiveModal", "CausalTransport.SupportedModal",
                       "CausalTransport.ChainCompilation", "CausalTransport.HedgeChannelCharacters",
                       "CausalTransport.ValueRefinementCounterexample",
                       "CausalTransport.KernelCompilation", "CausalTransport.KernelFailureExtraction"):
            with self.subTest(module=module):
                dependencies = reachable(self.graph, "Thesis." + module)
                self.assertNotIn("Thesis.CausalTransport.Completeness", dependencies)
                self.assertFalse(any(".Legacy." in name or ".CompletenessLegacy" in name or ".Historical." in name
                                     for name in dependencies))

    def test_moved_declarations_and_proofs_are_preserved_exactly(self):
        blocks = (
            ("CausalTransport.Hedge.ReadoutGeometry", "/--\nA vertex that is ancestral of `targets`",
             "/-- A remaining-set edge of `G_",
             "c5156eb01d7728daba3aa052f4d3e1b795504878070e8fbfd5d6fc927240b0ce"),
            ("CausalTransport.Hedge.ReadoutGeometry", "/-- A remaining-set edge of `G_",
             "/-- An exact walk on Boolean edges",
             "6bf25033381b1adb1d6d402693ae895b617be708d9ba276f2a425f5c1a64e989"),
            ("Causality.TermSupport", "/-- An empty-action unconditional kernel is always defined",
             "/-- An observational kernel `P(Y | Z)`",
             "3e78d174ad32c7a37414adfe807fcf44a05ec4e529e959c3d1d592063f45f8ec"),
            ("Causality.TermSupport", "/-- An observational kernel `P(Y | Z)`",
             "/-- Finite sum of an observational conditional",
             "3eaef3abcff2f49311ffc9a1626de77846d49c61bfdfdbf2af801ec0aec61f10"),
            ("Causality.TermSupport", "/-- Finite sum of an observational conditional",
             "end Causality",
             "e353fd7fb79a14f73105291dffc65dd76affd988ed5e76b8388bdc1d36f08007"),
            ("Causality.InterventionalCounterexample", "/-- Event-level disagreement",
             "end Causality",
             "bba2d0b79d386a002871fdd700dcb59f3c672ca8af832c2f10939e184a5f0ce1"),
            ("CausalTransport.Hedge.ReadoutGeometry", "/-- An exact walk on Boolean edges",
             "end Causality",
             "f60e20a287508585db3223645d58d32a69c4346475221d4b50706eca8ba41ce0"),
            ("CausalTransport.Hedge.Models", "/-! ## Positive-class countermodels from hedge data -/",
             "end Causality",
             "df39602c2cdb2e703e68dfbf3fe7adca5715f9eb909be6ccda5bda649cbc04bc"),
            ("CausalTransport.ActionDeletion", "/-- Outcome and action of a joint query",
             "end Causality",
             "62bfb4e2b25d14b52aa546c498549a4c6f32b2307a352ddb56b0cc0c4fac61b3"),
            ("Causality.CForestConstruction", "/--\nA bidirected component with a well-formed kept-child map",
             "end Causality",
             "e5545232ae27d60b98fcdb878b66f90ddd047a02495f66c210c8297daecbb6c5"),
            ("CausalTransport.Hedge.Parity", "/-- Correct a Boolean incidence target at one anchor",
             "/-!\n### C-forest incidence flow all the way to query outcomes",
             "4f5db4651640dac655343136089b9779dfb81451447c4b56474a2a5d165a4fee"),
            ("CausalTransport.Hedge.Parity", "/-!\n### C-forest incidence flow all the way to query outcomes",
             "end Causality",
             "7f78796ec777507f81eeee5208f184226db2f0eec93761fad854411522340f6c"),
            ("CausalTransport.ConditionalBayes", "/-- Bayes writes `P(Y | do(X), Z)`",
             "end Causality",
             "4fbd2e3b23e6eee094758718d98bc5a6e2b853108736efd94fd895e791552bd1"),
            ("CausalTransport.ConditionalFailureCarrierCases", "/-- A positive conditional countermodel whenever every common root",
             "end Causality",
             "ac95c0442153b5ee63c57331ab6c8b8d3e9d75c3ce55bc7b338b200b0bf35cce"),
            ("CausalTransport.Hedge.WitnessSearch", "/-- Unpack the Boolean hedge tests",
             "end Causality",
             "4fa577485830009b3306099454fb0d5f7f49ac0b32824bfb58c23db1791705c8"),
        )
        for module, start, end, expected in blocks:
            with self.subTest(module=module, start=start):
                source = self.source("Thesis." + module)
                block = source[source.index(start):source.index(end, source.index(start))].rstrip()
                self.assertEqual(hashlib.sha256(block.encode()).hexdigest(), expected)
        collector = self.source("Thesis.Causality.IdentificationOutcomeTraces")
        collector = collector[collector.index("namespace IdentificationOutcome\n"):
                              collector.rindex("end Causality")].rstrip()
        self.assertEqual(hashlib.sha256(collector.encode()).hexdigest(),
                         "6696879c589107a12774e18bb3e9f5d924ec16657a1eb7eb6152deaeee1e72f7")
        core = self.source("Thesis.CausalTransport.ConditionalFailureCore")
        start = "/-! ## Inspectable exchange traces and their semantic equality -/"
        core = core[core.index(start):core.rindex("end Causality")]
        core = re.sub(r"\n{3,}", "\n\n", core).rstrip()
        self.assertEqual(hashlib.sha256(core.encode()).hexdigest(),
                         "46c954b9164640331989efc3b212d0cc06bfb021111a0781dfd1b818da47dff1")

    def test_old_imports_reexport_the_new_foundations(self):
        pairs = (("CompletenessCertificates", "Thesis.Causality.TermSupport"),
                 ("CompletenessCertificates", "Thesis.Causality.CForestConstruction"),
                 ("CompletenessCertificates", "Thesis.CausalTransport.ActionDeletion"),
                 ("CompletenessCertificates", "Thesis.CausalTransport.ConditionalBayes"),
                 ("CompletenessFailureExtraction", "Thesis.CausalTransport.Hedge.ReadoutGeometry"),
                 ("CompletenessFailureExtraction", "Thesis.CausalTransport.Hedge.WitnessSearch"),
                 ("ConditionalFailureExtraction", "Thesis.CausalTransport.ConditionalFailureCore"),
                 ("ConditionalFailureExtraction", "Thesis.CausalTransport.ConditionalFailureCarrierCases"),
                 ("CompletenessHedgeParity", "Thesis.Causality.InterventionalCounterexample"),
                 ("CompletenessHedgeParity", "Thesis.CausalTransport.Hedge.Parity"),
                 ("CompletenessHedgeModels", "Thesis.CausalTransport.Hedge.Models"))
        for old, foundation in pairs:
            with self.subTest(old=old):
                self.assertIn(foundation, reachable(self.graph, "Thesis.CausalTransport." + old))
        self.assertIn("Thesis.Causality.IdentificationOutcomeTraces",
                      reachable(self.graph, "Thesis.Causality.Legacy.IdentificationInduction"))

    def test_both_shared_and_historical_layers_remain_inside_full_axiom_audit(self):
        covered = reachable(self.graph, "Thesis.AxiomAudit")
        for module in ("Causality.TermSupport", "Causality.InterventionalCounterexample",
                       "Causality.IdentificationOutcomeTraces", "Causality.CForestConstruction",
                       "CausalTransport.ActionDeletion",
                       "CausalTransport.Hedge.ReadoutGeometry", "CausalTransport.Hedge.Models",
                       "CausalTransport.Hedge.Parity",
                       "CausalTransport.ConditionalBayes",
                       "CausalTransport.ConditionalFailureCore", "CausalTransport.ConditionalFailureCarrierCases",
                       "CausalTransport.Hedge.WitnessSearch",
                       "CausalTransport.CompletenessLegacyShrinkFailures",
                       "CausalTransport.CompletenessLegacyProductFailures",
                       "CausalTransport.CompletenessLegacyNestedFailures"):
            with self.subTest(module=module):
                self.assertIn("Thesis." + module, covered)

    def test_historical_inventory_is_preserved_outside_the_public_facade(self):
        history = (self.root / "docs/history/completeness-development.md").read_text()
        block = history.split("```text\n", 1)[1].split("\n```", 1)[0]
        self.assertEqual(hashlib.sha256(block.encode()).hexdigest(),
                         "68a789944a66b368811c0507d92d590ae85bc088efe3e9f79249b099d1ce25b7")
        facade = self.source("Thesis.CausalTransport.Completeness")
        self.assertNotIn("Detailed implementation inventory.", facade)
        self.assertIn("docs/history/completeness-development.md", facade)

    def test_archived_failure_stacks_keep_every_original_declaration_and_proof(self):
        hashes = {
            "Shrink": "091e6b4864c4942638ce5bdbedace2b37b1cd829f7242285a4ef458a474d2677",
            "Product": "8332c4cf0eae0dfee1e776cc407831472133405e29e96c02ceb59cc1da7bda7f",
            "Nested": "147b9366088b80b3ffde953d3734730ed2db9e55563164ad1d0e3072e4041c00",
        }
        covered = reachable(self.graph, "Thesis.AxiomAudit")
        for kind, expected in hashes.items():
            with self.subTest(kind=kind):
                archived = "Thesis.CausalTransport.Historical.Legacy" + kind + "Failures"
                old = "Thesis.CausalTransport.CompletenessLegacy" + kind + "Failures"
                source = self.source(archived)
                body = source[source.index("namespace Thesis\n"):].rstrip()
                self.assertEqual(hashlib.sha256(body.encode()).hexdigest(), expected)
                self.assertIn(archived, reachable(self.graph, old))
                self.assertIn(archived, covered)
                self.assertIn(old, covered)


if __name__ == "__main__":
    unittest.main()
