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

    def test_soundness_extraction_keeps_a_one_way_import_chain(self):
        prefix = "Thesis.CausalTransport."
        for client, dependency in (("Soundness", "SoundnessRules"),
                                   ("SoundnessRules", "SoundnessRegions"),
                                   ("SoundnessRegions", "SoundnessFoundations")):
            self.assertEqual(self.graph[prefix + client], [prefix + dependency])
            self.assertNotIn(prefix + client, reachable(self.graph, prefix + dependency))

    def test_soundness_private_helpers_do_not_cross_extracted_layers(self):
        root = Path(__file__).resolve().parents[1] / "Thesis/CausalTransport"
        sources = {name: (root / (name + ".lean")).read_text() for name in
                   ("Soundness", "SoundnessFoundations", "SoundnessRegions", "SoundnessRules")}
        groups = {
            "SoundnessFoundations": ("factorizationAssignmentDecidableEq", "factorizationAssignments",
                "assignmentEvents", "rectangular_assignmentEvents", "unionList_event_true_of_mem",
                "exists_event_of_unionList_true"),
            "SoundnessRules": ("bool_and_four_pairs", "bool_and_mid_swap", "bool_and_rot_left"),
        }
        for owner, names in groups.items():
            for name in names:
                self.assertIn(name, sources[owner])
                for module, source in sources.items():
                    if module != owner:
                        self.assertNotIn(name, source, (name, owner, module))

    def test_soundness_layers_remain_in_full_axiom_audit_scope(self):
        root = Path(__file__).resolve().parents[1]
        graph = self.graph | {"Thesis": initial_project_imports((root / "Thesis.lean").read_text())}
        covered = reachable(graph, "Thesis.AxiomAudit")
        for name in ("Soundness", "SoundnessFoundations", "SoundnessRegions", "SoundnessRules"):
            self.assertIn("Thesis.CausalTransport." + name, covered)

    def test_completeness_extraction_keeps_order_and_import_compatibility(self):
        layers = ["CompletenessCertificates", "CompletenessFailureExtraction",
            "CompletenessLegacyShrinkFailures", "CompletenessLegacyProductFailures",
            "CompletenessLegacyNestedFailures", "CompletenessHedgeModels",
            "CompletenessHedgeParity", "CompletenessHedgeCountermodels", "Completeness"]
        prefix = "Thesis.CausalTransport."
        for earlier, later in zip(layers, layers[1:]):
            self.assertEqual(self.graph[prefix + later], [prefix + earlier])
            self.assertNotIn(prefix + later, reachable(self.graph, prefix + earlier))
        dependencies = reachable(self.graph, prefix + "Completeness")
        self.assertTrue({prefix + layer for layer in layers} <= dependencies)
        self.assertNotIn(prefix + "Soundness", dependencies)

    def test_completeness_preserves_immediate_query_header_and_audit_coverage(self):
        root = Path(__file__).resolve().parents[1]
        nested = (root / "Thesis/CausalTransport/CompletenessLegacyNestedFailures.lean").read_text()
        self.assertIn("theorem identifyJoint_eq_failed_immediate_query_site", nested)
        self.assertIn("def hedgeWitnessOfJoint", nested)
        graph = self.graph | {"Thesis": initial_project_imports((root / "Thesis.lean").read_text())}
        covered = reachable(graph, "Thesis.AxiomAudit")
        for module in self.graph:
            if module.startswith("Thesis.CausalTransport.Completeness"):
                self.assertIn(module, covered)

    def test_observational_evaluator_stays_below_causal_completeness(self):
        module = "Thesis.Causality.ObservationalEvaluation"
        self.assertEqual(self.graph[module], ["Thesis.Causality.Semantics"])
        self.assertFalse(any(name.startswith("Thesis.CausalTransport.")
                             for name in reachable(self.graph, module)))
        self.assertIn(module, self.graph["Thesis.CausalTransport.ObservationalFormulaSelection"])
        root = Path(__file__).resolve().parents[1]
        graph = self.graph | {"Thesis": initial_project_imports((root / "Thesis.lean").read_text())}
        self.assertIn(module, reachable(graph, "Thesis.AxiomAudit"))

    def test_frontdoor_value_check_retains_exact_syntax_and_model_bridges(self):
        root = Path(__file__).resolve().parents[1]
        source = (root / "Thesis/Examples/IdentificationRegression.lean").read_text()
        self.assertIn("kernelEngineFormula = compactKernelEngineFormula", source)
        self.assertIn("private theorem observedTable_agrees", source)
        for name in ("sourceAtReferenceHalf", "legacyEngineAtReferenceNineSixteenths",
                     "kernelEngineAtReferenceHalf", "mediatorSourceAtReferenceHalf",
                     "kernelMediatorAtReferenceHalf"):
            self.assertIn("def " + name + " :", source)
        value_check = source.split("def kernelEngineAtReferenceHalf :", 1)[1].split("/--", 1)[0]
        self.assertIn("ProbabilityTerm.observationalDenote_congr", value_check)
        self.assertNotIn("publishedSoundness", value_check)
        self.assertNotIn("denotational_sound", value_check)


if __name__ == "__main__":
    unittest.main()
