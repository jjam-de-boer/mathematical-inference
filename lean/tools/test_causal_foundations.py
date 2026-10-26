"""Protect causal foundations extracted without changing their mathematics.

The hashes compare exact source blocks (including proof bodies) with the
verified pre-extraction revision f7204c7 and causal checkpoints e2eee12/47904c8.
The failure-core check normalizes only extra blank lines left by extraction.
The countermodel check restores one precisely specified documentation
clarification before comparing its original hash; no proof text is normalized.
Import checks protect the smaller
current interfaces while keeping the useful negative regression audited.
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

    def test_consecutive_implication_stays_in_the_generic_walk_foundation(self):
        # The original recursive proof at maintenance baseline 4a29a2c is
        # retained exactly. Source preservation and dependency ownership are
        # distinct checks; neither establishes Lean elaboration by itself.
        owner = "Thesis.Causality.ReachabilityCorrectness"
        graph_layer = "Thesis.CausalTransport.DSeparationCorrectness"
        source = self.source(owner)
        start = source.index("theorem Consecutive.mono ")
        block = source[start:source.index("\n\n", start)].rstrip()
        self.assertEqual(hashlib.sha256(block.encode()).hexdigest(),
                         "7dc5b1d97c43c7cf7b96d7450457e95f5563574ab9997cb0bdfc5ff49fb66cce")
        self.assertNotIn("theorem Consecutive.mono ", self.source(graph_layer))
        self.assertIn(owner, reachable(self.graph, graph_layer))
        for module in ("Hedge.ReadoutGeometry", "Hedge.Models", "Hedge.Parity",
                       "HedgeChannelCharacters", "HedgeChannelCounterexample"):
            with self.subTest(module=module):
                dependencies = reachable(self.graph, "Thesis.CausalTransport." + module)
                self.assertIn(owner, dependencies)
                self.assertNotIn(graph_layer, dependencies)
                self.assertNotIn("Thesis.CausalTransport.DSeparation", dependencies)

    def test_generic_path_helpers_keep_their_original_proofs_and_old_import(self):
        # Full downstream CI exposed additional incidental reexports after
        # the first narrow check. These helpers belong below graph-specific
        # correctness too; putting that broad import back would hide the bug.
        owner = "Thesis.Causality.ReachabilityCorrectness"
        old = "Thesis.CausalTransport.DSeparationCorrectness"
        source = self.source(owner)
        blocks = (
            ("theorem Consecutive.pair_of_append ",
             "1eee0819416373252cc0e551757f05bcd97922ff2c3294464a4141d16fc20701"),
            ("theorem Consecutive.prefix_append ",
             "706defa40ee98ed25b3de433e45914d8aaa5b42d6b632a18f31172a1cfd3ffb6"),
            ("theorem Consecutive.drop ",
             "1dd0b882ea677c8e8f49597ddb9c54335c914e29d168c827ed80d427b40c6497"),
            ("theorem Consecutive.append ",
             "504d70b3a6d2a966fd9ae2dcbf9e41532f0591b1f6730eed8679582c9cee560e"),
            ("theorem Consecutive.delete_middle ",
             "55d0508ee5f2a564e13aec8c25d09bcd2952cd1b2b153d020c323333611017ec"),
            ("theorem Consecutive.map ",
             "90f69a08714bd7cd147177b1cf83c7b3f4ecaffdcbbca0f46bbcde2ff4a95220"),
            ("theorem Consecutive.snoc ",
             "996929fe09ba7f5ea743d5d9613259dbd869f9cfb68734c06da2f1f3f372eed0"),
            ("theorem Consecutive.reverse ",
             "07ffd3e90214f3b8a84b2c41bd71ad505b3bdc141452d6577c8e0d7572a23cec"),
            ("theorem FiniteReachability.Reachable.of_consecutive",
             "0df2bac2cf1e98c01e4f9960ac58e1508ff4dad033b8926b59650833f1305300"),
            ("theorem getLast?_suffix_append ",
             "3d401600b3b12117e54ec6349d90a7599b67ffd6b55fb84cfc6aa25003b53cf9"),
        )
        for start, expected in blocks:
            with self.subTest(start=start):
                self.assertEqual(source.count(start), 1)
                beginning = source.index(start)
                block = source[beginning:source.index("\n\n", beginning)].rstrip()
                self.assertEqual(hashlib.sha256(block.encode()).hexdigest(), expected)
                self.assertNotIn(start, self.source(old))
        self.assertIn(owner, reachable(self.graph, old))
        for module in ("HedgeChannelFlowDirection", "HedgeChannelEnvironmentIncidence"):
            dependencies = reachable(self.graph, "Thesis.CausalTransport." + module)
            self.assertIn(owner, dependencies)
            self.assertNotIn(old, dependencies)

    def test_current_foundations_and_selected_clients_avoid_legacy_completeness(self):
        for module in ("Causality.TermSupport", "Causality.InterventionalCounterexample",
                       "Causality.IdentificationOutcomeTraces", "Causality.CForestConstruction",
                       "CausalTransport.ActionDeletion",
                       "CausalTransport.Hedge.ReadoutGeometry", "CausalTransport.Hedge.Models",
                       "CausalTransport.Hedge.Parity", "CausalTransport.HedgePartialIncidence",
                       "CausalTransport.Hedge.Countermodels", "CausalTransport.HedgePositive",
                       "CausalTransport.HedgeOutcomeFlow", "CausalTransport.ConditionalFailureCarrierCases",
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

    def test_all_current_causal_implementations_avoid_historical_facades(self):
        # These are intentionally broad compatibility/archival entry points,
        # not current semantic implementations. Do not exempt public current
        # end-results merely because their names also contain "Completeness".
        historical = {"Completeness", "CompletenessCertificates", "CompletenessFailureExtraction",
                      "CompletenessLegacyShrinkFailures", "CompletenessLegacyProductFailures",
                      "CompletenessLegacyNestedFailures", "CompletenessHedgeModels",
                      "CompletenessHedgeParity", "CompletenessHedgeCountermodels"}
        prefix = "Thesis.CausalTransport."
        for module in self.graph:
            if not module.startswith(prefix):
                continue
            local = module.removeprefix(prefix)
            if local in historical or local.startswith("Historical."):
                continue
            with self.subTest(module=module):
                dependencies = reachable(self.graph, module)
                forbidden = {name for name in dependencies
                             if name == prefix + "Completeness" or ".Legacy." in name
                             or ".Historical." in name or ".CompletenessLegacy" in name}
                self.assertFalse(forbidden, f"Current implementation imports history: {sorted(forbidden)}")

    def test_production_modules_do_not_use_examples_as_foundations(self):
        # Full facades/policy gates deliberately assemble regression files.
        # Their convenience imports must not become a production dependency.
        for module, dependencies in self.graph.items():
            if module == "Thesis" or module.startswith("Thesis.Examples.") or module.endswith("Audit"):
                continue
            with self.subTest(module=module):
                self.assertFalse(any(name.startswith("Thesis.Examples.") for name in dependencies))

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
            ("CausalTransport.Hedge.Countermodels", "/-! ### Observational equivalence of the unsoftened parity pair -/",
             "end Causality",
             "40b7f44b870fc2f4716a58b8c8422f4ab75ef52c11dd83cfc2d29145dbf868cc"),
        )
        for module, start, end, expected in blocks:
            with self.subTest(module=module, start=start):
                source = self.source("Thesis." + module)
                block = source[source.index(start):source.index(end, source.index(start))].rstrip()
                if module == "CausalTransport.Hedge.Models":
                    # Correct one incomplete explanatory sentence while
                    # continuing to compare every declaration/proof exactly.
                    current = "The elementary `hedgeMixModel` reads every pair-root incident to a node. A"
                    original = "The elementary `hedgeMixModel` above every pair-root incident to a node.  A"
                    self.assertEqual(block.count(current), 1)
                    block = block.replace(current, original, 1)
                if module == "CausalTransport.Hedge.Parity" and start.startswith("/-!"):
                    # Only this exact stale positional reference changed.
                    # Restore it before applying the original whole-body hash;
                    # no declaration or proof is omitted or normalized.
                    current = "The abstract root-flow wrapper in `Hedge.Models` requires a caller to reconstruct"
                    original = "The abstract root-flow wrapper above still requires a caller to reconstruct"
                    self.assertEqual(block.count(current), 1)
                    block = block.replace(current, original, 1)
                if module == "CausalTransport.Hedge.Countermodels":
                    # Pass 2 corrected a misleading progress claim, not a
                    # declaration or proof. Keep the original whole-body hash
                    # and permit only this exact documented comment change.
                    current = (
                        "/-- Complete unrestricted-class counterexample for the common-root parity\n"
                        "query. This record concerns `w.rootParityQuery rich`, not the original outcome\n"
                        "query, and it does not claim positivity of its unsoftened pair. The separate\n"
                        "channel construction in `HedgeChannelCompleteness` supplies positive\n"
                        "countermodels for the original query. No unproved general-completeness\n"
                        "obligation is hidden in this root-parity constructor. -/")
                    original = (
                        "/-- Complete unrestricted-class counterexample for the common-root parity\n"
                        "query.  This packages compatibility, observational equivalence, and kernel\n"
                        "separation in the same record required by published hedge completeness.  The\n"
                        "remaining general-hedge work is precisely to transport this query from the\n"
                        "common roots to the original outcome and then restore observational\n"
                        "positivity. -/")
                    self.assertEqual(block.count(current), 1)
                    block = block.replace(current, original, 1)
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

    def test_current_conditional_extraction_exposes_both_checked_interfaces(self):
        facade = reachable(self.graph, "Thesis.CausalTransport")
        for foundation in ("Thesis.CausalTransport.ConditionalFailureCore",
                           "Thesis.CausalTransport.ConditionalFailureCarrierCases"):
            self.assertIn(foundation, facade)
        completeness = reachable(self.graph, "Thesis.CausalTransport.HedgeChannelCompleteness")
        self.assertIn("Thesis.CausalTransport.ConditionalFailureCore", completeness)
        self.assertNotIn("Thesis.CausalTransport.ConditionalFailureCarrierCases", completeness)
        self.assertNotIn("Thesis.CausalTransport.ConditionalFailureExtraction", self.graph)
        example = reachable(self.graph, "Thesis.Examples.ConditionalFailureExtraction")
        self.assertIn("Thesis.CausalTransport.ConditionalFailureCore", example)
        self.assertIn("Thesis.CausalTransport.ConditionalFailureCarrierCases", example)

    def test_action_deletion_certificate_is_promoted_into_current_mathematics(self):
        owner = "Thesis.CausalTransport.ActionDeletionCertificates"
        dependencies = reachable(self.graph, owner)
        self.assertFalse(any(".Legacy." in name or ".Historical." in name
                             or name.startswith("Thesis.Examples.") for name in dependencies))
        self.assertIn(owner, self.graph["Thesis.Examples.KernelCompilation"])
        source = self.source(owner)
        self.assertIn("PublishedJointCertificate C correct q", source)
        self.assertIn("sourceSupported", source)
        self.assertNotIn("positive : ObservationallyPositive", source)

    def test_retained_foundations_and_frontdoor_examples_remain_audited(self):
        covered = reachable(self.graph, "Thesis.AxiomAudit")
        for module in ("Causality.TermSupport", "Causality.InterventionalCounterexample",
                       "Causality.IdentificationOutcomeTraces", "Causality.CForestConstruction",
                       "CausalTransport.ActionDeletion",
                       "CausalTransport.Hedge.ReadoutGeometry", "CausalTransport.Hedge.Models",
                       "CausalTransport.Hedge.Parity",
                       "CausalTransport.Hedge.Countermodels",
                       "CausalTransport.ConditionalBayes",
                       "CausalTransport.ConditionalFailureCore", "CausalTransport.ConditionalFailureCarrierCases",
                       "CausalTransport.Hedge.WitnessSearch",
                       "Examples.Fixtures.FrontDoor",
                       "Examples.FrontDoorCurrentIdentification",
                       "Examples.IdentificationRegression"):
            with self.subTest(module=module):
                self.assertIn("Thesis." + module, covered)

    def test_retired_legacy_libraries_do_not_return_as_compatibility_imports(self):
        # The project has no external import clients. These obsolete paths
        # were retired, not replaced with another forwarding-file chain.
        retired = (
            "Causality.Legacy.IdentificationSearch", "Causality.Legacy.IdentificationInduction",
            "CausalTransport.Historical.LegacyShrinkFailures",
            "CausalTransport.Historical.LegacyProductFailures",
            "CausalTransport.Historical.LegacyNestedFailures",
            "CausalTransport.Completeness", "CausalTransport.CompletenessCertificates",
            "CausalTransport.CompletenessFailureExtraction",
            "CausalTransport.CompletenessHedgeModels", "CausalTransport.CompletenessHedgeParity",
            "CausalTransport.CompletenessHedgeCountermodels",
            "CausalTransport.CompletenessLegacyShrinkFailures",
            "CausalTransport.CompletenessLegacyProductFailures",
            "CausalTransport.CompletenessLegacyNestedFailures",
            "CausalTransport.ConditionalFailureExtraction")
        for local in retired:
            with self.subTest(module=local):
                name = "Thesis." + local
                self.assertNotIn(name, self.graph)
                self.assertFalse((self.root / (name.replace(".", "/") + ".lean")).exists())
                self.assertFalse(any(name in imports for imports in self.graph.values()))

    def test_modern_frontdoor_clients_do_not_import_the_negative_algorithm(self):
        fixture = "Thesis.Examples.Fixtures.FrontDoor"
        negative = "Thesis.Examples.IdentificationRegression"
        current = "Thesis.Examples.FrontDoorCurrentIdentification"
        for local in ("KernelCompilation", "ComponentCompilation", "ProductCompilation",
                      "KernelRecursionCompilation", "KernelProductCompilation",
                      "KernelSuccessCompilation", "ConditionalCompilation",
                      "HedgeChannelCompleteness", "PositiveModal"):
            with self.subTest(example=local):
                dependencies = reachable(self.graph, "Thesis.Examples." + local)
                self.assertIn(fixture, dependencies)
                self.assertNotIn(negative, dependencies)
        negative_dependencies = reachable(self.graph, negative)
        self.assertIn(fixture, negative_dependencies)
        self.assertNotIn(current, negative_dependencies)
        self.assertNotIn("Thesis.Causality.IdentificationKernel", negative_dependencies)

    def test_negative_example_retains_the_actual_refuted_algorithm(self):
        # Retain this exact old computation so the numerical bug is still
        # demonstrated, rather than substituting a hand-written bad formula.
        source = self.source("Thesis.Examples.IdentificationRegression")
        fuel = source[source.index("def Legacy.identifyFuel"):
                      source.index("def Legacy.identifyJoint")].rstrip()
        joint = source[source.index("def Legacy.identifyJoint"):
                       source.index("/-- A hypothetical certificate")].rstrip()
        self.assertEqual(hashlib.sha256(fuel.encode()).hexdigest(),
                         "b6226859062ea6869283ce4d94604b0798b6074b18b4f937a9b745feaf6aee63")
        self.assertEqual(hashlib.sha256(joint.encode()).hexdigest(),
                         "6aa6e34437ac2501d7e63a968f136d2448188e89583da4b3f52d5a4d27f02fd4")
        self.assertIn("theorem legacyEngineFormula_not_equivalent", source)
        self.assertIn("theorem legacyFormulaCompiler_is_uninhabited", source)


if __name__ == "__main__":
    unittest.main()
