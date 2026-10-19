"""Guard the transportation module's public import boundary without Lean.

These source checks protect ownership and import compatibility, not proof
correctness. The original statements/bodies were compared during extraction;
the full Lean build and transitive axiom audit remain the mathematical gates.
"""

from pathlib import Path
import re
import unittest

from test_example_coverage import initial_project_imports, reachable


class TransportationSplitTests(unittest.TestCase):
    def setUp(self):
        self.root = Path(__file__).resolve().parents[1]
        self.base = "Thesis.Probability.FourLabelTransportation"
        self.construction = self.base + "Construction"
        self.sources = {module: self.root.joinpath(*module.split(".")).with_suffix(".lean").read_text()
                        for module in (self.base, self.construction)}

    def test_public_boundary_reexports_construction_without_cycle(self):
        self.assertEqual(initial_project_imports(self.sources[self.base]), [self.construction])
        self.assertEqual(initial_project_imports(self.sources[self.construction]),
                         ["Thesis.Probability.Core"])
        for source in self.sources.values():
            self.assertIn("namespace FourLabelTransportation\n", source)

    def test_original_public_declarations_keep_their_owning_layer(self):
        expected = {
            self.construction: {
                "Masses", "Cells", "sum4", "label_cases", "sum4_congr", "sum4_add", "le_sum4",
                "Margins", "Transportation", "Eligible", "eligibleDecidable", "candidateEdges",
                "candidateEdges_complete", "candidateEdges_nodup", "nextStep", "decrementAt",
                "decrementAt_recover", "sum4_addAt", "sum4_decrementAt", "remainingMargins",
                "addEdge", "transport"},
            self.base: {"transportation_capacity", "transportation_exists_iff"},
        }
        for module, names in expected.items():
            found = re.findall(r"^(?:abbrev|def|theorem|structure|instance) (\w+)\b",
                               self.sources[module], re.MULTILINE)
            self.assertEqual(set(found), names, module)
            self.assertEqual(len(found), len(names), "duplicate public declarations")
        private = re.findall(r"^private theorem (\w+)\b", self.sources[self.construction], re.MULTILINE)
        self.assertEqual(set(private), {"forall_four", "positive_row_contradiction",
            "no_step_impossible", "sum4_singleton", "addEdge_row_sum", "addEdge_column_sum"})

    def test_split_is_in_full_axiom_audit_import_closure(self):
        paths = [self.root / "Thesis.lean", *(self.root / "Thesis").rglob("*.lean")]
        graph = {".".join(path.relative_to(self.root).with_suffix("").parts):
                 initial_project_imports(path.read_text()) for path in paths}
        self.assertTrue({self.base, self.construction} <= reachable(graph, "Thesis.AxiomAudit"))

    def test_local_memory_refactor_keeps_the_large_numerical_regressions(self):
        source = (self.root / "Thesis/Examples/FourLabelTransportationBatched.lean").read_text()
        self.assertIn("private theorem uniform_margins_general (mass : Nat)", source)
        self.assertIn("theorem uniform_margins : Margins 4000000 uniform uniform", source)
        self.assertIn("uniform_margins_general 1000000", source)
        self.assertIn("theorem large_cell : largeTable.cells 0 1 = 1000000000", source)
        self.assertIn("theorem uniform_first_cell : uniformTable.cells 0 1 = 1000000", source)


if __name__ == "__main__":
    unittest.main()
