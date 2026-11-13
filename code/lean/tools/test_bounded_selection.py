"""Protect the bounded-selector admission and guard-preservation boundary.

These source-shape checks complement, not replace, the Lean theorems, tiny
executable regressions and transitive axiom audit. They do not establish a
runtime bound or interpret a resource refusal as non-identifiability.
"""

from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]


class BoundedSelectionTests(unittest.TestCase):
    def test_bounded_entry_maps_the_metadata_admitted_catalogue(self):
        source = (ROOT / "Thesis/CausalTransport/NativeBoundedSelection.lean").read_text()
        body = source.split("def guardedSelectOnWithMetadata ", 1)[1].split("\ntheorem ", 1)[0].split(":=", 1)[1]
        self.assertIn("guardedCatalogueOnWithMetadata", body)
        self.assertIn("CheckedNativeFormula.select record reference", body)
        self.assertIn(".map", body)
        self.assertNotIn("catalogueOn graph", body)
        self.assertNotIn("completeSupportCatalogue", body)

    def test_scan_retains_actual_native_availability(self):
        source = (ROOT / "Thesis/CausalTransport/NativeFormulaSelection.lean").read_text()
        # Reuse the first-match list search without erasing native guards
        # or converting the candidate into the weaker plan interface.
        body = source.split("def select ", 1)[1].split("\ntheorem ", 1)[0]
        self.assertIn("candidate.available record reference", body)
        self.assertIn("List.find?", body)
        self.assertNotIn("ObservationalFormulaPlan", body)
        self.assertNotIn("guard :=", body)

    def test_source_and_conditional_support_are_explicit_in_soundness(self):
        source = (ROOT / "Thesis/CausalTransport/NativeBoundedSelection.lean").read_text()
        theorem = source.split("noncomputable def guardedSelectOnWithMetadata_soundAt ", 1)[1].split(":=", 1)[0]
        self.assertIn("decoded : source.decode S = some query", theorem)
        self.assertIn("sourceSupported : model.TermSupportedAt query reference", theorem)
        self.assertIn("CausalSupportAgreement entry.model model", theorem)
        self.assertIn("model.TermEquivalentAt query chosen.formula reference", theorem)


if __name__ == "__main__":
    unittest.main()
