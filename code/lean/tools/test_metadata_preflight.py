"""Keep eager value-list work after the resource gates meant to prevent it.

These are deliberately narrow source-order regressions, not a Lean parser,
proof verifier, compiler-cost model, or runtime memory test. Denotational
equality alone cannot detect eager evaluation of a subsequently unused list.
The complete Lean build and transitive axiom audit remain separate gates.
"""

from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]


def definition_body(module, name):
    source = (ROOT / (module.replace(".", "/") + ".lean")).read_text()
    definition = source.split("def " + name + " ", 1)[1].split("\ntheorem ", 1)[0]
    return definition.split(":=", 1)[1]


class MetadataPreflightTests(unittest.TestCase):
    def test_fallback_rejects_masks_before_reading_value_lists(self):
        body = definition_body("Thesis.Causality.CodeSearchPreflight", "preflightSyntax")
        self.assertNotIn("dictionaryEstimate", body)
        mask_gate = body.index("if masks >")
        value_work = body.index("signature.valueEnumeration")
        reference_gate = body.index("if references >")
        real_dictionary = body.index("CodeDictionaries.ofSignature")
        self.assertLess(mask_gate, value_work)
        self.assertLess(value_work, reference_gate)
        self.assertLess(reference_gate, real_dictionary)

    def test_metadata_path_reads_only_certified_sizes_before_dictionary_admission(self):
        body = definition_body("Thesis.Causality.CodeSearchMetadata", "preflightSyntaxWithMetadata")
        self.assertNotIn("valueEnumeration", body)
        self.assertNotIn("dictionaryEstimate", body)
        self.assertLess(body.index("if masks >"), body.index("metadata.cardinality"))
        self.assertLess(body.index("metadata.cardinality"), body.index("if references >"))
        self.assertLess(body.index("if references >"), body.index("CodeDictionaries.ofSignature"))

    def test_native_metadata_entry_does_not_fall_back_to_length_based_preflight(self):
        body = definition_body("Thesis.CausalTransport.NativeSearchMetadata", "guardedCatalogueOnWithMetadata")
        self.assertIn("preflightSyntaxWithMetadata", body)
        self.assertNotIn("preflightSyntax limits", body)
        self.assertLess(body.index("preflightSyntaxWithMetadata"), body.index("preflightProfiles"))
        self.assertLess(body.index("preflightTotal"), body.index("pure (catalogueOn"))

    def test_result_equality_is_not_a_compiler_rewrite_to_the_expensive_path(self):
        for module in ("Thesis/Causality/CodeSearchMetadata.lean",
                       "Thesis/CausalTransport/NativeSearchMetadata.lean"):
            with self.subTest(module=module):
                self.assertNotIn("[csimp]", (ROOT / module).read_text())


if __name__ == "__main__":
    unittest.main()
