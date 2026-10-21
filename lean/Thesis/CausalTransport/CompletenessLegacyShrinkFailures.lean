import Thesis.CausalTransport.CompletenessFailureExtraction
import Thesis.CausalTransport.Historical.LegacyShrinkFailures

/-!
# Compatibility import for historical shrink failure proofs

The original declarations, statements and proof scripts are retained in
`Thesis.CausalTransport.Historical.LegacyShrinkFailures`. They concern the
quarantined legacy program's control flow and locally qualified certificates,
not semantic correctness of its general identified formulas.

This facade retains the old import path and the preceding historical layer.
The full project and axiom audit still check the archived implementation;
current published completeness paths do not import it. See
`lean/docs/structure.md` for the source-location map and current reading order.
-/
