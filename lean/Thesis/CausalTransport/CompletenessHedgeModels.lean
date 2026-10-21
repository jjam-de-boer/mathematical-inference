import Thesis.CausalTransport.CompletenessLegacyNestedFailures
import Thesis.CausalTransport.Hedge.Models

/-!
# Compatibility imports for finite hedge models

The shared model, incidence and parity declarations now live in
`Thesis.CausalTransport.Hedge.Models`, with their original names, definitions
and proofs. Current mathematics should import that focused module directly.

This historical entry point deliberately also retains the preceding legacy
failure layers, so an existing import still exposes the original declaration
set. Those checked control-flow facts do not certify the legacy engine's
identified formulas. The full project and axiom audit continue to verify both
the shared implementation and the retained historical proofs.
-/
