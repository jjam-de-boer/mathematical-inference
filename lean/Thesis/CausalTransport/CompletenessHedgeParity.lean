import Thesis.CausalTransport.CompletenessHedgeModels
import Thesis.CausalTransport.Hedge.Parity

/-!
# Compatibility imports for C-forest parity and support

`Thesis.CausalTransport.Hedge.Parity` owns the unchanged shared incidence,
exact-support and parity proofs. Current clients should import it directly
instead of inheriting historical identification dependencies for these facts.

This older entry point also retains `CompletenessHedgeModels`, preserving its
original transitive interface. Both the focused implementation and retained
historical proofs remain in the complete build and transitive axiom audit.
No ready-case countermodel is promoted to an unrestricted theorem here.
-/
