import Thesis.Probability
import Thesis.Causality
import Thesis.CausalTransport
import Thesis.Examples.TenureTrack

/-!
Top-level convenience import for the thesis formalisation.

For a smaller dependency footprint, client developments should normally import
one stable facade directly: `Thesis.Probability`, `Thesis.Causality`, or
`Thesis.CausalTransport`.  This module additionally imports the executable
tenure-track example, so it is the appropriate root for the complete thesis
build and the axiom audit.
-/
