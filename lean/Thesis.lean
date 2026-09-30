import Thesis.Probability
import Thesis.Causality
import Thesis.CausalTransport
import Thesis.Examples.TenureTrack
import Thesis.Examples.IdentificationRegression
import Thesis.Examples.KernelCompilation

/-!
Top-level convenience import for the thesis formalisation.

For a smaller dependency footprint, client developments should normally import
one stable facade directly: `Thesis.Probability`, `Thesis.Causality`, or
`Thesis.CausalTransport`.  This module additionally imports the executable
tenure-track example and checked identification regressions, so it is the
appropriate root for the complete thesis build and the axiom audit.
The current-input compilation regressions additionally exercise supported
certificates on a gapped host, a nonempty external action, and an empty
observed signature.
-/
