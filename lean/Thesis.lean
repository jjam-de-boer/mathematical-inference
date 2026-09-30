import Thesis.Probability
import Thesis.Causality
import Thesis.CausalTransport
import Thesis.Examples.TenureTrack
import Thesis.Examples.IdentificationRegression
import Thesis.Examples.KernelCompilation
import Thesis.Examples.ComponentCompilation
import Thesis.Examples.KernelRecursionCompilation
import Thesis.Examples.ProductCompilation
import Thesis.Examples.KernelProductCompilation

/-!
Top-level convenience import for the thesis formalisation.

For a smaller dependency footprint, client developments should normally import
one stable facade directly: `Thesis.Probability`, `Thesis.Causality`, or
`Thesis.CausalTransport`.  This module additionally imports the executable
tenure-track example and checked identification regressions, so it is the
appropriate root for the complete thesis build and the axiom audit.
The current-input compilation regressions additionally exercise supported
certificates on a gapped host, a nonempty external action, and an empty
observed signature.  Component-extraction regressions additionally exercise
graph-derived action deletion and exchange, a genuinely recursive extracted
input, and the terminal complementary marginal.  The recursive branch
regression composes nonempty action augmentation, containing-component
action reindexing, and uncut ancestral pruning, and checks its certificate
throughout the positive compatible model class.
Product-regrouping regressions additionally exercise interleaving components,
duplicate factors, certificate substitution, and an empty outer partition;
their algebra does not impose observational positivity.
The complete component-product regression additionally checks the actual
replacement-engine output for a nonempty-action, two-component query and
its denotation throughout the positive compatible model class.
-/
