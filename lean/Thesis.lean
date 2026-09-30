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
import Thesis.Examples.KernelSuccessCompilation
import Thesis.Examples.KernelFailureExtraction
import Thesis.Examples.HedgeNoise
import Thesis.Examples.ConditionalCompilation
import Thesis.Examples.ConditionalFailureExtraction

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
Structural success-compilation regressions now construct those certificates
automatically from the actual engine success equations, including front-door,
nonempty augmentation, a recursive gapped host with external actions, empty
outcomes, and the zero-node signature.  No hand-supplied child certificate is
needed by the structural compiler.
Structural failure-extraction regressions exercise immediate failure with a
proper incoming-cut ancestry, uncut pruning, nonempty action augmentation,
containing-component restriction, and a failed product factor.  They check
hedges for the original queries with exact terminal forest coordinates, and
also cover a recursive host with external actions and an arbitrary current term.
Private-noise regressions check exact finite parity bias, unequal input
denominators, deterministic input support, the zero-noise boundary, and erasure
of separation by fair noise.  A three-value carrier checks support beyond the
two parity labels, and an actual extracted hedge checks its root-signal gap
after any finite biased-noise count.  This is not yet original-outcome routing.
Conditional regressions distinguish recursive IDC from Bayes alone: one query
has a failed joint numerator but succeeds after a rule-2 promotion, and a
longer query exchanges two conditioners while retaining the remaining given
set.  Terminal Bayes, empty conditioners, the empty signature, insufficient
fuel, and retained terminal failure are also checked with the general compiler.
Conditional failure regressions additionally check actual failed runs after
zero, one, and two exchanges, exact retained forest coordinates, and uniform
exhaustion of the terminal search.  A positive original-numerator countermodel
for a terminal with queried roots is converted to conditional separation and
transported through both exchanges without changing either model.  The
intermediate nonempty given-set and actual finite-search choices are checked;
this does not assert that every irreducible conditional terminal has a
countermodel.
A further conditional failure regression retains a nonempty conditioner and
blocks every exchange through an outcome-to-conditioner edge.  Its extracted
hedge produces positive models that separate the actual conditional query:
their denominator equality follows from the pair's private-background
mechanisms outside the forest, not from an assumed denominator-identifiability
theorem.  This checks a genuine irreducible terminal case as well as transport.
-/
