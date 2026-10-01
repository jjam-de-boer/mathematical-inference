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
import Thesis.Examples.HedgeReadout
import Thesis.Examples.HedgeReadoutPullback
import Thesis.Examples.HedgeConditionalReadout
import Thesis.Examples.HedgeInternalReadout
import Thesis.Examples.HedgeInterventionalSupport
import Thesis.Examples.HedgeInterventionalProbability
import Thesis.Examples.HedgePartialIncidenceProbability
import Thesis.Examples.HedgeConditionalMarginal
import Thesis.Examples.HedgeCarrierReplay
import Thesis.Examples.HedgeCarrierReplayPlan
import Thesis.Examples.HedgeCompensatedReadout
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
A private-readout regression also checks the actual original query on
`X → R → Y` with only `X ↔ R`: its extracted hedge root is `R`, not the queried
outcome `Y`.  The new private source at `Y` has a proved product law, preserves
full observational positivity and equality, and transports root separation
to the original outcome kernel through the real SCM mechanism.  This checks
the routing primitive without asserting the unrestricted routed theorem.
A merging-readout regression extracts two common roots from an actual joint
failure, XORs them at an unconfounded merge vertex, and then forwards that
signal through another unconfounded vertex to the original queried outcome.
The arbitrary finite-plan constructor supplies its positive countermodel;
the computed event pullback, not an intermediate semantic premise, restores
both roots.  Duplicate outcome checks also verify cancellation of the same
private noise and of the repeated source parity.
The same merging fixture now also uses the generated canonical all-root
plan.  Its pivot enumeration checks both roots, the merge, and the outcome
in order.  The original-query counterexample needs only the proved route
kept-sink condition; no hand-written instructions or pullback identity are
passed to this automatic constructor.
A separate support regression uses a genuine internal kept pivot from the
same three-node hedge, then updates vertices in descending order with repeats.
The general restoring-assignment theorem proves positivity of both complete
folded SCMs without a sink, non-influence, or ordering proof.  Compatibility
is also retained.  The test deliberately makes no claim of observational
equality or query separation for that unordered internal plan.
The same internal pivot now checks its exact one-coordinate private channel
and prefix-local parity reflection without a non-influence premise.  Odd and
even repeated occurrences respectively retain and cancel the same fresh bit;
later descendants are not silently included in this local event argument.
An internal-action overwrite also checks the opposite boundary: both models
remain positive and graph-compatible, but a root event distinguishes their
new observed laws.  Thus local support and signal facts cannot justify an
unrestricted full-law preservation theorem; free-pivot routing still needs
its separate constructive argument.
A further three-value regression checks a genuine internal small-forest
readout with a kept child.  Its full observational equality follows from
retained-state replay, without a non-influence or sink premise; compatibility
and strict positivity are also retained.  Two explicit old latent units have
the same complete observed assignment but different concealed backgrounds.
After the update their responding child emits `first` in one unit and the
third label in the other.  This verifies actual descendant evaluation and
why the stronger joint state law is necessary, rather than replacing the
response by a map of the old observed assignment alone.  The existing
negative outer-only action overwrite remains outside the small-pivot theorem.
No arbitrary finite-plan or original-query routing claim is made by this check.
A separate five-node three-value fixture now checks the finite-plan replay.
Its root-to-outcome route leaves the forest at an outside vertex and re-enters
at an internal small-forest vertex with a genuine kept child.  The generated
all-root plan has full observational equality, positivity, and compatibility.
A manual plan on the same graph repeats that internal pivot in descending
order, with unequal noise records, and retains the same three properties.
These are actual folded SCMs with successive independent priors.  The tests
do not infer original-query separation from observational replay alone.
The compensated-plan regression revisits that re-entry fixture with actual
mechanism responses.  Its internal non-root retains the old forest residual;
the outcome does not add a second copy of the kept parent's contribution.
For every original latent unit and fresh-bit family, the large outcome equals
the old common-root signal XOR all new noise bits, and the nested outcome
equals the weighted defect XOR that same fresh parity.  Observational equality,
positivity, and compatibility are checked for these actual folded SCMs.
The probability comparison and general large-flow argument are not inferred
from the fixture's pointwise identities.
Partial-incidence regressions retain the extracted two-root merging hedge.
They realize odd patterns after omitting an action equation or an inner-root
equation, and check equal fibre sizes without a full-pattern evenness premise.
The nested test also inspects an outer coordinate.  Under the original action,
one complete target has positive mass in both private-defect strata, and an
explicit pair-root compensation preserves full evaluation when the defect is
flipped at arbitrary latent coordinates.  These are support and coupling
checks, not an assumed equality of weighted conditional denominators.
Weighted interventional regressions now compare arbitrary observed events in
the merging hedge after conditioning on either defect.  A separate extracted
three-value hedge uses a composite action with intervention values outside
the two parity labels.  Its complete nonbinary target has positive mass in
both strata, strictly different raw slice masses in the original two-to-one
ratio, and equal normalized probabilities.  These checks retain the original
prior and do not assert a large/small conditional denominator comparison.
Cross-map partial-incidence regressions retain both an outer row and an inner
row of the merging hedge while omitting its other inner root.  Different
ordinary/nested targets have equal fibre counts, and defect-dependent targets
with arbitrary shared private predicates have equal probabilities under the
original biased prior.  A complete-row negative check shows why an inner row
must be omitted: the nested map realizes a target forbidden by the ordinary
map's full parity constraint.  A coupled private predicate in the three-value
fixture also checks that the exact product count retains all three permitted
background vectors, rather than replacing them by a Boolean encoding.
An actual-SCM marginal regression now retains the confounded three-node chain
with three-value alphabets and the irreducible query `P(Y | do(A), B)`.
Its conditioner belongs to both extracted forests, so the old outside-forest
constructor cannot apply.  The root-omitted marginal theorem matches the
denominator in the original positive carrier pair and the strengthened
queried-root constructor separates the conditional itself.  Exact IDC failure,
exhausted exchange search, failure-aligned forests with a checked kept chain,
and unchanged models are checked; the general extractor's child map is not
silently identified with that explicitly checked chain.
A direct cylinder comparison fixes the action to the third observed label
and tests that label at the internal conditioner under the actual intervention.
The common mass is strictly positive; an intervention-inconsistent target
has zero mass on both sides.  A second irreducible conditional reuses the
merging fixture's extracted two-root forests and queries one root while
conditioning on the other.  Its numerator covers both roots, but its outcome
does not.  The finite meeting-test constructor supplies the countermodel
without forcing all roots into the outcome or changing the retained forests.
These checks do not assert the unrestricted routed conditional theorem.
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
The routed conditional regression additionally retains two common roots
outside the queried outcome, an unconfounded merging readout, and a nonempty
conditioner connected by an outcome-to-conditioner edge.  The actual IDC
search cannot exchange that conditioner.  The canonical plan stops at the
outcome, and general off-pivot kernel preservation matches the denominator
in the same positive routed pair.  This checks conditional separation beyond
the earlier queried-root family without asserting the unrestricted terminal
countermodel theorem.
-/
