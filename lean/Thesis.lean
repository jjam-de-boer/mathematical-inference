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
import Thesis.Examples.HedgeCompensatedConservation
import Thesis.Examples.HedgeCompensatedCounterexample
import Thesis.Examples.HedgeConditionalCompensatedReadout
import Thesis.Examples.HedgeConditionalInstalledReadout
import Thesis.Examples.HedgeConditionalClosedReadout
import Thesis.Examples.HedgeOuterRouteAbsorption
import Thesis.Examples.HedgeOutcomeNormalization
import Thesis.Examples.HedgeCountermodelSearch
import Thesis.Examples.HedgeCarrierRouteObstruction
import Thesis.Examples.HedgeCarrierTwoSidedReplay
import Thesis.Examples.ConditionalCompilation
import Thesis.Examples.ConditionalFailureExtraction
import Thesis.Examples.ConditionalFailurePaths
import Thesis.Examples.ConditionalFailureActivation
import Thesis.Examples.ConditionalFailurePivot
import Thesis.Examples.ConditionalFailureFlow
import Thesis.Examples.ConditionalFailureFlowBoundary
import Thesis.Examples.ConditionalFailureActivationForest
import Thesis.Examples.ActivePathNormalization
import Thesis.Examples.ActivePathColliderRerouting
import Thesis.Examples.ActivePathPairRoots
import Thesis.Examples.HedgeChannelPathInputs
import Thesis.Examples.ActivePathBoundary
import Thesis.Examples.HedgeChannelPathRows
import Thesis.Examples.HedgeChannelPathDirection
import Thesis.Examples.ConditionalFailurePathNormalization
import Thesis.Examples.ConditionalFailureActivationAvoidance
import Thesis.Examples.ConditionalFailureActivationAvoidanceZero
import Thesis.Examples.ConditionalCutActivationRoute
import Thesis.Examples.ConditionalFailureActivationSelectionCounterexample
import Thesis.Examples.ConditionalFailureActivationInteraction
import Thesis.Examples.ConditionalFailureSmallInteraction
import Thesis.Examples.ConditionalCollider
import Thesis.Examples.HedgeConditionalRoot
import Thesis.Examples.HedgeConditionalCollider
import Thesis.Examples.HedgeConditionalColliderSelection
import Thesis.Examples.HedgeConditionalLatentCollider
import Thesis.Examples.ConditionalNoise
import Thesis.Examples.ConditionalReadout
import Thesis.Examples.ConditionalColliderEntry
import Thesis.Examples.ConditionalCounterexampleNormalization
import Thesis.Examples.ValueRefinement
import Thesis.Examples.HedgeObstructionLikelihood
import Thesis.Examples.HedgeObstructionModel
import Thesis.Examples.HedgeObstructionCounterexample
import Thesis.Examples.FiniteTablePerturbation
import Thesis.Examples.HedgeChannelTable
import Thesis.Examples.HedgeChannelMonomial
import Thesis.Examples.HedgeChannelCoefficients
import Thesis.Examples.HedgeChannelInstallation
import Thesis.Examples.HedgeChannelSurvivors
import Thesis.Examples.HedgeChannelFullTerms
import Thesis.Examples.HedgeChannelObservational
import Thesis.Examples.HedgeChannelInterventional
import Thesis.Examples.FiniteBooleanCharacter
import Thesis.Examples.HedgeChannelRouting
import Thesis.Examples.HedgeChannelMarginal
import Thesis.Examples.HedgeChannelConditionalGap
import Thesis.Examples.HedgeChannelLatentBoundary
import Thesis.Examples.HedgeChannelLatentBoundaryCounterexample
import Thesis.Examples.HedgeChannelEnvironment
import Thesis.Examples.HedgeChannelEnvironmentCounterexample
import Thesis.Examples.HedgeChannelEnvironmentParity
import Thesis.Examples.HedgeChannelEnvironmentAbsorption
import Thesis.Examples.HedgeChannelEnvironmentFusion

/-!
Top-level convenience import for the thesis formalisation.

General joint completeness is now implemented by `HedgeChannelJointCompleteness`:
every supplied original-query hedge has a full-alphabet positive counterexample,
and every identifiable joint query has a published certificate.  Universal
conditional terminal countermodels remain open.  The older restricted carrier
families below retain their genuine limitations; they are not the proof of
unrestricted coverage supplied by the newer channel construction.

The independent-channel table regressions check actual typed-input models,
full observed support, complete integrated likelihoods and projected-event
gap criteria without reducing private response-function priors.
`HedgeChannelMonomial` checks row-to-channel regrouping, cancellation of
mixed partial selections, actual action-cut terms, and complete expansions
with repeated local labels or zero channels.  These are checks of general
construction ingredients, not an inhabitant of `PublishedCompleteness`.

`ConditionalFailureActivation` checks actual collider-activation route data:
a descendant-activated back-door collider, a zero-edge branch at an already
conditioned collider, and a legal branch that revisits the omitted pivot while
avoiding a nonempty intervention.  That last case guards against treating IDC's
exchange-test given-set as the full conditional query's condition set.
`ConditionalFailurePivot` checks that latest-reachable selection removes that
particular overlap constructively: the earlier regression's later conditioner
is selected, and full-given-set freedom follows from the general maximality
theorem.  A genuine irreducible three-valued failure also exercises selection
from its actual fully inspected hedge flow and the resulting back-door path.
`ConditionalFailureFlow` checks a three-valued two-root hedge whose readouts
merge before an outside-small outcome sink.  The actual whole-route direction
supplies a positive original-query countermodel.  Inspecting an intermediate
vertex invalidates that direction despite endpoint omission, and both branches
of the general countermodel-or-latest-pivot split are checked separately.
`ConditionalFailureFlowBoundary` checks a three-valued hedge whose old paths
all meet evidence even though Small contains a queried outcome.  The certified
first-queried stopping policy gives an unconditioned path from that non-root
Small source, and the arbitrary-forest constructor supplies a genuine positive
original-query countermodel.  The existing collider graph checks the other
branch for every Small source, including the derived Small/outcome disjointness
and actual latest-pivot construction, without assuming those boundary facts.
`ConditionalFailureActivationForest` checks two genuinely activated observed
colliders whose branches merge before one conditioner.  The common forest
retains both incoming branches, uses one shared outgoing successor, and stops
at the conditioner.  The general path theorem proves equal endpoints after
the merge; a zero-edge branch checks an already-conditioned source.
`ActivePathNormalization` checks both normalization priorities on actual
search results: equal-count paths select the later observed collider, while
a collider-free genuine latent-pair path defeats both collider paths.
`ActivePathColliderRerouting` constructs a three-valued active detour with
a genuinely conditioned return collider.  One source collider disappears,
while the return stays active; the count-first score improves even though
the rank sum decreases.  A second fixture handles an outcome-endpoint return
with an empty suffix, and reversal retains the same proved score improvement.
`ActivePathPairRoots` checks a genuine reversed latent-pair label followed by
an observed directed edge.  The two expanded aliases select the same original
reserved input, which is available only at its two actual children.  The
installed rows use that very input: their full phase conserves the endpoint
character, and a shared-input direction leaves only the source row odd.  This
is a graph-to-input and cancellation regression, not universal conditional
completeness or a new independent switching coordinate.
`HedgeChannelPathInputs` checks the constructed, rather than manually supplied,
masks on that reversed-pair path and derives whole-point endpoint conservation
from the general installed-phase theorem.  A separate observed-fork path omits
the fork's own row, rejects a genuine off-path parent arrow and an unused
original reserved input, and retains one odd source row among the selected
heads.  The omitted fork's row is odd, guarding against selecting every path
vertex.  Raw selection also rejects an incoming-cut endpoint without claiming
that the old list remains a certified path after its edge is removed.
`ActivePathBoundary` applies the general endpoint/collider graph identity and
installed-phase bridge to the reversed-pair and observed-fork paths.  A new
three-valued path has a genuine conditioned collider and a reversed original
pair label.  Its installed head phase retains the collider bit at every cube
point, and the false conditioning cylinder removes exactly that term.  The
outgoing observed endpoint is not a head: its own row is odd but unselected,
while the actual shared-input direction leaves just the source head odd.
`HedgeChannelPathRows` checks general whole-cube local-row evaluation on the
observed chain, omitted fork, and mixed observed/latent conditioned collider.
A new three-valued conditioned path uses two distinct original reserved roots,
both with reversed labels.  Its collider reads those two coordinates once each
and ignores a genuine off-path observed parent.  Their equal values cancel
at a false collider bit, and a literal supported direction leaves only the
source head odd.  It does not supply the missing activation/complete-Small
terminal countermodel family.
`HedgeChannelPathDirection` uses the general supported-direction and
individual selected-row parity theorems on all four actual path fixtures.
An unused reserved bit can be true but unread; an omitted fork and outgoing
endpoint really have odd own rows.  The two-root collider's general direction
agrees at every original coordinate with the earlier literal control.  The
actual normalized exchange constructor also proves original-query support,
source oddness, other-head evenness and full path-head oddness without an
independent first-edge certificate.  That fixture has no joint hedge and
remains observationally identifiable, not a conditional countermodel.
`ConditionalFailurePathNormalization` checks a restored three-valued pair
path, its unchanged list, first incoming edge, and general count-minimality
certificate.  Its action-free query deliberately remains observationally
identifiable: normalized exchange data are not mistaken for a countermodel.
`ConditionalFailureActivationAvoidance` checks an actual nonzero common-policy
collider trace against the selected normal form.  The general theorem excludes
its conditioned endpoint from the path, while the auxiliary domain deliberately
still overlaps a path noncollider.  Its independent smaller companion
`ConditionalFailureActivationAvoidanceZero` checks an already-conditioned
collider: the singleton trace retains the allowed source intersection.  Both
regressions use original three-valued alphabets and the general theorem, not
fixture-specific avoidance assumptions.
`ConditionalCutActivationRoute` checks a genuinely nonlatest retained pivot:
it reaches a later conditioner in the larger graph, but the exact outgoing
cut removes that route.  Actual normal-form collider activity constructs a
surviving activation and applies general normalized-path avoidance without a
latest-pivot premise.  The old full-bar forest is proved impossible at this
pivot, clarifying the required cut-policy interface rather than forcing an
invalid adapter.  An independent zero-edge conditioned activation uses the
same constructor and theorem.  Both queries are identifiable graph regressions,
not conditional countermodels or numerator-failure certificates.
`ConditionalFailureActivationSelection` checks a genuine three-valued hedge
whose collider activation lies entirely inside Small.  Graph certificates and
structural normal-form reasoning prove that the pruned trace union contributes
no outside-Small row, while retaining the queried endpoint outside the union.
The separate graph-data and counterexample companions keep capped verification
small.  The counterexample uses one legal signal and all three mandatory Small
rows, proves actual whole-cylinder conservation, and yields a positive pair
for the unchanged original conditional query.  This genuine overlap case does
not assert universal conditional completeness or Small/activation disjointness.
`ConditionalFailureActivationInteraction` applies the general fused construction
to that genuine hedge's actual opaque normal form, proving original-query
cylinder matching and the installed selected-row parities without evaluating
its exhaustive search.  A separate already-conditioned collider checks the
actual zero-edge trace, whole-cube sink term and once-only overlap own bit.
It is an identifiable graph/signal fixture, not a conditional countermodel.
`ConditionalFailureSmallInteraction` proves complete mandatory-Small coverage
for the genuine five-vertex hedge's actual opaque normal form.  The queried
endpoint's unique outgoing neighbour forces the unconditioned Small row to
be a head; the original conditioners retain the other mandatory rows.  The
general adapter derives full Small-phase oddness and whole-cylinder matching,
then constructs positive original-alphabet countermodels without a hand-written
signal, direction or conservation premise.  Graph certificates and semantic
assembly remain separate capped modules.  This closes a genuine complete-Small
instance, not universal routing or the case of a pivot outside Small.
`HedgeChannelEnvironmentAbsorption` checks a conditioned collider on an
eight-vertex three-valued graph.  Two additional mandatory Small sources merge
at a genuine background row and feed an already selected Small collider.
The general installed-flow theorem preserves the complete interaction phase,
keeps the receiving own-bit once and derives the sole merge background's
evenness.  A positive full-original-alphabet countermodel uses every mandatory
Small row for the unchanged query.  The graph and semantic companions separate
finite certificates from covariance assembly to retain capped local checks.
`HedgeChannelEnvironmentFusion` tests two real complete activation traces merging
at one vertex and then one conditioned sink.  Their overlapping collider seeds
transmit onward, so the old stopped-at-core theorem does not apply.  The general
fusion theorem gives whole-cube conservation, preserves a nonzero seed parity,
and proves new-row evenness while keeping each own bit once.  The graph companion
certifies literal trace and successor equalities for reuse in lightweight checks.
These merged-interaction regressions do not claim mandatory-Small coverage.

`HedgeChannelCoefficients` installs the explicit power coefficients in a
positive actual bow-model pair with full observational equality and a
projected intervention gap.  Its independent two-outer-vertex mask check
retains the double interaction.  These finite tests do not replace the
separate arbitrary-hedge observational assembly or general original-outcome
projection theorem.
`HedgeChannelInstallation` checks actual models returned by the general
hedge installer, rather than a hand-written channel family.  Its bow uses
each outer mask once, retains an inactive background slot, and proves full
observational equality and a gap at the original intervened outcome.  This
fixture does not replace the general observed-law theorem or establish
universal original-outcome separation.
`HedgeChannelSurvivors` checks the exact reduction of twelve actual left
row choices to four repetition-free survivors, retaining both background
masks and full-channel contributions.  Its literal signed integrals and
full-sample equality criterion are checked on that same installed pair;
the general full sum is proved separately in `HedgeChannelObservational`,
while `HedgeChannelProjection` separately proves the general original-event gap.
`HedgeChannelFullTerms` checks the new actual term correspondence separately
from the earlier bow observational-equality test.  Literal anchored row
coefficients, complete prior normalization and the action-sensitive outer
background phase agree on the paired terms.  A zero ordinary-amplitude
boundary also checks that the reusable anchored product uses no division.
`HedgeChannelObservational` checks a three-node hedge with a genuine outside-
large background and parent-reading local signals.  Its four joined masks
retain both independent parts, and every observed event agrees by the
general installed-model theorem.  Literal signed terms additionally check
the retained prior mass and the outside-background phase.
`HedgeChannelInterventional` checks the actual original action cut, proper-
term cancellation, both signs of the full-small difference, and conflicting
forced cells.  The unchanged original outcome event retains the exact bow
gap.  Forcing a small-forest row instead removes the small block and restores
equality; this fixture does not supply the general projected-gap theorem.
`FiniteBooleanCharacter` checks retained and cancelled full cylinder sums,
empty and fully fixed products, and the excluded constant-odd phase boundary.
`HedgeChannelRouting` queries an outcome beyond the small forest.  Its bare
small character cancels at the unqueried intermediate row, while the routed
background term retains the original-event gap.  The complete likelihood
difference follows symbolically, with only its two surviving terms computed.
The same fixture now instantiates the unrestricted full-alphabet counterexample
and proves non-identifiability of the unchanged original outcome kernel.
Its retained-conditioner query additionally instantiates the new omitted-
small-flow-sink conditional construction and proves corrected-engine failure
from the actual counterexample and general engine correctness, without
evaluating the full exchange search.  `HedgeChannelMarginal` contrasts a
three-valued irreducible collider whose conditioner contains every flow sink:
conservation rules out every balance direction, although the separate collider
construction supplies a positive conditional counterexample.  This records
the balance family's genuine limit without asserting universal coverage.
`HedgeChannelConditionalGap` tests an alternative typed incoming-parent
signal on that collider.  Its actual evidence probabilities differ, while
the complete normalized cell change still separates the conditional.
Only the small canonical observed projections are evaluated.  The new
channel constructor now lifts this gap to the original three-valued positive
class.  Its final full-label conditioning probabilities are still unequal;
the lift retains the separated source cell rather than imposing denominator
equality.  A mixed-reference regression checks the explicit coordinate
recoding used by the general arbitrary-original-alphabet cell transport.
General countermodels for arbitrary irreducible terminals remain unproved.
`HedgeChannelLatentBoundary` supplies a genuine three-valued irreducible query
with a shared-latent back-door entry.  It proves that every typed parent-signal
choice in the observed-parent-only independent-channel family gives zero normalized change
at every reference, hence complete agreement of its Boolean conditional.
An actual positive shared-latent pair nevertheless separates the original
query.  The universal leaf must therefore compose real latent-path readouts
or use a broader model family, not assume that parent-signal tuning suffices.
`HedgeChannelEnvironment` verifies that such a broader pair separates this
same query.  Its small and outcome-background signals read one reserved bit
at their genuine common pair root, independently of the main forest channels.
All four actual projected masses are computed by the complete environment
sum with the large main-prior mass kept symbolic.  Its evidence change
cancels while its joint change survives.  The one-way countermodel companion
connects the strict cross-product gap to actual Boolean kernel cells and the
unchanged full three-valued positive class.  No observed arrow is added, and
the result does not stand in for general irreducible active-path construction.
`HedgeChannelEnvironmentParity` checks the same unchanged nonbinary query
through the general parity-to-countermodel constructor instead of evaluating
its event masses.  The actual incident-root masks, supported odd direction
and whole-cylinder matching identity supply every finite parity field.  Its
local observed/root conservation tests do not enumerate the main likelihood
support.  The general homogeneous basis theorem proves whole-cylinder matching
and derives small-phase oddness.  A separate negative check shows that the
fixed root is not globally balanced: only free coordinates are required to
balance.  The fixture does not claim arbitrary active-path coverage.

`ConditionalCollider` checks a real irreducible `P(U | do(A), R)` failure
on `U -> R <- A`, `A <-> R`, with three-valued observed alphabets.  The
installed incoming-parent collider supplies both positive SCMs, complete
observational equality, and separation of that original conditional kernel;
the root belongs to the conditioner rather than the queried outcome.
Its probability checks additionally retain unequal context denominators,
repeated source atoms, both posterior bits, and the balanced-noise erasure
boundary.  Neither the fixture nor its constructor claims universal
conditional completeness.
`HedgeConditionalRoot` checks the general root-conditional selector on an
actual extracted two-root hedge.  Its probability boundaries also exercise
different coordinate alphabets, unequal record denominators, equal individual
marginals with different joint dependence, and the zero-coordinate space.
The selected source gap and action-preserving labels are supplied by the
general theorem, not by a manually chosen root or assumed conditional gap.
`HedgeConditionalCollider` checks its semantic integration on the original
three-valued `P(U,E | do(A), R₁,R₂)` query.  The query has two conditioned
hedge roots, a genuine additional outcome, no legal IDC exchange, and an
actual ID failure.  The arbitrary-root constructor supplies positive SCMs,
the full observed-law equality, and separation of that complete kernel;
the other root's full label is retained rather than marginalized away.
`HedgeConditionalColliderSelection` additionally checks a two-root geometry
with distinct queried incoming parents and no eligible shared parent.  The
root-specific finite search supplies the parent's actual data after the
separated root is selected, while retaining the original conditional query.
`HedgeConditionalLatentCollider` checks the complementary latent-pair family
on the original three-valued `P(U,V,E | do(A), R₁,R₂)` query.  There are no
queried observed arrows into the roots and no eligible shared readout for
both roots.  The root-specific meeting searches return different neighbours.
The actual query fails IDC; the general constructor supplies the positive
compatible pair, the complete observed-law equality, third-label support,
and separation of the entire three-outcome, two-conditioner kernel.
`ConditionalReadout` checks the longer original-query route
`R <- U -> M -> Y` for the three-valued `P(Y,E | do(A), R)` failure.
The original numerator hedge supplies the separated source root.  Finite
graph searches then select the auxiliary parent and both readout arrows;
neither an auxiliary countermodel nor intermediate SCM non-influence is
assumed.  Neither auxiliary coordinate is queried, and the final extra
outcome is restored without changing the given set.  Full observational
equality and complete third-label support are retained.  The separate exact
IDC and path-code companions are not imported by this smoke test.
`ConditionalNoise` separately checks unequal evidence masses,
repeated labels, a zero-weight atom, both output bits, the full-event
conditioning transport, and the fair-noise erasure boundary.
`ConditionalColliderEntry` checks a two-root three-valued query whose first
root has only observed entry and whose second has only shared-latent entry.
Both auxiliary sources are unqueried and have directed tails to the original
outcome.  The uniform entry premises are proved false, while the combined
root-specific constructor supplies the full positive countermodel pair.

For a smaller dependency footprint, client developments should normally import
one stable facade directly: `Thesis.Probability`, `Thesis.Causality`, or
`Thesis.CausalTransport`.  This module additionally imports the executable
tenure-track example and checked identification regressions, so it is the
appropriate root for the complete thesis build and the axiom audit.
Constructive back-door regressions additionally check an actual conditional
failure with a retained conditioner, nonempty action avoidance, a latent-pair
first edge, descendant-activated colliders, blocked paths, and empty or equal
endpoints.  The path data is selected by verified finite search; these graph
certificates do not claim that the universal conditional countermodel exists.
A separate label-refinement regression starts with a binary bow pair whose
third labels have zero probability.  An actual private sweep makes the entire
three-valued alphabet positive while retaining the exact causal probabilities
`1/2` and `1/3`, the full observed-law equality, and the original projected
graph.  The ordinary Boolean-model adapter is also instantiated directly.
The marginal regressions additionally refine the inspected coordinate twice,
retain equality of a third-label event under arbitrary interventions, and
retain an actual forced third label in the full-value encoding theorem.
These are general alphabet transports, not by themselves hedge constructions.
The separate seven-node obstruction likelihood regression checks a different
strictly positive rational-table pair, with complete observed equality and
an exact truncated-table gap of `1/62208`.  Its structural realization uses
four independent pair sources and genuinely private finite response tables;
the semantic bridge proves full observed equality, positivity, and that
same causal gap for the actual SCMs.  Private label refinement then returns
a positive counterexample for the original three-valued `P(Y | do(A,B))`
query on the original graph.  This closes that outer-reentry regression,
not the universal hedge-countermodel obligation.
The finite table-perturbation boundary checks additionally cover three values,
repeated atom labels, zero direction weights, and zero environment coefficients.
The generated profiles are normalized and fully positive; their factual
response equality and changed-environment gap follow from the general
balanced-response criterion, not subtraction or division by a coefficient.
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
A seven-node outer-only re-entry regression separately checks the exact
two-sided replay without the small-pivot hypothesis.  A free outer update
produces different root responses from the same realized positive-probability
retained state.  Both installed models remain positive and graph-compatible;
their full observational laws are then separated by an exact root-event
comparison: `4/9` versus `1/3`.  An arbitrary-noise formula further proves
that changing only the fresh weights cannot repair this update while a flip
has positive mass.  No probability-preserving joint input/state recoding can
match this particular pair, even by mixing noise with retained state.
An occurrence-indexed repeated plan supplies different bits at the same
pivot and distinguishes that encoding from the older shared node bit.  The
actual whole-prior event identity and the necessary-and-sufficient averaged
replay comparison require no pivot distinctness, geometric permission, or
assumed observational equality.  These negative results concern the stated
toggle and base priors, not every possible routing plan or countermodel.
These checks do not establish an unrestricted toggle-family countermodel;
the separate channel construction supplies general joint countermodels instead.
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
The closed-coordinate regression now permits an installed responding
conditioner with no common root in the queried outcome.  An omitted small
vertex may have a genuine outgoing flow to a later uninspected outcome;
its parent-closed prefix still gives equality of the actual conditioning
kernels.  A second query uses a non-root balancing vertex with an original
kept child.  Both three-value queries have checked irreducible public-engine
failures and positive countermodels, rather than postulated denominator
equalities or exact extractor child-map assumptions.
The outer-route absorption regression changes the small forest first, then
constructs a new positive pair for the unchanged original query.  Its old
route permission test is proved false.  The checked enlargement absorbs
both route vertices and required off-route kept children, without changing
the common roots or canonical routes.  Joint separation and conditional
separation with a matching full-value denominator are proved in the new
pair; both public engines actually fail and the conditional is irreducible.
A reverse-normalization regression retains the positive private-readout pair
on `A → R → Y`, `A ↔ R`, but queries `P(R | do(A), Y)`.  Its conditioning
marginals are provably different, ruling out the matched-denominator adapter.
The reverse conditional is identified by the actual replacement program;
its compiled success certificate and two-way normalization yield separation
of the requested irreducible conditional in the unchanged models.  This
checks a new normalization case without asserting general completeness.
The outcome-ancestral rerooting regression uses a three-value composite
action for which same-map absorption provably forces an intervened vertex
into the small side.  Reconstructing the kept edges changes the common
roots, removes that obstruction, and supplies positive joint and irreducible
conditional countermodels for the unchanged queries.  A second bidirected
graph on the same signature proves that the new constructor's remaining
connectivity condition is not automatic for every valid hedge.
The alternative-hedge regression repairs that disconnected case using
finite search over both forest sets and kept edges.  Its first ordinary
selection fails the routing test, while a supplied alternative guarantees
that the filtered search succeeds.  Even the smaller alternative large
forest has a disconnected full outcome-ancestral small set, so the scan
must allow proper small subsets.  The actual search-returned witness
supplies the original-query positive countermodel; neither its exact forest
coordinates nor universal structural coverage are assumed.
The seven-node carrier-route obstruction regression then disproves that
universal coverage.  A valid original-query hedge and a checked corrected-ID
failure coexist with empty full-graph scans for both canonical routing and
arbitrary outer-avoiding routing.  Candidate-completeness turns those
finite computations into a refutation for every forest selection, not
just one normalization.  This distinguishes a genuine limitation of the old
carrier family from a route-policy or greedy-search failure.  The separate
unrestricted channel construction closes the general positive joint hedge leaf
without assuming this disproved carrier-coverage theorem.
-/
