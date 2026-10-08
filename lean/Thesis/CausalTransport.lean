import Thesis.CausalTransport.DSeparation
import Thesis.CausalTransport.DSeparationCorrectness
import Thesis.CausalTransport.DSeparationWitness
import Thesis.CausalTransport.ActivePathTransport
import Thesis.CausalTransport.Certificates
import Thesis.CausalTransport.Correspondence
import Thesis.CausalTransport.FiniteSource
import Thesis.CausalTransport.Soundness
import Thesis.CausalTransport.Completeness
import Thesis.CausalTransport.ChainCompilation
import Thesis.CausalTransport.KernelIdentification
import Thesis.CausalTransport.KernelCompilation
import Thesis.CausalTransport.ProductCompilation
import Thesis.CausalTransport.KernelSeparation
import Thesis.CausalTransport.KernelPartition
import Thesis.CausalTransport.ComponentCompilation
import Thesis.CausalTransport.KernelRecursionSeparation
import Thesis.CausalTransport.KernelRecursionCompilation
import Thesis.CausalTransport.KernelProductCompilation
import Thesis.CausalTransport.KernelSuccessCompilation
import Thesis.CausalTransport.KernelHedgeTransport
import Thesis.CausalTransport.KernelFailureExtraction
import Thesis.CausalTransport.HedgeOutcomeFlow
import Thesis.CausalTransport.HedgePositive
import Thesis.CausalTransport.HedgeConditionalRoot
import Thesis.CausalTransport.HedgeNoise
import Thesis.CausalTransport.HedgeReadout
import Thesis.CausalTransport.HedgeReadoutConditioning
import Thesis.CausalTransport.ConditionalReadoutCounterexample
import Thesis.CausalTransport.ConditionalReadoutRoute
import Thesis.CausalTransport.ConditionalReadoutReachability
import Thesis.CausalTransport.ConditionalCollider
import Thesis.CausalTransport.ConditionalColliderNonInfluence
import Thesis.CausalTransport.ConditionalColliderProbability
import Thesis.CausalTransport.ConditionalColliderCounterexample
import Thesis.CausalTransport.ConditionalMarginalization
import Thesis.CausalTransport.ConditionalColliderContextCounterexample
import Thesis.CausalTransport.HedgeConditionalCollider
import Thesis.CausalTransport.HedgeConditionalColliderRoute
import Thesis.CausalTransport.ConditionalLatentCollider
import Thesis.CausalTransport.ConditionalLatentColliderNonInfluence
import Thesis.CausalTransport.ConditionalLatentColliderProbability
import Thesis.CausalTransport.ConditionalLatentColliderCounterexample
import Thesis.CausalTransport.HedgeConditionalLatentCollider
import Thesis.CausalTransport.HedgeConditionalLatentColliderRoute
import Thesis.CausalTransport.HedgeConditionalColliderEntry
import Thesis.CausalTransport.HedgeReadoutSequence
import Thesis.CausalTransport.HedgeReadoutPullback
import Thesis.CausalTransport.HedgeRoutedCounterexample
import Thesis.CausalTransport.HedgeReadoutPlan
import Thesis.CausalTransport.CompletenessAssembly
import Thesis.CausalTransport.ValueRefinementCounterexample
import Thesis.CausalTransport.ConditionalCompilation
import Thesis.CausalTransport.ConditionalCounterexampleFailure
import Thesis.CausalTransport.ConditionalFailureExtraction
import Thesis.CausalTransport.ConditionalFailurePaths
import Thesis.CausalTransport.ConditionalCounterexampleNormalization
import Thesis.CausalTransport.HedgeConditionalReadout
import Thesis.CausalTransport.Counterfactual
import Thesis.CausalTransport.HiddenDAGModel
import Thesis.CausalTransport.HiddenDAG
import Thesis.CausalTransport.Construction
import Thesis.CausalTransport.Modal
import Thesis.CausalTransport.ModalRealization
import Thesis.CausalTransport.ConservativeLearningTransport
import Thesis.CausalTransport.ModalCounterfactual
import Thesis.CausalTransport.HedgeInterventionalSupport
import Thesis.CausalTransport.HedgeInterventionalProbability
import Thesis.CausalTransport.HedgePartialIncidenceProbability
import Thesis.CausalTransport.HedgeCarrierObservationalState
import Thesis.CausalTransport.HedgeInterventionalMarginal
import Thesis.CausalTransport.HedgeConditionalMarginal
import Thesis.CausalTransport.HedgeCarrierReplay
import Thesis.CausalTransport.HedgeCarrierReplayPlan
import Thesis.CausalTransport.HedgeReadoutEvaluation
import Thesis.CausalTransport.HedgeReadoutNoise
import Thesis.CausalTransport.HedgeReadoutInputs
import Thesis.CausalTransport.HedgeCarrierTwoSidedReplay
import Thesis.CausalTransport.HedgeCompensatedReadout
import Thesis.CausalTransport.HedgeCompensatedPreimage
import Thesis.CausalTransport.HedgeCompensatedMarginal
import Thesis.CausalTransport.HedgeReadoutPreservation
import Thesis.CausalTransport.HedgeCompensatedConservation
import Thesis.CausalTransport.HedgeCompensatedCounterexample
import Thesis.CausalTransport.HedgeConditionalCompensatedReadout
import Thesis.CausalTransport.HedgeSmallAbsorption
import Thesis.CausalTransport.HedgeOutcomeNormalization
import Thesis.CausalTransport.HedgeCountermodelSearch
import Thesis.CausalTransport.HedgeChannelCharacters
import Thesis.CausalTransport.HedgeChannelOrthogonality
import Thesis.CausalTransport.HedgeChannelIntegration
import Thesis.CausalTransport.HedgeChannelPairRoot
import Thesis.CausalTransport.HedgeChannelTable
import Thesis.CausalTransport.HedgeChannelLikelihood
import Thesis.CausalTransport.HedgeChannelMonomial
import Thesis.CausalTransport.HedgeChannelCoefficients
import Thesis.CausalTransport.HedgeChannelInstallation
import Thesis.CausalTransport.HedgeChannelSurvivors
import Thesis.CausalTransport.HedgeChannelFullTerms
import Thesis.CausalTransport.HedgeChannelFullCoefficients

/-!
Stable facade for external-theorem interfaces and their finite transports.

`Certificates` defines the shared certificate shapes, while `Correspondence`
states the graph-indexed `PublishedSoundness` and `PublishedCompleteness`
boundaries.  These records make theorem ownership explicit: soundness is
inhabited constructively below, while importing this facade still does not
assume completeness as an axiom.

`FiniteSource` supplies an independently executable finite-table semantics,
proves preservation into the intrinsic semantics, and exposes source-level
adapters.  `DSeparationCorrectness` connects the finite ancestry and moral
reachability searches to active-path separation.
`DSeparationWitness` additionally returns certified active-path data for every
negative separation answer, using a bounded finite search instead of choice.
`ActivePathTransport` restores cut edges along the same path by exploiting
the expanded DAG's strict rank, and excludes conditioned incoming-cut vertices
from that path.  `ConditionalFailurePaths` applies these facts to every
conditioner left by an exhausted IDC exchange search: it returns an active
back-door path in the action-cut graph, with an explicit first incoming edge
and no action vertices.  These are ingredients for the general conditional
countermodel argument, not an assumption or proof of that remaining argument.

`ConditionalCollider` realizes an incoming-parent collider with two fresh
private inputs in the original SCM graph.  It preserves positivity and,
under explicit pivot non-influence conditions, the full observational law.
`ConditionalColliderNonInfluence` derives readiness for later readouts from
the collider's actual mechanisms, retaining the full background labels.
The collider need not precede every destination in the ambient order; an
unused allowed edge is not mistaken for actual mechanism dependence.
`ConditionalColliderProbability` transports its actual evaluated posterior
to the finite collider channel, proving its numerator and denominator before
division and retaining arbitrary supported contexts away from the pivots.
`ConditionalColliderCounterexample` connects the true readout to a single
observed conditioning value on any `ValueRich` alphabet.  When the sole
common hedge root is the conditioner and a queried incoming parent is outside
the large forest, it constructs a positive counterexample for the original
conditional kernel.  `ConditionalMarginalization` restores arbitrary additional
outcomes without changing the action, conditioner, or countermodel pair.
`ConditionalColliderContextCounterexample` retains the full labels of every
other conditioner and compares each posterior at its own supported context,
without assuming equality of denominator marginals.
`HedgeConditionalRoot` supplies the multi-root source-signal step independently
of that geometry.  From an arbitrary hedge's positive carrier pair it selects
a genuinely separated root conditional given all other roots, with supported
contexts in the real interventional records and latent priors.  Its explicit
readout labels retain the original action values.  It does not assert that
the selected root is an admissible collider pivot for every original query.
`HedgeConditionalCollider` connects that source selector to the actual
context-aware countermodel construction.  It handles any number of conditioned
roots and additional queried outcomes when the selected root has a queried
incoming parent outside the large forest.  An automatic wrapper accepts a
parent with incoming edges to every common root; the root-specific wrapper
instead finds a possibly different queried incoming parent for each selected
root from its finite Boolean availability test.  The original action values
are preserved when the readout labels are chosen.
`ConditionalLatentCollider` supplies the complementary shared-latent first
edge without requiring an observed arrow between the readout and root.  It
installs a mask on an existing bidirected pair, then combines the old child
value, shared mask, and private noise before one full-value emission.  This
avoids losing nonbinary background labels through sequential bit carriers.
`ConditionalLatentColliderNonInfluence` proves that these actual updates
preserve every initially ignored observed coordinate.  The shared mask is
latent rather than a newly read observed parent, so there is no displayed-
parent exception and no ambient destination/collider order requirement.
`ConditionalLatentColliderProbability` constructs the actual channel
realization from the SCM's prior, evaluation equations, and unchanged context;
`ConditionalLatentColliderCounterexample` connects its supported posterior to
the original conditional kernel and restores all queried outcomes.
`HedgeConditionalLatentCollider` supplies the source gap internally from the
arbitrary hedge root selector and selects a possibly different queried outside
bidirected neighbour at each root by finite meeting search.  Both collider
families still require the common roots to be the original conditioner and
the selected readout to lie outside the large forest.
`HedgeReadoutConditioning` supplies an actual SCM posterior identity for a
private readout under unchanged full-label context.  Nonzero noise bias
reflects the old conditional signal gap even when evidence masses differ.
`ConditionalReadoutCounterexample` then carries any existing positive
singleton-outcome countermodel along a declared observed arrow, deriving its
reference and source gap internally by finite cell search.  The whole action
and conditioner are retained, and extra target outcomes are restored by
marginalization.  The target pivot must still be ignored in the source pair.
`ConditionalReadoutRoute` composes this actual adapter over an arbitrary
finite directed route, with independently supplied supported biased noise at
each destination.  Only the initial pair must ignore the route destinations:
the signature's arrow order transports that invariant through every update.
The empty route keeps the seed pair and restores any extra queried outcomes.
`ConditionalReadoutReachability` constructs genuine route data from the finite
incoming-cut reachability test, including avoidance of the cut at every
destination.  `HedgeConditionalColliderRoute` uses it to find a root-specific
outside parent and a route to an original outcome.  It reindexes the original
hedge at the auxiliary source query, constructs the collider countermodels,
and derives the initial route readiness internally.  The auxiliary parent
need not be queried, all common roots remain the conditioner, and additional
original outcomes are retained.  No seed pair, separated source cell, or
intermediate SCM non-influence invariant is supplied by the graph caller.
`HedgeConditionalLatentColliderRoute` supplies the complementary shared-latent
entry followed by an arbitrary directed tail, also finding unqueried auxiliary
sources and constructing their semantic readiness internally.  Both entry
families use `OutsideRoute` for the same incoming-cut destination proof.
`HedgeConditionalColliderEntry` permits either finite entry test independently
at each common root.  It first retains the genuinely separated semantic root,
then constructs that root's admissible observed or shared-latent entry; it
does not require all roots to admit one uniform kind or choose a root merely
because its graph geometry is convenient.
General mixed active-path composition, unrestricted outcome/conditioner
placement, and the universal
conditional terminal family remain separate obligations.
`ConditionalCounterexampleFailure` proves the converse easy direction:
an independently constructed positive conditional countermodel forces the
actual IDC program to fail, by success soundness and termination.  It returns
the program's own record by a finite case split, not by choice, and does not
construct a countermodel from an arbitrary failed run.

`Soundness` develops the graph-independent probability algebra and the finite
latent factorization needed by the three do-calculus rules.  The factorized
path arguments now construct every rule partition directly from projected
graph compatibility, and `ObservedGraph.publishedSoundness` assembles those
partitions with d-separation correctness into the complete published record.
The older hypothesis-bearing adapters remain useful as documented local
interfaces, but they are no longer obligations of the public theorem.

`Completeness` develops the executable ID side for the positive model class:
successful special cases compile to supported certificates, the two terminal
success-trace constructors compile to formula-aligned packages, finite search
extracts hedge data from checked failures, and shared-switch hedge models
provide positive counterexamples for the covered queries.  `HedgePositive`
uses finite marginalization to reduce full-query separation to one suitable
outcome coordinate.  Its strongest localized mix selects a directed-and-
bidirected action-parent bow and reads only that bow's pair-root.  This removes
parent-uniqueness, odd-parity, identical-neighbourhood assumptions, and all
restrictions on the pivot's other outgoing edges without choosing a family of
pointwise equivalences.  A complete `PublishedCompleteness`
inhabitant still needs a positive countermodel for an arbitrary original-query
hedge and the failure-side conditional non-identifiability argument.  `ChainCompilation`
supplies the probability-algebra foundation of that compiler: an exact,
support-carrying observational chain certificate on any finite host, including
hosts with topological gaps.  It does not identify a recursive ID input with
the host's observational marginal.  The front-door regression in
`Thesis.Examples.IdentificationRegression` proves that a legacy successful
engine formula is incorrect in a positive compatible model: its exact-output
success compiler cannot exist.  A total, action-free engine result is not
itself a certificate.
`IdentificationKernel` now implements the replacement recursion with
current-input prefix quotients, uncut ancestral pruning, and the separate
action-augmentation branch.  `KernelIdentification` proves a quadratic
fuel bound for every invocation of that replacement.  `KernelSuccessCompilation`
now compiles every successful invocation of the changed program by fuel
induction.  `KernelFailureExtraction` supplies the matching general failure
induction for the changed program; old failure traces are not silently reused.
The remaining semantic step is the positive original-query hedge countermodel.
`KernelCompilation` now certifies host marginals and the complete topological
chain product of an arbitrary certified current input, retaining external
intervention parameters and the engine's exact prefix-quotient syntax.  Its
positive-support invariant is propagated directly by finite SCM consistency
and probability algebra, without importing soundness.  Its shared finite
chain fold also assembles any family of certified component factors without
duplicating the prefix induction.  `KernelSeparation` proves the rule-3 later-
action and rule-2 outside-predecessor side conditions from topological order,
recursive host parent closure, and actual c-component membership.
`ComponentCompilation` uses those graph theorems to certify the exact
current-input product for every listed host component, retaining external
actions and supplying positive support for recursion.  It also compiles the
terminal complementary marginal; unions of entire components and empty
subsets are covered by its general closed-subset constructor.  The structural
success compiler applies it to arbitrary containing-component recursion.
`KernelRecursionSeparation` proves incoming-cut non-ancestor isolation and
connects full expanded ancestry to the engine's induced-host tests.  Its
pruning and augmentation side conditions retain their different uncut and
incoming-cut ancestry criteria.  `KernelRecursionCompilation` packages the
certified current-input, positive-support, and parent-closure invariants;
it transports arbitrary nested certificates through pruning, augmentation,
and containing-component restriction without resetting the current expression.
`KernelSuccessCompilation` now applies these constructors throughout the
complete recursion; the original-query hedge countermodel remains separate.
`ProductCompilation` supplies the product branch's graph-independent
regrouping step: inspectable rational associativity and commutativity turn
any indexed finite product into its nonempty partition blocks, including
interleaving components and repeated indices.  Its permutation compiler
uses explicit finite erasure with a constructive proof rather than the
library erasure theorem's choice dependency.  It also substitutes certified
factor reductions into products.  `KernelPartition` proves that the actual
collector is pairwise disjoint and its flattened component members are an
exact permutation of the host vertices.  Its component lookup uses Boolean
finite search, with success and uniqueness proved from the partition.
`KernelProductCompilation` combines arbitrary independently identified
components into their host joint, using reversed graph-derived factor rules,
the shared topological fold, exact regrouping, and support-sensitive formula
comparison.  Its complete split constructor retains the engine's exact
complementary marginal and positive target invariant.  It does not assume
the free joint's identification certificate, and covers arbitrary finite
partitions, external actions, and interleaving components.
`KernelSuccessCompilation` completes that induction over `identifyKernelFuel`.
Every successful invocation has an inspectable supported derivation whose
formula is the engine's literal returned term, with a positive target invariant.
Its public joint wrapper constructs the observational initial input internally;
it does not assume semantic identifiability or a hedge countermodel.
`KernelHedgeTransport` constructs the immediate-failure common-root forests
from the program's distinct uncut and incoming-cut ancestry guards, then lifts
hedges through pruning, augmentation, containing components, and product factors.
`KernelFailureExtraction` applies those transports by fuel induction to every
failed invocation.  It retains exact failure/forest node-set alignment and
constructs a hedge for the original public joint query without a model-class
or counterexample assumption; its graph argument is universe-polymorphic.
`HedgeOutcomeFlow`
proves exact finite support formulas for the general routed hedge models and
packages an unrestricted original-query counterexample when readout routing
does not re-enter `large \ small`; removing that geometric hypothesis and preserving
strict positivity remain the countermodel obligations.  `IdentificationInduction`
supplies exact legacy success, failure, and unfinished traces; the replacement
success and failure inductions instead follow the changed program directly,
not deeper legacy branch-name stacks.  `CompletenessAssembly` is the one-way
integration layer:
it imports the completed soundness theorem without creating a dependency from
`Completeness` back to `Soundness`.  Its support-sensitive Bayes constructor
now combines arbitrary joint certificates into a conditional certificate,
requiring denominator positivity only where the source conditional is defined.
It also proves correctness and identifiability of every successful replacement
joint result.  Its joint-completeness constructor now needs only the explicit
general original-query hedge countermodel leaf in the same model class;
termination, literal-output compilation, and structural failure extraction are
proved internally.  This conditional assembly is not a completed
`PublishedCompleteness` package: the positive hedge leaf and general conditional
failure-side non-identifiability still remain open.
`ValueRefinementCounterexample` separates the fixed-alphabet support issue
from that general semantic leaf.  Ordinary positive Boolean-valued models
on the same graph are deterministically encoded at the supplied rich labels;
then genuinely private, bit-preserving label refinements fill every supplied
value.  Full observational equality and the original bit-dependent causal
gap are retained.  This does not assume that an unrestricted binary hedge
pair has already been constructed, and it never enlarges an observed domain.
`HedgeNoise` supplies the independent finite-noise step of the remaining routed
countermodel: biased XOR channels retain separation after any finite number of
private flips, and full-alphabet carriers realize every background label.
It applies those results to the existing positive root-parity signal without
claiming that a signal distribution is itself a graph-compatible routed SCM.
`HedgeReadout` realizes such a channel as an actual SCM update with a fresh
private source.  At a sink of the kept forest map its common observable
readout preserves the full positive carrier pair's observational law, and
its new interventional bit has exactly the independent channel's probability.
`HedgeCarrierObservationalState` now proves a stronger base law: the observed
assignment, every original private background, and the actual weighted defect
have the same joint observational distribution in both carriers.  Background
predicates may couple arbitrary coordinates with a full observed target; no
independence from the observations is assumed.  These retained backgrounds
are essential when a changed parent flips a descendant away from `second`.
`HedgeInterventionalMarginal` exposes each mechanism's corresponding
retained-state parent-response equation.  `HedgeCarrierReplay` uses those
equations to replay the entire actual response to a single private readout
at any small-forest vertex.  Small-forest closure leaves outer-only vertices
unchanged; excluded parent contributions cancel in the old/new parity
difference, so both carriers use the same full replay.  The stronger joint
law and the actual independent noise product then prove observational
equality without a kept-sink or other-mechanisms-ignore premise.  Responding
descendants and nonbinary labels are included.  This closes that one-step
internal-small case, not arbitrary outer-only updates or finite-plan routing.
`HedgeCarrierReplayPlan` now transports a mechanism-level common response and
retained-state law through an arbitrary finite readout plan.  Pivots may mix
internal small-forest and outside-large-forest vertices; no increasing order,
distinct-pivot, kept-sink, or non-influence condition is needed.  Original
outer-only equations remain factual, while installed readouts compose at
their actual mechanisms and every fresh factor remains in the real prior.
This also proves observational equality of canonical all-root plans which
re-enter the small forest, including responding kept children.  Outer-only
updates and the interventional routing identity remain distinct obligations.
`HedgeReadoutSequence` executes arbitrary finite increasing readout plans.
Its sink-based observational theorem inherits later non-influence from the
original models rather than requesting it separately at every intermediate
update.  Compatibility is unrestricted.  Positivity has the stronger restoring proof:
`PrivateNoise` recovers the entire old target assignment whenever the fresh
bit restores its pivot.  It requires no non-influence or sink premise, so
support survives arbitrary finite plans, even descending or repeated updates
at an internal kept vertex.  The replay companion supplies the broader
small-or-outside observational theorem; support alone does not supply it or
interventional separation.  The remaining routing obligation is to connect
the final outcome signal to all common roots, including responding internal
vertices, and to handle routes that enter the outer-only forest.
`HedgeReadoutEvaluation` exposes the actual folded mechanism equations at
arbitrary current parent inputs, with explicit encodings of every fresh bit.
It does not replace responding descendants by independent coordinate maps.
`HedgeCompensatedReadout` uses those equations to remove the old kept-parent
parity before adding the new composed forest/outcome-flow parity.  It installs
every small-forest row, including old children outside the explicit route,
so obsolete incoming contributions are also removed.  The common plan stays
positive, graph-compatible, and observationally equal on small-or-outside
routes.  The nested model's final sink parity is proved to equal the original
weighted defect XOR all fresh inputs.  `HedgeCompensatedConservation` now
proves the corresponding general large-model identity by comparing effective
sources, including action-cut rows.  Protected outer-only vertices retain
their full values and incoming kept edges under arbitrary interventions;
installed rows need only remain free.  Composite actions, intervened non-sink
vertices, and arbitrary full intervention labels are included.
`HedgeReadoutNoise` integrates the actual private product factors of any
pivot-distinct finite plan.  Pointwise old-signal-plus-fresh-parity identities
then preserve and reflect signal-probability equality under separately biased
weighted noise records; different base latent spaces and denominators are
retained.  It explicitly proves exhaustive encoding of each augmented unit,
rather than inferring independent inputs from a node-indexed representation.
Its full-event slice theorem also integrates comparisons proved separately
at every fixed fresh-input family, without bias or support assumptions.
`HedgeReadoutInputs` supplies the more general occurrence-indexed encoding:
every repeated instruction has its own actual independent input, even when
it modifies the same pivot.  Its complete product-record identity represents
the real final prior for arbitrary plans, not only fixed-input sufficient
comparisons.  Installation order is retained in the mechanism response.
`HedgeCarrierTwoSidedReplay` uses that representation to keep the large and
nested parent maps separate.  Each exact replay permits outer-only updates
and arbitrary interventions.  The full actual event law is its pushforward
of one common retained-state record and the independent instruction inputs;
equality of the fully averaged records is necessary and sufficient for
observational equality.  An explicit probability-preserving recoding may
mix inputs with state and need match only positive-weight atoms.  Neither
that symmetry nor equality of the two different replays is assumed for an
arbitrary route.  The companion outer-re-entry regression exhibits unequal
pointwise responses on a realized positive-probability state and then proves
unequal averaged root-event probabilities.  Every fresh-noise record with
a positive flip also fails for this toggle and these base defect priors;
no probability-preserving joint recoding can match this stated update.
The obstruction does not refute a different plan or broader countermodel
family.  Exact whole-prior integration and independent repeated inputs are
checked separately, without inferring equality from either representation.
This removes an unnecessarily strong fixed-slice comparison boundary, but
does not itself construct an unrestricted positive hedge countermodel.
`HedgeChannelCharacters` begins a different, finite independent-channel
construction.  For every hedge, it transfers outer expansion bits through
actual kept parents and factors each large local character into an arbitrary
typed small-parent character and the selected outer-background characters.
No route-avoidance or protected-outer hypothesis is imposed on this identity.
`HedgeChannelOrthogonality` proves that partially reading a connected channel
gives exactly fair parity under a normalized pair-bit record, by an explicit
finite XOR translation.  A complete channel has even incidence.
`HedgeChannelIntegration` proves exact signed integration and proper-subset
cancellation against the actual independent product of channel records, even
when other channels have arbitrary selections.  The complete row-numerator
expansion is supplied by `Probability.BooleanChannelExpansion`.  The channel
product is only a prior presentation.  `HedgeChannelPairRoot` proves that its
explicit transpose preserves every mixed event and signed integrand of the
actual root-major prior from `Causality.PairRootChannels`, including equal
literal denominators.  Proper-subset cancellation therefore holds for the
original pair-root source grouping.  Its typed local incidence bridge reads
only sources actually incident to each receiving mechanism.
`HedgeChannelTable` realizes positive binary channel rows as actual rational
table SCMs, with compact channel-signal configuration indices, exact row
lookup and hard-intervention factors.  The real model is canonically
semi-Markovian, projects to exactly the supplied graph, and has full observed
Boolean support.  Its complete integrated private-row numerator expansion
retains all cross-row interactions without evaluating private response spaces.
`HedgeChannelLikelihood` connects that complete expansion to the actual
whole-model singleton probabilities, on a common positive denominator.
It integrates each monomial against the genuine root-major prior and proves
that matching all factual expansions with equal row capacities gives equality
of every observed event, not merely coordinate marginals.  Conflicting forced
zero cells and empty blocks are retained without cancelling probability cells.
Its arbitrary-event likelihood and gap criterion retain projection onto the
original queried outcomes: a full-assignment gap alone is not substituted for
an outcome-event gap.
`HedgeChannelMonomial` regroups each actual complete row choice by hidden
channel before using independence.  It derives selected support and forced
row exclusion from the real local choice lists.  A selected connected channel
in a nonzero term must be fully selected; channels sharing a pivot cannot
survive together, and cutting any support vertex kills its selected terms.
The complete likelihood numerator retains the sum of all these actual
monomial integrals, including repeated local labels and zero coefficients.
`HedgeChannelCoefficients` constructs explicit natural-power amplitudes at
one common capacity and proves the strict amplitude-sum bound for every row.
Its actual models are graph-compatible and fully positive.  Anchored large
and small coefficients agree literally at each outer mask, and their complete
finite signed mask sum equals the small coefficient times the entire outer
background product.
`HedgeChannelInstallation` installs the concrete nonredundant outer-mask
slots, forest supports, constructive anchors and typed parent signals for
every supplied hedge.  Its actual models retain one source alphabet, are
compatible and fully positive, and have identical row capacities.  The
installed Boolean signals satisfy the checked character identity.  Distinct
large channels cannot survive together, and forcing the stored original
action vertex cancels every term selecting a large channel, with arbitrary
extra interventions and background terms retained.
`HedgeChannelSurvivors` classifies every nonzero actual factual monomial as
background-only or one full main channel with backgrounds outside its
forest.  Its canonical lists are legal and repetition-free, and their exact
signed sums equal the original nonnegative likelihood numerators.  The full
common background block matches on the actual pair-root prior.  Equality of
the complete observed expansions is therefore exactly equality of the two
remaining full-channel sums, not an assumption that partial terms vanished.
`HedgeChannelFullTerms` evaluates a canonical full choice on that same actual
prior: full forest incidence cancels pointwise, singleton backgrounds have
no internal shared source, and every inactive source slot retains its mass.
`HedgeChannelFullCoefficients` evaluates the literal anchored row products.
Combining a left slot's selected outer mask with its outside-large mask
produces one legal outside-small mask; the corresponding actual right term
has exactly the same coefficient, phase and integrated signed mass.
No common hidden source incident to the entire hedge is introduced by either
construction.  Repetition-free reindexing of the full surviving sums is still
needed to finish universal observational equality of the installed family.
Original-query separation and universal conditional countermodels also
remain open; these constructions do not inhabit `PublishedCompleteness`.
`HedgeCompensatedPreimage` exposes the exact installed-row full-value
preimages in both actual carriers: ordinary/nested incidence equations have
a common private-background test.  That test retains the loss of a nonbinary
background when an old `second` value is flipped, so a parity-only pullback
is insufficient.  `HedgeCompensatedMarginal` assembles these local tests into
the exact full interventional cylinder pullback, compares its weighted
partial-incidence fibres, and integrates every real fresh factor.  Any
coordinate set closed under the original kept and composed flow parents,
and omitting a small-forest vertex, has equal full-value marginals.  That
vertex may have outgoing routes outside the set and need not be a root.
The unused-common-root theorem remains a corollary, and topological prefixes
provide automatic closed sets for installed responding conditioners.
The marginal comparison itself needs no noise support, bias, or route
permission; those are separate obligations of a positive separated pair.
`HedgeCompensatedCounterexample` combines this integration with both flow
identities, full observational replay, support, and compatibility.  It now
constructs positive countermodels for the original joint query on all
small-or-outside canonical routes, including responding internal kept
children and composite actions.  Routes modifying the outer-only forest and
the remaining conditional terminal families still prevent an unrestricted
published completeness theorem.
`ConditionalCounterexampleNormalization` supplies an alternative to matched
denominators: an existing positive joint countermodel with a common reverse
conditional separates the requested conditional in those same models.
Identifiability of the reverse query can supply that equality, but is not
assumed for every query.  The terminal adapter composes with the complete
exchange trace at arbitrary depth.  No general hedge countermodel or
irreducible-terminal countermodel family is asserted by importing it.
`HedgeOutcomeNormalization` reconstructs the kept forest on the unchanged
large vertex set, with all action-free large-side outcome ancestors in the
small set.  All old small vertices are retained, but the common roots may
change.  Action avoidance and small-or-outside routing are then proved
without the old-map absorption tests.  Only connectivity of the computed
small set is supplied; conditional parent closure refers to the new forest.
The companion regression proves both that rerooting repairs a forced-action
absorption obstruction and that the remaining connectivity test can fail.
`HedgeReadoutPullback` supplies the interventional finite-plan induction:
linear parent readouts substitute the final outcome parity backward through
the entire actual SCM sequence.  Retained private bits give biased channels;
even pivot multiplicities cancel the same noise and give identity channels.
Both cases preserve and reflect event equality, with arbitrary merging and
different noise records at different steps.  `HedgeRoutedCounterexample`
combines that theorem with the observational and positivity invariants to
construct a positive counterexample for the original joint query whenever
an explicit increasing sink-pivot plan pulls its outcome event back to common
root parity.  It assumes only those routing conditions, not the new models'
semantic separation or observed-law equality.
`HedgeReadoutPlan` now constructs the plan automatically from a well-formed
routing forest and proves its sink-event pullback by finite flow conservation.
Its hedge specialization uses the canonical all-root routes, so no caller
supplies a plan, ordering, or parity identity.  The positive original-query
constructor requires only that these route vertices be sinks of the original
kept c-forest map; a more general entry point allows different supported
biased noise records at every vertex.  Arbitrarily many sources, merging,
multiple outcome sinks, and the full observed alphabet are covered.
Internal-forest re-entry need not satisfy that non-influence condition.
The compensated constructor covers small-forest re-entry without it;
outer-only route updates remain an open general hedge-countermodel case.
`HedgePartialIncidence` develops the counting needed for intervention and
marginal events rather than incorrectly requiring complete even targets.
An untested component vertex absorbs ordinary incidence parity; an untested
inner vertex absorbs the nested constraint while retaining arbitrary outer
equations.  Explicit finite sections and XOR involutions prove equal sizes
of all partial target fibres for each map.  This is not yet a comparison
of two different maps by itself.  `HedgePartialIncidenceComparison` now
constructs injections between the two partial zero fibres when an inner row
is omitted, then uses the within-map translations to compare arbitrary
ordinary/nested targets on the same tested rows.  The omitted inner row also
supplies the outer parity correction.  `HedgePartialIncidenceProbability`
lifts that count to the actual biased prior, retaining arbitrary common
private-background predicates and defect-dependent targets.  Exact weighted
incidence-event masses and their probabilities agree.  The companion
`HedgeInterventionalMarginal` now proves the semantic pullback for the actual
carrier pair: agreement off a common root is exactly intervention consistency,
partial incidence, and a common full-alphabet background test.  Topological
recursion proves its reverse direction using only the kept parent equations.
Thus all root-omitted cylinder masses, and every event local to that marginal,
agree under arbitrary interventions.  The result includes nonbinary labels,
zero events, and intervention-inconsistent targets.  It does not assert full
law equality on the separating common root.
`HedgeInterventionalSupport` connects that section to the actual large
carrier SCM.  An intervened forest vertex absorbs the correction, so any
consistent full-alphabet target has positive mass with either specified
defect bit under arbitrary interventions fixing such a vertex.  The original
hedge action supplies its own balancing seed.  A fixed pair-root compensation
also preserves the complete interventional evaluation when the defect flips,
pointwise in all pair and private-background coordinates.
`HedgeInterventionalProbability` now connects that coupling to the original
biased prior.  Its two-to-one singleton weights give a two-to-one event-slice
mass ratio, not equality of the raw masses.  Conditioning on either defect
normalizes that ratio and gives the original probability for every observed
event under an intervention fixing a large-forest vertex.  The original hedge
action supplies such a vertex internally.  The root-omitted companion compares
large/small conditioning marginals in the original pair.  Denominators of
unrestricted routed pairs still need their own semantic argument; they are
not silently identified with these unmodified carriers.
`ConditionalCompilation` constructs supported, literal-output certificates
for every successful run of recursive IDC over the corrected joint engine.
Each successful single-conditioner rule-2 test is retained, arbitrary exchange
sequences are covered by fuel induction, and termination follows from strict
conditioner decrease.  The terminal Bayes denominator marginalizes the one
identified numerator certificate rather than making another ID call.  This
proves success correctness and identifiability, not the converse: an
irreducible terminal joint failure still needs a conditional countermodel or
the equivalent semantic non-identifiability argument.
`ConditionalFailureExtraction` supplies the matching general failure induction:
every failed conditional invocation retains its actual irreducible terminal,
exhausted singleton-exchange search, terminal numerator hedge, and complete
original-query exchange trace.  A terminal conditional countermodel transports
through that trace in the same positive model class using the same two models.
The chain-rule leaf proves conditional separation whenever a numerator's
countermodel pair agrees on the denominator; the empty-condition conversion
does not require positivity.  Its final assembly constructor therefore makes
the two remaining semantic families explicit rather than assuming that a
failed numerator automatically separates its conditional.  Those families
are not yet inhabited in general.
The constructor `HedgeWitness.positiveCounterexampleOfRootsSubsetOutcome`
in `HedgePositive` also restores the original joint query whenever all common
roots are selected outcomes, by
finite marginalization of the full positive carrier pair.  Arbitrary extra
outcomes and multiple roots are covered.  Root-to-outcome reachability alone
is not the subset hypothesis, so the unrestricted routing gap remains open.
That pair has identical intervention responses on every coordinate outside
the large forest, with the same latent units and prior.  Thus a conditioner
outside the forest has a matched denominator without a class-level
identifiability premise.  `ConditionalFailureExtraction` combines this fact
with root separation into a positive conditional countermodel when the
common roots are queried outcomes.  A nonempty-condition regression verifies
an actual failed numerator and exhausted exchange search, while a directed
outcome-to-conditioner edge makes the terminal genuinely irreducible.  The
conditioner may therefore be a graphical descendant, not only an isolated
coordinate.  `HedgeConditionalMarginal` strengthens the numerator-root case:
it removes the outside-forest condition entirely and permits some common
roots to be conditioners.  All roots must appear in the numerator, with only
one required to be a queried outcome.  Outcome/condition disjointness supplies
an omitted root, and the actual interventional marginal theorem matches the
denominator in the same numerator-separating pair.  A finite meeting test
recovers the queried root without choice.  An irreducible three-value
regression places its conditioner inside both forests; a two-root regression
queries one root while conditioning on the other, explicitly refuting the
older all-roots-in-outcome premise.  The general routing and remaining
conditional terminals are not silently included in these proved cases.
`HedgeConditionalReadout` extends that conditional construction to common
roots which are not queried outcomes.  Its canonical all-root plan produces
the routed numerator countermodel, while the off-pivot event and kernel
preservation theorems in `PrivateNoise` and `HedgeReadoutSequence` retain the
conditioning denominator on each actual updated model.  Conditioners must
be outside both the original large forest and the modified route nodes;
graphical descendants are permitted.  Arbitrary supported biased noise may
be specified independently by routing vertex.  The chain-rule conversion
uses the same routed pair, not an equality proved only for the base models.
The companion `HedgeConditionalCompensatedReadout` removes both the kept-sink
and outside-large conditioner requirements on its permitted routes.
`HedgeReadoutPreservation` transports local mechanism closure through arbitrary
finite plans, including descending order and repeated pivots with separate
actual private factors.  Protected coordinates outside the installed mask
keep their full values under every intervention; unprotected descendants may
respond.  The original root-omitted marginal theorem matches the base
denominator, and each actual fold preserves it separately.  Thus protected
outer-only conditioners are allowed even when internal small-forest readouts
have kept children.  Its terminal constructor transports the same models back
through any extracted IDC exchange depth without new nested-fail stacks.
A three-value regression checks an irreducible engine failure with a late
outer-only conditioner and an outside-to-internal re-entry route.  Balanced
and unsupported repeated noise factors additionally check that denominator
preservation itself needs neither support nor bias; those factors are not
used by the positive countermodel.
The full compensated marginal comparison supplies a second conditional
constructor when one common root meets the queried outcome.  Canonical
routing stops at that root, and disjointness omits it from the denominator;
all other conditioners may be installed, responding, or other common roots.
No coverage of every root by the numerator is required.  A second three-value
regression refutes `P(Y | do(A), B)` with an installed internal conditioner
and another root still requiring outside-to-small routing; neither older
conditional constructor applies to it.  Its empty-action marginal is checked
as well.  The general parent-closed constructor removes the queried-root
requirement: an omitted small-forest equation suffices when a closed set
contains the conditioner.  An arbitrary-depth IDC terminal adapter uses
the same construction before restoring the original query.  A further
three-value regression has no queried common root, an installed non-sink
conditioner, and an omitted root still routing to an outside outcome; a
second query balances at a non-root with an original kept child.  Both are
actual irreducible engine failures.  Conditioners without protection or a
suitable omitted-small closed set, and outer-only route updates, remain
open general cases; no universal terminal countermodel is asserted.
`HedgeSmallAbsorption` handles further outer-route cases by changing the
small forest before constructing the positive pair.  Its kept-descendant
closure absorbs every large route vertex and all original successors they
require, while preserving the query, large side, roots, and kept map.
Connectivity and action avoidance are checked explicitly; arbitrary larger
connected child-closed enlargements may supply additional connectors.
Minimality proves that a failing action-avoidance test cannot be fixed by
same-map enlargement alone.  The joint and conditional constructors concern
the newly indexed carrier pair, not an unsupported outer update of the old
models.  A three-value regression has formerly forbidden outer routes and
an absorbed responding conditioner whose off-route kept child is added by
closure and supplies a denominator balancing equation.  General failures
of this normalization and the remaining conditional denominator geometries
still require the unrestricted countermodel arguments.
`HedgeOutcomeNormalization` also changes the kept map and common roots,
using all action-free large outcome ancestors as the new small side.
Canonical routes then satisfy the compensated geometry automatically;
connectivity is a genuine remaining finite test, not a universal theorem.
`HedgeCountermodelSearch` searches alternative large sets, small sets, and
kept maps with the carrier-routing test inside the candidate scan.  Any
contained ready selection guarantees search success, and the returned
typed witness constructs the actual positive original-query countermodel.
Its universal coverage boundary is purely structural: proving a suitable
selection for every hedge would supply the general semantic hedge leaf
without choice on graphs with that property.  The seven-node regression in
`Thesis.Examples.HedgeCarrierRouteObstruction` proves that the property is
not true in general: both the canonical-route scan and the more permissive
arbitrary-route scan fail despite a valid hedge and an actual ID failure.
Every alternative hedge lacks an all-root family of paths avoiding its
outer-only vertices.  Consequently changing route tie-breaking or adding
more forest-search wrappers cannot complete the general positive hedge
leaf; that construction must be broadened or replaced.  The covered
countermodels remain valid, and the general hedge and conditional terminal
countermodel arguments remain open.

The remaining modules transport ordinary, modal, learning, hidden-DAG, and
counterfactual certificates.  The project-wide axiom audit checks declarations
reachable through this facade and permits only the foundational `propext` and
`Quot.sound` axioms.
-/
