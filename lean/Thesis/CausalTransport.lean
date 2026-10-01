import Thesis.CausalTransport.DSeparation
import Thesis.CausalTransport.DSeparationCorrectness
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
import Thesis.CausalTransport.HedgeNoise
import Thesis.CausalTransport.HedgeReadout
import Thesis.CausalTransport.HedgeReadoutSequence
import Thesis.CausalTransport.HedgeReadoutPullback
import Thesis.CausalTransport.HedgeRoutedCounterexample
import Thesis.CausalTransport.HedgeReadoutPlan
import Thesis.CausalTransport.CompletenessAssembly
import Thesis.CausalTransport.ConditionalCompilation
import Thesis.CausalTransport.ConditionalFailureExtraction
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
import Thesis.CausalTransport.HedgeCompensatedReadout
import Thesis.CausalTransport.HedgeCompensatedConservation
import Thesis.CausalTransport.HedgeCompensatedCounterexample

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
`HedgeCompensatedCounterexample` combines this integration with both flow
identities, full observational replay, support, and compatibility.  It now
constructs positive countermodels for the original joint query on all
small-or-outside canonical routes, including responding internal kept
children and composite actions.  Routes modifying the outer-only forest and
the remaining conditional terminal families still prevent an unrestricted
published completeness theorem.
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
Internal-forest re-entry and conditioners on those modified coordinates
still belong to the general terminal countermodel obligation.

The remaining modules transport ordinary, modal, learning, hidden-DAG, and
counterfactual certificates.  The project-wide axiom audit checks declarations
reachable through this facade and permits only the foundational `propext` and
`Quot.sound` axioms.
-/
