# Causal theorem coverage and application boundaries

This guide separates graph-level identification from applying a formula at a
particular law, and both from fixed-law identification. The actual Lean
statements remain authoritative. All implemented probability theorems concern
finite rational records, with zero-weight cells permitted unless an explicit positivity
assumption says otherwise. Original hidden DAG results allow arbitrary finite
hidden and private-noise alphabet sizes; observed alphabets remain fixed.
Research checkpoints below are labelled assessments, not additional Lean
theorems. The real-to-rational comparison only explains a limit of importing
an external method; it does not extend the probability framework.

## Graph-level ID/IDC

| Question | Public implementation | Essential boundary |
| --- | --- | --- |
| Are the three do-calculus rules sound? | `ObservedGraph.publishedSoundness`; native interpretation in `HiddenDAGSoundness` | Graphical hypotheses and support for the particular derivation; no external rule-soundness axiom. |
| Does ID/IDC characterize positive-class identifiability? | `HiddenDAGModelClass.identifyJointKernel_identifiable_iff` and `identifyConditionalKernel_identifiable_iff`, in `HiddenDAGCorrespondence` | A value-rich finite observed signature: two supplied distinct values at each node. |
| Are original hidden DAG countermodels actually constructed? | `FiniteLatentProjection.publishedHiddenDAGCompleteness`, in `HiddenDAGCompleteness` | The unchanged original query and original hidden DAG; not merely a counterexample in a chosen canonical family. |
| What completeness is established while allowing zeros? | `HiddenDAGSupportedDomain.identifyGuardedJointKernel_identifiable_iff` and `identifyGuardedConditionalKernel_identifiable_iff`, in `HiddenDAGSupportedCorrespondence` | Expression-qualified supported representation with positive-model coverage; not universal applicability of one chosen expression at every law. |

Joint and conditional statements are distinct. A conditional query's original
causal conditioner must itself have positive mass where its value is used.
This is not implied merely by evaluating an observational formula successfully.

The intrinsic supported domain deliberately need not require factual action
overlap. `PaperJointAdmissibleAt` and `PaperConditionalAdmissibleAt` retain the
additional displayed observational action condition as separately named
boundaries. Neither action positivity alone nor action positivity together
with an unrelated source condition guarantees all used conditionals exist.

## Applying a successful certificate

`GuardedAdmissibleCertificates` constructs inspectable successful derivations.
The joint certificate's `intrinsic_soundAt` needs the printed formula's
`UsedConditionalsAdmissibleAt` tests. The conditional version also needs
`ConditioningAdmissibleAt` for the original target. These premises are explicit;
undefined values are not interpreted as `0 / 0 = 0`.

There are four different situations an application must not conflate:

1. **Structural ID/IDC failure:** a graph-level failure, with native
   countermodels supplied by the applicable completeness theorem. This does
   not classify every special observed distribution separately.
2. **Guard rejected:** a supplied candidate's observable guard fails, such as
   its probability-one action condition. This candidate cannot be applied.
3. **Expression unavailable:** partial evaluation of this expression fails.
   For a certified action-free plan this concerns its own used denominators;
   an arbitrary uncertified plan may instead contain an actionful kernel leaf.
4. **Original conditional target support still required:** even a ready
   observational expression does not settle this separate causal requirement.

`ObservationalFormulaPlan.diagnose` in `ObservationalFormulaDiagnostics`
reports cases 2 and 3 separately and returns the evaluated value when ready.
`diagnose_isReady_eq_available` proves exact agreement with the existing
selector. `select_none_iff_no_ready_diagnosis` proves catalogue exhaustion
means every *listed* plan is unavailable. These diagnostics do not make a
general decision about case 1 or case 4, and do not certify arbitrary input
plans merely by evaluating them.

`ObservationalFormulaSelection` is complete within the supplied finite
certified catalogue. `BackdoorAdjustmentSearch.covariates_member_iff` and
`select_complete_iff` exhaust the covariate sets satisfying the implemented
two-do-rule adjustment criterion. Neither theorem ranges over all possible
identification formulas or every generalized adjustment criterion.

## Exact support-pattern applicability

`ProbabilityTerm.supportStatus_exact`, in `ObservationalFormulaSupport`,
proves an exact three-state evaluator: undefined, defined zero, or positive.
Its input is only the positive-support bits of complete observed assignments.
It covers every current term constructor, including finite marginalization,
fixed-reference evaluation and asymmetric zero-weighted multiplication.
Strict multiplication still propagates undefined values beside a zero;
division by a zero denominator remains undefined. Fractions need not be
reduced, and records may repeat labels or contain zero-weight atoms.

`ObservationalFormulaGuard.checkSupport_exact` also handles both current
guards. A probability-one action holds exactly when its complement contains
no supported assignment. `availableOnSupport_exact` therefore agrees with
the existing actual plan evaluator, and `available_eq_of_support_eq` proves
availability invariant under arbitrary positive reweighting on the same
support. Numerical formula values are **not** invariant; the one-variable
regression checks a fair and biased record with equal support and unequal
event probabilities. Signed cancellation or future numerical threshold
guards are outside this abstraction unless separately proved compatible.

`FormulaSupportCatalogue` enumerates Boolean support patterns and excludes
the impossible empty support. `coverageIncluded_iff` specifies its exhaustive
comparison of supplied catalogues over those patterns and all references;
`coverageIncluded_transfer` applies a passing comparison to every actual
normalized observed record. `sameCoverage` tests mutual inclusion, useful for
checking a proposed deletion. `mem_uncoveredPatterns_iff` specifies the
reported uncovered patterns. These are opt-in small-instance computations:
there are exponentially many patterns in the number of observed assignments.
Nonempty patterns may still be incompatible with the causal graph, so a
failed comparison is not automatically a native causal counterexample.

None of this certifies arbitrary input plans or discovers every valid
formula. The finite pattern space removes numerical weights from the
applicability question; it does not bound the length of a certificate that
might cover a previously uncovered pattern. Original conditional-target
support also remains a separate causal premise.

### Research checkpoint 5: alternative-formula coverage

This is a bounded assessment, not an additional Lean completeness theorem.
The natural first scope fixes the observed signature, the original finite
hidden DAG/projection and a joint query. Candidates are the current
`GuardedObservationalFormula` objects: current `ProbabilityTerm` syntax,
action-free output, either existing guard, and the native interpretation
proof. Maximal catalogue coverage would mean: for **every native model and
reference**, whenever **any such certified candidate** is available, some
member of one constructed finite catalogue is available. This is not merely
coverage of ID's chosen expression, nor fixed-law point identification.
A conditional-query version must retain its original source-support premise.

There are finitely many support/reference pairs, but that does not yet give
an algorithm for choosing a candidate for every coverable pair. In particular,
the current `interpret` field is an arbitrary native semantic proof, not a
serialized proof language with a decidable certificate checker. Bounding
expression depth alone therefore does not decide which expressions can be
certified by that interface.

A complete **bounded derivation search** has a concrete route: canonically
enumerate kernels, node selections, fixed assignments and terms up to an
explicit height; enumerate derivation trees up to a separate size bound;
check graphical leaves; reconstruct accepted derivations; then compile only
those whose intermediate support obligations have been discharged. The
`eqCongr` constructor requires extensional finite-function normalization,
not equality of arbitrary function implementations. All intermediate terms,
not only the final printed expression, must respect the declared bounds.
The bounded theorem would cover this specified proof grammar, not every
arbitrary semantic proof inhabiting `interpret`.

Intermediate support is a real additional obligation. Endpoint availability
alone is not a support witness for every intervened intermediate kernel.
The two current guards (`always`, `actionOne`) cannot express an arbitrary
extra support condition; generic support-certificate syntax or a richer
proved guard language may be needed. Enumerating terms and applying existing
soundness without addressing this step would be incomplete.

The universal stopping argument remains unresolved. Finitely many support
cells bound the number of *coverage gains*, not the delay until the next
gain: even one new cell can first appear after an arbitrarily long initial
plateau. Neither a plateau nor bounded-search exhaustion certifies universal
exhaustion. A proof-length bound, finite complete rewrite/derivation basis,
or another complete coverability decision is still needed. This refutes
that proposed stopping shortcut; it is not an impossibility proof for a
universal selector. Review checkpoint: specify the proof/guard grammar before
building generic search infrastructure.

## Fixed-law results beyond graph-level completeness

| Graph/target | Public theorem | Scope |
| --- | --- | --- |
| Binary confounded pair (bow), one risk | `BinaryBow.identified_iff_action_one` | Complete fixed-law classification; the requested action must have probability one. |
| Bow attainable values | `BinaryBow` results in `BinaryBowAttainable` | Every rational value between the sharp bounds has a native witness. |
| Binary IV compatibility | `BinaryInstrumental.computedBounds_compatible_iff` | The executable flag is equivalent to existence of an original-DAG native model with the entire law. |
| Binary IV sharp risks and ATE | `BinaryInstrumental.computedBounds_sharp` | Universal bounds, all four simultaneous risk corners, and native ATE endpoints; includes either null instrument arm. |
| Binary IV point identification | `riskIdentifiedAt_iff_bounds_equiv`, `effectIdentifiedAt_iff_bounds_equiv` in `BinaryInstrumentalIdentification` | Complete fixed-law classification for compatible observations, by coincident exact rational bounds. |
| Binary IV attainable sets | `risksAttainableAt_iff_computed_bounds`, `effectScoreAttainableAt_iff_computed_bounds` in `BinaryInstrumentalAttainable` | Exactly the rational risk rectangle and affine ATE-score interval when compatible; empty when incompatible. Every included pair has one native whole-law witness. |

IV has observed binary `Z -> X -> Y` and only the `X <-> Y` bidirected edge.
There is no monotonicity assumption. `lowerEffect` and `upperEffect` contain
the increasing affine score **`(ATE + 1) / 2`**, not raw ATE: decode by `2s - 1`.
Negative effects are not truncated natural subtractions. `EffectIdentifiedAt`
compares these injective scores for all models with the given whole law.
Compatibility is required to exclude vacuous identification on an empty class.

Sharp endpoint attainment alone would not state that every rational interior
value is attained. The additional IV mixture theorems now prove that claim:
they mix feasible response records while keeping the instrument independent,
then realize a native model on the original DAG. They do not assume arbitrary
independent-source model classes are convex. The separate polynomial layer
described below checks supplied certificates for explicit finite source
presentations; there is no claimed complete arbitrary-graph fixed-law optimizer.

## Constructive probability-record and independent-source compression

`FiniteIntegerCompression.compress` constructs a normalized finite probability
record preserving a supplied family of integer-valued expectations.
`FiniteRationalCompression.compress` extends this to arbitrary signed rational
responses by explicit finite denominator clearing. For `m` supplied responses,
the output contains at most `m + 1` positive atom occurrences, uses only original
labels, and preserves every normalized response expectation. Repeated labels,
zero input weights, negative response values and an empty response family are
allowed. Probability weights remain natural, never signed. The ambient sample
type need not itself have an enumeration or decidable equality.

`FiniteSourceCompression.compress` applies that theorem to one source paired
with an unchanged independent background. Its `Replacement.preserved` field
proves equality of each requested joint-event probability for the actual new
product record; `Replacement.independent` proves independence of the new source
and the entire unchanged background. Responses are computed by integrating the
background, not by conditioning on the source, so zero source probabilities
introduce no division or support premise.

`FiniteProductSourceCompression.compress` iterates coordinate replacement over
an explicitly finite independent family. It retains each earlier support bound
and positivity proof, constructs the full product law after every update, and
preserves every requested event. The original prior need only satisfy its
product law; it need not literally be a canonical product record. Whole-event
extensionality justifies reinserting the old factor and rebuilding a canonical
prior without accumulating unused overwritten coordinate copies.

`FiniteHiddenDAGSCM.compressSources`, in `HiddenDAGSourceCompression`, constructs
a native `SourceCompression.model` on the unchanged original hidden DAG. For
`m` supplied `NativeProbabilityQuery` values, every source has at most `m + 1`
positive atom occurrences, all sources remain independent, and every specified
observational/interventional event probability is preserved. The theorem
`withSourceLaw_evalObserved` proves unchanged structural readouts for every
noise assignment and every hard intervention. There is no observational-cell
positivity premise. An empty hard intervention specifies an observational
query; preserving a conditional additionally requires its joint and conditioner
probabilities and the original positive denominator, not a value at zero mass.
`SourceCompression.query_positive_iff` transports that support exactly, and
`quotient_preserved` proves equality of the corresponding supported ratios.

For fixed-observation applications, `compressSourcesPreservingObservation` in
`HiddenDAGObservationalCompression` automatically adds every observational
singleton query. Its `ObservationalSourceCompression.observational` field proves
equality of **every** observed event, in addition to all supplied target queries.
Each source then has at most `number of observed assignments + number of target
queries + 1` positive atom occurrences. This sufficient bound is not asserted
to be minimal; users need not remember to supply the factual table themselves.

These are constructed replacements, not external compression assumptions.
The bounds concern actual positive atom occurrences; the original ambient
noise types, node value types and structural mechanisms remain unchanged.
They do not themselves compress hidden endogenous alphabets, enumerate all
mechanisms, or supply a complete rational feasibility optimizer.

## Exact probability polynomials and supplied bound certificates

`RationalPolynomial` represents finite sparse polynomials with signed rational
coefficients and natural exponent vectors. `equalityCheck_sound` in
`RationalPolynomialIdentity` proves that an accepted identity holds for every
signed rational parameter assignment, not just numerical test points. Repeated
monomials, reordered products and unreduced coefficient fractions are allowed.

`PolynomialBoundCertificate.check_sound` checks an exact decomposition into
nonnegative rational weights times polynomial squares times products of listed
nonnegative constraints, plus arbitrary polynomial multiples of listed zero
constraints. It checks both the coefficient signs and the polynomial identity.
The theorem proves nonnegativity throughout the supplied constraint domain.
It does not trust an optimizer's reported bound or assume the identity printed
by a producer. Rejection does not establish that a bound is false.

`FiniteProbabilityPolynomial.compile_sound` connects the constructed event
polynomial to an actual finite independent law, using explicit complete source
enumerations and singleton-probability variables. The supplied prior need only
satisfy its product law, rather than literally be a canonical product record.
Zero source cells, repeated record atoms and duplicate enumeration labels are
handled; joint states are deduplicated before summation. This is unconditional
finite probability compilation, not a definition of an undefined conditional.

`FiniteProbabilityPolynomialEncoding` constructs a two-sided finite encoding
of coordinate/state pairs and their actual probability parameters. Its
`sourceParameters_nonnegative` and `normalization_sound` prove the basic source
constraints. `compileEncoded` in `FiniteProbabilityPolynomialCertificates`
packages that binding and those constraints with the compiled event.
`Compiled.checkLower_sound` and `checkUpper_sound` turn accepted supplied
certificates into inequalities about the original event probability, with no
external polynomial-likelihood correspondence or source-normalization premise.

`FiniteHiddenDAGSCM.probabilityProgram_sound` in `HiddenDAGPolynomial` applies
that construction to the noise event computed by an actual native structural
model under a hard intervention. Its `checkProbabilityLower_sound` and
`checkProbabilityUpper_sound` conclude bounds on that model's interventional
event value. The `*_sound_forSourceLaw` variants reuse the same checked
certificate for every independent law on the unchanged finite structural
template. The polynomial and basic constraints are invariant under that
replacement; source probabilities are parameters, not frozen coefficients.

`HiddenDAGPolynomialExpressions` compiles signed constants, primitive native
queries, sums, negatives and products using a shared source-variable encoding.
`expressionPolynomial_sound` preserves their actual signed rational semantics;
an effect difference is not forced into the type of nonnegative probabilities.

`HiddenDAGPolynomialEvidence` constructs additional zero constraints directly
from a finite catalogue of native query/reference pairs. Its
`checkExpressionNonnegative_sound`, `checkExpressionLower_sound` and
`checkExpressionUpper_sound` require that the candidate model fits that data.
The `*_sound_forSourceLaw` theorem reuses one checked certificate for every
fitted independent law on the same template. The fit premise concerns the
replacement law itself, not just the model used to build the polynomial.
`observationalEquations` automatically lists the full observed table, and
`satisfies_observationalEquations_iff` proves that satisfying this catalogue is
exactly equality of every observed event probability. Observed zeros are allowed.

Acceptance is a universal implication for fitted candidates, not a witness
that the data are compatible or that the proposed endpoint is attained.
An infeasible catalogue has no fitted models. General sharpness and point
identification therefore need separate feasibility and attainment theorems;
the IV results above establish those extra obligations for their own class.

The current compiled-bound API concerns explicit finite source presentations
and fixed structural templates. Source-atom compression alone does not prove
that one fixed choice of hidden endogenous alphabets and structural mechanisms
covers every model on a graph. No complete optimizer, general certificate
search, real-to-rational feasibility transfer, or universal arbitrary-graph
fixed-law decision procedure is asserted. Conditional bounds additionally
require justified cross-multiplication at a positive denominator.

### Graph-wide coverage: assessed route, not a proved theorem

For a **fixed full hidden DAG** with fixed observed domains, there is a
plausible finite constructive route beyond the current fixed-template checker.
Retain all observed singleton queries and the finitely many primitive queries
appearing in the requested target. Existing source compression gives a bound
`K = number of retained queries + 1` for each source's positive atom occurrences.
It does not yet change those sources' ambient types to a common finite alphabet.

The missing representation steps would be:

1. Relabel each compressed source by at most `K` atom positions, preserving
   independence and every retained intervention probability. Padding unused
   positions with zero mass must be justified, not identified with positive cells.
2. Enumerate the hidden values reached under the retained interventions and
   relabel them too. With `N` native nodes and `I` listed interventions, a
   crude candidate bound is `I * K^N` values per hidden node. Mechanisms on
   unreachable parent inputs need explicit defaults, while evaluator simulation
   must prove those defaults cannot change a retained trajectory.
3. Enumerate finite mechanism tables on those bounded domains, then prove that
   every original model has a representative in this family with the same
   observed law and target values. Only that coverage theorem would justify
   checking one certificate per template to establish a graph-wide bound.

These are proposed proof obligations, not existing formal cardinality or
coverage results. The finite search can also be enormous; mathematical
finiteness is not an efficiency guarantee. If only an observed projection is
fixed while the number and arrangement of hidden nodes vary, another graph
representation theorem is needed as well. A potentially better route for that
class starts with the existing intervention-preserving `HiddenDAGCollapse`:
group independent roots by their observed-child incidence set, prove the
grouped product law and readout preservation, then compress and relabel those
groups. There are at most `2^(number of observed nodes)` such incidence sets,
but the grouping and coverage theorems are not implemented. Roots with three
or more children must remain allowed; replacing them by independent pairwise
causes would not be justified by the current collapse theorem. This route
might avoid directly relabelling every internal hidden-node alphabet, and
should be compared with the unchanged-full-DAG route before implementation.
Even successful finite-template
coverage would leave infinitely many rational source-weight assignments;
it would not, by itself, prove complete certificate search, optimization or
rational feasibility decision. No excluded-middle, choice or real-to-rational
transfer principle is silently added at any of these boundaries.

### Research checkpoint 6: representation adapters

The first step has a direct constructive implementation strategy using
existing interfaces. Apply `FiniteProbRecord.atomPresentation` to each
compressed factor; its code size is that factor's actual atom count, already
bounded by `K`. Give the new native model the canonical product of these
finite code records and compose each mechanism with its coordinate decoder.
Use the original complete noise enumerations and
`FiniteProduct.probVal_extensional_of_rectangles` to prove that decoding the
new prior recovers every original noise-event probability. An evaluator
simulation through the native equations then transports every retained
intervention, the whole observed law and supported target ratios. The
decoder need not be a bijection of the old ambient noise type. Compact
`Fin k_j` sources avoid padding; a common `Fin K` presentation can be added
separately with zero-weight positions and an explicit decoded default.

For a fixed full DAG, the proposed hidden-value bound can be made precise
as follows: enumerate all coded noise assignments and each retained hard
intervention, evaluate each hidden vertex, and deduplicate its resulting
values. With `N` native nodes this gives at most `I * product_j k_j`, hence
at most `I * K^N`, values per hidden vertex. Defaults on other parent-table
rows must be proved unreachable on every retained trajectory by rank
induction. Normalize observed native values using their supplied two-sided
observed-value equivalences rather than discarding permitted null values.
This simulation and finite-table completeness are not implemented yet.

Preserving **all** hard-intervention distributions is still a finite target:
if coordinate `i` has `d_i` declared values, enumerate
`I = product_i (1 + d_i)` interventions and all `A` observed singleton
events for each. Source compression on that `I * A` query family gives the
candidate bound `K = I * A + 1`. This is an assessed sufficient route, not
a proved cardinality theorem or practical enumeration recommendation.
It concerns each intervention's distribution, not arbitrary joint
cross-world counterfactuals unless those are retained separately as well.

For a fixed observed projection with varying hidden topology,
`FiniteHiddenDAGSCM.toLatentRootSCM` in `HiddenDAGCollapse` is the useful
starting point. Group its
independent roots by identical observed-child incidence, keeping all child
sets, including sets of size greater than two. There are at most `2^n`
incidence masks for `n` observed nodes. The missing proofs are grouped-law
independence, local decoder/evaluator simulation and exact projection
preservation, followed by compression and finite mechanism enumeration.
Dummy constant sources cannot simply be given arbitrary children: their
arrows still add graphical bidirected edges. Omit unused masks, give them no
arrows, or justify that their arrows add no edge outside the required graph.

A cleaner fixed-template candidate is one root for **every bidirected
clique mask**, including singleton masks and optionally the empty mask.
Every original collapsed root's child set is such a clique. Group roots
with that exact mask; use a unit-valued source when a clique has no original
root. These dummy clique arrows add no forbidden edge, and including the
two-vertex masks recovers every required bidirected edge. The number of
roots is still at most `2^n`. This avoids a model-dependent incidence table,
but the probability/evaluator grouping and converse native-graph realization
still need proofs. It retains multi-child causes rather than wrongly
reducing to pairwise roots. This route changes the full hidden DAG and must
not be confused with the fixed-full-DAG representation above.
The current native APIs are indexed by a projection object that also fixes
its full hidden DAG. A projection-only search would need an explicit union
over full hidden DAGs with the same observed graph, rather than silently
changing the model class of an existing theorem.

Finite source bounds are also established for discrete independent-source
networks by [Rosset, Gisin and Wolfe](https://arxiv.org/abs/1709.00707).
That is supporting literature, not a Lean assumption or an automatic
rational/constructive transfer. The repository's existing compression proof
is the proposed rational foundation. Review checkpoint: implement the
compact source adapter first; choose fixed-full-DAG versus projection-wide
coverage before undertaking hidden-table or root-grouping infrastructure.

## Research checkpoint 7: fixed-observed-law procedures

This assessment separates three possible extensions. None is currently a
new unrestricted rational identification theorem.

**A further linearizable class.** A finite categorical confounded pair
(`X -> Y`, `X <-> Y`) has a direct constructive route beyond the existing
binary bow and binary IV results. For a fixed treatment `x`, let
`p_xy = P(X=x,Y=y)` and let `q_y` be the proposed intervention marginal.
The candidate attainable-set characterization is
`q_y >= p_xy` for every outcome, with nonnegative rational `q_y` summing to
one. The residual total is exactly `1 - P(X=x)`. At positive residual mass,
allocate its normalized categorical distribution to units factually outside
the requested action; at zero residual use the factual law without division.
A shared finite root carrying the factual pair and the residual outcome
gives the proposed native witness. Generic consistency bounds supply the
other inclusion, and the two-node canonical realization machinery provides
the original-DAG route. With at least two permitted outcome values, the
proposed full-marginal identification criterion is `P(X=x)=1`. A single
event needs its own qualification: the empty/full outcome events are trivial
even without action overlap. These are assessed statements and construction
steps, not yet formalized categorical-bow theorems.

**Explicitly bounded models.** For a fixed full graph, fixed finite node/source
alphabets and a supplied upper bound `D` on each source denominator, enumerate
all nonnegative weight vectors with positive total at most `D`, and all
typed finite mechanism tables. Filter by exact equality of every observed
singleton probability. An empty list means incompatible **within that bounded
class**; otherwise compare the actual target values, returning either a
common value or a pair of disagreeing native models. Constructing results
from this list needs no choice. Completeness requires the representation
normalization/padding theorem, and conditional targets need an explicit
policy for compatible models with null target conditioners. Increasing
`D` does not itself give a terminating unrestricted procedure.

**Unrestricted rational models.** Representation bounds control alphabet and
table sizes, not the infinitely many rational source weights. The remaining
constraints can be polynomial rather than linear. [Duarte et al.](https://arxiv.org/html/2109.13471v1)
develop polynomial causal optimization with successively refined inner/outer
bounds and an epsilon-sharp stopping criterion. Those results do not by
themselves provide a terminating exact rational-only feasibility/uniqueness
checker in this library. In particular, real feasibility must not be silently
treated as rational feasibility.

A concrete fixed-template obstruction makes that last warning substantive.
Take three independent binary sources with probabilities `u`, `v`, `f`.
Use the fixed observed mechanisms
`V = A && B` and `O = if F then A else !B`. Require the observed joint
table of `(O,V)` to be uniform. Its equations include
`P(V=1)=u*v=1/2`, `P(O=1,V=1)=f*u*v=1/4` and
`P(O=1)=f*u+(1-f)*(1-v)=1/2`. Hence `f=1/2`, `u=v` and
`2*u^2=1`. A real solution exists in the unit interval, but no rational one:
writing `u=a/b` in lowest terms gives `2*a^2=b^2`, forcing both `a` and `b`
even. Conversely, the positive real root with `f=1/2` makes all four observed
cells `1/4`. Exact truth-table polynomial expansion was checked during this
assessment; this argument is not yet a Lean theorem and adds no real-valued
probability implementation.

This obstruction concerns the **fixed mechanisms**, not the graph-wide
class: on the same parent graph, the different mechanisms `V=A`, `O=F`
with rational fair sources realize the uniform table. It therefore disproves
an automatic real-to-rational template transfer, not the existence of a
general rational causal decision procedure. No reduction proving that
general procedure impossible has been established here. Exact rational
feasibility/uniqueness or a genuinely applicable impossibility reduction
remains unresolved. Review checkpoint: the categorical bow or the explicitly
bounded-model checker is a credible next implementation; do not launch an
open-ended arbitrary-graph optimizer on the strength of finite representation
alone.

## Construction, execution, and proof verification

Finite distribution records can be used as private causal noise without
expanding their natural weights into unit cells. `FiniteRecordPresentation`
proves literal decoded record recovery, all-event probability preservation,
support equivalence and supported-conditional preservation. Its occurrence
codes may repeat an observable label. The separate declared-domain adapter
is bijective on the whole supplied finite subtype, retaining permitted null
values; it does not assert that an infinite ambient label type is finite.
`HiddenDAGFinitePresentation` converts an explicit `FiniteWitness` into the
native model's two-sided observed-value adapter. The corresponding native
example uses rational urn and multivariate hypergeometric laws as actual
independent private noise and checks intervention marginals and do-rule
soundness. This is integration with the existing causal theorems, not a new
or stronger completeness claim.

`Examples.HiddenDAGMultivaluedPresentation` additionally exercises genuinely
three-valued native observed nodes. Its hypergeometric count law permits the
declared value two while assigning it zero factual probability. The native
subtype-to-code conversion preserves every marginal event and each supported
conditional. Intervening on the other node at that null value preserves the
count law, both by direct evaluation and the actual native rule-3 theorem.
Forcing the count node itself to two instead gives two with probability one;
this final structural-model calculation is not a claim that unsupported
effects are identifiable from observations.

`FourLabelTransportation.transportBatched` reserves complete eligible-cell
capacities. Its positivity, saturation, residual feasibility, termination and
exact table guarantees justify the unchanged extremal interfaces. The older
unit-step `transport` is retained as a reference. A different valid output
table is allowed; equality of the two algorithms' literal cells is not needed.
Large-mass regressions check the actual batched constructor in the kernel.

This execution improvement is not a proof that full local compilation is
memory-safe. See [LOCAL_CHECKS.md](LOCAL_CHECKS.md) for the capped pilot's actual
result and limitations. CI checks the exact pushed commit with targeted and
complete builds plus `Thesis.AxiomAudit`. The audit permits only `propext`
and `Quot.sound`, rejecting choice, general propositional excluded middle
dependencies, admitted proofs and untrusted Boolean proof reduction. A cached
artifact or a successful isolated leaf check is not that project-wide gate.
