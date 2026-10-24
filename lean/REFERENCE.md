# Lean mathematical reference

This is the canonical mathematical coverage and source-navigation document.
The actual Lean statements remain authoritative. Build policy and the current
maintenance ledger live in [AGENTS.md](AGENTS.md); old progress narratives,
measurements and complete pre-consolidation guides are preserved in
[HISTORY.md](HISTORY.md). Historical commands are not current build advice.

## Contents

- [Source structure and reading order](#source-structure)
- [Named finite distributions](#named-distributions)
- [Causal results and application boundaries](#causal-results)
- [Entropy and auxiliary analytic values](#entropy-and-auxiliary-values)
- [Unresolved research boundaries](#research-boundaries)

The probability laws remain finite rational records. Auxiliary exact logarithms
and constructive real values are not irrational atom weights. Positive-class
completeness, expression-qualified supported-zero completeness, and arbitrary
fixed-law or alternative-formula questions must not be conflated.

<a id="source-structure"></a>

## Source structure and reading order

The library separates finite probability semantics, graph-indexed causal
programs, their mathematical verification, and applications. A broad facade
preserves convenient imports; focused implementation modules should use the
smallest mathematical layer that supplies their actual dependencies.

## Current reading order

| Start here | Mathematical responsibility | Continue with |
| --- | --- | --- |
| `Probability.Core`, `Urn`, `QualitativeUrn` | Finite rational probabilities, Boolean events and Clayton-style scale comparisons | `FiniteRecord`, finite products and support interfaces |
| `Probability.Distros.Basic`, `Distros.LawBasics` | Named distribution records, every-event law equality and almost-sure support | Specialized moment, concentration and entropy modules |
| `Probability.FiniteRecordSums`, `Distros.CategoricalSampling` | General selected-weight sums, valid colour counts and selected-head integrals | Aggregation and both urn-history families; no specialized urn import is needed for these facts |
| `ExactLog*`, `EntropyValue`, `Distros.Entropy` | Exact symbolic logarithms and information quantities over rational records | `EntropyGibbs`, `EntropyGibbsEquality` and their examples |
| `Causality.Graph`, `Model`, `Semantics`, `Identification` | Finite graph/model semantics, causal query meanings and identification specifications | Graph search and derivation certificates |
| `Causality.IdentificationSearch`, `ComponentConnectivity`, `IdentificationRank` | Shared executable graph tests and constructive correctness/progress facts | The current `IdentificationKernel` and `ConditionalIdentificationKernel` programs |
| `Causality.TermSupport`, `InterventionalCounterexample`, `CForestConstruction`, `IdentificationOutcomeTraces` | Shared support, event-to-kernel separation, forest construction and ordered result witnesses | Focused success/failure compilers without legacy imports |
| `CausalTransport.DSeparation*`, `Certificates`, `Soundness*` | Checked graphical side conditions, inspectable derivations and soundness of their interpretation | Positive-class or support-aware compilation |
| `CausalTransport.ActionDeletion`, `ChainCompilation`, `Kernel*Compilation` | Rule constructors and exact formula-aligned current-engine success certificates | `KernelSuccessCompilation` and `CompletenessAssembly` |
| `CausalTransport.Hedge.ReadoutGeometry`, `Hedge.Models`, `Hedge.Parity` | Explicit graph routes, finite latent models and reusable parity/flow identities | Channel installation, integration and original-query countermodels |
| `HedgeChannelCompleteness`, `HiddenDAGCorrespondence` | Completed positive-class joint/conditional results and original hidden-DAG transfer | Public theorem coverage and modal applications |
| `HiddenDAGSupportedCorrespondence`, `PositiveModal`, `SupportedModal` | Supported-zero qualifications and actual mode-indexed executions | Support diagnostics and application examples |
| IV/bow, compression, polynomial certificates and bounded-search families | Additional finite-domain identification, bounds and checked representations | Their topic-named examples and coverage qualifications |

The model classes and support hypotheses are part of the results, not layout
details. [The coverage guide](#causal-results) states their application
boundaries; this reading order does not enlarge any theorem.

## Shared hedge foundations

`CausalTransport/Hedge` contains reusable geometry and model construction,
with declaration namespaces kept under `Thesis.Causality`. Its boundaries
follow mathematical responsibility rather than a uniform file-size target:

- `ReadoutGeometry` computes routes from finite reachability evidence and
  proves typed lookup and common-sink properties. It is not a countermodel
  or positivity theorem.
- `Models` builds actual finite latent/parity models and proves their local
  invariants. Readiness conditions on the older model families remain explicit;
  the unrestricted channel counterexample is assembled in its own modules.
- `Parity` supplies full and nested incidence solvers, exact support and
  forest-flow identities, plus the one-anchor parity correction shared by
  partial incidence and carrier models. It does not import positive-model
  counterexamples merely to obtain that Boolean correction.
- `WitnessSearch` constructs an actual hedge from the executable graph tests.
  It has no semantic completeness or legacy engine premise.
- `Countermodels` proves the original observational parity equalities and
  geometrically qualified mix counterexamples. Positive carriers and routed
  outcome-flow support import it directly, without historical failure stacks.

None of these shared modules imports the historical identification recursion or
its branch-stack proofs. Current positive, supported-zero and modal theorem
paths, as well as the retained qualified-carrier development, are guarded
against accidentally regaining those historical dependencies.

Generic consecutive-list operations and their reachability conversion live in
`Causality.ReachabilityCorrectness`, not `DSeparationCorrectness`. Readout geometry
therefore uses the shared walk foundation without importing the semantic
correctness proof for active paths or moral graphs. The original graph-specific
import still reexports those generic declarations for existing callers.

The sampling boundary is analogous. `Distros.CategoricalSampling` owns the
coordinate-update/count lemmas and finite selected-head integral, while
`Probability.FiniteRecordSums` owns general mass factorization. Positive atom
witnesses reuse `FiniteProbRecord.eventMass_pos_iff_exists_atom` from
`Probability.FiniteRecordSupport`. The old
reinforced-urn spellings remain compatible; depleting clients no longer import
reinforced conditioning, exchangeability or update histories for these facts.
Their use of reinforced factorial-moment results remains legitimate and intact.

## Compatibility and historical material

`CompletenessHedgeModels` is an import-compatible facade for `Hedge.Models`.
It deliberately still exposes the preceding historical layers. Other original
completeness-layer paths likewise reexport the support, graph and derivation
declarations moved to their focused owners. Existing declaration names and
mathematical statements are unchanged.

Compatibility preserves each original defining-module path and the broad
public facades. Focused clients should explicitly import any other interface
they use: incidental historical reexports of a formerly broad dependency are
not a reason for a current implementation to keep importing the old engine.

`CompletenessHedgeParity` similarly reexports `Hedge.Parity` and retains the
older model facade. `HedgePartialIncidence` imports the focused parity layer
directly, so current channel integration no longer inherits the positive
carrier development or its historical engine imports for elementary parity.
`CompletenessHedgeCountermodels` likewise reexports `Hedge.Countermodels` while
retaining its original preceding compatibility imports. The broad `Completeness`
and `CausalTransport` facades intentionally continue to expose preserved history;
they are convenience/audit entry points, not foundational imports for current
implementation modules.

`Causality/Legacy` quarantines the obsolete executable engine and its checked
control-flow proofs. `CausalTransport/Historical` retains the historical
finite-depth unpackers and legacy trace-compiler interfaces. They remain built and axiom-audited;
they are not a substitute for current-engine semantic completeness and must
not be exposed as an unsafe unqualified identification API.

| Original import | Retained implementation |
| --- | --- |
| `CausalTransport.CompletenessLegacyShrinkFailures` | `CausalTransport.Historical.LegacyShrinkFailures` |
| `CausalTransport.CompletenessLegacyProductFailures` | `CausalTransport.Historical.LegacyProductFailures` |
| `CausalTransport.CompletenessLegacyNestedFailures` | `CausalTransport.Historical.LegacyNestedFailures` |

Each old file is a compatibility facade. Exact-body preservation guards cover
the archived namespaces, declarations and proofs; import guards ensure that
the full audit still reaches both the old paths and the archived payloads.
Current positive, hidden-DAG, supported-zero and modal completeness paths do
not import those historical layers. Moving them does not claim that the
mandatory whole-project verification can skip their checking cost.

`ConditionalFailureCore` contains general IDC exchange/failure extraction and
terminal assembly. `ConditionalFailureCarrierCases` retains a qualified
carrier counterexample separately, and the old `ConditionalFailureExtraction`
path reexports both. `ConditionalBayes` supplies the original source-local
support argument without importing historical certificates.

The measured conditional-readout regression has a topic-grouped fixture in
`Examples/HedgeConditionalReadout`. `Graph` defines its original concrete query,
`Exchange` retains the finite no-exchange check, and `Failure` retains the actual
engine equations. The original `Examples.HedgeConditionalReadout` module still
constructs and checks the same routed countermodels. This split keeps each
local invocation within the existing limit and lets semantic edits reuse the
independent graph computations; it does not skip any regression.

`Examples/HedgeConditionalClosedReadout` applies the same boundary to its two
independent query calculations: `Graph` supplies the original fixture data,
`PrimaryEngine` and `EarlierEngine` retain all six engine assertions, and the
original entry point retains the actual semantic countermodels. Both example
families remain reachable from the full build and axiom audit.

The long earlier completeness development inventory is retained in
[historical documentation](HISTORY.md#archived-completeness-inventory), not in the
current-status facade. Mathematical explanations and historical proved results
are preserved. A public end-result is not obsolete merely because no internal
module calls it, and qualified carrier countermodels are not historical junk
merely because a more general channel theorem exists.

The remaining topic-named probability, causal, bound and search modules retain
their established paths. A wholesale folder rename would add forwarding files
and invalidate import clients without a measured dependency or checking
benefit. New subfolders here therefore mark actual ownership boundaries
(`Hedge`, `Historical`, and the two measured example fixtures), not a target
file count or uniform size. The reading table supplies the broader topic map.

## Verification and build interfaces

`Thesis` remains the broad proof-and-example facade. The executable's Lake
prerequisite checks that facade even though its runtime needs only IO.
`Thesis.AxiomAudit` checks the transitive imported project declarations,
including retained history and regressions; only `propext` and `Quot.sound`
are allowed. Source-dependency and preservation tests guard the extracted
boundaries but do not replace Lean's checks.

[Local checks](AGENTS.md#builds-and-checks) documents ordinary native Lake builds and
the optional single-compiler resource-monitored route. The
[refactoring ledger](AGENTS.md#targeted-maintenance-ledger) records exact checkpoint evidence,
remaining work and the bounded review passes.

<a id="named-distributions"></a>

## Named finite distributions

[`Thesis.Probability.Distros`](Thesis/Probability/Distros.lean) exposes
the named finite laws and their checked interpretations. Geometric and
negative-binomial outcomes count Bernoulli failures before the requested
successes. Truncation conditions on success within the finite window;
censoring clips the failure count to the cap and retains the entire tail.
Both laws are derived from actual finite Bernoulli products, and the
one-success negative binomial equals geometric.

The lattice Gaussian uses the rational kernel `q^(x²)` on `x ∈ [-radius, radius]`,
with `0 ≤ q ≤ 1`. Zero gives a point mass and one gives the discrete uniform
law. Equivalent rational presentations of the kernel give the same Gaussian
and finite χ² laws on every event. Its signed mean is zero and its variance is the exact finite second
centred moment. The finite χ² law sums independent squared coordinates:
equal radius and kernel give additivity in the degrees of freedom, mean
`df · m₂`, and variance `df · (m₄ − m₂²)`.

The library includes reusable expectation, map, independent-sum and PGF laws;
closed Bernoulli, binomial, geometric, hypergeometric and beta-binomial
moments; general rational censored PGFs; and a multivariate multinomial PGF
with matching occupancy dimensions. Beta-binomial normalization is the
rising factorial `(α+β)↑trials`, and its success-count law agrees on every
event with sequential finite Pólya urn draws and same-colour reinforcement.
Ordered Pólya words are exchangeable. Conditioning on a supported prefix
updates the two urn counts by the observed colour counts, with the exact
future law and both next-draw probabilities proved. The `*DistroOfTotal`
constructors permit zero success weight in censored waiting times and one
zero beta-binomial colour count. Their deterministic point-mass laws are
proved; beta-binomial moments and the urn correspondence include both
endpoints. Existing strict constructors agree with these variants.
Law equivalence transports event agreement through maps, products, positive
conditioning, expectations, moments, variance and PGFs, without requiring
finite enumerations of outcome types. Chebyshev is connected to variance
and holds at every positive rational radius. Finite generating functions
determine numeric and bounded count-vector laws constructively. Independent draws from the categorical constructor produce
the multinomial occupancy law on every event, including zero-weight colours.
Arbitrary category partitions produce multinomial laws with summed weights;
coordinate counts have binomial marginals, closed means and variances.
Distinct-coordinate cross moments and nonpositive covariances are proved with
integer numerators over positive denominators. The generic covariance agrees
with the centered product integral and with witnessed variance on its diagonal.
The signed-observable API extends this to integer coordinates, with symmetry,
bilinearity, law/map transport, zero covariance under independence, and the
covariance term in dependent-sum variance. Integer-observable variance is
proved nonnegative and agrees with the existing witnessed natural variance.
Falling-factorial moments of binomial, hypergeometric and beta-binomial laws
are proved at every order,
including orders above their finite support. General negative-binomial
factorial moments reduce to shifted finite generating sums; their means,
second moments and witnessed variances include the cap boundary terms and
the censored zero-success-weight endpoint. Conditioning a larger truncated
geometric or NB law on a smaller window recovers that smaller law; clipping
a larger right-censored law gives the smaller censored law on every event.
Hypergeometric is also realized by actual sequential two-colour urn draws
without replacement: each Bernoulli colour draw removes one ball of that
colour. Its count law agrees on every event, including empty and single-colour
urns, and the mean and finite-population variance transport to that process.

Multicolour Pólya paths draw from the current categorical weights and add one
to the chosen colour. Their occupancy law is Dirichlet-multinomial, with
multinomial coefficients times rising-factorial factors and normalizer
`(sum α)↑trials`. The categorical first-step semantics, every-event count
correspondence, support and PMF are proved, with zero individual parameters
permitted. Two colours recover the positive-total beta-binomial numeric law.
Natural likelihood reweighting transports through law equivalence and maps.
A general urn can add any natural number of balls after each draw. Its
rising-factorial normalizer and count law recover multinomial at increment
zero and the existing Pólya / Dirichlet-multinomial at increment one.
Scaling initial counts and reinforcement together preserves the law.
Arbitrary nonnegative rational Pólya parameters are implemented by clearing
one common denominator and adding that denominator after each draw. The
ordered and occupancy laws are invariant under equivalent rational
presentations and recover the original natural-parameter constructors.
Every joint falling-factorial moment is proved for multinomial,
Dirichlet-multinomial and arbitrary reinforcement. The formula is the total
falling trial factor times the product of coordinate rising factors, divided
by the rising total; at zero reinforcement these become weight powers.
The identities include zero colours and orders above the trial count.
Merging any categories in a reinforced path or count law sums their initial
weights and retains their reinforcement increment. Every Dirichlet-multinomial
coordinate has its beta-binomial marginal, closed mean and variance, with
zero-weight and single-colour endpoints included. Joint factorial moments
also give the individual factorial moments, means and distinct-coordinate
cross moments and signed covariances for every reinforcement increment.
Ordered reinforced words are exchangeable: equal colour counts give equal
word probabilities. Conditioning the actual path record on observed counts
and dropping the observed draws gives exactly the urn with parameters
increased by the increment times those counts. Counts are therefore
sufficient for every future event; the next-colour probability is
`(alpha[i] + d * count[i]) / (sum alpha + d * observed draws)`.

Variance uses the existing witnessed `QProb.sub` operation, and boundary
cases are covered by theorem statements and kernel-checked
[`DistributionLaws`](Thesis/Examples/DistributionLaws.lean) and
[`DistributionExtensions`](Thesis/Examples/DistributionExtensions.lean) regressions.

<a id="causal-results"></a>

## Causal results and application boundaries

This guide separates graph-level identification from applying a formula at a
particular law, and both from fixed-law identification. The actual Lean
statements remain authoritative. All implemented probability theorems concern
finite rational records, with zero-weight cells permitted unless an explicit positivity
assumption says otherwise. Original hidden DAG results allow arbitrary finite
hidden and private-noise alphabet sizes; observed alphabets remain fixed.
Implemented constructions and remaining research are distinguished below.
External real-valued methods do not by themselves extend the rational
probability framework.

## Coverage overview

| Topic | Current result | Boundary |
| --- | --- | --- |
| 1. Safe local builds | Complete local Lean/native build and transitive axiom audit passed through the cache-aware sequential builder; measured caps and reusable ordinary artifacts are documented in `AGENTS.md`. | Use the guarded sequential route; success does not establish safety of unrestricted parallel cold builds or arbitrary external machine load. |
| 2. Shared graph infrastructure | Connectivity, reachability and rank infrastructure extracted without changing public theorem names; current-engine dependency guards pass. Resource-driven soundness/completeness splits retain the original declaration text. | Further splitting should address a measured bottleneck; it is not itself a mathematical repair or a guarantee of full local feasibility. |
| 3. Multivalued native example | Three declared observed values, an actual rational distribution, null intervention targets and supported conditionals checked through the native model. | The standalone-template regression now exercises the same boundary as well. |
| 4. Support-pattern applicability | Exact undefined/zero/positive analysis and exhaustive comparison within supplied finite formula catalogues; complete native causal support profiles also preserve recursive derivation support. | This does not enumerate every possible certified formula; observed support alone need not determine causal support. |
| 5. Universal alternative-formula coverage | Finite native support profiles, a serialized certificate checker, maximal proof-admissible guards, exact bounded enumeration, resource-admitted selection and a support-preserving elementary-path bridge constructed. A native counterexample refutes unconditional substitution through a common kernel. | Bounded selection is complete only for its admitted catalogue. A general support-preserving kernel normal form and universal stopping remain unresolved; the counterexample does not establish causal undecidability. |
| 6. Finite structural representation | Constructed standalone-template coverage both for a fixed full hidden DAG and across all finite hidden DAGs with a fixed observed projection. | Rational weight assignments remain infinite; compatibility, sharpness and complete search are separate obligations. |
| 7. Fixed-observed-law procedures | Restricted results retained; exact compatibility and unconditional/conditional-target comparison for a full hidden DAG with declared finite alphabet and denominator bounds. Conditional support and positive-evidence values are reported separately. | Unrestricted rational feasibility remains separate; increasing bounds has no proved stopping rule. |

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

### Positive-class modal connection

`PositiveModal` connects the inhabited positive joint/conditional completeness
package to the modal wrappers. `ObservedGraph.positive_joint_modal_iff` and
`positive_conditional_modal_iff` retain `GraphModelClass.positive`, without an
external completeness argument. `ModeIndexedJointDerivationIn` and its
conditional counterpart retain actual membership of the mode's stored model;
`realizeAt` constructs the kernel execution and every modal do-rule leaf.
The older unrestricted wrapper signatures remain available with their explicit
external completeness premise; they are not silently inhabited by this result.

The concrete front-door regression reads one half and three quarters from
executed intervention/observation records and also checks the atomic endpoint.
These executions start from the stored model's initial prior, not an arbitrary
updated belief.

### Native support-aware modal connection

`SupportedModal` connects the completed supported-zero completeness package
to actual modal traces without changing its application domain. The native
and mode-indexed `supported_joint_modal_iff` / `supported_conditional_modal_iff`
theorems retain the independent supported-representation predicate.
`NativeModalKernelRealization` stores the original native support tree,
the executed kernel, every realized do-rule leaf, and native source/formula
equations to the executed value. Local demand tests construct the support;
conditional execution additionally requires the original causal conditioner.
No positive-class membership or canonical two-child-root premise is inserted.

The mode index stores equality to the actual native model's proved collapse;
`sourceAtMode` reads the executed answer at that stored model. As in the
positive API, execution starts from that model's initial prior, not an
arbitrary updated epistemic belief. The native regression covers recursive
joint ID, conditional Bayes, recursive IDC promotion at a null factual action,
supported-zero endpoint values, structural atomic execution, and rejection
of a genuinely undefined original conditioner. All examples belong to the
full axiom-audit import closure. These bridges neither assert unrestricted
zero-class completeness nor cover every alternative formula's domain.

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

### Finite causal support-profile foundations

The first two stages are implemented independently of a future proof-code
language. `FiniteSupportCatalogue` enumerates actual normalized unit-weight
records for every nonempty mask on each finite source alphabet. It covers
the support of every original rational record, including repeated labels and
zero weights, with no input denominator bound. An empty alphabet has no
normalized support representative; an empty source family has one empty tuple.

`FiniteProductSupportLaw.record_eventPositive_iff_of_factor_support_eq` proves
that these reweightings preserve positivity of every mixed event in the
actual independent product. `CodeNativeTemplate.supportAgreement_of_factor_support_eq`
combines that result with unchanged native structural evaluation, retaining
support of every observed event under every hard intervention. It does not
preserve nonzero numerical values.

`CausalSupportAgreement.term_status` covers every current nonnegative term
constructor, including strict sums/products, explicit substitutions and the
directional zero-weight product. `localSupportToRight` rebuilds the complete
native derivation-support tree from the new model's own values, retaining
every marginal branch and demanding factor support only on positive weighted
branches. It does not transport an old probability value as though numerical
equivalence had been proved. Signed subtraction/cancellation is outside this
three-state abstraction.

`NativeSupportProfiles.queries` is a finite basis of singleton events under
all reference-valued intervention masks. Every permitted hard intervention is
included, also when its assigned observed value has factual probability zero.
The existing representation theorem preserves this entire finite basis;
singleton extensionality extends preservation to every interventional event.
Subsequent uniform reweighting forgets the values but retains their supports.

`FiniteLatentProjection.completeSupportCatalogue` therefore supplies a finite
list of actual native models covering the entire single-world hard-intervention
support behaviour of the original model class.
`FiniteHiddenDAGSCM.completeSupportCatalogue_covers`
keeps the original full hidden DAG fixed. The separate
`ProjectedHiddenDAGModel.completeSupportCatalogue_covers` ranges over all finite
full hidden DAGs with the same observed projection and uses the fixed
multi-child clique-root graph. Original hidden/source alphabets and rational
denominators are unrestricted in both statements. The derived structural
bounds belong to the representation proof, not extra input-model assumptions.

This is coverage of support profiles, not exact fitting of a numerical
observed law, numerical identity checking on uniform representatives, a
minimal or duplicate-free profile classification, or an unrestricted rational
identification procedure. The regressions explicitly show changed numerical
values. Joint cross-world/AAP support is not retained by this finite basis.
The regressions also show unchanged null cells, legal null intervention
targets, strict versus
weighted support and a transported complete weighted support tree. Both
current observable guards remain unchanged because their checks depend only
on observed support. Huge full model catalogues are not concretely expanded
by these regressions.

These support foundations do not themselves select a formula. The implemented
checker, bounded enumerator and native selector are distinct downstream layers,
with their exact finite-family guarantees and limitations described below.

### Serialized certificate checking

`ProbabilityTermCode` uses constructor trees and natural dictionary indices,
not arbitrary functions or supplied semantic proofs. Its dictionaries include
every declared observed value, also null intervention targets. Invalid indices
are rejected. This is an abstract serialized syntax, not a byte parser.
`DerivationCode.check` reconstructs actual existing do-calculus derivations:
all three executable graph rules, probability-algebra primitives, congruences,
transitivity and syntactic endpoint reindexing. Syntactic joins use constructive
finite equality, never numerical agreement at one model. Rule 3 retains its
incoming-arrow cut. The separate top-level `actionOne` certificate reuses the
already proved probability-one-action identity; it is not an unconditional
graph rule or an arbitrary nested semantic-proof language.

`HiddenDAGLocalDerivationSupport.check_exact` characterizes acceptance by an
inhabited complete native support tree. `ofCheck` constructs that tree from
the actual evaluated options; `check_of_supported` proves the converse.
`check_eq_of_agreement` transfers the entire check across causal support
profiles. Strict undefined intermediates remain mandatory even when both
printed endpoints have values. Zero-weighted congruence skips its factor
subtree only on the established defined-zero branch.

`NativeSupportGuard` rows contain the complete observed support bit-list and
a reference index. Runtime acceptance is observable. Certification checks
**every** matching actual causal profile, not one favorable representative.
Support demand is required wherever source and printed endpoints are both
supported. The guard checker never tries to prove a numerical causal identity
from uniform profile values: that identity comes from the reconstructed
causal derivation or the proved `actionOne` theorem.

`NativeCertificateCode.checkFixed` and `checkProjected` additionally verify
the coded source and action-free printed output. Their accepted formulas have
native soundness theorems `CheckedNativeFormula.fixed_soundAt` and
`projected_soundAt`, respectively. The latter applies to every original
finite hidden DAG with the fixed observed projection, not merely the clique
graph used for finite checking. These adapters supply constructed profile
coverage automatically; `checkOn` exposes a generic smaller-list interface
whose application theorem explicitly requires coverage of the applied model.
The existing two-guard formula API is unchanged.

Application still requires the **original causal source support** separately.
The regression even checks a printed formula that is available while its
original conditional target is null: without the source premise it gives no
soundness conclusion. Further regressions reject invalid dictionaries, false
graphical steps, mismatched joins/sources, actionful printed branches and a
strict cycle with a hidden undefined intermediate; they accept the genuine
weighted null-factor case and the guarded action-one identity. Only tiny
explicit profile lists are executed, not enormous full catalogues.

This checker certifies supplied codes in its declared grammar. Enumeration
is a separate downstream stage, described below; neither the checker alone
nor the bounded enumerator covers arbitrary Lean semantic proofs.

### Generated proof-admissible guards

`NativeGuardCompilation` generates a guard for one supplied checked proof.
Its rows use only observed patterns actually represented in the supplied
causal-profile catalogue, paired with every declared reference index. Thus
factually null intervention values remain included, without enumerating a
separate cube of impossible observed patterns. Duplicate rows are permitted;
there is no minimal-size or efficient general execution claim.

`NativeSupportGuard.compile_checked` proves the generated table passes the
existing universal matching-profile checker. `compile_maximalAt` proves that
any other passing table for the **same demand** has no greater acceptance on
represented observed patterns. `compile_soundAt` applies a passing generated
guard to an original model using support invariance and actual coverage.
The complete fixed-DAG and projection-wide profile catalogues supply that
coverage throughout their respective native model classes.

`CheckedNativeFormula.withCompiledGuard` changes only the guard, retaining the
source, formula and actual proof. `withCompiledGuard_available` proves that
no previously available application is lost on a covered model.
`NativeProofCode.compileGuardOn`, `compileGuardFixed` and
`compileGuardProjected` also accept raw source/proof codes: the existing
source-match, graphical and action-free checks run before guard generation.
The existing native soundness application theorems apply unchanged.

This is **maximal proof-admissible coverage**, not semantic maximality of a
formula. A strict chain/inverse-chain proof has an unsupported intermediate
at a null reference where direct reflexivity certifies the same endpoints.
The regression compares those generated guards, preserves the legitimate
zero-weighted exception, and checks the guarded probability-one-action leaf.
It also retains the example with an available printed answer but an undefined
original conditional source: source support is still a separate application
premise. Executable regressions use tiny actual-profile lists; whole-class
adapters are checked symbolically rather than expanding enormous catalogues.
Proof enumeration, bounded proof-search completeness and formula selection
are not implemented by this guard construction.

### Bounded code enumeration and native acceptance coverage

`ProbabilityTermEnumeration` and `DerivationEnumeration` construct finite
lists with independent **expression-tree depth** and **proof-tree depth**
budgets. Zero admits no tree; each constructor consumes one level. Bounded
arity consequently also bounds total tree size. These are not byte-length
budgets, numerical probability bounds or complexity guarantees.

Expression depth bounds every explicit `TermCode` field anywhere inside a
proof, including intermediate subproofs and `eqCongr` fields. It is not a
bound merely on the source and final formula. Primitive rules construct
their existing derived endpoints when checked; those expansions are not
the encoded term fields counted by this budget. All natural indices are
bounded by finite dictionary ranges. `CodeDictionaries.ofSignature` uses all
declared masks and assignments, not only factually supported assignments.

The `TermCode.mem_enumerate_iff` and `DerivationCode.mem_enumerate_iff`
theorems prove exact membership for the independent recursive `Within`
predicates. Every existing constructor, primitive tag and congruence tag is
included. Raw generation deliberately does not assert a graphical condition,
a valid endpoint join, an action-free output or native support.

`NativeProofEnumeration` includes both native code branches. Its wrapper
consumes one proof level, and its `actionOne` branch is a leaf.
`NativeProofCode.mem_enumerate_iff` proves exact native code membership.
`catalogueOn` applies the existing checker and guard compiler to every
enumerated proof for a fixed supplied source. `mem_catalogueOn_iff` specifies
exactly which successful bounded codes produce catalogue members. Members
are actual `CheckedNativeFormula` objects, with their existing native
soundness theorems, not unproved numerical identities.

`NativeCertificateCode.compileGuardOn_of_checkOn` connects an accepted old
supplied guard to that same proof's generated guard. Consequently
`NativeProofCode.catalogueOn_covers` proves more than raw syntax coverage:
every accepted supplied guard for a bounded proof has all its accepted
applications retained by a generated member on a covered original model.
`catalogueFixed_covers` and `catalogueProjected_covers` supply the constructed
profile coverage for their entire respective native model classes. No bound
on original hidden alphabets or source denominators is added. Original
conditional-source support remains a separate soundness premise.

The regressions execute tiny literal syntax lists and use the exactness
theorems for larger symbolic membership and native coverage. They include
insufficient wrapper depth, a bad reference hidden in an intermediate term,
raw graphical failures, a strict cycle with null intermediate support, and
preservation of the three-valued fixture's null reference. Complete native
catalogues are not concretely expanded. The enumeration layer itself selects
no formula; no minimality, duplicate-free output or practical large-instance execution
claim is made. This stage covers the bounded serialized grammar, not every
arbitrary Lean proof of a semantic identity.

The universal stopping argument remains unresolved. Finitely many support
cells bound the number of *coverage gains*, not the delay until the next
gain: even one new cell can first appear after an arbitrarily long initial
plateau. Neither a plateau nor bounded-search exhaustion certifies universal
exhaustion. A proof-length bound, finite complete rewrite/derivation basis,
or another complete coverability decision is still needed. This refutes
that proposed stopping shortcut; it is not an impossibility proof for a
universal selector. The declared proof/guard grammar now has an exact bounded
enumerator and acceptance-coverage theorem. Increasing its budgets still
has no proved stopping criterion for universal coverage. The bounded selector
below uses an admitted finite family; it does not close that research gap.

### Resource preflight for bounded proof catalogues

`CodeEnumerationCounts` proves exact list-entry counts for the raw expression
and derivation enumerators. `NativeProofCode.count_eq_length` adds the native
wrapper. `CappedCount.term_exact`, `derivation_exact` and `native_exact` prove
that executable saturated arithmetic returns the exact count clipped at
`limit + 1`. Overflow is not displayed as an exact size. The three-binary-node
example has **135,298,563** raw native candidates already at expression depth
1 / native proof depth 2; the regression computes only this arithmetic.

`CodeSearchPreflight` checks explicit node/depth policies before counting.
It checks the mask limit before calling any coordinate value enumeration;
only a passing mask count permits the coordinate-length reference estimate.
These estimates gate construction of the full mask/assignment dictionaries.
The actual dictionary and accepted candidate counts are bounded
by `preflightSyntax_bounds`. No probability-zero intervention value is dropped.

`DomainSizeMetadata` in `CodeSearchMetadata` supplies numerical domain sizes
with proofs equating them to the declared enumeration lengths. Its
`preflightSyntaxWithMetadata` checks both dictionary limits without generating
or measuring those lists. For `Fin n`, an existing symbolic length theorem
certifies the number `n`; no `n`-element list need be generated on refusal.
`preflightSyntaxWithMetadata_eq` proves equality with the existing preflight
for **all** results, including refusals, and `_bounds` retains its size bounds.
The result equality is deliberately not a compiler-replacement rule: the two
paths have the same meaning but need not have the same execution cost.

`NativeSearchPreflight` additionally limits supplied profile count, guard
rows, per-certificate profile comparisons and total comparisons across raw
candidates. Source-query depth is a separate policy. Successful
`guardedEnumeration` and `guardedCatalogueOn` results equal the old complete
bounded lists; no silent truncation weakens their mathematical coverage.
`guardedCatalogueOn_admission` exposes the successful gates, and
`guardedCatalogueOn_total_bound` proves the admitted structural comparison
allowance. `Except.error` is resource/policy refusal, while `Except.ok []`
is an empty result in this particular checked bounded family. Neither is a
general non-identifiability certificate.

`NativeSearchMetadata` exposes `guardedEnumerationWithMetadata` and
`guardedCatalogueOnWithMetadata`. Their equality and exactness theorems
preserve the entire existing bounded enumeration/catalogue, while
`guardedCatalogueOnWithMetadata_total_bound` retains the structural comparison
allowance. All source, supplied-profile and total-work checks remain mandatory.
Regressions include early refusal with a symbolically certified billion-value
domain and retention of the three-valued fixture's observationally null cell.
They do not execute a billion-element list or a large raw proof catalogue.
Source-order regressions and inspection of generated code supplement the
logical equalities, since equality alone cannot establish eager execution cost.

This is **not a complete runtime-cost or memory model**. Evaluating one
profile/demand can itself be expensive, and inputs can contain arbitrary
enumeration functions. Metadata should itself be prepared cheaply: computing
its numbers by generating and measuring lists would defeat this optimization.
The fallback without metadata still measures lists after its mask gate.
Profiles are already supplied: in strict evaluation,
passing `completeSupportCatalogue` first builds that list. Accordingly there
is no new supposedly guarded automatic fixed/projection-wide profile generator.
Its generation cost needs separate analysis; external CPU/RSS safeguards are
still necessary for concrete execution. The preflight layer itself does not
select formulas.

### Selection within admitted bounded native catalogues

`NativeFormulaSelection` scans a supplied finite native-certificate list in
its given order, retaining each full support-table guard. It does not coerce
native guards into the older two-constructor observable-guard language or
erase a guard to reuse that selector. `select_mem`, `select_available`,
`select_none_iff` and `select_complete` specify exact finite-list behaviour.
The first available candidate wins; a rejected first candidate cannot mask
an available fallback. Defined zero is available; undefined is not.

`guardedSelectOnWithMetadata` in `NativeBoundedSelection` (namespace
`ProbabilityCode.NativeProofCode`) first uses the existing metadata
admission and then scans the entire admitted checked catalogue. Its outputs
are deliberately distinct: resource/policy refusal, admitted search with no
available member, and an available checked native formula. Refusal propagation
is exact. Empty success is characterized only within that admitted list;
neither negative result proves general non-identifiability.

`checkOn_source`, `compileGuardOn_source`, `catalogueOn_source` and
`guardedSelectOnWithMetadata_source` retain the literal decoded input query.
`guardedSelectOnWithMetadata_soundAt` therefore interprets the selected formula
as an answer to that query on a covered original native model, with original
conditional-source support still an explicit premise. Finding an available
printed formula does not decide whether its causal source has a value.

`guardedSelectOnWithMetadata_covers` turns the existing bounded acceptance
coverage into selection success: any accepted supplied guard for a bounded
serialized proof forces a result on a covered original model, provided that
the search is admitted. The chosen syntax need not be that witness's syntax.
`guardedCatalogueOnWithMetadata_length_bound` bounds the scan's input length
by the admitted raw-candidate limit, without silent truncation.

This is not universal formula coverage, a universal stopping theorem, or a
new complete runtime-cost model. The whole admitted catalogue is constructed
before scanning. The existing profile-comparison allowances concern catalogue
certification; arbitrary observational formula evaluation is not bounded by
them. Profiles, the observational record and cheap metadata are prepared
inputs, not lazily generated under these gates. The new regression executes
only eight-leaf catalogues and uses symbolic coverage for deeper proof budgets.

### Support-preserving elementary-path bridge

`DerivationLinearization` separates the old nonstructural leaves into
`DoCalculusAtom`. A `DoCalculusRewriteStep` contains exactly one such leaf,
possibly reversed and placed under expression frames; it cannot hide a
transitivity tree. `DoCalculusRewritePath` is a finite chain with the original
source and target retained in its type. `DoCalculusDerivation.linearize`
constructs one path from the proof syntax before seeing any model or profile.
Binary congruences change the left operand first; weighted congruence thus
changes its weight before changing its factor.

`NativeRewritePathSupport` proves `DoCalculusRewriteStep.check_eq_endpoints`:
an elementary step needs exactly its complete endpoints' support, including
all marginal substitutions and the positive-only weighted branch. This does
**not** apply to an arbitrary derivation tree. `checkVertices` scans every
vertex, retaining the source even for an empty path. `toDerivation_support`
reconstructs the old complete recursive support tree from actual vertex
values, without supplying a new causal law. `checkVertices_eq_toDerivation`
proves exact agreement between the vertex scan and the old checker on that
reconstructed path, not merely a sufficient support condition.

`NativeDerivationLinearization` proves `linearize_equivalentVertices` and
`linearize_supportedVertices`. Every original supported application retains
equivalent numerical values and support at all vertices of this same path.
The invariant is genuine rational equivalence, not equal support status.
`linearize_checkVertices` and `linearize_toDerivation_check` preserve the old
checker's accepted applications. Their graph is the model's actual observed
projection. No global positivity or bound on the original finite alphabets
or rational denominators is added.

`NativeLinearizedCertificate` transforms reconstructed native certificates.
`linearized_guardChecked` checks every supplied matching profile, provided
its actual projected graph agrees with the certificate graph.
`CheckedNativeFormula.linearized_source`, `linearized_formula` and
`linearized_guard` preserve the original application boundary;
`linearized_available` proves availability equal on arbitrary records and
references. Original conditional-source support remains separate.
`actionOne` stays an unchanged top-level leaf, not a new composable do-rule.

The small regressions retain an unsupported strict intermediate under
positive weight, skip it under a genuinely changed zero weight, inspect null
marginal substitutions and fixed evaluation references, and preserve the old
certificate guard and null-source boundary. Decoded proof equalities are
handled through symbolic preservation theorems, not a native decision axiom.

This is a typed proof-presentation bridge, not a serialized-code exporter or
a general rewrite solver. It proves no proof-length bound or universal
stopping law. A possible later reduction must keep every intermediate inside
the supported-expression set and preserve one common certificate across all
matching profiles. Ordinary unconstrained rewrite reachability does not
settle that support-constrained question; its decidability for this particular
causal grammar remains an explicit research obligation.

### Proved common-kernel substitution obstruction

A general support-preserving finite-key normal form remains unproved and unrefuted. This pass tests a
specific proposed composition rule, rather than treating the phrase "finite
keys" as a normal-form theorem. `Examples.NativeKernelInterfaceObstruction`
gives a checked counterexample to the following **common-carrier shortcut**:
after two candidate proofs from the same kernel have matching complete
formula-status and conditional-demand tables, replace one printed formula
by the other using symmetry and transitivity through that kernel, without
losing any application where the printed formulas are supported.

In the existing three-valued native fixture, put `K = P(empty | Z)`,
`U = P(empty)` and `V = U * U`. Actual rule 1 gives `K -> U`; an actual
empty-set chain step gives `U -> V`. The candidate proofs from `K` end in
`U` and `V`. `unit_demand_always`, `product_demand_always`,
`formula_statuses_agree` and `candidate_metadata_agree` prove that the two
conditional demands are always true and their output statuses agree, for
every reference of every native model on the declared signature. Therefore
enlarging the supplied profile list to a complete one does not distinguish
this metadata; the proof does not execute any complete catalogue.

Both candidates also admit the same observable null-reference guard, and
both printed formulas are available there. But `K` is undefined at that
reference. Original source support stays an independent premise, so neither
certificate may be used to assign a value to this original conditional query.
This is not a flaw in the existing certificate checker or causal soundness.

The direct proof `U -> V` passes its full native support check. Replacing it
by `U -> K -> V` fails. `conditional_demand_does_not_compose` is stronger
than merely observing that an endpoint-only support test can miss an
intermediate: each of the two pieces passes the existing conditional demand
test, while their composition fails it. The pieces are accepted vacuously
because one endpoint is undefined. The composite has defined endpoints and
must inspect its undefined carrier. `formulas_are_distinct` rules out a
merely reflexive syntactic loop, and `supported_carrier_detour_passes` checks
that the same detour succeeds at a reference where the carrier is supported.

There is a restricted positive composition argument directly from the
checker definitions. If the carrier and both printed formulas are supported
at every **active** profile/reference, then accepted conditional demands
provide accepted recursive checks for both pieces. Symmetry and transitivity
then reconstruct the carrier detour's full support. Dropping the carrier
premise is exactly the invalid step exposed above. This argument alone does
not show that every usable original proof admits such supported carriers.

Nor may a repair simply demand every syntactically mentioned carrier
everywhere. `zero_weight_can_hide_detour` accepts the whole failed detour
inside a defined zero-weight factor, while
`positive_weight_cannot_hide_detour` rejects it under a positive weight.
Marginal substitutions and fixed references must likewise be retained by any
proposed active-interface discipline.

**Scope of the negative result.** The common-carrier substitution rule is
false, even with metadata agreement over every native model/reference. This
does not prove that those keys are unusable in every possible algorithm:
another proof reconstruction may avoid the carrier, as the supported direct
chain proof does here. It does not refute every finite-key or context-indexed
normal form, and it is not an impossibility result. A general
positive result still needs a support-preserving lifting theorem, not merely
finite metadata or conditional-demand transitive closure. No solver or
production proof interface was added during this bounded attempt.

The example uses empty-outcome kernels, which the current checked language
permits. It does not rule out a normal form that first proves a suitable
unit-kernel elimination theorem, or a nonempty-interface restriction with a
proved coverage guarantee. Such elimination must preserve supported
applications: the partial conditional `K` and the always-defined `U` do not
have identical availability. These are additional proof obligations, not a
reason to treat the example as a general impossibility theorem.

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

### Actual finite source alphabets

`HiddenDAGSourcePresentation` now replaces native private sources with finite
sampling codes on the unchanged original hidden DAG. `presentSources_evalNode`
and `presentSources_evalObserved` prove unit-level decoder simulation;
`presentSources_interventionalValue` proves every hard-intervention event
probability preserved, not only marginal source events. The generic
`FiniteProduct.presentation_probVal` establishes full decoded joint-law
agreement even when the original prior is not literally a canonical product.
`presentSources_eventPositive_iff` and `presentSources_conditionOn_probVal`
retain zero/support distinctions and all actually supported conditionals.

`HiddenDAGCompactSources` connects that adapter to both compression interfaces.
`SourceCompression.codeModel` has actual private types `Fin (codeCard node)`
with `codeCard_bound <= number of retained queries + 1`.
`ObservationalSourceCompression.codeModel` has the corresponding bound
`number of observed assignments + number of target queries + 1`, preserves
the entire observed law, and preserves every listed target. Both interfaces
also prove their finite noise-enumeration lengths equal those code sizes.
Their `codeModel_quotient_preserved` theorems require the original positive
denominator. The observational interface's `codeModel_conditionOn_probVal`
specifically requires retaining both the joint event and evidence under the
same intervention. Observation preservation alone does not supply those
interventional probabilities.

Source presentation alone preserves all intervention laws of its input
model. After **compression**, only the compression's retained probabilities
are asserted equal to the original uncompressed model. Unit-level equation
simulation at decoded assignments does not imply that all those probabilities
are unchanged after the prior law changes. Endogenous hidden-node types,
mechanism tables and the original observed domain are not compressed here.
The multivalued regression reduces a private alphabet from three values to
two sampling codes while retaining the observed null value two as a valid
intervention target. A five-node hidden-relay fixture also checks the adapter
without imposing pairwise-only latent causes.

### Bounded hidden values on a fixed full DAG

`HiddenDAGReachableValues` enumerates trajectories for each supplied hard
intervention and every declared noise assignment, always adding the factual
intervention. A literal first atom of the normalized joint prior supplies a
factual default, without choice and without assuming that atom has positive
individual weight. Hidden nodes retain reached values; observed nodes retain
their entire declared domains, including null intervention values.

`valueWitness_card_bound` proves at most
`(actions.length + 1) * product_j noiseEnumeration[j].length` codes per hidden
node. `valueWitness_card_bound_of_noise_bound` gives the corresponding
`(actions.length + 1) * K^N` bound when every source enumeration has length at
most `K`. Repeated action positions are counted, not silently deduplicated.

`HiddenDAGValuePresentation.retainedValueModel` constructs an actual native
model with finite endogenous code types and the unchanged full graph and
private-source law. `retainedValueModel_evalNode` and
`retainedValueModel_evalObserved` prove trajectory simulation. Off-domain
equation outputs have an explicit default; inverse-decoding proofs establish
that it cannot alter a retained trajectory. `retainedValueModel_interventionalDist`
proves literal equality of the entire record for each retained intervention,
not merely selected event probabilities. Factual records and supported
conditionals are preserved too. `retainedObservedEquiv_card` proves observed
code sizes equal the public domain sizes, independently of repetitions in
the original native enumerations. The public observed signature is unchanged.

The separate source compression may already have changed unretained effects
of the original model. Hidden-value presentation preserves the retained
intervention laws of its own input model; it does not undo that distinction.
Trajectory coding itself does not enumerate mechanisms. The later code-table
catalogue described below supplies that separate enumeration and coverage.

`HiddenDAGFiniteRepresentation` composes both steps.
`FiniteHiddenDAGSCM.boundedRepresentation original targets` constructs a
`BoundedRepresentation` on the same full hidden DAG and observed signature.
For `t = targets.length`, `A = S.assignmentEnumeration.length` and `N` full
nodes, its private types are actual `Fin k_j` with `k_j <= A + t + 1`, and
its endogenous types are actual finite codes with hidden sizes at most
`(t + 1) * (A + t + 1)^N`. Observed code sizes equal the original public
domain sizes. The package contains the actual independent native model and
proved full-observation/target preservation; it does not ask the caller to
supply those correspondences. Arbitrary rational denominators are retained.

The underlying `finiteModel_observational`, `finiteModel_preserved`,
`finiteModel_hidden_bound`, and `finiteModel_observed_card` expose these
properties for any constructed observational source compression.
`finiteModel_conditionOn_probVal` transports supported conditionals when
their joint-event and evidence queries were both retained. Only retained
probabilities agree with the original uncompressed model; the whole
intervention-law equality in the value step is with its compressed input.
The later code-table catalogue covers all bounded cardinality shapes and
compatible equations; the standalone native-template boundary is described
separately below.

### Exhaustive finite code-mechanism tables

`FiniteFunctionTables` constructs explicit finite row witnesses, enumerates
all output tables, and proves `lookup_tabulate` and `tabulate_lookup`. The
proof-indexed parent choices use supplied Boolean edge decisions. An absent
parent contributes one vacuous function even when its unused value type is
empty; it is not incorrectly treated as a required full-node assignment.

`HiddenDAGMechanismTables.codeMechanismCatalogue` is fixed by the full graph
and node/source cardinality vectors, independently of any model's equations
or weights. `codeMechanismCatalogue_complete` and
`lookupCodeMechanisms_tabulate` prove exhaustive graph-compatible equation
coverage and reconstruction at **every** declared parent/noise input, not
just positive or retained trajectories. The equations can read only their
declared parents and their own private source.

`HiddenDAGMechanismTableModels.withCodeTables_ownCodeTables` proves exact native
model reconstruction through explicit two-sided value/noise conversions.
For a `BoundedRepresentation`, `mechanismTables_mem` lists its actual equations;
`tabulatedModel_eq`, `tabulatedModel_observational` and
`tabulatedModel_preserved` retain the model and its original-law guarantees.

`HiddenDAGMechanismCatalogue.boundedMechanismCatalogue` then enumerates every
bounded cardinality shape and each shape's complete table list. The uniform
node bound adds the sum of public observed-domain sizes to the hidden-value
bound. `BoundedRepresentation.catalogueEntry_mem` proves that every original
model's explicitly constructed representative has an entry in this **same**
finite list, fixed only by the full graph, signature and target count. No
equation from that original model is used to generate the list.

This intermediate code-table replay retains the base model's observed
conversions and independent source law. The standalone construction below
removes that dependency. Raw mechanism entries can still include incompatible
observed cardinalities or source alphabets with no normalized law; a raw table
alone is not a native model.

### Standalone native templates and full fixed-DAG coverage

`FiniteValueEquivalenceCatalogue` enumerates forward/backward maps on the
declared finite domains, checks both inverse laws, and constructs actual
`ValueEquivalence` records only after acceptance. `catalogue_complete` includes
every supplied two-sided conversion, including conversions of null observed
values. No support restriction substitutes for the declared domain.

`HiddenDAGNativeTemplates.nativeTemplateCatalogue` combines the bounded
mechanism entries with all checked observed conversions. A
`FiniteHiddenDAG.CodeNativeTemplate.model` takes only that standalone entry
and actual normalized rational source-factor records, not a base model or an
external semantic-preservation premise. Its prior is the independent product
of those factors. Zero-weight source cells are permitted. A zero-sized source
alphabet cannot silently acquire a normalized law.

`HiddenDAGNativeTemplateCoverage.nativeTemplateModel_evalNode` and
`nativeTemplateModel_evalObserved` prove explicit evaluator simulation under
the two-sided value/noise encodings. `nativeTemplateModel_interventionalValue`
preserves every event under every hard intervention of the encoded input
model; `nativeTemplateModel_conditionOn_probVal` preserves actual conditionals
with positive causal evidence. The decoded product-law proof uses the mapped
factor records, rather than assuming the old prior is literally a canonical
product record.

Finally, `HiddenDAGNativeTemplateRepresentation.nativeTemplateRepresentation`
constructs a listed standalone template and its rational factors for **every**
original model on the fixed full hidden DAG. The finite list depends only on
the graph, public signature and target count. Its proved `observational` and
`preserved` fields retain the complete observational law and each listed
target. `NativeTemplateRepresentation.conditionOn_probVal` combines retained
joint/evidence queries for supported conditional targets. These fields are
constructed theorems, not an uninhabited transfer interface.

The compression stage retains only the requested causal probabilities; its
representative need not preserve unlisted interventions of the original
model. The later two-sided encoding preserves all interventions of that
representative. Hidden-relay and three-valued native regressions check these
distinct guarantees. This is a finite **structural** family with infinitely
many rational source-weight assignments, not a finite feasibility search or
an optimizer-completeness theorem. It does not vary the full hidden topology.

### Projection-wide native realization and finite structural coverage

`LatentRootDAG.graph` constructs a full hidden DAG from any finite root
incidence table, with no two-child restriction. Its hidden-internal paths are
single edges because roots have rank zero and no incoming arrows. The proved
directed and bidirected projection theorems retain precisely the observed
arrows and shared-root incidences.

`ObservedGraph.cliqueRootProjection`, in `CliqueRootGraph`, fixes one root for
every bidirected clique mask. Empty masks, singletons and larger shared-child
sets are retained. Its exact projection adds no forbidden bidirected edge;
two-node masks recover every required edge. `cliqueRootCount_le_pow` and
`cliqueRootHiddenDAG_count_le` prove at most `2^n` roots and `n + 2^n` total
nodes, independently of an original model's hidden topology.

`FiniteProductGrouping` separately constructs independent block factors from
an explicit ownership map. Proof-indexed slots eliminate unowned coordinates
without chosen defaults. `decode_encode` and `encode_decode` give a total
two-sided assignment conversion. `decoded_probVal` proves complete decoded-law
agreement with every original independent prior, not only its one-coordinate
marginals. Repeated labels, zero-weight atoms and empty blocks are included.

`FiniteLatentSCM.cliqueGroupedModel`, in `LatentRootGrouping`, computes each
old root's owner from its exact observed-child mask. Projected-graph agreement
proves that mask is a listed clique; no canonical two-child premise is used.
`cliqueGroupedModel_evalUnder` and `cliqueGroupedModel_interventionalValue`
preserve every hard-intervention event probability, while the grouped model's
root count and incidences depend only on the observed graph. Graph, block-law
and original hidden-relay regressions exercise empty/private slots, zero cells
and a shared cause that still has three children after grouping.

`LatentRootNativeModel` constructs an actual `FiniteHiddenDAGSCM` for any
finite latent-root model, including shared causes with more than two children.
Root nodes copy their private blocks; observed mechanisms read exactly their
old observed parents and incident roots. `LatentRootNativeEvaluation` proves
unitwise evaluation preservation under every hard intervention by observed
topological induction, then transports the entire independent law, support
and actual supported conditioned records. No extra semantic transfer premise
or positive-trajectory assumption is requested.

`FiniteHiddenDAGSCM.toCliqueRootSCM`, in `CliqueRootNative`, composes full-DAG
collapse, independent grouping and native realization. It preserves every
interventional event and the whole observational law. Its target is the same
`graph.cliqueRootProjection` for every original full graph in the projection
class. Projection reindexing uses proved equality of the graph data; it does
not assume a correspondence theorem.

`ProjectedHiddenDAGModel graph` explicitly ranges over original full hidden
DAGs and their actual native records, requiring only agreement with the fixed
observed projection. Hidden topology, hidden alphabets and source alphabets
may vary without a supplied common bound. In the universe-zero public
signature used by the finite-template APIs,
`ProjectedHiddenDAGModel.projectionTemplateRepresentation` constructs an
actual member of the graph-fixed finite structural catalogue and its actual
independent rational factors. It preserves every observational event and
each requested causal probability. `asProjectedModel` supplies the converse
membership boundary: the instantiated representative is itself a legitimate
original full-DAG model with that observed projection.

The structural bounds depend only on the observed graph, its public signature
and target-list length, not the original hidden-node count or denominators.
`conditionOn_probVal` preserves supported conditional targets when the joint
and evidence queries are retained and the original causal evidence is positive.
The projection-wide regression checks hidden relays, three-child shared
causes, factual zeros, multivalued count laws and null intervention targets.
Unlike the uncompressed clique representative, the final compressed template
need not preserve unlisted interventions. Neither construction makes rational
parameter assignments finite or decides their feasibility.

## Exact bounded-class compatibility and fixed-law target comparison

`FiniteRecordCatalogue` enumerates normalized laws on a declared `Fin card`
alphabet below an explicit denominator bound. `canonical_mem` covers arbitrary
original records by aggregating singleton masses; repeated labels and zero
occurrences are allowed. `canonical_den` retains the original denominator,
and `canonical_probVal` and `canonicalProduct_probVal` preserve every event
and the full independent product law without expanding weights into unit cells.
Empty alphabets and a zero denominator bound cannot invent normalized factors.

`FiniteLatentProjection.boundedNativeCatalogue`, in `BoundedNativeCatalogue`,
combines the exhaustive bounded structural catalogue with these finite source
laws. Every entry instantiates an actual native SCM. Membership enforces the
declared node, source and denominator bounds; completeness covers all bounded
mechanisms, observed conversions and rational factor presentations.

`BoundedNativeRepresentation` closes the original-type boundary. Its
`boundedSearchRepresentative` constructs two-sided codes from the actual
native model's deduplicated complete enumerations, then aggregates source
weights. It preserves every hard-intervention event and the original source
denominators. `boundedSearchRepresentative_mem` proves catalogue membership
from bounds on the original supplied enumeration lengths and denominators,
without asking for an external coverage or simulation theorem. Repeated
enumeration entries count honestly toward the stated input length bounds.
`boundedSearchRepresentative_eventPositive_iff` and
`boundedSearchRepresentative_num_zero_iff` retain
positive and null causal evidence in both directions.
`boundedSearchRepresentative_conditionOn_probVal` preserves the actual
supported conditioned record, with positivity explicitly supplied from the
original interventional law. A three-valued regression retains a factual null
at count two and its supported conditional after that null value is forced.
The conditional-search policy built on this bridge reports support and values
separately, as described below; the representation itself imposes no policy.

`NativeTemplateInstance.observationCheck_exact` proves that checking all
observational singleton probabilities is equivalent to matching the supplied
whole observed law. `BoundedNativeSearch.solve` filters the finite catalogue
by that exact test and returns one of three proof-carrying results:

- **Incompatible:** no original native model satisfying those enumeration and
  denominator bounds has the supplied observed law.
- **Identified:** an actual fitted native witness attains a value shared by
  every original native model in that bounded class.
- **Ambiguous:** two actual fitted native models in that class have different
  requested target values.

`BoundedNativeClassification` exposes the same guarantees as public semantic
predicates over all original native models: `Compatible`, `PointIdentified`
and `Separated`. Point identification requires compatibility, so an impossible
input law does not count as vacuously identified. Each computed `Result`
supplies explicit `Decidable` values and exact Boolean checks; these are not
global instances that might automatically start a large catalogue search.
`compatible_iff_pointIdentified_or_separated` and
`not_pointIdentified_iff_incompatible_or_separated` give constructive exact
alternatives. Their proof inspects the finite search result, rather than
assuming a general negated-universal-to-counterexample or excluded-middle rule.

These are unconditional interventional event probabilities; no conditional
is evaluated at null evidence. Observational zero cells and null action
targets are retained. The regression on `X -> Y` has two factual point-mass
models which disagree after forcing an observationally null action. The full
solver must report ambiguity for that effect, identification for the factual
query and incompatibility at denominator bound zero. Those outcome theorems
use the solver's proved obligations, not expansion of the whole catalogue;
small two-entry tests separately execute the comparison algorithm.

`BoundedNativeConditionalSearch.solve` extends the same bounded original-model
class to `NativeConditionalQuery`, with three explicit inputs: intervention,
evidence and event. It first reports incompatibility or an actual fitted
witness. For a compatible law it returns two independent proof-carrying reports:

- **Support:** positive causal evidence in every original fitted model, or an
  actual fitted native model whose causal evidence numerator is exactly zero.
- **Supported values:** no original fitted model has positive evidence; an
  actual positive-evidence witness attains a value shared by every supported
  original fitted model; or two positive-evidence fitted native models have
  different conditional values.

The null-witness branch does not suppress the supported-value report. Mixed
support with a common supported value is therefore different from both an
everywhere-defined identified conditional and value ambiguity. Likewise,
compatibility with uniformly null evidence is different from incompatibility.
`representative_supported_iff` and `representative_value` justify transporting
the finite inspections through canonical coding to all original bounded
records. They preserve the actual conditioned-record semantics, not a default
zero value at null evidence. The observational fitting list is shared by the
two inspections. Regression tests cover mixed support with a common supported
value, uniformly null evidence, uniformly positive evidence with disagreeing
values, and incompatibility, without kernel expansion of the full catalogue.
A separate three-valued `X -> Y` regression has mixed support and two different
supported values: after a null factual action, evidence `Y != 0` is null in
one fitted model and positive at responses one and two in two others.
`solver_mixed_ambiguous` proves that the full bounded checker reports both a
null-evidence witness and supported-value ambiguity for that same input law.

This is an opt-in finite procedure, not a practical large-graph optimizer.
Bounds are part of its class definition. In particular, projection-wide source
compression has not been proved to preserve a prescribed denominator bound.
Bounded identification or incompatibility does not imply the corresponding
unrestricted conclusion. A returned pair of disagreeing models is, however,
a genuine fixed-law counterexample in any larger class containing that pair.
No rule for stopping an increasing-bound search is asserted.

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

### Fixed-full-DAG and projection-wide coverage boundaries

For a **fixed full hidden DAG** with fixed observed domains, the constructive
finite structural coverage theorem is implemented above.
Retain all observed singleton queries and the finitely many primitive queries
appearing in the requested target. Existing source compression gives a bound
`K = number of retained queries + 1` for each source's positive atom occurrences.
`HiddenDAGCompactSources` now relabels them by actual `Fin k_j` sources with
`k_j <= K`, retaining the selected probabilities and the whole observed law
when requested. Uniform zero-padding to a common `Fin K` is not needed by
this compact adapter and is not asserted implemented.

Hidden-value enumeration, finite coding, explicit defaults and evaluator
simulation on a fixed full DAG are now implemented as described above. The
factual intervention is always included, so the bound uses `actions.length + 1`
positions. Bounded cardinality-shape and code-mechanism enumeration, their
complete membership proofs, and exact native table replay are implemented.
Checked finite observed conversions, independent rational source parameters,
the standalone constructor and its native-law coverage theorem now close the
fixed-full-DAG representation boundary. They provide the transfer needed to
extend a uniformly valid target bound from all listed templates and their
source parameters to the original full fixed-DAG family. The existing
polynomial-bound API has not yet been wrapped as an automatic catalogue-wide
checker. Neither representation nor a supplied bound certificate establishes
feasibility, sharpness or completeness of certificate search.

The finite search can also be enormous; mathematical finiteness is not an
efficiency guarantee. When only the observed projection is fixed, the separate
projection-wide construction above now handles varying hidden topologies:
collapse, group by child masks, realize the fixed clique graph natively, then
apply the fixed-DAG coverage theorem. There are at most
`2^(number of observed nodes)` roots in that intermediate graph. Roots with
three or more children remain allowed; they are not replaced by independent
pairwise causes. This route avoids bounding the original internal hidden-node
alphabets individually.

Both finite-template coverage results leave infinitely many rational
source-weight assignments. Neither proves complete certificate search,
optimization, sharpness or rational feasibility decision. No excluded-middle,
choice or real-to-rational transfer principle is added at these boundaries.

## Proved rational fixed-template obstruction

A concrete fixed-template obstruction makes that last warning substantive.
Its rational negative direction is now formalized in
`IndependentBooleanObstruction`, using actual independent Boolean records and
their deterministic readout, not an assumed polynomial-binding interface.
Take three independent binary sources with probabilities `u`, `v`, `f`.
Use the fixed observed mechanisms
`V = A && B` and `O = if F then A else !B`. Require the observed joint
table of `(O,V)` to be uniform. Its equations include
`P(V=1)=u*v=1/2`, `P(O=1,V=1)=f*u*v=1/4` and
`P(O=1)=f*u+(1-f)*(1-v)=1/2`. Hence `f=1/2`, `u=v` and
`2*u^2=1`. A real solution exists in the unit interval, but no rational one:
writing `u=a/b` in lowest terms gives `2*a^2=b^2`, forcing both `a` and `b`
even. Conversely, the positive real root with `f=1/2` makes all four observed
cells `1/4`. The enlarged-scalar comparison in this sentence is explanatory,
not a real-valued Lean probability implementation. The formal theorem
`no_target_marginals` excludes even the three displayed marginal/joint targets
for every original finite rational Boolean source record, including repeated
labels, zero cells and unreduced denominators. `not_uniform` then excludes
the full observed uniform law. `v_mass`, `joint_mass` and `o_mass` prove the
actual finite-product event equations; no symbolic likelihood is trusted.
`RationalSquareObstruction.twice_square_ne_square` closes the contradiction by
strict natural-denominator descent, without selecting a lowest-terms fraction.
`sourceLaw_probVal` proves the full pushforward identity for arbitrary private
sampling records and their explicit Boolean readouts. `sourceLaw_not_uniform`
therefore retains the negative theorem for any finite private source alphabet
sizes and unbounded denominators, not just sources literally labelled by
`Bool`. Heterogeneous sampling presentations, zero cells and repeated natural
labels are exercised separately. The observed mechanisms remain fixed.

This obstruction concerns the **fixed mechanisms**, not the graph-wide
class: on the same parent graph, the different mechanisms `V=A`, `O=F`
with rational fair sources realize the uniform table. The regression theorem
`alternative_uniform` proves this alternative readout's entire event law,
not just its marginals. It therefore disproves
an automatic real-to-rational template transfer, not the existence of a
general rational causal decision procedure. No reduction proving that
general procedure impossible has been established here. Exact rational
feasibility/uniqueness or a genuinely applicable impossibility reduction
remains unresolved. The explicitly bounded unconditional and conditional
checkers are constructed results, not assessment-only proposals. Their bounds
and separate support/value semantics must not be dropped; the categorical bow remains a separate assessed
extension. Do not launch an open-ended arbitrary-graph optimizer on the
strength of finite representation or bounded-class search alone.

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
memory-safe. See [the operating guide](AGENTS.md#builds-and-checks) for current local
commands and [the history](HISTORY.md) for the measured pilot limitations. CI checks the exact pushed commit with targeted and
complete builds plus `Thesis.AxiomAudit`. The audit permits only `propext`
and `Quot.sound`, rejecting choice, general propositional excluded middle
dependencies, admitted proofs and untrusted Boolean proof reduction. A cached
artifact or a successful isolated leaf check is not that project-wide gate.

<a id="entropy-and-auxiliary-values"></a>

## Entropy and auxiliary analytic values

The goal retains rational probability laws and the existing constructive axiom
policy. Entropy values may be irrational; exact symbolic logarithms and rational
interval certificates are auxiliary values, never new atom weights. Units are bits.

### exact logarithmic arithmetic

- `PositiveRatio` supplies unreduced positive rational arguments, equivalence,
  order, products, inverses and powers.
- `ExactLog` represents `log₂(argument) / degree` with a positive natural degree.
  Equivalence and order compare rational powers at common degrees. Addition,
  negation, natural scaling and positive natural division respect the value.
- `ExactLogRational` embeds signed rational numbers of bits and proves exact
  correspondence with integer cross-product comparison.
- `ExactLogEnclosure.enclose` terminates for every positive rational tolerance.
  It returns a common-denominator rational interval containing the exact value,
  with a proved width strictly below the requested tolerance. Binary-length
  initial bounds and depth selection avoid a linear-depth precision search.
- `Thesis.Examples.ExactLog` checks root/argument presentation changes, negative
  values, exact bounds around `log₂(3)`, and executed certified bisection.
  Both full and early arithmetic axiom gates import the regressions.

These are symbolic logarithms with an exact ordered arithmetic interpretation,
not a newly assumed real logarithm. The separately proved `ExactLogInterpretation` bridge below supplies an
auxiliary constructive real interpretation; it does not change atom weights.

### entropy and positive-reference KL

- `ExactLogWeights` proves congruence for both rational coefficients and exact
  logarithm values, monotonicity, and finite-sum congruence/permutation laws.
- `EntropyValue` defines `-p log₂(p)` and `p log₂(p/r)`, with explicit zero
  observed-mass branches and positive reference masses. Both respect unreduced
  rational presentations. Entropy contributions in `[0,1]` are nonnegative.
- `Distros.EntropyGrid` requires distinct observable outcomes. `Distro.entropy`
  and `Distro.relativeEntropy` require almost-sure grid support, so extra null
  atom labels remain admissible. They aggregate the original singleton PMFs.
- Entropy and KL are invariant under `SameLaw`. Entropy is nonnegative and
  invariant under grid permutation and adjoining a zero-mass cell. Positive
  reference laws have zero self-divergence.
- Executed regressions cover fair and point laws, duplicate/split/reordered
  records, rescaled denominators, a retained null outlier, grid changes, and
  unequal positive prior weights. The fair-law/prior `(1/4,3/4)` KL value is
  certified exactly as `log₂(4/3)/2`.

### constructive arithmetic–geometric mean foundation

`FiniteAMGM` proves the denominator-cleared finite inequality at every list
length, using Cauchy's finite doubling/descending proof. Natural multiplicities
then give weighted AM–GM, including zero values and weights. Both non-strict and
strict common-denominator product bounds are available for the rational Gibbs
inequality. Later checkpoints use this foundation to establish KL and entropy
bounds. Strict concavity and the certified rational optimizer are proved in
separate downstream layers described below.

### rational Gibbs inequality and KL nonnegativity

`RationalAMGM` clears the finitely supplied argument denominators and proves
weighted rational products are at most one whenever their arithmetic mean is
at most one, including empty and zero-weight families. `LogMeanInequality`
transports that algebraic result to common-degree exact logarithms.

`Distros.EntropyGibbs` proves grid PMF normalization and numerator sums, then
`Distro.relativeEntropy_nonnegative` for every rational law and positive reference
law on the declared grid. It imposes no positivity assumption on observed masses.
The proof includes aggregation of duplicate atom occurrences and null outliers.
Executed regressions include a point law on a three-state grid with two zero
observed cells, whose uniform-reference KL equals `log₂(3)` exactly.

KL nonnegativity alone does not establish the equality or optimality results;
the following checkpoints prove those additional statements separately.

### equality in Gibbs and KL

`FiniteAMGMEquality` proves the weighted equality case using midpoint
comparisons and the already established finite AM–GM bound. `RationalAMGMEquality`
and `LogMeanEquality` transport it to arbitrary positive rational arguments;
zero-weight arguments remain unrestricted.

`Distro.relativeEntropy_equiv_zero_iff` proves that KL vanishes exactly when
the laws agree on every Boolean event. Equality at positive observed cells
and normalization also force equality at zero observed cells. The regressions
check a split/rescaled/reordered law with a null outlier, a genuinely different
point law, and an unrestricted zero-weight argument in the rational equality
lemma. No literal atom-list equality is assumed.

### entropy bounds and the cross-entropy criterion

`ExactLogLinear` proves rational bilinearity and the finite-sum identities needed
for entropy comparisons. `CrossEntropyValue` and `Distros.CrossEntropy` establish
KL = cross entropy minus entropy, the global cross-entropy upper bound, and a
positive-candidate optimality criterion: fixing the candidate cross entropy
makes the candidate a global entropy maximum, with equality exactly at the same
law. The signed-moment/log-linear layer below supplies the bridge from the
original rational moment constraints to this cross-entropy equality.

`EntropyGrid.uniform` retains every declared cell with weight one.
`Distros.EntropyUniform` proves its entropy is exactly `log₂(cardinality)` and
that every supported law satisfies `0 ≤ H ≤ log₂(cardinality)`. Equality in the
upper bound holds exactly for the uniform law. Null cells in the declared grid
remain part of the cardinality, and null atom outliers remain admissible.

`Thesis.Examples.EntropyBounds` checks the three-state uniform bound and its
equality case, and the nonuniform candidate `(1/4, 1/4, 1/2)` with entropy `3/2`
bits. A competitor with the same cross entropy and a retained null outlier has
strictly smaller entropy.

### strict concavity, including the boundary

`Distro.mixture` wraps the scale-and-append rational record construction, keeping
both atom lists and their null outliers. Singleton masses and cross entropy obey
the expected affine formulas even when input denominators differ.

`Distro.entropy_mixture_comparison` proves concavity for any two positive natural
mixing masses, normalized by their sum, and equality exactly when the input laws
are `SameLaw`. `Distro.entropy_strict_concave` states the strict consequence for
different laws. Shared zero-mass cells are handled by an internal positive-support
restriction with a proved entropy-preservation lemma; the caller's declared grid
and atom records are never replaced. No full-grid positivity premise remains.

`Distro.entropy_maximum_unique` proves that any attained maximum in a class closed
under midpoints is unique as a law. This is a conditional uniqueness theorem,
not an existence assertion for exact rational maximizers. Regressions exercise
shared zero cells, null outliers, unequal denominators, unequal mixing weights,
strict inequality for distinct point laws, and equality for split presentations.

### moment feasibility and the first continuity estimate

`EntropyMomentConvex` proves affine signed rational expectations for the actual
mixture constructor, and preservation of every closed rational moment interval.
`PartialMomentProblem.Admissible` includes the original almost-sure grid support
and all existing constraint rows. Its entropy uniqueness theorem now applies
directly to exact and interval problems, with no row independence or interior
mass hypothesis. The existing feasibility/refutation solver remains the source
of exactly feasible rational witnesses and infeasibility certificates.

Regressions combine an exact mean, a signed response interval, a forced-zero
coordinate, duplicate redundant rows, unrelated input denominators and retained
null outliers. Mixture feasibility is proved for all such problems, not checked
only on a denominator grid.

`FiniteBernoulli` proves finite power difference and complement bounds by natural
induction. `EntropySmallMass` derives
`log₂(den/(den-1)) ≤ 1/m` whenever `2m ≤ den`, and exact-log monotonicity in a
nonnegative rational coefficient. These are proved ingredients for the boundary
continuity argument. The full modulus and certified optimizer are separate
implemented layers described below.

### quantitative entropy continuity at zero

`EntropyTermBounds` derives a scalar cross-entropy bound from the actual
Gibbs theorem, using an auxiliary two-state reference. The observed mass may
be zero or one. For every `k`, it proves
`p ≤ 1/2^(k+1) → -p log₂ p ≤ (k+3)/2^(k+1)`.

`entropyBoundaryThreshold` supplies a positive rational threshold for every
positive rational tolerance. `entropyTerm_near_zero` proves that every rational
probability below that threshold has entropy contribution at most the requested
error. Its construction uses finite powers and binary lengths, with no
unbounded search, real logarithm axioms or denominator restriction on the input.
Regressions include probability zero and a non-dyadic mass `3/10000000`.

This scalar boundary estimate is an input to the implemented uniform two-point
modulus, moment/log-linear bridge and certified constrained optimizer below.

### uniform two-point entropy continuity

`EntropyIncrement` proves algebraic bounds on the change of an entropy term
between positive probabilities. `EntropyContinuity` combines those bounds with
the zero-boundary estimate. For every natural precision `n`, coordinate distance
at most `1/2^(3n+6)` gives entropy-contribution error at most `1/2^n`. The theorem
covers arbitrary unreduced rational presentations and both probability endpoints.
A total rational threshold interface also accepts every positive rational error.

`Distros.EntropyContinuity` lifts that result to full entropy on the caller's
declared grid. Its explicit coordinate threshold depends only on grid cardinality
and requested error. The resulting symmetric entropy bounds quantify over all
supported rational laws, without a denominator cap or an interior-support premise.
Regressions exercise zero, one, interior probabilities, unrelated denominators,
a zero cell gaining positive mass, a shared null cell and null record outliers.

Uniform continuity is a proved input to the finite-box constrained optimizer,
not an assumption left to its caller. Both that optimizer and the separate
moment/log-linear optimality bridge are implemented below.

### total certified rational entropy optimization

`ProbabilityBoxes` enumerates a finite cover by rational coordinate intervals.
Every rational probability in `[0,1]` has a floor-selected box, and any two points
in one box differ by at most its width. The mesh controls interval width, never
the denominator of an input law or a feasible solver witness.

`EntropyBoxes` adds these coordinate intervals to the unchanged
`PartialMomentProblem` grid and original exact/interval rows. `EntropyBoxSearch`
uses the existing complete feasibility solver in each box. A box containing a
feasible law cannot be rejected, and its exactly feasible witness is close enough
for the proved entropy continuity bound. Exact comparisons select a maximum
among those finitely many candidates. The result bounds every feasible rational
law, not just those candidates. A universal-entropy-bound fast path can avoid the
exhaustive cover when it already certifies the supplied feasible witness.

`ExactLogPositiveEnclosure` clips a lower endpoint at zero only under a proved
nonnegativity hypothesis. Its integer conversions use explicit constructive
cases. `PartialMomentProblem.solveEntropy` either retains the original certified
infeasibility result or returns an `EntropyCertificate` containing an actual
compatible rational law `q` and nonnegative rational `L,U` with

- `L ≤ H(q)`;
- `H(p) ≤ U` for every exactly feasible rational law `p`;
- `L ≤ U ≤ L + epsilon`.

Optimization error and enclosure width each receive half of the requested
positive rational tolerance. The fallback is a total reference algorithm; its
finite Cartesian box enumeration may be very expensive. No practical runtime or
exact rational maximizer is asserted.

Executed regressions check arbitrary-denominator box indexing, feasible and
infeasible boxes, an infeasible moment problem, the full singleton solver with a
clipped zero lower endpoint, and a fair-law certificate at tolerance `1/1000`.
The whole dependency closure passes the constructive arithmetic axiom gate.

### signed-moment log-linear optimality

`LogExpectation` integrates exact logarithmic observables against aggregated
PMFs and proves finite affine integration. `ShiftedMoments` computes a finite
offset for each signed integer response on the original declared grid. Fixed
signed expectations therefore fix the corresponding nonnegative natural moments;
unsupported zero-weight atom labels impose no extra shift hypothesis.

`PartialMomentProblem.LogLinearReference` records a positive rational reference,
an affine log score and selected exact rows from the original problem. The
coefficients are arbitrary exact logarithm values and may be negative. The
selected endpoints need only be equivalent rational presentations; redundant
rows and other interval constraints remain admissible.

`LogLinearReference.crossEntropy_fixed` proves equal cross entropy for every two
feasible laws. A feasible anchor consequently gives a universal entropy upper
bound even when the reference itself has the wrong target expectation. If the
positive reference is feasible, `LogLinearReference.optimal` proves global
maximality and equality exactly at the same probability law. This is the promised
fixed-expectation bridge, not merely a stationary-point assertion.

The reference positivity premise includes every declared cell. A candidate with
forced zeros cannot satisfy that premise on the full grid; the total optimizer
has no such premise and already handles those boundaries. The entropy-preserving
internal support restriction is available for separate boundary score arguments.
Regressions prove a nonuniform global maximum under a negative integer response,
with a retained null outlier. The constructive arithmetic audit passes.

### tight mean-one-half certificate and validation

`EntropyHomogeneous` proves an equivalent common-degree entropy formula, allowing
concrete certificates to execute without multiplying all the individual root
degrees. `Thesis.Examples.EntropyMeanHalf` uses the exactly feasible rational law
`(62/100, 26/100, 12/100)`, with a split atom and a retained null outlier. It keeps
the original grid, exact mean `1/2` and duplicate redundant signed rows.

A rational Gibbs reference with ratio `13/30` gives a global upper bound through
the proved moment/log-linear bridge, even though that reference has a different
mean. Exact rational-power comparisons certify the interval `[2599/2000,
2601/2000] = [1.2995,1.3005]` bits, with width exactly `1/1000`, for the requested
rational optimum certificate. No exact rational maximizer is asserted.

The same example exposes the general total algorithm at every positive rational
tolerance. Additional executed regressions retain a forced-zero cell and repeated
signed constraint rows. `EntropyCertificate.width_bound` also states the width as
the existing witnessed rational subtraction `U - L ≤ epsilon`.

All six planned mathematical activities are now implemented for rational laws.
The complete build and full axiom audit remain mandatory publication gates.
Practical improvements to the exhaustive fallback and the separate real-number
semantic development are extensions beyond this completed rational scope.

### Real feasible-law and optimizer bridge: separate research

The kernel results above concern exact symbolic logarithms and the framework's
rational probability laws. The auxiliary constructive real type and rational-logarithm interpretation
below are proved separately. No real logarithm axiom, choice principle or
real-valued maximizer is silently imported.

The full real feasible-law/optimizer bridge has the following distinct parts.
The first is implemented for rational arguments by `ExactLogInterpretation`
and `EntropyInterpretation`; the density and optimizer-transfer obligations
in parts 2 and 3 remain separate research.

1. Interpret an `ExactLog` as `log₂(argument)/degree` in a real-number model with
   a logarithm on positive arguments, and prove that equivalence, addition, rational scaling and
   rational-power order agree with that interpretation. Embed rational bit bounds
   by the same ordered map. This identifies the symbolic entropy with
   `-sum p_i log₂(p_i)`, using the proved zero convention.
2. Embed the original rational moment rows into real finite-coordinate space and
   prove density of exactly feasible rational points in their real feasible
   polytope. Rounding coordinates independently is insufficient for exact moment
   equalities. A suitable route is a finite rational-vertex representation followed
   by rational approximation of convex combination coefficients; that preserves
   exact equalities, closed intervals, forced-zero faces and redundant rows.
3. Prove continuity of real finite entropy, including zero. Density and the closed
   order relation then transfer each universal rational upper certificate to
   every real feasible law. Compactness of the nonempty bounded closed polytope
   and continuity yield an attained usual real maximum, if that existence claim
   is wanted. Constructive real existence would require its own corresponding
   compactness or effective-limit proof.

These are additional semantic/density theorems, not premises exposed by the
rational algorithm. The implementation already returns the requested universal
rational certificates without assuming those real theorems.

## The three-state mean-one-half real model

In the usual real interpretation, a positive Gibbs law on `{0,1,2}` with mean
`1/2` has probabilities `(1,r,r²)/(1+r+r²)`, where `3r²+r-1=0`. The positive
solution is `r=(sqrt(13)-1)/6`. It satisfies the constraint, and the global Gibbs
inequality certifies it as the real entropy maximum. Strict concavity gives
uniqueness. Since `r` is irrational and equals the ratio of its second and first
probabilities, that exact real optimizer cannot have all rational probabilities.

This real-model explanation is not asserted as a new Lean theorem about a real
number type. The rational library instead certifies exactly feasible rational
approximations and universal error bounds. Its separate real semantic/density
bridge, described above, is what would formally connect those certificates to
the displayed real optimizer.

## Verification and scope

Every new example is included in both the early constructive audit and the full
project audit. Completed mathematical checkpoints are published to main only
after the complete CI build and full axiom gate pass. The implementation keeps
rational laws, exact symbolic logarithms, and certified rational approximations;
it does not claim an efficient exhaustive search or a completed general
real feasible-polytope/optimizer semantics.

Ordinary local Lake builds use `LEAN_NUM_THREADS=1`, the committed 4608 MiB
compiler threshold and the existing cache. Only one build may run on the machine
at a time. Targeted checks do not establish full-project success; the full build
and axiom audit remain mandatory. Remote CI repeats both gates for published
checkpoints before they are reported as verified on main.


### Separately authorized auxiliary and physical research

The completed six-activity rational implementation above defines Shannon
entropy and proves its theory and certified optimization. The subsequent
seven-activity goal additionally asks for a characterization from uncertainty
requirements, constructive analytic semantics, a real feasible-polytope and
optimizer bridge, multiplier necessity and sufficiency, partition-function
calculus, and a conditional finite thermodynamic identification. These further
activities are not claimed complete by the earlier checkpoint descriptions.

The first foundation now includes:

- `EntropyGrouping`: the exact product-mass identity, finite two-stage grouping,
  independent-product additivity, rational presentation congruence, permutation
  and insertion of null coordinates. Zero branch weights are allowed.
- `Distros.UncertaintyMeasure`: normalized rational probability vectors and an
  explicit abstract uncertainty specification. Its requirements are coordinate
  representation invariance, permutation, null insertion, grouping, monotone
  uniform uncertainty, and fair-bit normalization in `ExactLog`. No uniform
  logarithm formula, derivative or uniqueness conclusion is a premise.
- `UncertaintyMeasure.shannon`: the implemented entropy satisfies every listed
  requirement. The bridge from an existing `Distro` uses aggregated singleton
  masses, so split records and null outliers do not become extra states.
- `Distros.UncertaintyUniform`: grouping implies `h(mn) = h(m) + h(n)`,
  `h(1) = 0`, and `h(n^k) = k h(n)` for every abstract measure, including
  exponent zero. These are the first steps of the number-theoretic proof.
  The subsequent checkpoints establish uniform uniqueness and then the full
  rational-vector characterization.

The new regressions include unequal rational denominators, a three-way
refinement with a zero-weight branch, retained zero coordinates, abstract
uniform power laws, and the aggregated distribution bridge. Both early and
full audits import the regression module. The remaining analytical and
physical work retains its full requested scope and requires separate proofs.

### Uniform uncertainty is now characterized

`ExactLogSeparation` proves an explicit Archimedean separation principle for
exact symbolic logarithms. A positive exact value has a computed natural
multiple of at least one bit, by a finite Bernoulli lower bound. Consequently,
if every natural amplification of `x` is at most the same amplification of
`y` plus one bit, then `x ≤ y`. No real completion, derivative, general excluded
middle, or extra separation axiom is used.

`Distros.UncertaintyUniformUniqueness` compares each uniform choice with the
two adjacent powers of two around its repeated product. Grouping and fair-bit
normalization put every admissible uncertainty measure inside the same bit
bracket. The proved separation principle forces two such measures to agree.
Thus `UncertaintyMeasure.uniform_log` derives `h(n) = log₂(n)` from the listed
requirements. The subsequent refinement checkpoint applies this result to
arbitrary rational vectors, including their null cells.

### Complete rational Shannon characterization

`ProbabilityVectorCounts` computes a common natural-count presentation of every
normalized rational vector using the existing constructive denominator-clearing
algorithm. It proves coordinate equivalence without imposing a denominator cap.
`UncertaintyRefinement` groups a uniform space into positive count blocks and
uses the proved uniform uniqueness to force agreement between any two admissible
uncertainty measures on those rational vectors.

`UncertaintyCharacterization` extends the result to arbitrary zero coordinates
using permutation and null insertion. These transformations occur inside the
proof; its public theorem concerns the entire original vector. Its theorem
`UncertaintyMeasure.unique` compares any two measures satisfying the listed
requirements. `UncertaintyMeasure.characterization` then specializes one of them
to the proved Shannon instance and yields exactly the implemented entropy.
`distro_characterization` connects the result to the existing `Distro.entropy`
on aggregated observable grids, including split atoms and null outliers.

This completes the rational `ExactLog` characterization requested in activity 1.
No uniform logarithm formula, continuity, derivative or entropy formula was a
premise about the arbitrary measure. The proof uses the established order
separation of the chosen exact value space. It does not assert a characterization
for arbitrary other value spaces or for unrestricted real probability vectors.

The uncertainty requirements identify the quantity. They do not alone imply
that an inference procedure must maximize it. Choosing maximal uncertainty
subject to known constraints is an additional inference criterion; the existing
certified optimizer proves that criterion is met to the supplied tolerance.
An alternative justification through a sampling/allocation model requires that
model and its asymptotic argument as additional premises. Neither the probability
rules nor fixed averages alone silently supply this policy.

Activity 2 has the partial analytic development described below. Activities 3–6
remain open: real feasible-law and optimizer bridges, multiplier necessity and
interval/boundary qualifications, partition-function calculus, and the
conditional physical correspondence.
Activity 7 remains ongoing as each new stage is tested and audited. The rational
characterization regressions include unreduced unequal denominators, null cells
at several positions, generic arbitrary measures, and the existing law adapter.


### Constructive analytic values: first foundation

`RationalApproximation` proves rational order closure under arbitrarily small
positive rational errors, with an explicit separating precision. The proof
works with unreduced signed fractions. `ConstructiveReal` then presents an
auxiliary real value by an executable enclosure at every positive rational
precision. Its intervals are mutually consistent and their widths are bounded
by the requested precision. Rational values have singleton enclosures. Closed
order is a proposition comparing all enclosure bounds; no arbitrary real
comparison or equality decision is assumed.

`ConstructiveRealAdditive` and `ConstructiveRealScaling` construct addition,
negation, finite sums, natural division and nonnegative rational scaling, with
proved congruence and additive/order laws. These values remain auxiliary;
`Distro` atom weights and exactly feasible solver outputs are still rational.
The current arithmetic gives correctness constructions, without a claim of
an optimized numerical evaluator.

`ExactLogRationalArithmetic` proves signed rational-bit addition and natural
amplification identities. `ExactLogInterpretation` constructs a real presentation
from the existing rational bisection certificates. It preserves and reflects
`ExactLog` order and equivalence, agrees with the rational embedding, and
preserves addition, negation, finite sums, natural division and rational scaling.
Thus existing exact comparisons can be used as real-value bounds, and the
interpretation does not identify unequal exact values.

`EntropyInterpretation` constructs base-two logarithms of positive rational
arguments in this value space, proves their product/inverse laws, and connects
the existing rational entropy and KL summands to `−p log₂(p)` and
`p (log₂(p) − log₂(r))`. The finite entropy sum is preserved. Zero observed
mass contributes zero without evaluating `log(0)`; KL retains its explicit
positive-reference hypothesis.

This initial value foundation is not the complete current analytic layer.
The later sections now include effective real limits, real ring/order laws,
product stability and logarithms on explicitly bounded positive domains.
A general real exponential and differentiation still require separate proofs;
the certified rational-series and rational-argument Taylor constructions are described
below. No calculus, ideal optimizer existence,
rational feasible-polytope density, multiplier existence or physical entropy
identification is claimed by this initial value foundation.

The new audited regressions compute rational enclosures of `log₂(3)`, transfer
an exact lower bound to real order, exercise arbitrary-presentation additive
laws and rational scaling, and preserve null entropy coordinates and KL terms.


### Effective rational limits

`ConstructiveRealLimits` completes a regular rational approximation net by an
explicit interval construction. It proves a bound around every supplied
approximant and uniqueness of the resulting real value among presentations
satisfying those bounds. A `RationalCauchySequence` includes an executable
modulus and a proved tail-error estimate. A common later index turns it into
a regular net, without requiring a monotone modulus. The resulting limit has
proved error bounds for every sufficiently late sequence term.

Every existing `ConstructiveReal` also supplies a regular net of computed
rational lower endpoints. Completing that net is proved equivalent to the
original real presentation. This is scalar rational reconstruction; it does
not independently round probability coordinates or establish density inside
a constrained feasible polytope.

The regressions construct the nonconstant sequence `1 − 1/(n+1)`, give it a
valid modulus, and prove its independently constructed limit equals one.
They also check tail bounds and reconstruction for arbitrary real presentations
and the certified `log₂(3)` presentation. The approximation modulus is explicit
input data: these results do not assert convergence from strict concavity or
supply the quantitative optimizer estimates still required in activity 3.


### Exact rational error calculus

`RationalNorm` defines the magnitude of an auxiliary signed rational as an
unreduced nonnegative fraction. It proves presentation invariance, negation
and product identities, the triangle inequality, and equivalence between an
absolute-error bound and its two signed inequalities. Magnitude zero is proved
equivalent to rational zero, including unreduced presentations.

The product-error theorem bounds `|ab − cd|` by
`|a − c| |b| + |c| |b − d|`, with a corollary using supplied error and magnitude
bounds. Inputs may be negative and the nonnegative bounds need not be at most
one. These are exact auxiliary arithmetic estimates for constructing real
multiplication and later certified series. General real products, ring laws
and their order/stability properties are described below; calculus is separate.
Regressions cover mixed signs, cancellation,
unreduced magnitudes and a product difference of magnitude `1/24`.


### Certified real products

`ConstructiveRealDistance` defines two-sided rational error certificates in the
closed real order. It proves the triangle and congruence rules and that values
within every positive rational tolerance are equivalent. Regular rational
approximants satisfy these real error bounds. Two regular nets with the same
limit satisfy cross-error bounds, and any fixed natural multiple of the
requested errors still forces agreement of their limits.

`RationalPrecision` computes positive precision division and a cap at one.
`RegularRationalAlgebra` computes integer magnitude bounds for approximants at
precision at most one. It then constructs product nets whose input precision
is divided by those bounds, using the exact product-error theorem. The proof
allows different input presentations to compute different bounds and schedules.
Equivalent input limits are proved to give equivalent product limits.

`ConstructiveRealMultiplication` consequently defines multiplication of general
real presentations. It proves presentation congruence, commutativity, zero and
unit laws, agreement with exact signed-rational multiplication, and certified
bounds around the computed rational product approximants. The regressions
compute a negative product enclosure, change unreduced input presentations,
and exercise the generic laws, including multiplication of `log₂(3)` by one.

### Real ring laws, ordered products and effective real limits

`ConstructiveRealAssociativity`, `ConstructiveRealAdditionLimits` and
`ConstructiveRealDistributivity` compare different approximation schedules
and prove general associativity, completion of sums and both distributive
laws. `ConstructiveRealRing` supplies signed products, subtraction, natural
powers and finite-sum identities. These are equalities of values, not an
assumption of decidable equality of real presentations.

`ConstructiveRealCauchy` computes limits of real-valued sequences from a
supplied executable Cauchy modulus and proved tail estimates. Moduli need not
be monotone. Tail error, uniqueness, presentation invariance, constants, sums
and agreement with rational completion are proved. `ConstructiveRealCauchyOrder`
and `ConstructiveRealCauchyStability` pass closed order, intervals and supplied
errors through those effective limits.

`ConstructiveRealOrderedRing` proves nonnegative products, multiplication of
closed inequalities and nonnegative squares without deciding real signs.
`ConstructiveRealStability` gives explicit product perturbation estimates.
`ConstructiveRealProductLimits` constructs pointwise products and powers of
effective real sequences and proves the corresponding limit identities.
`ConstructiveRealRationalScaling` relates rational scaling to ordinary real
multiplication; `EntropyRealProducts` uses it for the existing rational-mass
Shannon/KL summands, retaining zero-mass and positive-reference qualifications.

### Positive reciprocals and real logarithms

`ConstructiveRealReciprocal` takes an explicit positive rational lower bound
on a real value. It constructs a reciprocal, proves its inverse and congruence
laws, and never decides arbitrary real equality with zero. That supplied bound
is computational input, not an assumption that every real has a chosen sign.

`ConstructiveRealLogarithm` similarly constructs `positiveLog2` from certified
positive rational approximations and their effective limit. It proves tail
error, rational agreement and independence of both presentation and positive
lower-bound witness. `ConstructiveRealLogContinuity` supplies an explicit
uniform modulus on a given positive half-line. `ConstructiveRealLogOrder`
proves monotonicity, the value at one, and the appropriate nonnegative or
nonpositive conclusion when the argument is respectively above or below one.

`ConstructiveRealLogLimits` transports the logarithm through effective limits
on a supplied positive half-line. `ConstructiveRealLogMultiplication` proves
the general positive-real product law, deriving the product's lower bound from
its two inputs. `ConstructiveRealLogReciprocal` computes a lower bound for the
constructed reciprocal and proves logarithm inverse and quotient laws, rather
than leaving their domain certificates as extra unexplained premises.

### Certified rational series and exponentials

`RationalGeometricSeries` constructs effective limits of signed rational series
with supplied bounds `|term n| ≤ C / 2ⁿ`, including `C = 0`, and proves the
explicit remainder bound `2C / 2ⁿ` at every truncation.
`RationalTaylorExponential` computes `xⁿ/n!` by recurrence. For a supplied
rational input satisfying `|x| ≤ 1/2`, it constructs `expSmall`, proves
presentation congruence and the value at zero, and certifies its remainder.
Regressions compute enclosures for positive and negative half-arguments.

`RationalSeriesTail` extends the construction to a finite prefix followed by a
dyadically bounded tail. It proves remainder estimates after that prefix and
limit congruence for rational sequences even when their Cauchy moduli differ.
`RationalNaturalBound` computes a positive natural bound from the represented
rational quotient, avoiding a bound determined only by an unreduced numerator.
`RationalExponential` uses these results to construct the Taylor exponential
for every signed rational argument. It computes a finite prefix after which
absolute coefficients shrink by at least one half, supplies an effective Cauchy
modulus, proves the remainder bound at each later truncation, and establishes
presentation invariance, agreement with `expSmall`, and the value at zero.
Regressions compute enclosures at `1`, `−1` and `2` and preserve large unreduced
presentations.

General real arguments, exponential addition/inverse identities, the connection
to the bit logarithm and differentiation remain separate proof obligations.

These newer results were combined from published auxiliary-value work through
`8b1f99b`, `ca8d9cb`, `22fd3b9` and `dec7a44`, not proved by the maintenance refactor. The updated
guide through `8b1f99b` is preserved in [history](HISTORY.md#archived-entropy-8b1f99b).
General real exponentials, differentiation, constrained-optimizer convergence and the
physical activities are not supplied by these interfaces. Probability atom
weights remain finite and rational throughout.

<a id="research-boundaries"></a>

## Unresolved research boundaries

The core graphical soundness/completeness results above are implemented with
their explicit model-class and support qualifications. The following stronger
questions are separate research, not missing premises to assume:

- Universal coverage across every alternative formula's application domain.
  Bounded proof/catalogue selection is implemented, but increasing budgets has
  no proved universal stopping criterion. The common-kernel substitution
  obstruction refutes one shortcut, not every finite-key strategy.
- Exact arbitrary-graph identification at one fixed observed distribution.
  Binary bow/IV and explicitly bounded native classes have their stated
  complete results; unrestricted rational polynomial feasibility remains a
  separate obligation. Structural finiteness does not make rational parameters
  finite, and real feasibility is not automatically rational feasibility.
- A full analytic feasible-polytope/optimizer and physical interpretation.
  Existing auxiliary real-value results are retained, but their partial
  development does not silently supply the remaining density, calculus,
  multiplier or thermodynamic theorems.
- Unrestricted multiworld counterfactual completeness. Existing semantics,
  identities and explicitly parameterized interfaces are not an inhabited
  general multiworld identification package.

The complete earlier bounded assessments, unsuccessful stopping arguments and
literature notes are preserved in [HISTORY.md](HISTORY.md#archived-theorem-coverage).
Do not launch an open-ended solver or enlarge theorem claims as maintenance.
