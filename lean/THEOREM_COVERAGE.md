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

## Seven-point work-plan checkpoint

| Point | Current result | Next boundary |
| --- | --- | --- |
| 1. Safe local builds | Complete local Lean/native build and transitive axiom audit passed through the cache-aware sequential builder; measured caps and reusable ordinary artifacts are documented in `LOCAL_CHECKS.md`. | Use the guarded sequential route; success does not establish safety of unrestricted parallel cold builds or arbitrary external machine load. |
| 2. Shared graph infrastructure | Connectivity, reachability and rank infrastructure extracted without changing public theorem names; current-engine dependency guards pass. Resource-driven soundness/completeness splits retain the original declaration text. | Further splitting should address a measured bottleneck; it is not itself a mathematical repair or a guarantee of full local feasibility. |
| 3. Multivalued native example | Three declared observed values, an actual rational distribution, null intervention targets and supported conditionals checked through the native model. | The standalone-template regression now exercises the same boundary as well. |
| 4. Support-pattern applicability | Exact undefined/zero/positive analysis and exhaustive comparison within supplied finite formula catalogues; complete native causal support profiles also preserve recursive derivation support. | This does not enumerate every possible certified formula; observed support alone need not determine causal support. |
| 5. Universal alternative-formula coverage | Finite native support profiles, a serialized certificate checker, maximal proof-admissible guards, and exact bounded code enumeration with native acceptance-coverage theorems constructed. | Formula selection remains a separate stage; no universal stopping, unrestricted formula-coverage or impossibility theorem yet. |
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

### Research checkpoint 5: alternative-formula coverage

Universal formula coverage remains a bounded assessment, not an additional
formula-completeness theorem. The implemented support foundations are
recorded separately below.

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

### Approved support-foundation stages for goal 5

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

These two support stages did not themselves implement proof codes or a new
selector. After their verified publication and review, the separately approved
certificate-checker stage below adds proof codes and supplied guard-table
checking. Derivation enumeration and formula selection remain unimplemented.

### Approved serialized certificate-checker stage for goal 5

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

### Generated proof-admissible guards for goal 5

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

### Bounded code enumeration and native acceptance coverage for goal 5

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
catalogues are not concretely expanded. No formula is selected, and no
minimality, duplicate-free output or practical large-instance execution
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
has no proved stopping criterion for universal coverage. Formula selection
is the next separate implementation checkpoint.

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

### Research checkpoint 6: representation adapters

The compact source-alphabet step is now implemented by the product/native
presentation and compact-source theorems described above. They apply
`FiniteProbRecord.atomPresentation` to compressed factors, use their actual
independent product prior, and prove complete decoded-law equality through
`FiniteProduct.probVal_extensional_of_rectangles`. The decoder need not be a
bijection of the old ambient noise type. A common `Fin K` presentation can
still be added separately with zero-weight positions and an explicit decoded
default; the compact `Fin k_j` construction avoids that unnecessary padding.

For a fixed full DAG, `HiddenDAGReachableValues` and
`HiddenDAGValuePresentation` now implement the hidden-value coding and
simulation. Their bound is `I * product_j k_j`, hence at most `I * K^N`,
where `I = actions.length + 1` counts the included factual action. The existing
acyclic evaluator-uniqueness theorem proves simulation of the explicit
retained trajectories; observed values are converted two-sidedly rather than
restricted to positive support. Code-mechanism completeness, bounded-shape
catalogue membership, checked observed conversions and standalone native-law
coverage are implemented by the modules above. The assembled
`nativeTemplateRepresentation` constructs the final finite structural entry
and its source parameters for every original fixed-DAG model.

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
incidence masks for `n` observed nodes. Grouped-law independence, local
decoder/evaluator simulation and exact projected-root graph preservation are
now proved by the modules above. The remaining step realizes that grouped
model on the fixed full clique-root DAG, before invoking the existing native
compression and finite mechanism enumeration.
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
and the probability/evaluator grouping is now proved. Native-graph realization
and assembled coverage still need proofs. It retains multi-child causes rather than wrongly
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
is the rational foundation. The user selected the fixed-full-DAG route first;
source and hidden-value coding, finite structural enumeration and standalone
native-law coverage are now implemented. Following the bounded reassessment,
the user approved staged projection-wide implementation. The fixed clique
graph, independent block law, grouped causal root model, native realization
and assembled projection-wide model-class coverage are now constructed and
proved. The last step uses those actual bridges, rather than inferring
projection-wide coverage merely from fixed-DAG compression or root grouping.

### Bounded reassessment after fixed-full-DAG coverage

The bounded assessment below was reviewed and the user approved staged
implementation. Its graph, grouping, native-realization and projection-wide
coverage stages are now implemented as described above. The completed
fixed-DAG constructor supplies the final compression and enumeration step.
The reviewed order and the construction used at each boundary are:

1. **A fixed clique-root graph (implemented).** Enumerate the Boolean observed-child masks
   whose distinct members are pairwise bidirected-adjacent. Include singleton
   and empty masks. Construct one hidden root per listed mask, with its mask
   incidences and the signature's unchanged observed directed edges. Prove
   exact projection and a node bound of `n + 2^n`. Including all two-node edge
   masks recovers every required bidirected edge; larger clique masks add no
   forbidden edge. Graph compatibility permits an unused root's mechanism to
   be constant, so unused clique slots need not be deleted model-dependently.
2. **An independent-law grouping adapter (implemented).** Collapse an arbitrary original
   model using `toLatentRootSCM`, then assign each root to its exact child mask.
   Each such mask is a clique by projected-graph agreement. A grouped value can
   be a proof-indexed product `source -> owner source = mask -> Value source`.
   The existing `ProofFunction` enumeration/equality construction handles its
   absent coordinates without choosing values from unused alphabets. Construct
   the actual block factors and prove that decoding their independent product
   gives the whole old joint law, not only its one-source marginals. Finite
   product exchange and singleton/rectangle extensionality prove the complete
   disjoint-block law in `FiniteProductGrouping`.
3. **Multi-child native realization (implemented).** `LatentRootNativeModel`
   installs the actual blocks as hidden-root values/private sources, with
   vacuous observed-node noise. `LatentRootNativeEvaluation` proves equation
   simulation and all-hard-intervention event preservation. The older
   `HiddenDAGRootPlacement.sharedInput` data can describe arbitrary child
   families, but `hiddenDAGRootPlacements` and `toHiddenDAGSCM` currently require
   `Compatible`, which includes **at most two children per root**. They cannot
   be applied directly to the grouped multi-child model. The new constructor
   avoids that restricted API without weakening or disguising its premise.
4. **Representation coverage with the right quantifiers (implemented).**
   `ProjectedHiddenDAGModel` explicitly ranges over full original hidden DAGs
   with the same observed projection. `toCliqueRootSCM` preserves all their
   interventions on the fixed graph, which is itself a valid original graph
   in the class. Composing with `nativeTemplateRepresentation` yields a listed
   standalone template with structural bounds independent of the original
   hidden-node count and with the requested probabilities preserved.
5. **Regression and review.** Graph and grouping examples cover empty
   graphs/masks, unused slots and zero-weight cells. The projection-wide
   examples check an internal relay, a three-child shared cause, supported
   conditionals through retained joint/evidence queries, a multivalued law
   and intervention at a factual null value. Review the verified coverage
   checkpoint before adding substantial feasibility/search infrastructure.

The staged implementation closes this representation boundary, not the
unrestricted feasibility problem. Infinitely many rational weights remain,
and goal 5's formula-search termination question is independent. The approved
projection-wide stages do not authorize an open-ended feasibility/search
implementation afterward.

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

**Explicitly bounded models (unconditional and conditional targets).** The
finite weight-vector coverage proof, original-type native adapter, exact
observational filter and proof-carrying compatibility/uniqueness search are
implemented above. Source masses are aggregated without unit-cell expansion,
retaining repeated-label probabilities and the original denominator.
Enumerating bounded cardinality shapes avoids a separate zero-padding step.
The class fixes the full hidden DAG and bounds the original supplied finite
enumerations and source denominators. Source compression is not asserted to
preserve that denominator bound for arbitrary original models. Conditional
targets report evidence support separately from value agreement among the
positive-evidence members, including actual null-evidence witnesses when
present. Increasing `D` does not itself give a terminating unrestricted
procedure, and this implementation does not settle that separate question.

**Unrestricted rational models.** Representation bounds control alphabet and
table sizes, not the infinitely many rational source weights. The remaining
constraints can be polynomial rather than linear. [Duarte et al.](https://arxiv.org/html/2109.13471v1)
develop polynomial causal optimization with successively refined inner/outer
bounds and an epsilon-sharp stopping criterion. Those results do not by
themselves provide a terminating exact rational-only feasibility/uniqueness
checker in this library. In particular, real feasibility must not be silently
treated as rational feasibility.

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
memory-safe. See [LOCAL_CHECKS.md](LOCAL_CHECKS.md) for the capped pilot's actual
result and limitations. CI checks the exact pushed commit with targeted and
complete builds plus `Thesis.AxiomAudit`. The audit permits only `propext`
and `Quot.sound`, rejecting choice, general propositional excluded middle
dependencies, admitted proofs and untrusted Boolean proof reduction. A cached
artifact or a successful isolated leaf check is not that project-wide gate.
