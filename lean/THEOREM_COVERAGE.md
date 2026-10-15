# Causal theorem coverage and application boundaries

This guide separates graph-level identification from applying a formula at a
particular law, and both from fixed-law identification. The actual Lean
statements remain authoritative. All probabilities below are finite rational
records, with zero-weight cells permitted unless an explicit positivity
assumption says otherwise. Original hidden DAG results allow arbitrary finite
hidden and private-noise alphabet sizes; observed alphabets remain fixed.

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
independent-source model classes are convex. Polynomial certificates remain
a separate work item; there is no claimed
complete arbitrary-graph fixed-law optimizer.

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

These are constructed replacements, not external compression assumptions.
The bounds concern actual positive atom occurrences; the original ambient
noise types, node value types and structural mechanisms remain unchanged.
They do not themselves compress hidden endogenous alphabets, enumerate all
mechanisms, or supply a complete rational feasibility optimizer.

## Construction, execution, and proof verification

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
