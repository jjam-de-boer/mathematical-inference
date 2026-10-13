import Thesis.CausalTransport.HiddenDAGSupportedCorrespondence
import Thesis.Examples.HiddenDAGAdmissibleCompleteness
import Thesis.Examples.GuardedAdmissibleCertificates
import Thesis.Examples.AdmissibleFrontDoorBoundary

namespace Thesis
namespace Causality
namespace Examples
namespace NativeSupportedCorrespondenceRegression

open Probability

/-!
# Supported-zero correspondence and completeness regressions

The observational examples first supply independently written finite
representations, before calling the new completeness package.  Their
semantic premises mention no engine result or graph derivation.  Completeness
must recover the actual guarded outputs, not those independently supplied
candidate expressions.  A genuinely recursive intervention example also
passes through the new package and retains its exact multi-component formula.
The returned certificates are applied in the existing zero-containing native
record from primitive tests, without caller-filled compiler Data.

Failure and hedge examples reuse actual positive original-DAG pairs, which
are admitted by every positive-covered candidate domain.  The syntax
boundary checks allow a literal zero and a skipped `0/0` while rejecting a
demanded `0/0`; positive coverage is not a disguised `ZeroFree` restriction.

Finally the deterministic-mediator graph is supported-identifiable at the
query level, but its exhibited crossed-cell reference is excluded by the
returned formula's primitive demand tests.  This checks that the supported
theorem does not assert the already refuted primitive-domain reverse claim.
-/

section SuccessfulQueries

open GuardedKernelZeroRegression (signature projection model reference)

noncomputable def published : PublishedSupportedAdmissibleCompleteness projection :=
  projection.publishedSupportedAdmissibleCompleteness NativeAdmissibleCompletenessRegression.rich

/-- An independent observational joint representation computes its own
query.  Positive coverage is obtained from the primitive kernel syntax,
not from the engine's formula or a denotational soundness theorem. -/
theorem observational_joint_identifiable : HiddenDAGSupportedDomain.jointIdentifiable
    projection GuardedConditionalZeroRegression.query.jointNumerator := by
  refine ⟨GuardedConditionalZeroRegression.query.jointNumerator.sourceTerm, (fun _ => rfl),
    HiddenDAGSupportedDomain.positiveCovered_of_zeroFree _ trivial, ?_⟩
  intro native assignment _admissible
  exact ⟨ProbabilityResult.refl (native.termDenote GuardedConditionalZeroRegression.query.jointNumerator.sourceTerm assignment)⟩

/-- The independently specified observational conditional has the same
representation property on its meaningful original-source domain. -/
theorem observational_conditional_identifiable : HiddenDAGSupportedDomain.conditionalIdentifiable
    projection GuardedConditionalZeroRegression.query := by
  refine ⟨GuardedConditionalZeroRegression.query.sourceTerm, (fun _ => rfl),
    HiddenDAGSupportedDomain.positiveCovered_of_zeroFree _ trivial, ?_⟩
  intro native assignment _admissible
  exact ⟨ProbabilityResult.refl (native.termDenote GuardedConditionalZeroRegression.query.sourceTerm assignment)⟩

noncomputable def observationalJointCertificate := published.joint_complete
  GuardedConditionalZeroRegression.query.jointNumerator observational_joint_identifiable

noncomputable def conditionalCertificate := published.conditional_complete
  GuardedConditionalZeroRegression.query observational_conditional_identifiable

/-- The program's literal output is recovered even though the semantic
candidate was a different observational kernel expression. -/
theorem observational_joint_formula : observationalJointCertificate.formula = GuardedConditionalZeroRegression.numeratorFormula :=
  IdentificationOutcome.identified.inj
    (observationalJointCertificate.result.symm.trans GuardedConditionalZeroRegression.numerator_identified)

theorem conditional_formula : conditionalCertificate.formula = GuardedConditionalZeroRegression.formula :=
  IdentificationOutcome.identified.inj
    (conditionalCertificate.result.symm.trans GuardedConditionalZeroRegression.identified)

/-- The actual recursive joint certificate also inhabits the independent
representation predicate.  Its native validity ranges over all admissible
records, not only the earlier concrete supported-zero fixture. -/
theorem recursive_joint_identifiable : HiddenDAGSupportedDomain.jointIdentifiable projection GuardedKernelZeroRegression.query :=
  GuardedAdmissibleCertificateRegression.joint_certificate.supported_identifiable

noncomputable def recursiveJointCertificate := published.joint_complete
  GuardedKernelZeroRegression.query recursive_joint_identifiable

theorem recursive_joint_formula : recursiveJointCertificate.formula = GuardedKernelZeroRegression.guardedFormula :=
  IdentificationOutcome.identified.inj
    (recursiveJointCertificate.result.symm.trans GuardedKernelZeroRegression.guarded_identified)

private theorem conditional_source_admissible : model.ConditioningAdmissibleAt
    GuardedConditionalZeroRegression.query.operationKernel reference := by
  unfold FiniteHiddenDAGSCM.ConditioningAdmissibleAt
  decide +kernel

/-- Read a displayed supported-zero result directly into its primitive
used-conditional tests.  The `some` branch retains its own rational value;
no witness is selected from propositional existence. -/
private theorem usedConditionalsOfNumeratorZero (nativeModel : FiniteHiddenDAGSCM signature projection)
    (term : ProbabilityTerm signature)
    (zero : (nativeModel.termDenote term reference).map (fun value => value.num) = some 0) :
    nativeModel.UsedConditionalsAdmissibleAt term reference := by
  cases result : nativeModel.termDenote term reference with
  | none =>
      rw [result] at zero
      cases zero
  | some value =>
      apply (nativeModel.usedConditionalsAdmissibleAt_iff_supported term reference).mpr
      exact ⟨value, by rw [result]; exact .value (QProb.equiv_refl value)⟩

/-- Apply the new completeness output's own support constructor in a
nonpositive native model at the literal recursive multi-component formula. -/
noncomputable def recursive_joint_native_sound : model.TermEquivalentAt
    GuardedKernelZeroRegression.query.sourceTerm recursiveJointCertificate.formula reference := by
  apply recursiveJointCertificate.intrinsic_soundAt model reference
  rw [recursive_joint_formula]
  exact usedConditionalsOfNumeratorZero model _ GuardedKernelZeroRegression.guarded_value_is_supported_zero

/-- The new conditional field likewise constructs the full native tree for
the actual Bayes expression from its primitive source and printed tests. -/
noncomputable def conditional_native_sound : model.TermEquivalentAt
    GuardedConditionalZeroRegression.query.sourceTerm conditionalCertificate.formula reference := by
  apply conditionalCertificate.intrinsic_soundAt model reference conditional_source_admissible
  rw [conditional_formula]
  exact usedConditionalsOfNumeratorZero model _ GuardedConditionalZeroRegression.formula_supported_zero

theorem model_is_not_globally_positive : ¬ model.ObservationallyPositive :=
  GuardedConditionalZeroRegression.model_not_observationally_positive

end SuccessfulQueries

section NullActionGenerality

open GuardedKernelZeroRegression (signature projection reference)
open NullActionPromotionSupport (model query formula identified)

/-- The same inhabited completeness package covers the actual successful
conditional promotion at a null factual action.  Its intrinsic application
domain is broader than the separate action restriction in the papers. -/
noncomputable def promotionCertificate := published.conditional_complete query
  (identifyGuardedConditionalKernel_admissibleCertificate query identified).supported_identifiable

theorem promotion_certificate_formula : promotionCertificate.formula = formula :=
  IdentificationOutcome.identified.inj (promotionCertificate.result.symm.trans identified)

/-- Only actual causal source positivity and the printed primitive demand
tests are supplied.  Factual action overlap is unavailable here and is not
smuggled into a compiler-data or support-tree argument. -/
theorem promotion_reference_is_intrinsically_admissible :
    HiddenDAGSupportedDomain.ConditionalAdmissibleAt model query promotionCertificate.formula reference := by
  constructor
  · exact (model.conditioningAdmissibleAt_iff_supported query.operationKernel reference).mpr
      ⟨NullActionPromotionSupport.original_supported⟩
  · rw [promotion_certificate_formula]
    exact usedConditionalsOfNumeratorZero model _ NullActionPromotionSupport.formula_supported_zero

theorem promotion_factual_action_is_null :
    (model.observationalDist.probVal (Kernel.agreesOn query.action reference)).num = 0 :=
  NullActionPromotionSupport.observational_action_is_null

/-- This application really exceeds the published factual-action boundary,
not just a differently named positive-model wrapper. -/
theorem promotion_reference_outside_published_domain : ¬
    (HiddenDAGAdmissibleDomain.ConditionalAdmissibleAt model query reference ∧
      model.UsedConditionalsAdmissibleAt promotionCertificate.formula reference) :=
  fun application => GuardedAdmissibleCertificateRegression.null_factual_action_not_admissible application.1.1

/-- The new completeness output's own native support constructor interprets
its exact promoted formula despite the null observed action. -/
noncomputable def promotion_intrinsic_native_sound : model.TermEquivalentAt
    query.sourceTerm promotionCertificate.formula reference :=
  promotionCertificate.intrinsic_soundAt model reference
    promotion_reference_is_intrinsically_admissible.1 promotion_reference_is_intrinsically_admissible.2

end NullActionGenerality

section FailedQueries

open HiddenDAGCollapse (projection)
open HiddenDAGCompleteness (failedJointQuery failedConditionalQuery jointFailure conditionalFailure)

noncomputable def jointCounterexample := identifyGuardedJointKernel_supported_failed_counterexample HiddenDAGCompleteness.rich failedJointQuery
  ((identifyGuardedJointKernel_failed_iff projection.observedGraph failedJointQuery jointFailure.val).mpr jointFailure.property)

noncomputable def conditionalCounterexample := identifyGuardedConditionalKernel_supported_failed_counterexample HiddenDAGCompleteness.rich failedConditionalQuery
  ((identifyGuardedConditionalKernel_failed_iff projection.observedGraph failedConditionalQuery conditionalFailure.val).mpr conditionalFailure.property)

/-- Existing native failure pairs refute the independent existence of any
positive-covered observational representation, not just one guessed AST. -/
theorem failed_joint_not_supported_identifiable : ¬ HiddenDAGSupportedDomain.jointIdentifiable projection failedJointQuery :=
  jointCounterexample.not_supported_identifiable

theorem failed_conditional_not_supported_identifiable : ¬ HiddenDAGSupportedDomain.conditionalIdentifiable projection failedConditionalQuery :=
  conditionalCounterexample.not_supported_identifiable

noncomputable def hedgeCounterexample :=
  (projection.publishedSupportedAdmissibleCompleteness HiddenDAGCompleteness.rich).hedge_counterexample failedJointQuery
    (identifyJointKernelFailedHedge failedJointQuery jointFailure.property).witness

/-- Every candidate domain with the explicit non-vacuity coverage admits
the actual hedge pair at every reference, including its causal action test. -/
theorem hedge_left_admitted_every_candidate (term : ProbabilityTerm HiddenDAGCollapse.signature)
    (covered : HiddenDAGSupportedDomain.PositiveCovered projection term) (assignment : HiddenDAGCollapse.signature.Assignment) :
    HiddenDAGSupportedDomain.JointAdmissibleAt hedgeCounterexample.left failedJointQuery term assignment :=
  hedgeCounterexample.supported_left_admissible term covered assignment

theorem conditional_right_admitted_every_candidate (term : ProbabilityTerm HiddenDAGCollapse.signature)
    (covered : HiddenDAGSupportedDomain.PositiveCovered projection term) (assignment : HiddenDAGCollapse.signature.Assignment) :
    HiddenDAGSupportedDomain.ConditionalAdmissibleAt conditionalCounterexample.right failedConditionalQuery term assignment :=
  conditionalCounterexample.supported_right_admissible term covered assignment

end FailedQueries

section SyntaxBoundary

open HiddenDAGCollapse (signature projection)

private def nullQuotient : ProbabilityTerm signature := .divide .zero .zero

/-- Unlike a syntactic ZeroFree restriction, the final semantic domain
permits a genuine literal zero expression. -/
theorem literal_zero_is_covered : HiddenDAGSupportedDomain.PositiveCovered projection (ProbabilityTerm.zero : ProbabilityTerm signature) :=
  HiddenDAGSupportedDomain.positiveCovered_zero

/-- A zero guard has no demand for the invalid factor, even in positive
records.  This zero-containing syntax is a valid positive-covered candidate. -/
theorem skipped_null_quotient_is_covered : HiddenDAGSupportedDomain.PositiveCovered projection
    (ProbabilityTerm.weightedMultiply .zero nullQuotient) := by
  intro _native _positive _assignment
  constructor
  · trivial
  · intro demanded
    cases demanded

/-- An actually demanded null quotient is not an admissibility domain that
may discard all positive countermodels and claim identification vacuously. -/
theorem demanded_null_quotient_not_covered : ¬ HiddenDAGSupportedDomain.PositiveCovered projection nullQuotient := by
  intro covered
  have used := covered HiddenDAGIdentification.positiveModel HiddenDAGIdentification.positiveModel_positive (fun _ => true)
  have impossible := used.2.2
  cases impossible

theorem strict_null_product_not_covered : ¬ HiddenDAGSupportedDomain.PositiveCovered projection
    (ProbabilityTerm.multiply .zero nullQuotient) := by
  intro covered
  have used := covered HiddenDAGIdentification.positiveModel HiddenDAGIdentification.positiveModel_positive (fun _ => true)
  have impossible := used.2.2.2
  cases impossible

end SyntaxBoundary

/-- Supported query-level identification and primitive-domain failure can
coexist: the returned formula's crossed-cell application is inadmissible.
This does not falsely strengthen the supported theorem to action-only cells. -/
theorem frontdoor_supported_identifiable : HiddenDAGSupportedDomain.jointIdentifiable
    GuardedKernelZeroRegression.projection GuardedKernelZeroRegression.query :=
  GuardedAdmissibleCertificateRegression.joint_certificate.supported_identifiable

theorem frontdoor_reference_excluded : ¬ HiddenDAGSupportedDomain.JointAdmissibleAt
    AdmissibleFrontDoorBoundary.constantModel GuardedKernelZeroRegression.query
    GuardedKernelZeroRegression.guardedFormula AdmissibleFrontDoorBoundary.reference :=
  AdmissibleFrontDoorBoundary.used_conditionals_not_admissible

end NativeSupportedCorrespondenceRegression
end Examples
end Causality
end Thesis
