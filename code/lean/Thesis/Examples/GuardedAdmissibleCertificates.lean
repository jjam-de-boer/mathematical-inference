import Thesis.CausalTransport.GuardedAdmissibleCertificates
import Thesis.Examples.GuardedConditionalCompilation
import Thesis.Examples.ConditionalPromotionSupport

namespace Thesis
namespace Causality
namespace Examples
namespace GuardedAdmissibleCertificateRegression

open Probability

/-!
# Check the explicit admissibility boundary, not a positive-model shortcut

The joint and conditional certificates below use the actual successful
programs in the original zero-containing hidden-DAG record.  Only observable
action overlap, primitive used-conditional tests and the original native
conditioner's positivity are supplied.  No fixture-specific compiler data,
support subtree or semantic equation is supplied to a certificate.

The used-conditional tests are read from already checked finite printed
results via their proved necessity direction, not from causal soundness.
Both certificates interpret supported-zero outcomes outside the globally
positive model class.  The null-factual-action promotion fixture is deliberately
excluded by the paper's separate action-admissibility boundary, even though
the stronger intrinsic soundness theorem can interpret its defined endpoints.

The small generic syntax checks also distinguish a skipped undefined quotient
from the same quotient demanded by a strict product.  Thus the admissibility
predicate does not impose every factor's conditioner at a zero guard.
-/

/-- Inspect the already computed partial result rather than select a value
from existence.  This helper converts a finite supported-zero check directly
into the primitive native used-conditional predicate. -/
private theorem usedConditionalsOfNumeratorZero {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}
    (model : FiniteHiddenDAGSCM S P) (term : ProbabilityTerm S) (reference : S.Assignment)
    (zero : (model.termDenote term reference).map (fun value => value.num) = some 0) :
    model.UsedConditionalsAdmissibleAt term reference := by
  cases result : model.termDenote term reference with
  | none =>
      rw [result] at zero
      cases zero
  | some value =>
      apply (model.usedConditionalsAdmissibleAt_iff_supported term reference).mpr
      exact ⟨value, by rw [result]; exact .value (QProb.equiv_refl value)⟩

/-- With no observed external action parents, one positive action cell
supplies the uniform supported-parent test.  The proved native/root test
preservation keeps the construction in the actual original DAG. -/
private theorem actionAdmissibleOfNoParents {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}
    (model : FiniteHiddenDAGSCM S P) (action : NodeSet S) (reference : S.Assignment)
    (noParents : S.actionParents action = NodeSet.empty)
    (pointwise : model.ObservationalActionAdmissibleAt action reference) :
    model.ObservationalActionAdmissibleOnParentSupport action reference :=
  (model.observationalActionAdmissibleOnParentSupport_iff_collapsed action reference).mpr
    (Thesis.Causality.ObservationalActionAdmissibleOnParentSupport.of_noParents noParents
      ((model.observationalActionAdmissibleAt_iff_collapsed action reference).mp pointwise))

private theorem joint_action_admissible :
    GuardedKernelZeroRegression.model.ObservationalActionAdmissibleOnParentSupport
      GuardedKernelZeroRegression.query.action GuardedKernelZeroRegression.reference := by
  apply actionAdmissibleOfNoParents
  · exact (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)
  · unfold FiniteHiddenDAGSCM.ObservationalActionAdmissibleAt
    decide +kernel

/-- An inhabited joint certificate for the literal multi-component output,
with the zero-containing application justified by primitive tests. -/
noncomputable def joint_certificate := identifyGuardedJointKernel_admissibleCertificate
  GuardedKernelZeroRegression.query GuardedKernelZeroRegression.guarded_identified

noncomputable def joint_sound : GuardedKernelZeroRegression.model.TermEquivalentAt
    GuardedKernelZeroRegression.query.sourceTerm joint_certificate.formula GuardedKernelZeroRegression.reference :=
  joint_certificate.soundAt GuardedKernelZeroRegression.model GuardedKernelZeroRegression.reference joint_action_admissible
    (usedConditionalsOfNumeratorZero _ _ _ GuardedKernelZeroRegression.guarded_value_is_supported_zero)

private theorem conditional_action_admissible :
    GuardedKernelZeroRegression.model.ObservationalActionAdmissibleOnParentSupport
      GuardedConditionalZeroRegression.query.action GuardedKernelZeroRegression.reference := by
  apply actionAdmissibleOfNoParents
  · exact (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)
  · unfold FiniteHiddenDAGSCM.ObservationalActionAdmissibleAt
    decide +kernel

private theorem conditional_source_admissible : GuardedKernelZeroRegression.model.ConditioningAdmissibleAt
    GuardedConditionalZeroRegression.query.operationKernel GuardedKernelZeroRegression.reference := by
  unfold FiniteHiddenDAGSCM.ConditioningAdmissibleAt
  decide +kernel

/-- The actual terminal Bayes certificate has a zero outcome numerator and
a positive native conditioner.  Its full recursive tree is built internally. -/
noncomputable def conditional_certificate := identifyGuardedConditionalKernel_admissibleCertificate
  GuardedConditionalZeroRegression.query GuardedConditionalZeroRegression.identified

noncomputable def conditional_sound : GuardedKernelZeroRegression.model.TermEquivalentAt
    GuardedConditionalZeroRegression.query.sourceTerm conditional_certificate.formula GuardedKernelZeroRegression.reference :=
  conditional_certificate.soundAt GuardedKernelZeroRegression.model GuardedKernelZeroRegression.reference
    conditional_action_admissible conditional_source_admissible
    (usedConditionalsOfNumeratorZero _ _ _ GuardedConditionalZeroRegression.formula_supported_zero)

/-- Both applications really lie outside the old positive-model class. -/
theorem model_is_not_globally_positive : ¬ GuardedKernelZeroRegression.model.ObservationallyPositive :=
  GuardedConditionalZeroRegression.model_not_observationally_positive

/-- Intrinsic conditional soundness can exceed the paper's action boundary.
The null-action promotion fixture does not accidentally satisfy uniform action
overlap merely because its original causal conditioner is meaningful. -/
theorem null_factual_action_not_admissible : ¬
    NullActionPromotionSupport.model.ObservationalActionAdmissibleOnParentSupport
      NullActionPromotionSupport.query.action GuardedKernelZeroRegression.reference := by
  intro admissible
  have pointwise := admissible GuardedKernelZeroRegression.reference (by decide +kernel) (by decide +kernel)
  change 0 < (NullActionPromotionSupport.model.observationalDist.probVal
    (Kernel.agreesOn (NodeSet.union NullActionPromotionSupport.query.action
      (GuardedKernelZeroRegression.signature.actionParents NullActionPromotionSupport.query.action))
      GuardedKernelZeroRegression.reference)).num at pointwise
  have zero : (NullActionPromotionSupport.model.observationalDist.probVal
    (Kernel.agreesOn (NodeSet.union NullActionPromotionSupport.query.action
      (GuardedKernelZeroRegression.signature.actionParents NullActionPromotionSupport.query.action))
      GuardedKernelZeroRegression.reference)).num = 0 := by decide +kernel
  rw [zero] at pointwise
  exact Nat.not_lt_zero _ pointwise

section SyntaxBoundary

variable {S : ObservedSignature.{0}} (model : ExactModel S) (reference : S.Assignment)

private def nullQuotient : ProbabilityTerm S := .divide .zero .zero

/-- A null quotient that is actually demanded fails its primitive denominator
test.  A zero numerator is not used to complete `0/0`. -/
theorem null_quotient_not_admissible : ¬ (nullQuotient : ProbabilityTerm S).UsedConditionalsAdmissibleAt model reference := by
  intro admissible
  have positive := admissible.2.2
  cases positive

/-- A defined zero guard skips that same missing quotient, exactly as the
paper's positive-event restriction permits unused null branches to be skipped. -/
theorem zero_guard_skips_null_quotient :
    (ProbabilityTerm.weightedMultiply .zero nullQuotient).UsedConditionalsAdmissibleAt model reference := by
  constructor
  · trivial
  · intro positive
    cases positive

/-- Ordinary multiplication remains strict.  These support qualifications do
not make the old unguarded product admissible by silently absorbing `0/0`. -/
theorem strict_zero_product_not_admissible : ¬
    (ProbabilityTerm.multiply .zero nullQuotient).UsedConditionalsAdmissibleAt model reference := by
  intro admissible
  exact null_quotient_not_admissible model reference admissible.2

end SyntaxBoundary

end GuardedAdmissibleCertificateRegression
end Examples
end Causality
end Thesis
