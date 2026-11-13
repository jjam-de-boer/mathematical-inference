import Thesis.CausalTransport.HiddenDAGAdmissibleCompleteness
import Thesis.Examples.GuardedConditionalCompilation
import Thesis.Examples.HiddenDAGCompleteness

namespace Thesis
namespace Causality
namespace Examples
namespace NativeAdmissibleCompletenessRegression

open Probability

/-!
# Exercise the inhabited primitive-admissible completeness package

The successful queries are genuinely observational in the existing native
zero-containing mediator graph.  Their semantic identification premise is
proved directly by observational invariance, before invoking completeness;
neither an engine success equation nor a printed-support assumption is used
to establish that premise.  The returned certificates must then retain the
literal guarded joint and conditional formulas.  Primitive tests apply both
certificates to the zero-containing native model, not a positive substitute.

The failed queries reuse the noncanonical five-node original hidden DAG.
Only the previously checked small graph search is used; all native
countermodel records, action overlap, original conditioner positivity and
query separation come from the general constructive theorems.  Their
admissibility is checked at every reference, without enumerating the
potentially large realized hidden alphabets or choosing a separating cell.

All three completeness fields are exercised.  These regressions do not
assert that primitive external query tests alone define every possible
printed formula or prove a whole-domain success equivalence.
-/

section SuccessfulQueries

open GuardedKernelZeroRegression (signature projection model reference)

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => false
  second := fun _ => true
  first_enumerated := by intro _; change false ∈ [false, true]; decide +kernel
  second_enumerated := by intro _; change true ∈ [false, true]; decide +kernel
  different := fun _ => Bool.false_ne_true

noncomputable def published : PrimitiveAdmissibleCompleteness projection :=
  projection.primitiveAdmissibleCompleteness rich

/-- This premise quantifies over all original native records, including
zeros.  The source has no action and therefore depends only on the common
observed law, whether or not a particular marginal outcome has positive mass. -/
theorem joint_identifiable : HiddenDAGAdmissibleDomain.jointIdentifiable
    projection GuardedConditionalZeroRegression.query.jointNumerator := by
  intro left right observational assignment _leftAdmissible _rightAdmissible
  exact ⟨FiniteHiddenDAGSCM.actionFree_invariant left right observational
    GuardedConditionalZeroRegression.query.jointNumerator.sourceTerm (fun _ => rfl) assignment⟩

/-- The original observational conditional is invariant on its admissible
domain.  Both native conditioners are retained; no causal support transfer
is inferred from the observational equality used for the value comparison. -/
theorem conditional_identifiable : HiddenDAGAdmissibleDomain.conditionalIdentifiable
    projection GuardedConditionalZeroRegression.query := by
  intro left right observational assignment _leftAdmissible _rightAdmissible
  exact ⟨FiniteHiddenDAGSCM.actionFree_invariant left right observational
    GuardedConditionalZeroRegression.query.sourceTerm (fun _ => rfl) assignment⟩

noncomputable def jointCertificate := published.joint_complete
  GuardedConditionalZeroRegression.query.jointNumerator joint_identifiable

noncomputable def conditionalCertificate := published.conditional_complete
  GuardedConditionalZeroRegression.query conditional_identifiable

/-- Completeness reads the actual program's output.  It does not replace
the generated expression by an observational kernel with the same value. -/
theorem joint_certificate_formula : jointCertificate.formula = GuardedConditionalZeroRegression.numeratorFormula :=
  IdentificationOutcome.identified.inj
    (jointCertificate.result.symm.trans GuardedConditionalZeroRegression.numerator_identified)

theorem conditional_certificate_formula : conditionalCertificate.formula = GuardedConditionalZeroRegression.formula :=
  IdentificationOutcome.identified.inj
    (conditionalCertificate.result.symm.trans GuardedConditionalZeroRegression.identified)

/-- At an empty action one positive displayed action cell supplies all
parent contexts.  Only small finite primitive tests are computed here; the
general no-parent theorem constructs the universal application witness. -/
private theorem action_admissible : model.ObservationalActionAdmissibleOnParentSupport
    GuardedConditionalZeroRegression.query.action reference := by
  apply (model.observationalActionAdmissibleOnParentSupport_iff_collapsed _ reference).mpr
  apply Thesis.Causality.ObservationalActionAdmissibleOnParentSupport.of_noParents
  · exact (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)
  · apply (model.observationalActionAdmissibleAt_iff_collapsed _ reference).mp
    unfold FiniteHiddenDAGSCM.ObservationalActionAdmissibleAt
    decide +kernel

private theorem source_admissible : model.ConditioningAdmissibleAt
    GuardedConditionalZeroRegression.query.operationKernel reference := by
  unfold FiniteHiddenDAGSCM.ConditioningAdmissibleAt
  decide +kernel

/-- Inspect a computed result directly to obtain its primitive demand tests.
No value is chosen from an existential, and no causal soundness theorem is
used to establish printed admissibility.  A zero numerator still has a value. -/
private theorem usedConditionalsOfNumeratorZero (term : ProbabilityTerm signature)
    (zero : (model.termDenote term reference).map (fun value => value.num) = some 0) :
    model.UsedConditionalsAdmissibleAt term reference := by
  cases result : model.termDenote term reference with
  | none =>
      rw [result] at zero
      cases zero
  | some value =>
      apply (model.usedConditionalsAdmissibleAt_iff_supported term reference).mpr
      exact ⟨value, by rw [result]; exact .value (QProb.equiv_refl value)⟩

/-- The actual joint certificate produced from semantic identification is
usable in the original zero-containing model without manually filling Data. -/
noncomputable def joint_native_sound : model.TermEquivalentAt
    GuardedConditionalZeroRegression.query.jointNumerator.sourceTerm jointCertificate.formula reference := by
  apply jointCertificate.soundAt model reference action_admissible
  rw [joint_certificate_formula]
  exact usedConditionalsOfNumeratorZero _ (by decide +kernel)

/-- The conditional completeness field likewise supplies the complete
native tree for the exact Bayes output, including its supported-zero outcome. -/
noncomputable def conditional_native_sound : model.TermEquivalentAt
    GuardedConditionalZeroRegression.query.sourceTerm conditionalCertificate.formula reference := by
  apply conditionalCertificate.soundAt model reference action_admissible source_admissible
  rw [conditional_certificate_formula]
  exact usedConditionalsOfNumeratorZero _ GuardedConditionalZeroRegression.formula_supported_zero

theorem model_is_not_globally_positive : ¬ model.ObservationallyPositive :=
  GuardedConditionalZeroRegression.model_not_observationally_positive

end SuccessfulQueries

section FailedQueries

open HiddenDAGCollapse (projection)
open HiddenDAGCompleteness (failedJointQuery failedConditionalQuery jointFailure conditionalFailure)

/-- Recover the guarded failure equation from the literal checked strict
engine failure.  No second search or truncation to a fixed recursion depth
is substituted for the proved engine-decision equivalence. -/
noncomputable def jointCounterexample := identifyGuardedJointKernel_admissible_failed_counterexample HiddenDAGCompleteness.rich failedJointQuery
  ((identifyGuardedJointKernel_failed_iff projection.observedGraph failedJointQuery jointFailure.val).mpr jointFailure.property)

noncomputable def conditionalCounterexample := identifyGuardedConditionalKernel_admissible_failed_counterexample HiddenDAGCompleteness.rich failedConditionalQuery
  ((identifyGuardedConditionalKernel_failed_iff projection.observedGraph failedConditionalQuery conditionalFailure.val).mpr conditionalFailure.property)

/-- Failure is genuine non-identification on the independently specified
primitive domain, not a failure occurring only at inadmissible action values. -/
theorem failed_joint_not_identifiable : ¬ HiddenDAGAdmissibleDomain.jointIdentifiable projection failedJointQuery :=
  jointCounterexample.not_identifiable

theorem failed_conditional_not_identifiable : ¬ HiddenDAGAdmissibleDomain.conditionalIdentifiable projection failedConditionalQuery :=
  conditionalCounterexample.not_identifiable

/-- The native failure pair is retained literally by admissibility transport;
only its independently proved application witnesses are added. -/
theorem joint_counterexample_keeps_left_record :
    jointCounterexample.left = HiddenDAGCompleteness.jointCounterexample.left := rfl

theorem conditional_counterexample_keeps_right_record :
    conditionalCounterexample.right = HiddenDAGCompleteness.conditionalCounterexample.right := rfl

/-- Exercise the package's actual hedge field on the unchanged original
query hedge.  Its native records satisfy action admissibility everywhere. -/
noncomputable def hedgeCounterexample : HiddenDAGAdmissibleJointCounterexample projection failedJointQuery :=
  (projection.primitiveAdmissibleCompleteness HiddenDAGCompleteness.rich).hedge_counterexample failedJointQuery
    (identifyJointKernelFailedHedge failedJointQuery jointFailure.property).witness

theorem hedge_left_admissible (assignment : HiddenDAGCollapse.signature.Assignment) :
    HiddenDAGAdmissibleDomain.JointAdmissibleAt hedgeCounterexample.left failedJointQuery assignment :=
  hedgeCounterexample.left_admissible assignment

theorem conditional_right_admissible (assignment : HiddenDAGCollapse.signature.Assignment) :
    HiddenDAGAdmissibleDomain.ConditionalAdmissibleAt conditionalCounterexample.right failedConditionalQuery assignment :=
  conditionalCounterexample.right_admissible assignment

end FailedQueries

end NativeAdmissibleCompletenessRegression
end Examples
end Causality
end Thesis
