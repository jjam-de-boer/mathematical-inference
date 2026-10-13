import Thesis.CausalTransport.GuardedPrintedSoundness
import Thesis.Examples.GuardedConditionalCompilation
import Thesis.Examples.ConditionalPromotionSupport
import Thesis.Examples.GuardedHiddenDAGZeroBoundary

namespace Thesis
namespace Causality
namespace Examples
namespace GuardedPrintedSoundnessRegression

open Probability

/-!
# Native guarded soundness without hand-populated recursive data

Reuse the already checked finite zero-containing records and literal engine
outputs.  A value with displayed numerator zero is still a genuine supported
value; inspecting its existing partial result supplies that endpoint witness.
The new uniform availability theorem, not fixture-specific component or
family data, constructs every intermediate support tree.

The joint fixture exercises a multi-component split, containing-component
restriction and ancestral pruning behind a zero prefix.  The first conditional
fixture exercises Bayes with a zero numerator and positive denominator.  The
second exercises conditioner promotion at a null factual action.  That last
case checks intrinsic conditional soundness, not the paper's separate
observational action-admissibility condition.

Finally the null-action counterexample remains excluded: an actually undefined
returned expression supplies no printed-support premise.  Neither the uniform
construction nor these regressions silently complete its null quotient.
-/

/-- Read the rational already present in a checked supported-zero result.
The `none` branch contradicts the supplied finite check; the `some` branch
returns its own value, without choice or a selected representative. -/
private noncomputable def supportedOfNumeratorZero (result : ProbabilityResult.Result)
    (zero : result.map (fun value => value.num) = some 0) : ProbabilityResult.Supported result := by
  cases result with
  | none => cases zero
  | some value => exact ⟨value, .value (QProb.equiv_refl value)⟩

/-- The real recursive joint program is interpreted from just its defined
printed value.  No local-data record or complete derivation tree is provided. -/
noncomputable def joint_native_sound :
    GuardedKernelZeroRegression.model.TermEquivalentAt GuardedKernelZeroRegression.query.sourceTerm
      GuardedKernelZeroRegression.guardedFormula GuardedKernelZeroRegression.reference :=
  identifyGuardedJointKernel_hiddenDAG_soundAt_of_printed_support
    GuardedKernelZeroRegression.query GuardedKernelZeroRegression.guarded_identified
    GuardedKernelZeroRegression.model GuardedKernelZeroRegression.reference
    (supportedOfNumeratorZero _ GuardedKernelZeroRegression.guarded_value_is_supported_zero)

/-- The generated Bayes quotient has supported zero numerator.  Only its
original and printed endpoints are supplied to the generic native theorem. -/
noncomputable def bayes_native_sound :
    GuardedKernelZeroRegression.model.TermEquivalentAt GuardedConditionalZeroRegression.query.sourceTerm
      GuardedConditionalZeroRegression.formula GuardedKernelZeroRegression.reference :=
  identifyGuardedConditionalKernel_hiddenDAG_soundAt_of_printed_support
    GuardedConditionalZeroRegression.query GuardedConditionalZeroRegression.identified
    GuardedKernelZeroRegression.model GuardedKernelZeroRegression.reference
    (supportedOfNumeratorZero _ GuardedConditionalZeroRegression.source_supported_zero)
    (supportedOfNumeratorZero _ GuardedConditionalZeroRegression.formula_supported_zero)

/-- Actual recursive promotion, pruning and component extraction at a null
factual action require no hand-written recursive boundary.  The original
conditioner's positive mass is retained explicitly by its support witness. -/
noncomputable def promotion_native_sound :
    NullActionPromotionSupport.model.TermEquivalentAt NullActionPromotionSupport.query.sourceTerm
      NullActionPromotionSupport.formula GuardedKernelZeroRegression.reference :=
  identifyGuardedConditionalKernel_hiddenDAG_soundAt_of_printed_support
    NullActionPromotionSupport.query NullActionPromotionSupport.identified
    NullActionPromotionSupport.model GuardedKernelZeroRegression.reference
    NullActionPromotionSupport.original_supported
    (supportedOfNumeratorZero _ NullActionPromotionSupport.formula_supported_zero)

/-- Structural success at an unsupported action remains outside the new
theorem's premise.  Its literal formula has no value, rather than an arbitrary
zero supplied to make the soundness adapter apply. -/
theorem null_action_has_no_printed_support : ¬ Nonempty
    (GuardedZeroClassBoundary.constantModel.TermSupportedAt GuardedZeroClassBoundary.formula
      GuardedZeroClassBoundary.reference) := by
  rintro ⟨supported⟩
  have missing : GuardedZeroClassBoundary.constantModel.termDenote GuardedZeroClassBoundary.formula
      GuardedZeroClassBoundary.reference = none := by
    have undefined := GuardedZeroClassBoundary.formula_is_undefined
    cases result : GuardedZeroClassBoundary.constantModel.termDenote GuardedZeroClassBoundary.formula
        GuardedZeroClassBoundary.reference with
    | none => rfl
    | some _value => simp only [result, Option.isNone_some, Bool.false_eq_true] at undefined
  have impossible := supported.2
  rw [missing] at impossible
  cases impossible

end GuardedPrintedSoundnessRegression
end Examples
end Causality
end Thesis
