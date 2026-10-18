import Thesis.CausalTransport.SupportedModal
import Thesis.Examples.HiddenDAGSupportedCorrespondence

namespace Thesis
namespace Causality
namespace Examples
namespace SupportedModalRegression

open Probability
open GuardedKernelZeroRegression (signature projection model query reference)

/-!
# Native zero-containing completeness through executed modal endpoints

The actual model has a common cause with three observed children and an
outcome that is constantly false.  It cannot be treated as a globally
positive substitute.  The joint query takes recursive multi-component ID;
the conditional query takes the supported Bayes branch of IDC.

Completeness constructs both literal formulas and their traces.  Only
primitive demand tests and the conditional source's positivity are supplied
to execution.  The action/observation transitions and atomic endpoint compute
the native causal zero.  A separate impossible-condition example rejects an
undefined source instead of conflating it with that supported zero.
-/

def mode : CausalMode signature := model.initialCausalMode "native/zero"

noncomputable def jointCertificate := mode.supportedJointModalCompleteness model rfl
  NativeAdmissibleCompletenessRegression.rich query
  NativeSupportedCorrespondenceRegression.recursive_joint_identifiable

noncomputable def conditionalCertificate := mode.supportedConditionalModalCompleteness model rfl
  NativeAdmissibleCompletenessRegression.rich GuardedConditionalZeroRegression.query
  NativeSupportedCorrespondenceRegression.observational_conditional_identifiable

theorem joint_formula : jointCertificate.encoded.certificate.formula = GuardedKernelZeroRegression.guardedFormula :=
  IdentificationOutcome.identified.inj
    (jointCertificate.encoded.certificate.result.symm.trans GuardedKernelZeroRegression.guarded_identified)

theorem conditional_formula : conditionalCertificate.encoded.certificate.formula = GuardedConditionalZeroRegression.formula :=
  IdentificationOutcome.identified.inj
    (conditionalCertificate.encoded.certificate.result.symm.trans GuardedConditionalZeroRegression.identified)

/-- Inspect the supplied computed result; no rational witness is selected
from a propositional existence statement and no null quotient is completed. -/
private def valueZero (result : ProbabilityResult.Result)
    (checked : result.map (fun value => value.num) = some 0) :
    ProbabilityResult.Equivalent result (some QProb.zero) := by
  cases result with
  | none => cases checked
  | some value =>
      change some value.num = some 0 at checked
      have numerator : value.num = 0 := Option.some.inj checked
      exact .value (by change value.num * 1 = 0 * value.den; rw [numerator]; rfl)

private theorem usedOfZero {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}
    (native : FiniteHiddenDAGSCM S P) (term : ProbabilityTerm S) (assignment : S.Assignment)
    (checked : (native.termDenote term assignment).map (fun value => value.num) = some 0) :
    native.UsedConditionalsAdmissibleAt term assignment :=
  (native.usedConditionalsAdmissibleAt_iff_supported term assignment).mpr
    ⟨⟨QProb.zero, valueZero _ checked⟩⟩

theorem joint_used : model.UsedConditionalsAdmissibleAt jointCertificate.encoded.certificate.formula reference := by
  rw [joint_formula]
  exact usedOfZero model _ reference GuardedKernelZeroRegression.guarded_value_is_supported_zero

theorem conditional_used : model.UsedConditionalsAdmissibleAt conditionalCertificate.encoded.certificate.formula reference := by
  rw [conditional_formula]
  exact usedOfZero model _ reference GuardedConditionalZeroRegression.formula_supported_zero

theorem conditional_source : model.ConditioningAdmissibleAt
    GuardedConditionalZeroRegression.query.operationKernel reference := by
  unfold FiniteHiddenDAGSCM.ConditioningAdmissibleAt
  decide +kernel

noncomputable def jointExecution := jointCertificate.realizeAt reference joint_used

noncomputable def conditionalExecution :=
  conditionalCertificate.realizeAt reference conditional_source conditional_used

/-- The indexed mode really stores the executed native model's collapse. -/
theorem execution_source_record :
    jointExecution.operation.actionTransition.source.record = mode.record := rfl

theorem joint_action_realizes : CausalTransition.Realizes
    jointExecution.operation.actionTransition (.intervene query.action) :=
  jointExecution.operation.actionTransition_realizes

theorem conditional_observation_realizes : CausalTransition.Realizes
    conditionalExecution.operation.observationTransition
      (.observe GuardedConditionalZeroRegression.query.condition) :=
  conditionalExecution.operation.observationTransition_realizes

private theorem joint_value_zero : QProb.Equiv jointExecution.operation.value QProb.zero := by
  have agreement := ProbabilityResult.trans
    (ProbabilityResult.symm jointExecution.nativeValue)
    (valueZero _ GuardedKernelZeroRegression.actual_effect_is_supported_zero)
  cases agreement with
  | value equivalent => exact equivalent

private theorem conditional_value_zero : QProb.Equiv conditionalExecution.operation.value QProb.zero := by
  have agreement := ProbabilityResult.trans
    (ProbabilityResult.symm conditionalExecution.nativeValue)
    (valueZero _ GuardedConditionalZeroRegression.source_supported_zero)
  cases agreement with
  | value equivalent => exact equivalent

/-- A defined zero is read from the executed record, not introduced as a
fallback for a missing formula value.  `formulaValue` separately retains the
native interpretation of the completeness-generated observational formula. -/
theorem joint_endpoint_zero : QProb.Equiv
    ((query.operationKernel.observedRecord model.toLatentRootSCM reference
      jointExecution.operation.conditionPositive).observedValue
      (query.operationKernel.outcomeEvent reference)) QProb.zero :=
  QProb.equiv_trans jointExecution.operation.operationValue joint_value_zero

theorem conditional_endpoint_zero : QProb.Equiv
    ((GuardedConditionalZeroRegression.query.operationKernel.observedRecord model.toLatentRootSCM reference
      conditionalExecution.operation.conditionPositive).observedValue
      (GuardedConditionalZeroRegression.query.operationKernel.outcomeEvent reference)) QProb.zero :=
  QProb.equiv_trans conditionalExecution.operation.operationValue conditional_value_zero

theorem atomic_joint_endpoint_zero : QProb.Equiv
    (QProb.div (query.operationKernel.atomicNumerator model.toLatentRootSCM reference)
      (query.operationKernel.atomicDenominator model.toLatentRootSCM reference)
      jointExecution.operation.atomicDenominator_positive) QProb.zero :=
  QProb.equiv_trans jointExecution.operation.atomicConditionedValue joint_value_zero

theorem native_formula_zero : ProbabilityResult.Equivalent
    (model.termDenote jointCertificate.encoded.certificate.formula reference) (some QProb.zero) :=
  ProbabilityResult.trans jointExecution.formulaValue (.value joint_value_zero)

theorem model_not_positive : ¬ model.ObservationallyPositive :=
  GuardedConditionalZeroRegression.model_not_observationally_positive

/-! ## Missing source support is not a zero-valued execution -/

def nullKernel : Kernel signature :=
  ⟨NodeSet.singleton GuardedKernelZeroRegression.z, NodeSet.empty,
    NodeSet.singleton GuardedKernelZeroRegression.y⟩

/-- The conditioner asks for the impossible value of the constant outcome. -/
theorem null_source_undefined : model.kernelDenote nullKernel reference = none := by
  decide +kernel

theorem null_source_not_admissible : ¬ model.ConditioningAdmissibleAt nullKernel reference := by
  decide +kernel

/-- Even if a syntactic derivation is supplied, an unsupported source cannot
inhabit the checked native modal execution payload. -/
theorem no_null_source_execution (formula : ProbabilityTerm signature)
    (derivation : DoCalculusDerivation projection.observedGraph (.kernel nullKernel) formula)
    (trace : ModalDerivationTrace projection.observedGraph derivation) :
    ¬ Nonempty (NativeModalKernelRealization model nullKernel formula reference derivation trace) := by
  rintro ⟨realized⟩
  exact realized.source_ne_none null_source_undefined

/-! ## Recursive IDC promotion without factual action overlap -/

namespace NullAction

def mode : CausalMode signature :=
  NullActionPromotionSupport.model.initialCausalMode "native/null-action"

/-- The completed supported-domain theorem supplies the promoted formula;
no factual action-overlap premise can be supplied in this fixture. -/
noncomputable def certificate := mode.supportedConditionalModalCompleteness
  NullActionPromotionSupport.model rfl NativeAdmissibleCompletenessRegression.rich
  NullActionPromotionSupport.query
  (identifyGuardedConditionalKernel_admissibleCertificate
    NullActionPromotionSupport.query NullActionPromotionSupport.identified).supported_identifiable

theorem formula : certificate.encoded.certificate.formula = NullActionPromotionSupport.formula :=
  IdentificationOutcome.identified.inj
    (certificate.encoded.certificate.result.symm.trans NullActionPromotionSupport.identified)

theorem source : NullActionPromotionSupport.model.ConditioningAdmissibleAt
    NullActionPromotionSupport.query.operationKernel reference :=
  (NullActionPromotionSupport.model.conditioningAdmissibleAt_iff_supported
    NullActionPromotionSupport.query.operationKernel reference).mpr
      ⟨NullActionPromotionSupport.original_supported⟩

theorem used : NullActionPromotionSupport.model.UsedConditionalsAdmissibleAt
    certificate.encoded.certificate.formula reference := by
  rw [formula]
  exact usedOfZero NullActionPromotionSupport.model _ reference
    NullActionPromotionSupport.formula_supported_zero

noncomputable def execution := certificate.realizeAt reference source used

theorem factual_action_null :
    (NullActionPromotionSupport.model.observationalDist.probVal
      (Kernel.agreesOn NullActionPromotionSupport.query.action reference)).num = 0 :=
  NullActionPromotionSupport.observational_action_is_null

private theorem execution_value_zero : QProb.Equiv execution.operation.value QProb.zero := by
  have observedZero : ProbabilityResult.Equivalent
      (NullActionPromotionSupport.model.termDenote certificate.encoded.certificate.formula reference)
      (some QProb.zero) := by
    rw [formula]
    exact valueZero _ NullActionPromotionSupport.formula_supported_zero
  have agreement := ProbabilityResult.trans (ProbabilityResult.symm execution.formulaValue) observedZero
  cases agreement with
  | value equivalent => exact equivalent

/-- Actual conditional execution remains valid at this null factual action,
because its original intervened evidence and used conditionals are defined. -/
theorem endpoint_zero : QProb.Equiv
    ((NullActionPromotionSupport.query.operationKernel.observedRecord
      NullActionPromotionSupport.model.toLatentRootSCM reference
      execution.operation.conditionPositive).observedValue
      (NullActionPromotionSupport.query.operationKernel.outcomeEvent reference)) QProb.zero :=
  QProb.equiv_trans execution.operation.operationValue execution_value_zero

end NullAction

end SupportedModalRegression
end Examples
end Causality
end Thesis
