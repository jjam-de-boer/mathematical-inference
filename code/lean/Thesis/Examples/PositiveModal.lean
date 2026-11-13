import Thesis.CausalTransport.PositiveModal
import Thesis.Examples.ConditionalCompilation

namespace Thesis
namespace Causality
namespace Examples
namespace PositiveModalRegression

open Probability
open FrontDoorIdentification

/-!
# Positive completeness reaches actual modal operations

The existing front-door SCM has a genuinely confounded treatment/outcome pair
and a strictly positive eight-cell observed law.  Its current ID/IDC results
are reused; the legacy formula is never passed to a new certificate.

Both certificates below are obtained from the completed *semantic*
completeness package, then indexed by the concrete model's mode.  The
realization traverses the resulting modal trace and executes each supported
kernel's action and observation locks.  The final probability is read from
the executed record and agrees with the independently checked causal value.
Thus these are not merely type checks of an interface with an assumed
completeness input, nor import-only regressions.
-/

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => false
  second := fun _ => true
  first_enumerated := by intro _; change false ∈ [false, true]; decide +kernel
  second_enumerated := by intro _; change true ∈ [false, true]; decide +kernel
  different := fun _ => Bool.false_ne_true

def mode : CausalMode signature :=
  ⟨"front-door/positive", CausalEpistemicRecord.initial model⟩

theorem mode_member : (GraphModelClass.positive graph).Mem mode.record.model :=
  ⟨model_compatible, model_positive⟩

/-- Genuine joint completeness, rather than a hand-assembled front-door
derivation, supplies the action-free formula and its modal annotation. -/
noncomputable def jointCertificate :=
  mode.positiveJointModalCompleteness graph rich mode_member query
    CurrentKernelSuccessCompilation.frontDoor_identifiable

/-- The same positive package supplies the conditional front-door query.
Its semantic input is the already checked current IDC certificate. -/
noncomputable def conditionalCertificate :=
  mode.positiveConditionalModalCompleteness graph rich mode_member
    CurrentConditionalCompilation.frontDoorConditionalQuery
    (CurrentConditionalCompilation.frontDoorConditionalCertificate.compile.identifiable graph.publishedSoundness)

/-- This returns both the actual kernel execution and recursively realized
Pearl-rule leaves of the completeness-generated modal trace. -/
noncomputable def jointExecution :=
  jointCertificate.realizeAt graph.publishedSoundness reference (query.supportedAt model reference)

noncomputable def conditionalExecution :=
  conditionalCertificate.realizeAt graph.publishedSoundness reference
    ⟨CurrentConditionalCompilation.threeQuarters,
      CurrentConditionalCompilation.frontDoor_conditional_source_value⟩

/-- Execute the intervention lock of the completed joint certificate. -/
theorem joint_action_realizes : CausalTransition.Realizes
    jointExecution.1.actionTransition (.intervene query.action) :=
  jointExecution.1.actionTransition_realizes

/-- Execute the observation lock as well, rather than just attach a name. -/
theorem conditional_observation_realizes : CausalTransition.Realizes
    conditionalExecution.1.observationTransition
      (.observe CurrentConditionalCompilation.frontDoorConditionalQuery.condition) :=
  conditionalExecution.1.observationTransition_realizes

private theorem joint_value : QProb.Equiv jointExecution.1.value ⟨1, 2, by decide⟩ := by
  have agreement := ProbabilityResult.trans
    (ProbabilityResult.symm jointExecution.1.denotation) sourceAtReferenceHalf
  cases agreement with
  | value equivalent => exact equivalent

private theorem conditional_value : QProb.Equiv conditionalExecution.1.value
    CurrentConditionalCompilation.threeQuarters := by
  have agreement := ProbabilityResult.trans
    (ProbabilityResult.symm conditionalExecution.1.denotation)
    CurrentConditionalCompilation.frontDoor_conditional_source_value
  cases agreement with
  | value equivalent => exact equivalent

/-- The edited joint endpoint actually reports the correct one-half risk. -/
theorem joint_endpoint_half : QProb.Equiv
    ((query.operationKernel.observedRecord model reference
      jointExecution.1.conditionPositive).observedValue
      (query.operationKernel.outcomeEvent reference)) ⟨1, 2, by decide⟩ :=
  QProb.equiv_trans jointExecution.1.operationValue joint_value

/-- Conditioning at the edited endpoint gives three quarters, using the
actual positive evidence rather than replacing an undefined conditional. -/
theorem conditional_endpoint_three_quarters : QProb.Equiv
    ((CurrentConditionalCompilation.frontDoorConditionalQuery.operationKernel.observedRecord
      model reference conditionalExecution.1.conditionPositive).observedValue
      (CurrentConditionalCompilation.frontDoorConditionalQuery.operationKernel.outcomeEvent reference))
    CurrentConditionalCompilation.threeQuarters :=
  QProb.equiv_trans conditionalExecution.1.operationValue conditional_value

/-- The atomic edit path's endpoint yields the same risk.  This exercises
structural intervention compilation, not only the compact override record. -/
theorem atomic_joint_endpoint_half : QProb.Equiv
    (QProb.div (query.operationKernel.atomicNumerator model reference)
      (query.operationKernel.atomicDenominator model reference)
      jointExecution.1.atomicDenominator_positive) ⟨1, 2, by decide⟩ :=
  QProb.equiv_trans jointExecution.1.atomicConditionedValue joint_value

end PositiveModalRegression
end Examples
end Causality
end Thesis
