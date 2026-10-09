import Thesis.CausalTransport.HedgeChannelProjection
import Thesis.CausalTransport.HedgeChannelObservational
import Thesis.CausalTransport.ValueRefinementCounterexample

namespace Thesis
namespace Causality
namespace HedgeChannelInstallation

open Probability

/-!
# Positive countermodels for every supplied original-query hedge

The projection theorem separates the actual installed Boolean models on the
original outcome event, under the entire original action.  This module turns
that gap into a counterexample in the supplied graph's full-alphabet positive
model class.  The previously proved private label refinement supplies every
original label with positive mass; it neither adds observed nodes nor changes
the graph, action, or outcome sets.

The query adapter below makes the two semantic interfaces explicit.  Labels
at action coordinates are set to `rich.first`, whose decoded bit is false.
The event asks that the decoded original outcome coordinates are all false.
Its locality is proved from coordinate agreement, not assumed.  The witness's
stored action seed proves the action is nonempty, so the event-query evaluator
uses the actual interventional law rather than its empty-action branch.

Compatibility, positivity, complete observational equality, and the original
causal gap all concern the same installed pair.  No readiness predicate or
countermodel premise is added to the supplied hedge.  This is the general
joint hedge leaf; the conditional terminal leaf remains a separate obligation.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {q : JointKernelQuery S}

/-! ## An original-label event with the exact Boolean hard cut -/

/-- Force each original action coordinate to its supplied first label.
The target set is exactly the action, including any additional action nodes. -/
def firstLabelIntervention (rich : ObservedSignature.ValueRich S) (action : NodeSet S) :
    HardIntervention S :=
  ⟨fun child => if action child then some (rich.first child) else none⟩

/-- The original-label hard intervention retains the complete action set. -/
theorem firstLabelIntervention_targets (rich : ObservedSignature.ValueRich S) (action : NodeSet S) :
    (firstLabelIntervention rich action).targets = action := by
  funext child
  cases selected : action child <;>
    simp only [firstLabelIntervention, HardIntervention.targets, selected,
      Bool.false_eq_true, if_false, if_true, Option.isSome]

/-- Decode the original-label target exactly, rather than replacing it by
a seed-only intervention or another convenient hard cut. -/
theorem firstLabelIntervention_decoded (rich : ObservedSignature.ValueRich S) (action : NodeSet S) :
    BinaryEncoding.intervention rich (firstLabelIntervention rich action).value =
      falseActionTarget action := by
  funext child
  cases selected : action child with
  | false => simp only [BinaryEncoding.intervention, firstLabelIntervention,
      falseActionTarget, selected, Bool.false_eq_true, if_false, Option.map_none]
  | true =>
      simp only [BinaryEncoding.intervention, firstLabelIntervention,
        falseActionTarget, selected, if_true, Option.map_some]
      exact congrArg some (BinaryEncoding.bit_value rich child false)

/-- The separating event on the original signature reads precisely the
original outcome's decoded bits.  Extra labels are kept, not discarded. -/
def originalFalseEventQuery (rich : ObservedSignature.ValueRich S) (query : JointKernelQuery S) :
    InterventionalQuery S where
  intervention := firstLabelIntervention rich query.action
  outcomeNodes := query.outcome
  action_outcome_disjoint := by
    rw [firstLabelIntervention_targets]
    exact query.action_outcome_disjoint
  event := fun sample => FiniteProduct.falseCylinder S.count query.outcome
    (ObservedValueRefinement.bits rich sample)
  event_local := by
    intro first second agree
    apply FiniteProduct.falseCylinder_congr
    intro child selected
    exact congrArg (ObservedValueRefinement.bit rich child) (agree child selected)

/-- The adapter is literally the original joint kernel query.  Event
separation therefore establishes separation of that kernel, not a surrogate. -/
theorem originalFalseEventQuery_kernelQuery (rich : ObservedSignature.ValueRich S)
    (query : JointKernelQuery S) : (originalFalseEventQuery rich query).kernelQuery = query := by
  cases query
  simp only [InterventionalQuery.kernelQuery, originalFalseEventQuery,
    firstLabelIntervention_targets]

private theorem binary_originalFalseEventQuery_value (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (model : ExactModel S.binary) :
    (ObservedValueRefinement.binaryQuery rich (originalFalseEventQuery rich q)
      (FiniteProduct.falseCylinder S.count q.outcome) (fun _ => rfl)).value model =
    model.interventionalValue (falseActionTarget q.action)
      (FiniteProduct.falseCylinder S.count q.outcome) := by
  have target : (ObservedValueRefinement.binaryQuery rich (originalFalseEventQuery rich q)
      (FiniteProduct.falseCylinder S.count q.outcome) (fun _ => rfl)).intervention.value =
      falseActionTarget q.action := firstLabelIntervention_decoded rich q.action
  have targets : (ObservedValueRefinement.binaryQuery rich (originalFalseEventQuery rich q)
      (FiniteProduct.falseCylinder S.count q.outcome) (fun _ => rfl)).intervention.targets = q.action := by
    change (fun child => ((ObservedValueRefinement.binaryQuery rich (originalFalseEventQuery rich q)
      (FiniteProduct.falseCylinder S.count q.outcome) (fun _ => rfl)).intervention.value child).isSome) = q.action
    rw [target]
    funext child
    cases selected : q.action child <;>
      simp only [falseActionTarget, selected, Bool.false_eq_true, if_false, if_true, Option.isSome]
  have active : finAny S.binary.count q.action = true :=
    finAny_eq_true_of q.action w.actionSeed w.actionSeed_in_action
  unfold InterventionalQuery.value InterventionalQuery.distribution
  rw [targets, active]
  simp only [if_true]
  rw [target]
  rfl

/-! ## The unrestricted joint counterexample leaf -/

/-- Every supplied hedge has two compatible, fully positive original-label
models with equal complete observational laws and different original joint
interventional kernels.  All model fields and the causal gap are proved;
the only alphabet premise supplies two distinct labels at every node.

The final label sweep is the existing constructive refinement.  This result
does not require seed/sink-only actions, shared-switch children as outcomes,
or extra Boolean readiness conditions. -/
noncomputable def counterexample (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    CounterexampleIn (GraphModelClass.positive G) q := by
  have compatible := models_compatible w rich (outcomeFlowSignal w) (outcomeFlowSignal w)
  have positive := models_positive w rich (outcomeFlowSignal w) (outcomeFlowSignal w)
  have separated : ¬ QProb.Equiv
      ((ObservedValueRefinement.binaryQuery rich (originalFalseEventQuery rich q)
        (FiniteProduct.falseCylinder S.count q.outcome) (fun _ => rfl)).value
        (leftModel w rich (outcomeFlowSignal w) (outcomeFlowSignal w)))
      ((ObservedValueRefinement.binaryQuery rich (originalFalseEventQuery rich q)
        (FiniteProduct.falseCylinder S.count q.outcome) (fun _ => rfl)).value
        (rightModel w (outcomeFlowSignal w) (outcomeFlowSignal w))) := by
    rw [binary_originalFalseEventQuery_value w, binary_originalFalseEventQuery_value w]
    exact models_original_event_not_equiv w rich
  have result := ObservedValueRefinement.positiveCounterexampleOfBinaryEvent rich
    (originalFalseEventQuery rich q)
    (leftModel w rich (outcomeFlowSignal w) (outcomeFlowSignal w))
    (rightModel w (outcomeFlowSignal w) (outcomeFlowSignal w))
    compatible.1 compatible.2 positive.1 positive.2
    (models_observationallyEquivalent w rich (outcomeFlowSignal w) (outcomeFlowSignal w))
    (FiniteProduct.falseCylinder S.count q.outcome) (fun _ => rfl) separated
  exact {
    left := result.left
    right := result.right
    left_mem := result.left_mem
    right_mem := result.right_mem
    observationally_equal := result.observationally_equal
    query_separated := by
      simpa only [originalFalseEventQuery_kernelQuery] using result.query_separated }

end HedgeChannelInstallation
end Causality
end Thesis
