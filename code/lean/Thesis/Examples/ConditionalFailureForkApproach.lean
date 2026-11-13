import Thesis.CausalTransport.ConditionalFailureForkApproach
import Thesis.Examples.ConditionalFailureSmallPrefixDirection

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureForkApproach

open PathSpecification Probability FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation
open CurrentConditionalFailureSmallPrefixDirection

/-!
# Exact general transfer on a genuine outside-Small-pivot failure

The existing three-valued hedge has Small `U,R`, conditioner `P` outside
Small, and the actual normalized path `P <- Y`.  The fork-aware target mask
contains `P` and the omitted outgoing endpoint `Y`; no original query is
changed.  The real Small-source approach remains the literal `U -> R -> P`.

The general new construction proves that every proper approach vertex is
off the normalized path and outside the actual activation union.  Its
receiving original-row residual is therefore zero by theorem, not by this
example's finite parity calculation.  The new installed signal changes only
rows `U,P` when that actual proper prefix is flipped.  Complete original
support, outcome oddness and every original reserved input are retained.

The companion already constructs this query's positive original-alphabet
countermodels.  Here it serves as a genuine terminal/hedge regression for
the now-universal local transfer operation.  Neither the example nor that
local operation substitutes for the remaining global contact-connectivity
and even-background direction proof.
-/

private theorem source_in_small : witness.small source = true := by decide +kernel

/-- The literal combined target mask used only after proving equality to
the actual normalized core-plus-fork classifier. -/
def targets : NodeSet signature := NodeSet.union (NodeSet.singleton pivotNode) (NodeSet.singleton outcome)

private theorem receives : NodeSet.Subset query.condition targets := NodeSet.subset_union_left _ _

theorem actual_targets : normal.forkAbsorptionTargets pivot forest = targets := by
  unfold ConditionalBackdoorPathNormalForm.forkAbsorptionTargets
  rw [actual_core]
  unfold PathSpecification.ActivePath.forkNodes
  rw [normal_window]
  funext child
  decide +kernel +revert

/-- This is the actual general constructor, not a manually supplied route. -/
def approach := normal.forkApproachPath boundary pivot forest source source_in_small

/-- Transport only the path's list through the proved mask equality;
the finite check never unfolds the opaque normalization search. -/
theorem actual_path : approach.nodes = [source, commonRoot, pivotNode] := by
  rw [approach, normal.forkApproachPath_nodes_of_targets_eq boundary pivot forest targets receives actual_targets]
  decide +kernel

theorem actual_endpoint : approach.endpoint = pivotNode := by
  rw [approach, normal.forkApproachPath_endpoint_of_targets_eq boundary pivot forest targets receives actual_targets]
  decide +kernel

/-- Use the computed proper prefix on the full original-input cube. -/
def correction : Cube graph := normal.forkApproachPrefixDirection boundary pivot forest source source_in_small

theorem correction_supported : correction ∈
    FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
      (cubeMask graph (NodeSet.union query.action query.condition)) :=
  normal.forkApproachPrefixDirection_supported boundary pivot forest source source_in_small

/-- The actual original receiving residual is zero by the general
noncontact proof, for every core row, not by enumerating signal values. -/
theorem original_receiving_read_zero (child : Fin signature.count)
    (selected : normal.smallInteractionRows pivot forest child = true) :
    ((normal.activationInteractionSignal pivot forest).rowPhase child).value correction = false :=
  normal.activationInteraction_forkApproach_read_zero boundary pivot forest source source_in_small child selected

/-- The exact installed correction is Small source `U` XOR receiver `P`.
Intermediate Small row `R` and every other row have zero correction. -/
theorem actual_two_row_transfer (child : Fin signature.count) :
    ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase child).value correction =
      Bool.xor (decide (child = source)) (decide (child = pivotNode)) := by
  have rows := normal.forkApproachPrefixDirection_rows boundary pivot forest source source_in_small child
  change _ = Bool.xor (decide (child = source)) (decide (child = approach.endpoint)) at rows
  rw [actual_endpoint] at rows
  exact rows

def shifted : Cube graph := normal.forkApproachShift boundary pivot forest source source_in_small normal.pathDirection

theorem shifted_supported : shifted ∈
    FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
      (cubeMask graph (NodeSet.union query.action query.condition)) :=
  normal.forkApproachShift_supported boundary pivot forest source source_in_small normal.pathDirection normal.pathDirection_member

theorem shifted_outcome_odd : (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value shifted = true := by
  rw [shifted, normal.forkApproachShift_outcome boundary pivot forest source source_in_small]
  exact normal.activationInteraction_outcome_odd pivot

/-- Both original pair-root coordinates are literally retained; no
independent latent direction or extra globally readable input is introduced. -/
theorem original_roots_retained : cubeEnvironment graph shifted = cubeEnvironment graph normal.pathDirection :=
  normal.forkApproachShift_roots boundary pivot forest source source_in_small normal.pathDirection

end CurrentConditionalFailureForkApproach
end Examples
end Causality
end Thesis
