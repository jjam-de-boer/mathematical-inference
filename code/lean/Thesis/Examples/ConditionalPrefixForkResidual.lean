import Thesis.CausalTransport.HedgeChannelEnvironmentPrefixDirection
import Thesis.Examples.ConditionalCutActivationInteraction

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalPrefixForkResidual

open Probability PathSpecification FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation
open CurrentConditionalCutActivationRoute

/-!
# A real prefix-fork read cancels the proposed receiving correction

The existing cut-path fixture has the actual fork `U` on `P <- U -> C <- Y`
and activation `C -> Z`.  The selected interaction omits `U`, but original
pivot row `P` genuinely reads it.  The proper-prefix direction of the legal
one-edge forest `U -> P` flips `U`, not `P` or a reserved input.

Its original pivot-row residual is therefore true.  Absorption adds the
receiving boundary bit, also true, and the two cancel.  The corrected pivot
contribution is false, not the receiver indicator alone.  This regression
checks the residual retained by the exact general prefix identity and rules
out an unjustified zero-prefix-read simplification.

This is a graph/signal regression on the existing identifiable-query fixture,
not a hedge or a conditional countermodel.  It does not refute completeness;
the universal terminal argument still needs the actual hedge/contact geometry.
-/

def domain : NodeSet signature := NodeSet.union (NodeSet.singleton parent) (NodeSet.singleton pivotNode)
def successor : ForestChild signature := fun node => if node = parent then some pivotNode else none

theorem well_formed : childWellFormedBool domain successor = true := by decide +kernel

def path : SuccessorPath domain successor parent := .ofForest domain successor well_formed parent (by decide +kernel)
def prefixDirection : Cube graph := LinearSignal.successorPrefixDirection path

theorem actual_prefix_bits : path.prefixBits = NodeSet.singleton parent := by funext child; decide +kernel +revert
theorem actual_endpoint : path.endpoint = pivotNode := by decide +kernel

private theorem core_prefix_free : forall node, node ∈ path.nodes -> node ≠ path.endpoint -> interactionRows node = false := by
  have nodes : path.nodes = [parent, pivotNode] := by decide +kernel
  rw [nodes, actual_endpoint]
  intro node visited different
  rcases List.mem_cons.mp visited with same | endpoint
  · subst node; exact irrelevant_fork_pruned.2.2
  · exact False.elim (different (List.mem_singleton.mp endpoint))

private theorem trace_zero : forall child, traces child = true -> cubeSample graph prefixDirection child = false := by
  rw [actual_trace_mask]
  intro child selected
  rw [prefixDirection, LinearSignal.successorPrefixDirection_sample, actual_prefix_bits]
  exact (by decide +kernel : forall child, NodeSet.union (NodeSet.singleton collider) (NodeSet.singleton evidence) child = true ->
    NodeSet.singleton parent child = false) child selected

/-- The actual original pivot reads the proper-prefix fork.  The trace
domain is zero here, so activation preserves that genuine path-row read. -/
theorem original_pivot_prefix_read : (interactionSignal.rowPhase pivotNode).value prefixDirection = true := by
  have pivotHead := normal.pathDirection_source_odd retainedPivot.selected
  rw [interactionSignal, ConditionalBackdoorPathNormalForm.activationInteractionSignal]
  have kept := LinearSignal.absorbSuccessor_rowPhase_inside_of_domain_zero
    (LinearSignal.ofActivePath normal.cutPath) normal.pathHeads
    (normal.activationTraceNodes retainedPivot cutForest) (normal.activationTraceSuccessor retainedPivot cutForest)
    (normal.activationTraceSuccessor_wellFormed retainedPivot cutForest) prefixDirection trace_zero pivotNode pivotHead.1
  apply kept.trans
  rw [LinearSignal.ofActivePath_rowPhase_first_pair normal.cutPath (.observed parent)
    [.observed collider, .observed outcome] normal_window]
  rw [prefixDirection, LinearSignal.successorPrefixDirection_sample, actual_prefix_bits]
  unfold LinearSignal.incomingValue LinearSignal.expandedInput
  decide +kernel

/-- The endpoint indicator is canceled by the real original-row residual.
Replacing that residual by zero would give the wrong parity at this receiver. -/
theorem absorbed_pivot_prefix_even :
    (((interactionSignal.absorbSuccessor interactionRows successor).rowPhase pivotNode).value prefixDirection) = false := by
  have original := original_pivot_prefix_read
  change (interactionSignal.rowPhase pivotNode).value (LinearSignal.successorPrefixDirection path) = true at original
  unfold prefixDirection
  rw [LinearSignal.absorbedPrefixDirection_row_inside interactionSignal interactionRows path well_formed
    core_prefix_free pivotNode actual_selected_parities.1, original, actual_endpoint]
  decide +kernel

end CurrentConditionalPrefixForkResidual
end Examples
end Causality
end Thesis
