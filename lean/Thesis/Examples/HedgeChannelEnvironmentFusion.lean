import Thesis.CausalTransport.HedgeChannelEnvironmentFusion
import Thesis.Examples.HedgeChannelEnvironmentFusionGraph

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentHedgeChannelEnvironmentFusion

open Probability PathSpecification FiniteBooleanInteraction HedgeChannelEnvironmentInstallation
open CurrentConditionalFailureActivationForest

/-!
# Transmitting overlap seeds and real merged activation branches

The existing eight-vertex three-valued graph supplies two genuine colliders
and the complete common-policy paths `C -> M -> Z` and `D -> M -> Z`.
We retain exactly their actual path union, not the larger ancestor policy.
Both collider seeds are original interaction rows with outgoing successors;
the absorbing theorem's stopped-at-interaction premise is genuinely false.

One legal incoming read is selected at each collider: `C xor U` and
`D xor V`.  Fusing the actual forest installs `M xor C xor D` and
`Z xor M`, once each.  The entire union therefore has phase `U xor V xor Z`
at every original cube point.  A direction changing only `U` preserves
the first collider's odd row and makes both activation-only rows even.
The merge row and overlapping seeds retain their own bits once.

This checks the arbitrary-overlap installation, not a universal normalized
conditional countermodel.  The queried fixture is unchanged and no claim
of its nonidentifiability follows from this local interaction regression.
-/

/-- These are actual declared parent reads, not a mechanism evaluating
arbitrary graph coordinates.  Each installed row retains its own bit. -/
def signalData : LinearSignal graph where
  parentMask := fun child parent => decide
    ((child = leftCollider ∧ parent = leftParent) ∨ (child = rightCollider ∧ parent = rightParent))
  rootMask := fun _ _ => false

/-- Fuse the original collider reads with the certified actual trace policy. -/
def installed : LinearSignal graph := signalData.absorbSuccessor interaction successor
/-- One membership entry per core or trace row, including the shared suffix. -/
def rows : NodeSet signature := NodeSet.union interaction traces
/-- Change only the first original observed parent; retain the original root block. -/
def direction : Cube graph := joinCube graph (fun _ => false) (basisAssignment signature.count leftParent)

private theorem base_phase (point : Cube graph) :
    (signalData.forestPhase interaction).value point =
      (maskPhase _ (cubeMask graph (fun child => Bool.xor (interaction child)
        (Bool.xor (NodeSet.singleton leftParent child) (NodeSet.singleton rightParent child))))).value point := by
  apply HomogeneousPhase.value_eq_of_basis _ _ (fun _ => false) (sample := point)
  · decide +kernel
  · intro coordinate impossible
    cases impossible

/-- The general theorem conserves the complete original cube, retaining
the overlap correction and both merging branches.  Shared rows are not
XORed as two complete mechanisms or discarded as a duplicated suffix. -/
theorem complete_merged_phase (point : Cube graph) :
    (installed.forestPhase rows).value point = Bool.xor (cubeSample graph point leftParent)
      (Bool.xor (cubeSample graph point rightParent) (cubeSample graph point conditionNode)) := by
  rw [installed, rows, LinearSignal.absorbSuccessor_forestPhase_with_overlap signalData interaction traces successor actual_trace_wellFormed,
    base_phase, cubeMaskPhase_value, nodeXor_xor_masks, nodeXor_xor_masks, nodeXor_singleton, nodeXor_singleton,
    LinearSignal.ofSuccessor_forestPhase traces successor actual_trace_wellFormed, actual_merged_rows.2.2, nodeXor_singleton]
  have overlap : NodeSet.inter interaction traces = interaction := by
    rw [actual_trace_mask]
    funext node
    decide +kernel +revert
  rw [overlap]
  have cancel (seeds left right sink : Bool) :
      Bool.xor (Bool.xor seeds (Bool.xor left right)) (Bool.xor sink seeds) = Bool.xor left (Bool.xor right sink) := by
    cases seeds <;> cases left <;> cases right <;> cases sink <;> rfl
  exact cancel _ _ _ _

private theorem trace_direction_zero (node : Fin signature.count) (selected : traces node = true) :
    cubeSample graph direction node = false := by
  have actual : forall node, traces node = true -> basisAssignment signature.count leftParent node = false := by
    rw [actual_trace_mask]
    decide +kernel
  rw [direction, cubeSample, joinCube, FiniteProduct.BooleanBlocks.rightBlock_join]
  exact actual node selected

/-- The generous ancestor policy really has a nonzero coordinate that
the actual trace selection prunes.  Zero trace bits cannot be replaced by
an assertion that the whole auxiliary policy is zero in this direction. -/
theorem pruned_ancestor_is_nonzero : forest.nodes leftParent = true ∧ traces leftParent = false ∧
    cubeSample graph direction leftParent = true := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · rw [actual_trace_mask]
    decide +kernel
  · rw [direction, cubeSample, joinCube, FiniteProduct.BooleanBlocks.rightBlock_join, basisAssignment_self]

/-- General zero-domain fusion preserves the original nonzero collider
read.  Only actual retained trace bits are zero; the larger policy has an
ancestor bit equal to one and is not substituted for the trace domain. -/
theorem transmitting_seed_parity_preserved :
    (installed.rowPhase leftCollider).value direction = true := by
  rw [installed, LinearSignal.absorbSuccessor_rowPhase_inside_of_domain_zero signalData interaction traces successor
    actual_trace_wellFormed direction trace_direction_zero leftCollider (by decide +kernel)]
  decide +kernel

/-- The new merge and evidence rows are even by the general row theorem,
with no separately supplied row-evenness or stopped-at-core certificate. -/
theorem new_activation_rows_even : (installed.rowPhase mergeNode).value direction = false ∧
    (installed.rowPhase conditionNode).value direction = false := by
  constructor
  · exact LinearSignal.absorbSuccessor_rowPhase_new_of_domain_zero signalData interaction traces successor
      actual_trace_wellFormed direction trace_direction_zero mergeNode (by decide +kernel) actual_merged_rows.1
  · exact LinearSignal.absorbSuccessor_rowPhase_new_of_domain_zero signalData interaction traces successor
      actual_trace_wellFormed direction trace_direction_zero conditionNode (by decide +kernel)
        (by rw [actual_trace_mask]; decide +kernel)

/-- One own bit remains at an overlapping transmitting seed.  XORing its
two complete row phases would erase it, just as at a zero-edge overlap. -/
theorem overlap_own_bit_not_duplicated :
    (installed.rowPhase leftCollider).value (joinCube graph (fun _ => false) (basisAssignment signature.count leftCollider)) = true ∧
    Bool.xor ((signalData.rowPhase leftCollider).value
      (joinCube graph (fun _ => false) (basisAssignment signature.count leftCollider)))
      (((LinearSignal.ofSuccessor (G := graph) successor).rowPhase leftCollider).value
        (joinCube graph (fun _ => false) (basisAssignment signature.count leftCollider))) = false := by
  rw [installed, actual_successor_map]
  decide +kernel

end CurrentHedgeChannelEnvironmentFusion
end Examples
end Causality
end Thesis
