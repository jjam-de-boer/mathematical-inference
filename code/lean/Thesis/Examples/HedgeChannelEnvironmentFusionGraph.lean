import Thesis.Examples.ConditionalFailureActivationForest

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentHedgeChannelEnvironmentFusion

open PathSpecification CurrentConditionalFailureActivationForest

/-!+# Original graph data for the transmitting-overlap fusion regression

Retain the two complete actual policy traces `C -> M -> Z` and
`D -> M -> Z` from the existing genuine collider fixture.  Their Boolean
union deduplicates the common suffix, while their two source colliders
remain interaction rows with outgoing activation edges.

The literal finite masks below are proved equal to these executable trace
and policy selections.  The semantic companion can reuse those equalities
without repeatedly reducing the larger auxiliary-policy construction.
No alternative successor, guessed stopping condition, or new graph is used.
Separating these graph certificates keeps local checks within the fixed cap.
-/

/-- Both genuine original collider seeds are core rows before forest fusion. -/
def interaction : NodeSet signature := NodeSet.union (NodeSet.singleton leftCollider) (NodeSet.singleton rightCollider)

/-- Keep both complete actual traces, including their shared suffix and
conditioned endpoint; do not substitute the larger ancestor-policy domain. -/
def traces : NodeSet signature := fun node => decide (node ∈ leftPath.nodes) || decide (node ∈ rightPath.nodes)

/-- Restrict the original common successor, without choosing a new merge policy. -/
def successor : ForestChild signature := restrictChild traces forest.successor

/-- The literal selection is certified against the actual complete traces.
This equality is a reusable graph fact, not a replacement constructor. -/
theorem actual_trace_mask : traces = (fun node => decide (2 ≤ node.val ∧ node.val ≤ 5)) := by
  funext node
  decide +kernel +revert

/-- The certified policy retains both incoming branches at one merge and
then stops at the original conditioner.  Off-trace vertices have no arrow. -/
theorem actual_successor_map : successor = (fun node =>
    if node = leftCollider ∨ node = rightCollider then some mergeNode
    else if node = mergeNode then some conditionNode else none) := by
  funext node
  decide +kernel +revert

/-- Well-formedness concerns the actual restricted policy.  The displayed
equalities merely avoid reevaluating its ancestor construction during checking. -/
theorem actual_trace_wellFormed : childWellFormedBool traces successor = true := by
  rw [actual_trace_mask, actual_successor_map]
  decide +kernel

/-- Both overlaps genuinely transmit: the old absorber's stopped-at-core
premise is false, and the common receiving vertex is not a core row. -/
theorem overlap_seeds_transmit : interaction leftCollider = true ∧ interaction rightCollider = true ∧
    successor leftCollider = some mergeNode ∧ successor rightCollider = some mergeNode ∧
    interaction mergeNode = false := by
  rw [actual_successor_map]
  decide +kernel

/-- Both real branches share a single merge row and one original sink.
Boolean domain membership counts the shared suffix once. -/
theorem actual_merged_rows : traces mergeNode = true ∧ successor mergeNode = some conditionNode ∧
    keptSinks traces successor = NodeSet.singleton conditionNode := by
  rw [actual_trace_mask, actual_successor_map]
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  funext node
  decide +kernel +revert

end CurrentHedgeChannelEnvironmentFusion
end Examples
end Causality
end Thesis
