import Thesis.CausalTransport.HiddenDAGReachableValues
import Thesis.Examples.HiddenDAGCompactSources
import Thesis.Examples.HiddenDAGMultivaluedPresentation

namespace Thesis.Causality.Examples.HiddenDAGReachableValues

open Probability HiddenDAGCollapse

/-!
# Retained hidden trajectories and full null-valued observed domains

The existing five-node hidden relay supplies a non-root hidden vertex and a
shared hidden ancestor with three observed children. Test factual and forced
trajectories at arbitrary noise units, without evaluating their whole cube.
The actual compact source model gives a uniform cardinality bound independent
of the old source denominators. A separate multivalued fixture verifies that
observed domains are not restricted to reached or positive-probability values.

These regressions test domain membership and finite coding. The separate native
value-presentation regressions test complete evaluator and law preservation.
-/

def actions : List (HardIntervention signature) := [forceXFalse]

theorem factual_trajectory_retained (noise : model.NoiseAssignment) (node : Fin fullGraph.count) :
    model.evalNode (HardIntervention.empty signature) noise node ∈ model.retainedNodeValues actions node :=
  model.evalNode_mem_retainedNodeValues actions _ List.mem_cons_self noise node

theorem forced_trajectory_retained (noise : model.NoiseAssignment) (node : Fin fullGraph.count) :
    model.evalNode forceXFalse noise node ∈ model.retainedNodeValues actions node :=
  model.evalNode_mem_retainedNodeValues actions _ (List.mem_cons_of_mem _ List.mem_cons_self) noise node

theorem code_round_trip (node : Fin fullGraph.count) (code : model.ValueCode actions node) :
    model.encodeValue actions node (model.decodeValue actions node code) = code :=
  model.encodeValue_decodeValue actions node code

theorem retained_trajectory_round_trip (noise : model.NoiseAssignment) (node : Fin fullGraph.count) :
    model.decodeValue actions node (model.encodeValue actions node (model.evalNode forceXFalse noise node)) =
      model.evalNode forceXFalse noise node :=
  model.decodeValue_encodeValue actions node _ (forced_trajectory_retained noise node)

/-- With no extra action the factual default is still represented; there
is no empty-domain exception or assumed inhabitant. -/
theorem empty_request_has_default (node : Fin fullGraph.count) :
    model.decodeValue [] node (model.encodeValue [] node (model.factualNodeValue node)) = model.factualNodeValue node :=
  model.decodeValue_encodeValue [] node _ (model.factualNodeValue_mem [] node)

/-- This bound uses the *actual* three-code alphabets proved by the compact
source adapter. It does not count an expanded denominator or hidden labels. -/
theorem compact_hidden_bound (node : Fin fullGraph.count) (hidden : fullGraph.hidden node = true) :
    (HiddenDAGCompactSources.queryModel.valueWitness actions node).card ≤ 2 * 3 ^ 5 :=
  HiddenDAGCompactSources.queryModel.valueWitness_card_bound_of_noise_bound actions 3
    HiddenDAGCompactSources.actual_alphabet_bounded node hidden

namespace NullObserved

open HiddenDAGMultivaluedPresentation

/-- Count two is permitted even though it has zero factual mass. Membership
uses the full observed domain, independently of the extra intervention list. -/
theorem permitted_null_value_retained (requested : List (HardIntervention signature)) :
    nullValue ∈ model.retainedNodeValues requested (projection.hiddenDAG.observedNode y) :=
  model.observedValue_mem_retainedNodeValues requested y nullValue

theorem null_value_round_trip (requested : List (HardIntervention signature)) :
    model.decodeValue requested (projection.hiddenDAG.observedNode y)
        (model.encodeValue requested (projection.hiddenDAG.observedNode y) nullValue) = nullValue :=
  model.decodeValue_encodeValue requested _ nullValue (permitted_null_value_retained requested)

end NullObserved
end Thesis.Causality.Examples.HiddenDAGReachableValues
