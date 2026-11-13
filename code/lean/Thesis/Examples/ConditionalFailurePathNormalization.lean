import Thesis.CausalTransport.ConditionalFailurePathNormalization

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailurePathNormalization

open PathSpecification

/-!
# The normalized exchange witness retains its private-pair first edge

The two three-valued observed vertices have a genuine bidirected pair, no
directed edges, and no intervention.  The query asks for the second vertex
given the first.  Its singleton exchange test is negative, so the general
constructor supplies a collider-normal outgoing-cut path and restores it to
the action-cut graph with its exact latent-pair list and first incoming edge.

This graph query is observationally identifiable by ordinary conditioning.
The fixture therefore tests normalized graph data without misrepresenting
exchange exhaustion as an ID failure or as a conditional counterexample.
The universal parity-network obligation still needs the actual joint hedge.
-/

def signature : ObservedSignature where
  count := 2
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by intro _ _ edge; cases edge

def conditioner : Fin signature.count := ⟨0, by decide⟩
def outcome : Fin signature.count := ⟨1, by decide⟩

def graph : ObservedGraph signature where
  bidirected := fun left right => decide (left ≠ right)
  bidirected_symmetric := by intro left right edge; simpa only [ne_comm] using edge
  bidirected_irreflexive := by intro node; simp

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcome
  action := NodeSet.empty
  condition := NodeSet.singleton conditioner
  action_outcome_disjoint := NodeSet.disjoint_empty_left _
  action_condition_disjoint := NodeSet.disjoint_empty_left _
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

theorem no_exchange : conditionalExchangeStep? graph query = none := by decide +kernel

def normal : ConditionalBackdoorPathNormalForm graph query conditioner :=
  .ofNoExchange graph query no_exchange conditioner (by decide +kernel)

def backdoor : ConditionalBackdoorPath graph query conditioner := normal.backdoor (by decide +kernel)

/-- The normal-form search returns the actual expanded pair path.  Its
private latent vertex is retained instead of silently contracting that pair. -/
theorem cut_path_codes : normal.cutPath.nodes.map SeparationNode.code =
    [0, (SeparationNode.latentPair conditioner outcome).code, 1] := by decide +kernel

/-- Restoration uses the shared adapter and preserves the selected list.
This check applies the general equality rather than running a second search. -/
theorem restored_path_nodes : backdoor.path.nodes = normal.cutPath.nodes := normal.backdoor_nodes _

theorem restored_first_incoming : graph.expandedMutilatedEdge (GraphMutilation.bar query.action)
    backdoor.first (.observed conditioner) = true := backdoor.first_incoming

/-- Minimality is obtained from the public normal-form theorem certificate,
not asserted by a fixture-specific finite decision of all competing paths. -/
theorem cut_count_minimal (competitor : ActivePath graph
    (GraphMutilation.barUnderline query.action (NodeSet.singleton conditioner))
    (NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton conditioner)))
    (.observed conditioner) (.observed normal.outcome)) :
    colliderCount graph (GraphMutilation.barUnderline query.action (NodeSet.singleton conditioner))
      normal.cutPath.nodes ≤
    colliderCount graph (GraphMutilation.barUnderline query.action (NodeSet.singleton conditioner))
      competitor.nodes := normal.count_minimal competitor

end CurrentConditionalFailurePathNormalization
end Examples
end Causality
end Thesis
