import Thesis.CausalTransport.ActivePathBoundary

namespace Thesis
namespace Causality

open PathSpecification

/-!
# An outgoing-only endpoint forces an actual neighbouring head

An observed endpoint with no incoming expanded arrow cannot be the receiving
end of its final path edge.  On a nonsingleton active path it therefore sends
an actual kept arrow to its neighbouring observed vertex.  That neighbour
is selected by the same executable head scan used by the installed signal.

The proof reads the first pair of the reversed, certified path and transports
its consecutive-pair fact back to the original list.  It does not enumerate
path searches or assume that every observed path vertex is a selected head.
The resulting neighbour is existential only in this proposition; no witness
is chosen from a proposition to construct signal or model data.
-/

universe u
variable {S : ObservedSignature.{u}}

namespace ActivePathInput

/-- Every nonsingleton observed-endpoint active path ending at a vertex
with no incoming expanded arrows selects an actual outgoing neighbour as
a head.  A graph with a unique such child can use this to prove mandatory
row coverage without evaluating the normal-form search. -/
theorem target_has_outgoing_head {graph : ObservedGraph S} {m : GraphMutilation S} {given : NodeSet S}
    {source target : Fin S.count} (path : ActivePath graph m given (.observed source) (.observed target))
    (distinct : source ≠ target)
    (noIncoming : forall neighbor, graph.expandedMutilatedEdge m neighbor (.observed target) = false) :
    Exists fun child : Fin S.count => graph.expandedMutilatedEdge m (.observed target) (.observed child) = true ∧
      headRows graph m path.nodes child = true := by
  have starts : path.nodes.reverse.head? = some (.observed target) := path.reverse.starts
  have finishes : path.nodes.reverse.getLast? = some (.observed source) := path.reverse.finishes
  have adjacent : Consecutive (Adjacent graph m) path.nodes.reverse := path.reverse.adjacent
  cases shape : path.nodes.reverse with
  | nil => rw [shape] at starts; cases starts
  | cons head tail =>
      have same : head = .observed target := by
        simpa only [shape, List.head?_cons, Option.some.injEq] using starts
      subst head
      cases tail with
      | nil =>
          rw [shape, List.getLast?_singleton] at finishes
          have equal := SeparationNode.observed.inj (Option.some.inj finishes)
          exact False.elim (distinct equal.symm)
      | cons next rest =>
          rw [shape] at adjacent
          have outgoing : graph.expandedMutilatedEdge m (.observed target) next = true := by
            rcases adjacent.1 with actual | incoming
            · exact actual
            · rw [noIncoming next] at incoming
              cases incoming
          cases next with
          | latentPair left right => cases outgoing
          | observed child =>
              refine ⟨child, outgoing, incomingEdge_head (parent := .observed target) ?_⟩
              apply Bool.and_eq_true_iff.mpr
              refine ⟨?_, outgoing⟩
              rw [← stepOnPath_reverse, shape]
              exact (stepOnPath_eq_true_iff (.observed target) (.observed child) _).mpr ⟨[], rest, Or.inl rfl⟩

end ActivePathInput
end Causality
end Thesis
