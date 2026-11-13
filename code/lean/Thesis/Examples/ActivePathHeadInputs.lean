import Thesis.CausalTransport.ActivePathHeadInputs
import Thesis.Examples.HedgeChannelPathInputs

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentActivePathHeadInputs

open PathSpecification CurrentHedgeChannelPathInputs.ObservedFork

/-!
# Chain heads keep their genuine receiver in either path-list orientation

The existing original three-valued graph has path `A <- F -> B -> Y`,
with ambient extra arrow `F -> Y` and an unused bidirected pair `F <-> Y`.
The chain head `B` has the one genuine outgoing path read at `Y`.  Its
receiver occurs after it in the displayed path, but before it in the
reversed path.  Applying the same general internal-head theorem to both
orientations proves the identical complete parent-input column.

This differs from omitted-fork routing: a chain's only outgoing receiver
cannot be changed by choosing the source-side or outcome-side neighbour.
The actual incoming endpoint `Y` has no outgoing path read at all.  Its
ambient graph relationships do not invent a second path incidence.

The tests reuse certified real graph/path data and apply the general
structural column theorem.  They do not supply a sparse signal matrix or
assert a conditional countermodel for this action-free graph.
-/

/-- In the original list, `B`'s only receiving head is its following `Y`.
The universal theorem supplies uniqueness; a real displayed arrow identifies
that unique receiver without evaluating a path search. -/
theorem chain_following_receiver (row : Fin signature.count) :
    ActivePathInput.incomingEdge graph cut actualPath.nodes (.observed middle) row = decide (row = outcome) := by
  rcases ActivePathInput.head_internal_unique_input actualPath [.observed source] [] (.observed fork) (.observed outcome)
    middle rfl (by decide +kernel) (by decide +kernel) with ⟨child, column⟩
  have input : ActivePathInput.incomingEdge graph cut actualPath.nodes (.observed middle) outcome = true := by decide +kernel
  have same : outcome = child := of_decide_eq_true ((column outcome).symm.trans input)
  rw [← same] at column
  exact column row

/-- Reversing the list moves `Y` before `B`, but the actual kept arrow
and unique receiver stay unchanged.  Neither a numbering rule nor a fork
source-side convention is silently substituted for chain direction. -/
theorem chain_preceding_receiver (row : Fin signature.count) :
    ActivePathInput.incomingEdge graph cut actualPath.reverse.nodes (.observed middle) row = decide (row = outcome) := by
  rcases ActivePathInput.head_internal_unique_input actualPath.reverse [] [.observed source] (.observed outcome) (.observed fork)
    middle rfl (by decide +kernel) (by decide +kernel) with ⟨child, column⟩
  have input : ActivePathInput.incomingEdge graph cut actualPath.reverse.nodes (.observed middle) outcome = true := by decide +kernel
  have same : outcome = child := of_decide_eq_true ((column outcome).symm.trans input)
  rw [← same] at column
  exact column row

/-- The incoming endpoint is a real head but cannot transmit to any
other path row.  This is the universal endpoint theorem, not a guessed
one-incidence row formula. -/
theorem incoming_endpoint_parent_absent (row : Fin signature.count) :
    ActivePathInput.incomingEdge graph cut actualPath.nodes (.observed outcome) row = false :=
  ActivePathInput.target_head_parent_absent actualPath (by decide +kernel) row

end CurrentActivePathHeadInputs
end Examples
end Causality
end Thesis
