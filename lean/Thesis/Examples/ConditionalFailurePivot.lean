import Thesis.CausalTransport.ConditionalFailurePivot
import Thesis.Examples.ConditionalFailureActivation
import Thesis.Examples.HedgeChannelMarginal

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailurePivot

/-!
# Regression checks for latest-reachable conditional pivots

The first graph is the preceding activation regression: using its earlier
conditioner permits an activation branch to pass through that omitted pivot.
The normalized selection really chooses the later reachable conditioner.
For the new pivot, the same collider's activation stops at the earlier
conditioner, so maximality proves pivot avoidance and full-given-set freedom
of the preceding activation vertices.

The second fixture is a genuine, three-valued irreducible failed conditional
whose entire composed hedge-flow boundary is conditioned.  The new hard-case
constructor derives its eligible list from that actual hedge flow, rather
than receiving a separately chosen reachable conditioner.  Exhausted exchange
search then returns the actual normalized back-door path.

These checks concern the graph normalization.  They do not infer a universal
parity witness, assume that every pivot has this maximality property, or erase
intersections with the hedge's small forest.
-/

open CurrentConditionalFailureActivation

/-! ## The earlier omitted-pivot regression is normalized, not assumed away -/

/-- The initial eligible conditioner is `Z(3)`, but `D(4)` is also reachable
from `C(2)`.  The ordered member list supplies the latter as actual data. -/
def normalizedPivot : LatestConditionalPivot pivotGraph pivotQuery pivotCollider :=
  .ofReachableConditioner pivotGraph pivotQuery pivotCollider pivotNode
    (by decide +kernel) (by decide +kernel)

theorem later_conditioner_selected : normalizedPivot.node = pivotEndpoint := by
  decide +kernel

/-- With `D(4)` omitted instead, the other conditioner `Z(3)` immediately
activates `C(2)`.  The branch is `C -> Z`, not `C -> Z -> D`. -/
def normalizedActivation : ConditionalColliderActivationRoute
    pivotQuery normalizedPivot.node pivotCollider :=
  .ofAncestor pivotGraph pivotQuery normalizedPivot.node pivotCollider
    (by decide +kernel) (by decide +kernel)

theorem normalized_activation_codes :
    (normalizedActivation.before ++ [normalizedActivation.endpoint]).map Fin.val = [2, 3] := by
  decide +kernel

theorem latest_pivot_not_on_activation :
    normalizedPivot.node ∉ normalizedActivation.before ++ [normalizedActivation.endpoint] :=
  normalizedPivot.activation_pivot_not_mem normalizedActivation

/-- This is now the *full* conditional given-set, unlike the earlier branch
which legally passed its omitted pivot.  Freedom is supplied by the general
maximality theorem, not by deciding this fixture's displayed list. -/
theorem normalized_preceding_vertices_unconditioned (node : Fin pivotSignature.count)
    (member : node ∈ normalizedActivation.before) : pivotQuery.condition node = false :=
  normalizedPivot.activation_before_condition_free normalizedActivation node member

/-! ## An actual irreducible failure derives its pivot from its own hedge -/

open ConditionalColliderRegression

private theorem all_flow_sinks_inspected :
    NodeSet.Subset (keptSinks witness.smallOutcomeFlowNodes witness.smallOutcomeFlowSuccessor) query.condition := by
  intro node selected
  rw [HedgeChannelMarginal.actual_flowSinks_are_condition] at selected
  exact selected

/-- The actual source is the original hedge's stored action root.  Following
its composed flow reaches the conditioned `R(2)` and proves eligibility. -/
def terminalPivot : LatestConditionalPivot graph query witness.actionRoot :=
  witness.latestConditionalPivotOfInspectedSinks all_flow_sinks_inspected

theorem actual_terminal_pivot : terminalPivot.node = collider := by
  decide +kernel

/-- This uses a proved exhausted exchange search on the genuine failed query,
not an invented back-door path at an arbitrary reachable conditioner. -/
def terminalBackdoor : ConditionalBackdoorPath graph query terminalPivot.node :=
  terminalPivot.backdoor no_exchange

theorem actual_terminal_backdoor_codes : terminalBackdoor.path.nodes.map SeparationNode.code = [2, 0] := by
  decide +kernel

end CurrentConditionalFailurePivot
end Examples
end Causality
end Thesis
