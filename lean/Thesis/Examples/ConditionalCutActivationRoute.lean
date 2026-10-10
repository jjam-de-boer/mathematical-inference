import Thesis.CausalTransport.ConditionalFailureActivationAvoidance
import Thesis.Examples.ConditionalCutActivationRouteGraph
import Thesis.Examples.ConditionalFailureActivationAvoidanceZero

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalCutActivationRoute

open PathSpecification

/-!
# Cut activation and normalized-path avoidance without a latest pivot

The graph companion supplies the actual cut-normalized collider at `P`,
even though `P -> Z` reaches a later original conditioner.  The general
cut-activity constructor returns `C -> Z` with every arrow certified in
the exact comparison graph.  Pivot avoidance and freedom of all preceding
conditioned coordinates are theorems of that route, not maximality flags.

The older full-bar activation forest cannot exist at this nonlatest pivot:
its coverage interface would also cover the bar route `P -> Z`, forcing
the omitted pivot into a domain required to avoid it.  This explains why a
future common cut-policy forest needs cut-route or actual-seed coverage;
it cannot simply be substituted into the older stronger interface.

The independent already-conditioned fixture checks the same constructor
on a zero-edge activation.  All regressions retain original three-valued
alphabets and use the general avoidance theorem.  Neither fixture has a
joint hedge or supplies a conditional nonidentifiability claim.
-/

/-- The actual normal-form collider supplies its own cut activity and
action freedom to the constructor.  No additional activation proof is passed. -/
def activation : ConditionalCutColliderActivationRoute graph query pivotNode collider :=
  normal.cutColliderActivationRoute (by decide +kernel) [.observed pivotNode] [] (.observed parent) (.observed outcome)
    collider normal_window actual_collider

theorem activation_codes : (activation.before ++ [activation.endpoint]).map Fin.val = [3, 4] := by decide +kernel

/-- The pivot really is nonlatest under the original incoming cut.  This
case cannot be represented by the former latest-pivot-only route API. -/
theorem pivot_not_latest : ¬ (Exists fun latest : LatestConditionalPivot graph query pivotNode => latest.node = pivotNode) := by
  rintro ⟨latest, same⟩
  have reaches : FiniteReachability.within finBeq (NodeSet.enumerated signature)
      (mutilatedDirected signature query.action) signature.count pivotNode evidence = true := by decide +kernel
  have bound := latest.latest evidence (by decide +kernel) reaches
  rw [same] at bound
  change 4 ≤ 2 at bound
  omega

/-- The larger bar graph reaches `Z` from `P`, but the actual outgoing
cut removes that route.  The new observed search relation retains this cut. -/
theorem exact_cut_blocks_pivot_route :
    FiniteReachability.within finBeq (NodeSet.enumerated signature)
      (mutilatedDirected signature query.action) signature.count pivotNode evidence = true ∧
    FiniteReachability.within finBeq (NodeSet.enumerated signature)
      (ConditionalCutActivationRouting.observedEdge query pivotNode) signature.count pivotNode evidence = false := by
  decide +kernel

theorem actual_pivot_avoided : pivotNode ∉ activation.before ++ [activation.endpoint] := activation.pivot_not_mem

theorem actual_prefix_condition_free (node : Fin signature.count) (member : node ∈ activation.before) :
    query.condition node = false := activation.before_condition_free node member

/-- Actual cut-route avoidance applies at this genuinely nonlatest pivot.
It does not ask for a second selected return, route-avoidance or parity flag. -/
theorem actual_normal_intersection (node : Fin signature.count)
    (onRoute : node ∈ activation.before ++ [activation.endpoint])
    (onPath : .observed node ∈ normal.cutPath.nodes) : node = collider :=
  normal.cut_activation_path_intersection_eq_collider [.observed pivotNode] [] (.observed parent) (.observed outcome)
    collider normal_window actual_collider activation node onRoute onPath

/-- This allowed bar-route API witness actually passes through the omitted
pivot.  It is deliberately not declared to be an actual path collider. -/
def barRouteFromPivot : ConditionalColliderActivationRoute query pivotNode pivotNode where
  before := [pivotNode]
  endpoint := evidence
  endpoint_condition := by decide +kernel
  endpoint_ne_pivot := by decide +kernel
  starts := rfl
  simple := by decide +kernel
  consecutive := by decide +kernel
  action_free := by decide +kernel
  before_given_free := by decide +kernel

/-- The older forest's universal bar-route coverage is too strong here:
it would select its excluded pivot.  A common cut forest must have the
correct narrower graph interface, not an asserted impossible constructor. -/
theorem old_bar_forest_impossible : ¬ Nonempty (ConditionalColliderActivationForest query pivotNode) := by
  rintro ⟨forest⟩
  have covered := forest.contains_activation pivotNode barRouteFromPivot
  rw [forest.pivot_free] at covered
  cases covered

end CurrentConditionalCutActivationRoute

namespace CurrentConditionalCutActivationRouteZero

open CurrentConditionalFailureActivationAvoidanceZero

/-- Cut activity supplies the same actual zero-edge activation without
using the existing latest-pivot certificate of the fixture. -/
def activation : ConditionalCutColliderActivationRoute graph query pivot.node collider :=
  normal.cutColliderActivationRoute pivot.selected [.observed pivotNode] [] (.observed parent) (.observed outcome)
    collider normal_window actual_collider

theorem activation_codes : (activation.before ++ [activation.endpoint]).map Fin.val = [3] := by decide +kernel

/-- The already-conditioned source is retained as the permitted own
intersection; no invented directed suffix or distinct-source premise occurs. -/
theorem actual_normal_intersection (node : Fin signature.count)
    (onRoute : node ∈ activation.before ++ [activation.endpoint])
    (onPath : .observed node ∈ normal.cutPath.nodes) : node = collider :=
  normal.cut_activation_path_intersection_eq_collider [.observed pivotNode] [] (.observed parent) (.observed outcome)
    collider normal_window actual_collider activation node onRoute onPath

end CurrentConditionalCutActivationRouteZero
end Examples
end Causality
end Thesis
