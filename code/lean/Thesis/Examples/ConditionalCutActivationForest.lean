import Thesis.CausalTransport.ConditionalCutActivationForest
import Thesis.Examples.ConditionalCutActivationRoute

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalCutActivationRoute

open PathSpecification HedgeChannelInstallation

/-!
# A complete common cut policy at a genuinely nonlatest pivot

The route regression already proves that the older universal bar forest
cannot exist at this original pivot.  The narrower cut interface does exist:
its constructor computes one policy and covers the actual normalized collider.
Its complete path is `C -> Z`, and the general normalized-path avoidance
theorem applies with no original-graph latest certificate.

The policy also contains the irrelevant ancestor `U`, whose complete trace
is `U -> C -> Z`.  The two paths genuinely merge at `C` and retain the same
successor and conditioned sink.  `U` is a noncollider of the normalized path;
this is deliberate evidence that the auxiliary domain is not itself the
eventual interaction selection.  Only the actual collider trace is asserted
to avoid that path away from its source.

The independent already-conditioned fixture checks a zero-edge common
trace.  These are original three-valued graph regressions, not supplied
conditional countermodels or claims of universal conditional completeness.
-/

/-- This common forest exists even though `old_bar_forest_impossible`
rules out the larger bar-route interface at the same original pivot. -/
def cutForest : ConditionalCutColliderActivationForest query pivotNode :=
  .ofRetainedPivot graph query pivotNode (by decide +kernel)

/-- The actual window supplies coverage; the constructor does not request
an independently chosen collider path or a selected-domain flag. -/
def cutForestPath : SuccessorPath cutForest.nodes cutForest.successor collider :=
  normal.cutActivationForestPath cutForest (by decide +kernel) [.observed pivotNode] [] (.observed parent) (.observed outcome)
    collider normal_window actual_collider

theorem cutForestPath_codes : cutForestPath.nodes.map Fin.val = [3, 4] := by decide +kernel

theorem cutForest_original_wellFormed : childWellFormedBool cutForest.nodes cutForest.successor = true :=
  cutForest.wellFormed

theorem cutForest_pivot_avoided : cutForest.nodes pivotNode = false := cutForest.pivot_free

/-- The complete shared-policy path inherits avoidance at this nonlatest
pivot; its endpoint and all intermediate vertices are retained. -/
theorem cutForest_actual_normal_intersection (node : Fin signature.count)
    (onRoute : node ∈ cutForestPath.nodes) (onPath : .observed node ∈ normal.cutPath.nodes) : node = collider :=
  normal.cut_activation_forest_path_intersection_eq_collider cutForest (by decide +kernel)
    [.observed pivotNode] [] (.observed parent) (.observed outcome) collider normal_window actual_collider node onRoute onPath

/-- The generous auxiliary domain includes this irrelevant path fork.
No domain-wide avoidance theorem is being asserted. -/
theorem cutForest_contains_path_fork : cutForest.nodes parent = true := by decide +kernel

def cutForestAncestorPath : SuccessorPath cutForest.nodes cutForest.successor parent :=
  cutForest.path parent cutForest_contains_path_fork

theorem cutForestAncestorPath_codes : cutForestAncestorPath.nodes.map Fin.val = [0, 3, 4] := by decide +kernel

/-- The two real traces merge at `C`.  Complete-path determinism gives
their common sink, rather than a uniqueness assumption on incoming parents. -/
theorem cutForest_merged_endpoints : cutForestAncestorPath.endpoint = cutForestPath.endpoint := by
  apply cutForest.path_endpoints_eq_of_shared parent collider cutForest_contains_path_fork
    (cutForest.contains_activation collider activation) collider
  · decide +kernel
  · decide +kernel

theorem cutForest_actual_cut_arrow : graph.expandedMutilatedEdge cut (.observed collider) (.observed evidence) = true :=
  cutForest.successor_cut_edge graph collider evidence (by decide +kernel)

end CurrentConditionalCutActivationRoute

namespace CurrentConditionalCutActivationRouteZero

open PathSpecification HedgeChannelInstallation CurrentConditionalFailureActivationAvoidanceZero

/-- The same policy constructor permits an already-conditioned collider
to stop immediately, retaining its original row as a singleton trace. -/
def cutForest : ConditionalCutColliderActivationForest query pivot.node :=
  .ofRetainedPivot graph query pivot.node pivot.selected

def cutForestPath : SuccessorPath cutForest.nodes cutForest.successor collider :=
  normal.cutActivationForestPath cutForest pivot.selected [.observed pivotNode] [] (.observed parent) (.observed outcome)
    collider normal_window actual_collider

theorem cutForestPath_codes : cutForestPath.nodes.map Fin.val = [3] := by decide +kernel

theorem cutForestPath_stopped : cutForest.successor collider = none := by decide +kernel

/-- The zero-edge trace keeps precisely its allowed source intersection. -/
theorem cutForest_actual_normal_intersection (node : Fin signature.count)
    (onRoute : node ∈ cutForestPath.nodes) (onPath : .observed node ∈ normal.cutPath.nodes) : node = collider :=
  normal.cut_activation_forest_path_intersection_eq_collider cutForest pivot.selected
    [.observed pivotNode] [] (.observed parent) (.observed outcome) collider normal_window actual_collider node onRoute onPath

end CurrentConditionalCutActivationRouteZero
end Examples
end Causality
end Thesis
