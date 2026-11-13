import Thesis.CausalTransport.ConditionalFailureActivation
import Thesis.Examples.ConditionalFailurePaths

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureActivation

/-!
# Regression checks for actual collider-activation routes

The first fixture reuses an active back-door path whose collider is activated
by a conditioned descendant, not by its own membership in the given-set.  The
route constructor obtains that activation from the actual path window.
The second check permits the essential zero-edge case: an already conditioned
collider is its own activating endpoint.

The final fixture retains a nonempty intervention and exhibits an activation
branch passing through the omitted back-door pivot.  IDC conditions on all
*other* conditioners while testing that pivot, so such a branch is legal.
This checks a boundary that the universal parity-network construction must
handle; activation alone must not invent pivot avoidance or forest disjointness.
No fixture asserts conditional non-identifiability merely from an active path.
-/

open PathSpecification
open CurrentConditionalFailurePaths

/-! ## A descendant activates the actual path collider -/

def descendantCollider : Fin colliderSignature.count := ⟨3, by decide⟩
def descendantEndpoint : Fin colliderSignature.count := ⟨4, by decide⟩
def descendantParent : Fin colliderSignature.count := ⟨0, by decide⟩

private theorem descendant_window : colliderBackdoor.path.nodes =
    [.observed colliderConditioner, .observed descendantParent,
      .observed descendantCollider, .observed colliderOutcome] := by
  apply (List.map_inj_right SeparationNode.code_injective).mp
  exact collider_path_codes

/-- The actual triple's activity supplies descendant ancestry; no separate
activation or action-avoidance premise is fed to the route constructor. -/
def descendantRoute : ConditionalColliderActivationRoute
    colliderQuery colliderConditioner descendantCollider :=
  colliderBackdoor.colliderActivationRoute [.observed colliderConditioner] []
    (.observed descendantParent) (.observed colliderOutcome) descendantCollider
    descendant_window (by constructor <;> decide +kernel)

theorem descendant_route_codes :
    (descendantRoute.before ++ [descendantRoute.endpoint]).map Fin.val = [3, 4] := by
  decide +kernel

theorem descendant_endpoint_given : colliderQuery.condition descendantRoute.endpoint = true :=
  descendantRoute.endpoint_condition

theorem descendant_preceding_vertices_open (node : Fin colliderSignature.count)
    (member : node ∈ descendantRoute.before) :
    NodeSet.diff colliderQuery.condition (NodeSet.singleton colliderConditioner) node = false :=
  descendantRoute.before_given_free node member

/-! ## An already conditioned collider has a zero-edge activation branch -/

def conditionedColliderQuery : ConditionalKernelQuery colliderSignature where
  outcome := NodeSet.singleton colliderOutcome
  action := NodeSet.empty
  condition := fun node => decide (node.val = 1 ∨ node.val = 3)
  action_outcome_disjoint := NodeSet.disjoint_empty_left _
  action_condition_disjoint := NodeSet.disjoint_empty_left _
  outcome_condition_disjoint := by
    apply (NodeSet.disjointBool_eq_true_iff _ _).mp
    decide +kernel

def zeroEdgeRoute : ConditionalColliderActivationRoute
    conditionedColliderQuery colliderConditioner descendantCollider :=
  .ofAncestor colliderGraph conditionedColliderQuery colliderConditioner descendantCollider rfl
    (colliderGraph.ancestorOf_target _ _ (by decide +kernel))

theorem zero_edge_route_codes :
    (zeroEdgeRoute.before ++ [zeroEdgeRoute.endpoint]).map Fin.val = [3] := by
  decide +kernel

/-! ## The omitted pivot may occur inside an activation branch -/

/-- Parents `0,1 -> C(2)`, `0 -> Z(3)`, and `C -> Z -> D(4)`.
The isolated action `A(5)` remains present in the query.  Given `D`, the path
`Z <- 0 -> C <- 1` is active even though `C`'s activation passes through `Z`.
The route API does not require this path to be the shortest active path. -/
def pivotSignature : ObservedSignature where
  count := 6
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val < 2 ∧ child.val = 2) ∨ (parent.val = 0 ∧ child.val = 3) ∨
      (parent.val = 2 ∧ child.val = 3) ∨ (parent.val = 3 ∧ child.val = 4))
  directed_earlier := by
    intro parent child edge
    have endpoints := of_decide_eq_true edge
    omega

def pivotGraph : ObservedGraph pivotSignature where
  bidirected := fun _ _ => false
  bidirected_symmetric := by intro _ _ edge; cases edge
  bidirected_irreflexive := by intro _; rfl

def pivotParent : Fin pivotSignature.count := ⟨0, by decide⟩
def pivotOutcome : Fin pivotSignature.count := ⟨1, by decide⟩
def pivotCollider : Fin pivotSignature.count := ⟨2, by decide⟩
def pivotNode : Fin pivotSignature.count := ⟨3, by decide⟩
def pivotEndpoint : Fin pivotSignature.count := ⟨4, by decide⟩
def pivotAction : Fin pivotSignature.count := ⟨5, by decide⟩

def pivotQuery : ConditionalKernelQuery pivotSignature where
  outcome := NodeSet.singleton pivotOutcome
  action := NodeSet.singleton pivotAction
  condition := fun node => decide (node.val = 3 ∨ node.val = 4)
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := by
    apply (NodeSet.disjointBool_eq_true_iff _ _).mp
    decide +kernel
  outcome_condition_disjoint := by
    apply (NodeSet.disjointBool_eq_true_iff _ _).mp
    decide +kernel

/-- Display the legal, nonminimal active path explicitly.  Its collider's
activation is allowed to return to the path's first vertex before reaching
the other conditioner.  No simple-route claim is transferred across that
intersection: the path and its activation branch are certified separately. -/
def pivotBackdoor : ConditionalBackdoorPath pivotGraph pivotQuery pivotNode where
  outcome := pivotOutcome
  outcome_selected := by decide +kernel
  path := {
    nodes := [.observed pivotNode, .observed pivotParent, .observed pivotCollider, .observed pivotOutcome]
    starts := rfl
    finishes := rfl
    simple := by simp [List.nodup_cons, pivotNode, pivotParent, pivotCollider, pivotOutcome]
    adjacent := ⟨Or.inr (by decide +kernel), Or.inl (by decide +kernel),
      Or.inr (by decide +kernel), True.intro⟩
    source_open := by decide +kernel
    target_open := by decide +kernel
    internal_active := .step
      ((TripleActive_iff_tripleActiveBool _ _ _ _ _ _).mpr (by decide +kernel))
      (.step ((TripleActive_iff_tripleActiveBool _ _ _ _ _ _).mpr (by decide +kernel))
        (.pair (.observed pivotCollider) (.observed pivotOutcome)))
  }
  first := .observed pivotParent
  rest := [.observed pivotCollider, .observed pivotOutcome]
  nodes_eq := rfl
  first_incoming := by decide +kernel

def pivotRoute : ConditionalColliderActivationRoute pivotQuery pivotNode pivotCollider :=
  pivotBackdoor.colliderActivationRoute [.observed pivotNode] [] (.observed pivotParent)
    (.observed pivotOutcome) pivotCollider rfl (by constructor <;> decide +kernel)

theorem pivot_route_codes :
    (pivotRoute.before ++ [pivotRoute.endpoint]).map Fin.val = [2, 3, 4] := by
  decide +kernel

/-- The route really passes a queried conditioner that the exchange test
omits.  Claiming that every preceding vertex avoids the *full* condition set
would be incorrect, even with genuine action-cut ancestry. -/
theorem omitted_pivot_is_preceding_and_conditioned :
    pivotNode ∈ pivotRoute.before ∧ pivotQuery.condition pivotNode = true := by
  decide +kernel

theorem pivot_route_avoids_nonempty_action (node : Fin pivotSignature.count)
    (member : node ∈ pivotRoute.before ++ [pivotRoute.endpoint]) : pivotQuery.action node = false :=
  pivotRoute.action_free node member

end CurrentConditionalFailureActivation
end Examples
end Causality
end Thesis
