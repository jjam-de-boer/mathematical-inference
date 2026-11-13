import Thesis.CausalTransport.ConditionalFailureActivationForest

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureActivationForest

open PathSpecification

/-!
# Two genuine collider activations merge under one common policy

The observed graph has `U,V -> C,D -> M -> Z`, and `U -> P`.  Both `C`
and `D` are actual observed colliders with descendant activation at the same
conditioner `Z`.  The other conditioner `P` has no outgoing edges, so it is
the latest conditioner reachable from itself.  A separate isolated action
keeps the incoming-cut graph nonvacuous without cutting an activation edge.

The common policy returns `C -> M -> Z` and `D -> M -> Z`.  It retains both
incoming branches at `M` while giving that vertex just one outgoing successor.
The general complete-path theorem proves equal endpoints after that merge.
Each path's preceding vertices are fully unconditioned, and the omitted pivot
is outside the whole routing domain.  A zero-edge path at `Z` checks stopping
at an already-conditioned source.

These are graph-routing regressions, not a new semantic countermodel or an
assertion of universal IDC failure.  In particular the activation forest is
not substituted for the still-missing combined path/small-forest parity data.
-/

def signature : ObservedSignature where
  count := 8
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val ≤ 1 ∧ (child.val = 2 ∨ child.val = 3)) ∨
      ((parent.val = 2 ∨ parent.val = 3) ∧ child.val = 4) ∨
      (parent.val = 4 ∧ child.val = 5) ∨ (parent.val = 0 ∧ child.val = 6))
  directed_earlier := by
    intro parent child edge
    have endpoints := of_decide_eq_true edge
    omega

def leftParent : Fin signature.count := ⟨0, by decide⟩
def rightParent : Fin signature.count := ⟨1, by decide⟩
def leftCollider : Fin signature.count := ⟨2, by decide⟩
def rightCollider : Fin signature.count := ⟨3, by decide⟩
def mergeNode : Fin signature.count := ⟨4, by decide⟩
def conditionNode : Fin signature.count := ⟨5, by decide⟩
def pivotNode : Fin signature.count := ⟨6, by decide⟩
def actionNode : Fin signature.count := ⟨7, by decide⟩

def graph : ObservedGraph signature where
  bidirected := fun _ _ => false
  bidirected_symmetric := by intro _ _ edge; cases edge
  bidirected_irreflexive := fun _ => rfl

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton rightParent
  action := NodeSet.singleton actionNode
  condition := NodeSet.union (NodeSet.singleton conditionNode) (NodeSet.singleton pivotNode)
  action_outcome_disjoint := by unfold NodeSet.Disjoint; decide +kernel
  action_condition_disjoint := by unfold NodeSet.Disjoint; decide +kernel
  outcome_condition_disjoint := by unfold NodeSet.Disjoint; decide +kernel

def pivot : LatestConditionalPivot graph query pivotNode :=
  .ofReachableConditioner graph query pivotNode pivotNode (by decide +kernel) (by decide +kernel)

def forest : ConditionalColliderActivationForest query pivot.node := .ofLatestPivot pivot

/-- These are actual colliders of the action-cut graph, not merely two
vertices chosen as the starts of otherwise unrelated directed routes. -/
theorem actual_colliders :
    IsCollider graph (GraphMutilation.bar query.action)
      (.observed leftParent) (.observed leftCollider) (.observed rightParent) ∧
    IsCollider graph (GraphMutilation.bar query.action)
      (.observed leftParent) (.observed rightCollider) (.observed rightParent) := by
  unfold IsCollider
  decide +kernel

def leftActivation : ConditionalColliderActivationRoute query pivot.node leftCollider where
  before := [leftCollider, mergeNode]
  endpoint := conditionNode
  endpoint_condition := by decide +kernel
  endpoint_ne_pivot := by decide +kernel
  starts := rfl
  simple := by decide +kernel
  consecutive := by decide +kernel
  action_free := by decide +kernel
  before_given_free := by decide +kernel

def rightActivation : ConditionalColliderActivationRoute query pivot.node rightCollider where
  before := [rightCollider, mergeNode]
  endpoint := conditionNode
  endpoint_condition := by decide +kernel
  endpoint_ne_pivot := by decide +kernel
  starts := rfl
  simple := by decide +kernel
  consecutive := by decide +kernel
  action_free := by decide +kernel
  before_given_free := by decide +kernel

def leftPath := forest.path leftCollider (forest.contains_activation leftCollider leftActivation)
def rightPath := forest.path rightCollider (forest.contains_activation rightCollider rightActivation)

theorem actual_path_codes : leftPath.nodes.map Fin.val = [2, 4, 5] ∧ rightPath.nodes.map Fin.val = [3, 4, 5] := by
  decide +kernel

/-- Both declared incoming branches remain, but the shared vertex's common
outgoing map value is installed only once.  Stopping at `Z` is genuine. -/
theorem actual_merge_successors :
    forest.successor leftCollider = some mergeNode ∧ forest.successor rightCollider = some mergeNode ∧
    forest.successor mergeNode = some conditionNode ∧ forest.successor conditionNode = none := by
  decide +kernel

theorem merged_paths_have_same_endpoint : leftPath.endpoint = rightPath.endpoint :=
  forest.path_endpoints_eq_of_shared leftCollider rightCollider
    (forest.contains_activation leftCollider leftActivation) (forest.contains_activation rightCollider rightActivation)
    mergeNode (by decide +kernel) (by decide +kernel)

/-- Full conditioning freedom is obtained from the common policy theorem,
not by separately deciding the displayed path's two intermediate labels. -/
theorem preceding_vertices_unconditioned (node : Fin signature.count)
    (member : node ∈ leftPath.nodes) (notEndpoint : node ≠ leftPath.endpoint) : query.condition node = false :=
  forest.path_before_condition_free leftCollider (forest.contains_activation leftCollider leftActivation) node member notEndpoint

theorem omitted_pivot_outside_domain : forest.nodes pivot.node = false := forest.pivot_free

def zeroPath := forest.path conditionNode (by decide +kernel)

theorem already_conditioned_source_stops : zeroPath.nodes.map Fin.val = [5] := by decide +kernel

end CurrentConditionalFailureActivationForest
end Examples
end Causality
end Thesis
