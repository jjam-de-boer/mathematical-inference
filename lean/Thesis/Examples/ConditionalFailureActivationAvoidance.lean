import Thesis.CausalTransport.ConditionalFailureActivationAvoidance

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureActivationAvoidance

open PathSpecification

/-!
# Actual normalized collider activations avoid the rest of their path

The graph has `U(0) -> P(2)`, `U(0),Y(1) -> C(3) -> Z(4)`.
For the query with conditioners `P,Z`, the retained-pivot path is
`P <- U -> C <- Y`, with `C` activated by `Z`.  The latest conditioner
reachable from `P` is `P` itself: `P` has no outgoing arrows.  The general
normal-form constructor supplies the displayed path, and its actual common
activation policy supplies `C -> Z`.  The proved intersection theorem,
not a fixture-specific assertion of disjointness, excludes `Z` from the path.

The auxiliary forest domain deliberately also contains `U` and `Y`, which
are ancestors of `Z` on the path.  Thus avoiding the path is a theorem about
the actual collider's activation trace, not about the entire auxiliary domain.

The companion `ConditionalFailureActivationAvoidanceZero` regression checks
an already-conditioned collider on a smaller independent signature.  Splitting
the two executable normalization checks keeps their individual kernel checks
small; it does not weaken either application of the general theorem.

This signature uses the original three-valued alphabets.  This is a graph
normalization regression, not a claim of joint ID failure or a conditional
counterexample: the action-free query is observationally identifiable.
-/

def signature : ObservedSignature where
  count := 5
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val = 0 ∧ child.val = 2) ∨
      ((parent.val = 0 ∨ parent.val = 1) ∧ child.val = 3) ∨
      (parent.val = 3 ∧ child.val = 4))
  directed_earlier := by intro parent child edge; have parts := of_decide_eq_true edge; omega

def parent : Fin signature.count := ⟨0, by decide⟩
def outcome : Fin signature.count := ⟨1, by decide⟩
def pivotNode : Fin signature.count := ⟨2, by decide⟩
def collider : Fin signature.count := ⟨3, by decide⟩
def evidence : Fin signature.count := ⟨4, by decide⟩

def graph : ObservedGraph signature where
  bidirected := fun _ _ => false
  bidirected_symmetric := by intro _ _ edge; cases edge
  bidirected_irreflexive := fun _ => rfl

/-- Finite verified vertex equality supports only the explicit list checks
below.  It is not a classical equality instance for the path constructors. -/
private instance : DecidableEq (SeparationNode signature) := fun left right =>
  if equal : SeparationNode.beq left right = true then
    isTrue ((SeparationNode.beq_eq_true_iff left right).mp equal)
  else isFalse (fun same => equal ((SeparationNode.beq_eq_true_iff left right).mpr same))

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcome
  action := NodeSet.empty
  condition := NodeSet.union (NodeSet.singleton pivotNode) (NodeSet.singleton evidence)
  action_outcome_disjoint := NodeSet.disjoint_empty_left _
  action_condition_disjoint := NodeSet.disjoint_empty_left _
  outcome_condition_disjoint := by unfold NodeSet.Disjoint; decide +kernel

def cut : GraphMutilation signature := .barUnderline query.action (NodeSet.singleton pivotNode)
def given : NodeSet signature := NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton pivotNode))

def actualPath : ActivePath graph cut given (.observed pivotNode) (.observed outcome) where
  nodes := [.observed pivotNode, .observed parent, .observed collider, .observed outcome]
  starts := rfl
  finishes := rfl
  simple := by decide +kernel
  adjacent := by refine ⟨Or.inr ?_, Or.inl ?_, Or.inr ?_, True.intro⟩ <;> decide +kernel
  source_open := by decide +kernel
  target_open := by decide +kernel
  internal_active := .step
    (Or.inr ⟨graph.not_collider_of_outgoing cut (by decide +kernel), by unfold NonColliderOpen; decide +kernel⟩)
    (.step (Or.inl ⟨⟨by decide +kernel, by decide +kernel⟩,
      graph.ancestorOf_prepend cut given (middle := .observed evidence) (by decide +kernel)
        (graph.ancestorOf_target cut given (target := evidence) (by decide +kernel))⟩)
      (.pair (.observed collider) (.observed outcome)))

/-- The negative exchange test follows from a certified active path, not
from an expensive evaluation of moral-graph closure in this regression. -/
theorem exchange_test_false : conditionalExchangeTest graph query pivotNode = false := by
  cases answer : conditionalExchangeTest graph query pivotNode with
  | false => rfl
  | true =>
      exact False.elim ((graph.dSeparated_implies_pathDSeparated cut query.outcome
        (NodeSet.singleton pivotNode) given answer)
        ⟨outcome, pivotNode, by decide +kernel, by decide +kernel, ⟨actualPath.reverse⟩⟩)

def pivot : LatestConditionalPivot graph query pivotNode :=
  .ofReachableConditioner graph query pivotNode pivotNode (by decide +kernel) (by decide +kernel)

theorem pivot_eq : pivot.node = pivotNode := by decide +kernel

def normal : ConditionalBackdoorPathNormalForm graph query pivot.node :=
  .ofExchangeTestFalse graph query pivot.node (by simpa only [pivot_eq] using exchange_test_false)

theorem normal_window : normal.cutPath.nodes =
    [.observed pivotNode] ++ .observed parent :: .observed collider :: .observed outcome :: [] := by decide +kernel

theorem actual_collider : IsCollider graph
    (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node))
    (.observed parent) (.observed collider) (.observed outcome) := by
  unfold IsCollider
  decide +kernel

def forest : ConditionalColliderActivationForest query pivot.node := .ofLatestPivot pivot

def activation := normal.activationForestPath pivot forest [.observed pivotNode] []
  (.observed parent) (.observed outcome) collider normal_window actual_collider

theorem activation_codes : activation.nodes.map Fin.val = [3, 4] := by decide +kernel

/-- The actual complete path gets its intersection property from the
general first-intersection theorem, including both possible return orders. -/
theorem intersection_is_own_collider (node : Fin signature.count) (onRoute : node ∈ activation.nodes)
    (onPath : .observed node ∈ normal.cutPath.nodes) : node = collider :=
  normal.activation_forest_path_intersection_eq_collider pivot forest [.observed pivotNode] []
    (.observed parent) (.observed outcome) collider normal_window actual_collider node onRoute onPath

theorem endpoint_not_on_path : Not (.observed evidence ∈ normal.cutPath.nodes) := by
  intro onPath
  have same := intersection_is_own_collider evidence (by decide +kernel) onPath
  exact (by decide +kernel : evidence ≠ collider) same

/-- The whole auxiliary domain really overlaps the selected path.  A
future interaction-row selection must use the actual branch traces rather
than misreading the new avoidance theorem as domain-wide disjointness. -/
theorem auxiliary_domain_overlaps_path : forest.nodes parent = true ∧ .observed parent ∈ normal.cutPath.nodes := by
  rw [normal_window]
  decide +kernel

end CurrentConditionalFailureActivationAvoidance
end Examples
end Causality
end Thesis
