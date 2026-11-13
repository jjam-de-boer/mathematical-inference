import Thesis.CausalTransport.ConditionalFailureActivationAvoidance

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureActivationAvoidanceZero

open PathSpecification

/-!
# An already-conditioned collider has the permitted source intersection

The four-vertex graph has `U(0) -> P(2)` and `U(0),Y(1) -> C(3)`.
For conditioners `P,C`, the retained-pivot path is `P <- U -> C <- Y`.
The collider `C` is itself conditioned, so its complete common-policy
activation trace is `[C]`: no extra edge or endpoint distinct from the
source is required.  The general avoidance theorem allows precisely this
intersection, rather than incorrectly asserting empty intersection.

This independent, smaller fixture complements the nonzero activation in
`ConditionalFailureActivationAvoidance`.  Each module computes only its own
finite normal form, keeping the kernel checks suitable for capped local
verification.  The original alphabets remain three-valued.  The action-free
query is observationally identifiable; this tests graph normalization and
route adaptation, not a conditional counterexample or an ID failure.
-/

def signature : ObservedSignature where
  count := 4
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val = 0 ∧ child.val = 2) ∨
      ((parent.val = 0 ∨ parent.val = 1) ∧ child.val = 3))
  directed_earlier := by intro parent child edge; have parts := of_decide_eq_true edge; omega

def parent : Fin signature.count := ⟨0, by decide⟩
def outcome : Fin signature.count := ⟨1, by decide⟩
def pivotNode : Fin signature.count := ⟨2, by decide⟩
def collider : Fin signature.count := ⟨3, by decide⟩

def graph : ObservedGraph signature where
  bidirected := fun _ _ => false
  bidirected_symmetric := by intro _ _ edge; cases edge
  bidirected_irreflexive := fun _ => rfl

/-- Equality is decided by the verified finite vertex comparison.  No
classical equality instance is used by the explicit list regressions. -/
private instance : DecidableEq (SeparationNode signature) := fun left right =>
  if equal : SeparationNode.beq left right = true then
    isTrue ((SeparationNode.beq_eq_true_iff left right).mp equal)
  else isFalse (fun same => equal ((SeparationNode.beq_eq_true_iff left right).mpr same))

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcome
  action := NodeSet.empty
  condition := NodeSet.union (NodeSet.singleton pivotNode) (NodeSet.singleton collider)
  action_outcome_disjoint := NodeSet.disjoint_empty_left _
  action_condition_disjoint := NodeSet.disjoint_empty_left _
  outcome_condition_disjoint := by unfold NodeSet.Disjoint; decide +kernel

def cut : GraphMutilation signature := .barUnderline query.action (NodeSet.singleton pivotNode)
def given : NodeSet signature := NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton pivotNode))

/-- The collider is activated by membership in the given set itself.
There is no invented directed suffix beyond this already-conditioned node. -/
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
      graph.ancestorOf_target cut given (target := collider) (by decide +kernel)⟩)
      (.pair (.observed collider) (.observed outcome)))

/-- Derive the negative exchange answer from actual path activity rather
than recomputing the full moral-graph closure in this finite regression. -/
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

theorem activation_codes : activation.nodes.map Fin.val = [3] := by decide +kernel

/-- The zero-edge trace has a real source intersection.  The universal
theorem must retain it, even though the source is also a conditioner. -/
theorem source_intersection_allowed : collider ∈ activation.nodes ∧
    .observed collider ∈ normal.cutPath.nodes ∧ query.condition collider = true := by
  rw [normal_window]
  decide +kernel

/-- This is the same general theorem used for a nonzero activation; no
special source-distinct-from-endpoint hypothesis is supplied. -/
theorem intersection_is_own_collider (node : Fin signature.count) (onRoute : node ∈ activation.nodes)
    (onPath : .observed node ∈ normal.cutPath.nodes) : node = collider :=
  normal.activation_forest_path_intersection_eq_collider pivot forest [.observed pivotNode] []
    (.observed parent) (.observed outcome) collider normal_window actual_collider node onRoute onPath

end CurrentConditionalFailureActivationAvoidanceZero
end Examples
end Causality
end Thesis
