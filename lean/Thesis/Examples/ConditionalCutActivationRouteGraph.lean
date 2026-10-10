import Thesis.CausalTransport.ConditionalCutActivationRoute

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalCutActivationRoute

open PathSpecification

/-!
# A genuine cut-path collider at a retained but nonlatest pivot

The five three-valued vertices are `U,Y,P,C,Z`.  Actual arrows are
`U -> P`, `U,Y -> C`, and `P,C -> Z`.  The original conditioners are
`P,Z`.  The actual singleton exchange cut removes `P -> Z`, so
`P <- U -> C <- Y` remains active with collider `C` activated by `C -> Z`.

The retained pivot `P` is not latest: it reaches the later conditioner `Z`
in the larger incoming action cut.  The new construction uses `P` itself
and its exact cut-normal form, not the later pivot or a maximality premise.
This lightweight graph companion checks the actual path and normalization;
its semantic-free route companion checks cut activation and general avoidance.

The action-free query is identifiable.  This is a graph-construction
regression, not a claimed conditional countermodel or numerator failure.
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
      ((parent.val = 2 ∨ parent.val = 3) ∧ child.val = 4))
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

/-- Only the verified finite vertex comparison decides equality. -/
private instance : DecidableEq (SeparationNode signature) := fun left right =>
  if same : SeparationNode.beq left right = true then isTrue ((SeparationNode.beq_eq_true_iff left right).mp same)
  else isFalse (fun equal => same ((SeparationNode.beq_eq_true_iff left right).mpr equal))

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcome
  action := NodeSet.empty
  condition := NodeSet.union (NodeSet.singleton pivotNode) (NodeSet.singleton evidence)
  action_outcome_disjoint := NodeSet.disjoint_empty_left _
  action_condition_disjoint := NodeSet.disjoint_empty_left _
  outcome_condition_disjoint := by unfold NodeSet.Disjoint; decide +kernel

def cut : GraphMutilation signature := .barUnderline query.action (NodeSet.singleton pivotNode)
def given : NodeSet signature := NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton pivotNode))

/-- The original directed edge out of the pivot is genuinely cut.  The
remaining displayed path and its activating suffix use real kept arrows. -/
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

/-- Path activity proves the negative exchange answer without evaluating
the whole moral-graph closure as a second independent finite computation. -/
theorem exchange_test_false : conditionalExchangeTest graph query pivotNode = false := by
  cases answer : conditionalExchangeTest graph query pivotNode with
  | false => rfl
  | true =>
      exact False.elim ((graph.dSeparated_implies_pathDSeparated cut query.outcome
        (NodeSet.singleton pivotNode) given answer)
        ⟨outcome, pivotNode, by decide +kernel, by decide +kernel, ⟨actualPath.reverse⟩⟩)

/-- The general constructor is used at the actual retained pivot `P`,
without a latest-pivot certificate. -/
def normal : ConditionalBackdoorPathNormalForm graph query pivotNode :=
  .ofExchangeTestFalse graph query pivotNode exchange_test_false

theorem normal_window : normal.cutPath.nodes =
    [.observed pivotNode] ++ .observed parent :: .observed collider :: .observed outcome :: [] := by decide +kernel

theorem actual_collider : IsCollider graph cut (.observed parent) (.observed collider) (.observed outcome) := by
  unfold IsCollider
  decide +kernel

end CurrentConditionalCutActivationRoute
end Examples
end Causality
end Thesis
