import Thesis.CausalTransport.ConditionalFailureActivationSelection

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureActivationSelection

open PathSpecification

/-!
# Original graph data for the Small-overlap selection regression

The five three-valued vertices are `X,Y,C,Z,P`.  The actual arrows are
`X -> P`, `Y -> C -> Z`; the original bidirected pairs are `X <-> P`,
`P <-> C`, and `C <-> Z`.  The displayed hedge for the unchanged numerator
of `P(Y | do(X), P,Z)` has Small `C,Z,P` and roots `Z,P`.

This light graph-data module checks its finite hedge certificates, an actual
active path, and the latest-pivot certificates.  It constructs the general
normal form but does not evaluate its exhaustive search.  Its separate
`ConditionalFailureActivationSelection` companion proves the structural
selection facts and builds a genuine positive conditional countermodel from
the complete Small phase.  Separating graph and semantic checks keeps each
local verification within the fixed memory cap.
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
    ((parent.val = 0 ∧ child.val = 4) ∨ (parent.val = 1 ∧ child.val = 2) ∨
      (parent.val = 2 ∧ child.val = 3))
  directed_earlier := by intro parent child edge; have parts := of_decide_eq_true edge; omega

def actionNode : Fin signature.count := ⟨0, by decide⟩
def outcome : Fin signature.count := ⟨1, by decide⟩
def collider : Fin signature.count := ⟨2, by decide⟩
def evidence : Fin signature.count := ⟨3, by decide⟩
def pivotNode : Fin signature.count := ⟨4, by decide⟩

private def pairMask (left right : Fin signature.count) : Bool :=
  decide ((left.val = 0 ∧ right.val = 4) ∨ (left.val = 2 ∧ right.val = 4) ∨
    (left.val = 2 ∧ right.val = 3))

def graph : ObservedGraph signature where
  bidirected := fun left right => pairMask left right || pairMask right left
  bidirected_symmetric := by intro _ _ selected; simpa only [Bool.or_comm] using selected
  bidirected_irreflexive := by
    intro node
    have absent : pairMask node node = false := by unfold pairMask; apply decide_eq_false; omega
    simp only [absent, Bool.false_or]

private instance : DecidableEq (SeparationNode signature) := fun left right =>
  if equal : SeparationNode.beq left right = true then
    isTrue ((SeparationNode.beq_eq_true_iff left right).mp equal)
  else isFalse (fun same => equal ((SeparationNode.beq_eq_true_iff left right).mpr same))

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcome
  action := NodeSet.singleton actionNode
  condition := NodeSet.union (NodeSet.singleton pivotNode) (NodeSet.singleton evidence)
  action_outcome_disjoint := by unfold NodeSet.Disjoint; decide +kernel
  action_condition_disjoint := by unfold NodeSet.Disjoint; decide +kernel
  outcome_condition_disjoint := by unfold NodeSet.Disjoint; decide +kernel

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := by intro _ same; have values := congrArg Fin.val same; cases values

def small : NodeSet signature := fun node => decide (2 ≤ node.val)
def large : NodeSet signature := NodeSet.union small (NodeSet.singleton actionNode)
def child : ForestChild signature := fun node =>
  if node = actionNode then some pivotNode else if node = collider then some evidence else none
def selection : HedgeSelection signature := ⟨large, small, child⟩

theorem hedge_tests : hedgeTestsHold graph query.jointNumerator selection = true := by decide +kernel

def witness : HedgeWitness graph query.jointNumerator :=
  hedgeWitness_of_sets graph query.jointNumerator selection hedge_tests

/-- The displayed pivot is the actual stored action root in Small, not
an unrelated starting node supplied only for the activation regression. -/
theorem action_root_eq : witness.actionRoot = pivotNode := by decide +kernel

def cut : GraphMutilation signature := .barUnderline query.action (NodeSet.singleton pivotNode)
def given : NodeSet signature := NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton pivotNode))
def shared : SeparationNode signature := .latentPair collider pivotNode

/-- The path uses an original pair root, not an observed replacement for
that input or a new switching variable shared with every child. -/
def actualPath : ActivePath graph cut given (.observed pivotNode) (.observed outcome) where
  nodes := [.observed pivotNode, shared, .observed collider, .observed outcome]
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

theorem exchange_test_false : conditionalExchangeTest graph query pivotNode = false := by
  cases answer : conditionalExchangeTest graph query pivotNode with
  | false => rfl
  | true =>
      exact False.elim ((graph.dSeparated_implies_pathDSeparated cut query.outcome
        (NodeSet.singleton pivotNode) given answer)
        ⟨outcome, pivotNode, by decide +kernel, by decide +kernel, ⟨actualPath.reverse⟩⟩)

/-- `P` is a sink, so these directly checked latest-pivot certificates
are finite graph facts, not an extra assumption of the general constructor. -/
def pivot : LatestConditionalPivot graph query pivotNode :=
  ⟨pivotNode, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem pivot_eq : pivot.node = pivotNode := by decide +kernel

/-- Keep this certified result opaque to reduction in the regression.
The general executable constructor is still the value being checked, but
the companion proves its properties structurally from the certificates
rather than repeatedly evaluating the exhaustive search during conversion. -/
opaque normal : ConditionalBackdoorPathNormalForm graph query pivot.node :=
  .ofExchangeTestFalse graph query pivot.node (by simpa only [pivot_eq] using exchange_test_false)

def forest : ConditionalColliderActivationForest query pivot.node := .ofLatestPivot pivot

end CurrentConditionalFailureActivationSelection
end Examples
end Causality
end Thesis
