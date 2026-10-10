import Thesis.CausalTransport.ConditionalFailureSmallAbsorption
import Thesis.CausalTransport.HedgeChannelEnvironmentPrefixDirection
import Thesis.CausalTransport.ActivePathEndpointHeads

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureSmallPrefixDirection

open PathSpecification

/-!
# A genuine hedge whose first conditioned pivot lies outside Small

The five original three-valued nodes are `X,Y,U,R,P`.  Declared arrows are
`X,U -> R -> P` and `Y -> P`; the actual bidirected pairs are `X <-> R`
and `U <-> R`.  Large is `X,U,R`, Small is `U,R`, and the common forest
root is `R`.  Its real queried readout is the conditioner `P`, outside Small.

For the unchanged query `P(Y | do(X),P)`, both mandatory Small-source paths
reach evidence, and the only singleton exchange fails by the actual incoming
path `P <- Y`.  The general no-exchange constructor supplies its normal form.
The semantic companion uses the real proper prefix `U,R` to transfer its odd
pivot parity into Small without flipping conditioned `P`.  No extra shared
switch, graph edge, outcome, conditioner or original label is introduced.
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
    (((parent.val = 0 ∨ parent.val = 2) ∧ child.val = 3) ∨
      (parent.val = 3 ∧ child.val = 4) ∨ (parent.val = 1 ∧ child.val = 4))
  directed_earlier := by intro parent child edge; have parts := of_decide_eq_true edge; omega

def actionNode : Fin signature.count := ⟨0, by decide⟩
def outcome : Fin signature.count := ⟨1, by decide⟩
def source : Fin signature.count := ⟨2, by decide⟩
def commonRoot : Fin signature.count := ⟨3, by decide⟩
def pivotNode : Fin signature.count := ⟨4, by decide⟩

private def pairMask (left right : Fin signature.count) : Bool :=
  decide ((left.val = 0 ∨ left.val = 2) ∧ right.val = 3)

def graph : ObservedGraph signature where
  bidirected := fun left right => pairMask left right || pairMask right left
  bidirected_symmetric := by intro _ _ selected; simpa only [Bool.or_comm] using selected
  bidirected_irreflexive := by
    intro node
    have absent : pairMask node node = false := by unfold pairMask; apply decide_eq_false; omega
    simp only [absent, Bool.false_or]

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcome
  action := NodeSet.singleton actionNode
  condition := NodeSet.singleton pivotNode
  action_outcome_disjoint := by unfold NodeSet.Disjoint; decide +kernel
  action_condition_disjoint := by unfold NodeSet.Disjoint; decide +kernel
  outcome_condition_disjoint := by unfold NodeSet.Disjoint; decide +kernel

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := by intro _ same; have values := congrArg Fin.val same; cases values

def selection : HedgeSelection signature where
  large := fun node => decide (node.val = 0 ∨ node.val = 2 ∨ node.val = 3)
  small := fun node => decide (node.val = 2 ∨ node.val = 3)
  child := fun node => if node.val = 0 ∨ node.val = 2 then some commonRoot else none

theorem hedge_tests : hedgeTestsHold graph query.jointNumerator selection = true := by decide +kernel

def witness : HedgeWitness graph query.jointNumerator :=
  hedgeWitness_of_sets graph query.jointNumerator selection hedge_tests

def boundary : ConditionedSmallFlowBoundary witness where
  encounters_condition := by decide +kernel

private def cut : GraphMutilation signature := .barUnderline query.action (NodeSet.singleton pivotNode)
private def given : NodeSet signature := NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton pivotNode))

private def actualPath : ActivePath graph cut given (.observed pivotNode) (.observed outcome) where
  nodes := [.observed pivotNode, .observed outcome]
  starts := rfl
  finishes := rfl
  simple := by decide +kernel
  adjacent := ⟨Or.inr (by decide +kernel), True.intro⟩
  source_open := by decide +kernel
  target_open := by decide +kernel
  internal_active := .pair _ _

private theorem exchange_test_false : conditionalExchangeTest graph query pivotNode = false := by
  cases answer : conditionalExchangeTest graph query pivotNode with
  | false => rfl
  | true =>
      exact False.elim ((graph.dSeparated_implies_pathDSeparated cut query.outcome
        (NodeSet.singleton pivotNode) given answer)
        ⟨outcome, pivotNode, by decide +kernel, by decide +kernel, ⟨actualPath.reverse⟩⟩)

/-- The only original conditioner has a displayed active exchange path;
exhaustion is proved without evaluating the full moral-closure search. -/
theorem no_exchange : conditionalExchangeStep? graph query = none := by
  cases answer : conditionalExchangeStep? graph query with
  | none => rfl
  | some step =>
      have same := (NodeSet.singleton_eq_true_iff pivotNode step.node).mp step.selected
      have separated := step.separated
      rw [same, exchange_test_false] at separated
      cases separated

def pivot : RetainedConditionalPivot query := ⟨pivotNode, by decide +kernel⟩
opaque normal : ConditionalBackdoorPathNormalForm graph query pivot.node :=
  .ofNoExchange graph query no_exchange pivot.node pivot.selected
def forest : ConditionalCutColliderActivationForest query pivot.node :=
  .ofRetainedPivot graph query pivot.node pivot.selected

theorem pivot_outside_small : witness.small pivot.node = false := by decide +kernel

/-- The endpoint has just its original parentless outgoing neighbour `P`.
Simplicity forces the exact normal path; no normal-form search is reduced. -/
theorem normal_window : normal.cutPath.nodes = [.observed pivotNode, .observed outcome] := by
  have endpoint : normal.outcome = outcome := (NodeSet.singleton_eq_true_iff _ _).mp normal.outcome_selected
  have distinct : pivot.node ≠ normal.outcome := by
    rw [endpoint]
    decide +kernel
  have unique : forall neighbor, Adjacent graph
      (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node))
        (.observed normal.outcome) neighbor -> neighbor = .observed pivot.node := by
    rw [endpoint]
    intro neighbor adjacent
    cases neighbor with
    | observed child =>
        exact (by decide +kernel : forall child : Fin signature.count,
          Adjacent graph cut (.observed outcome) (.observed child) -> child = pivotNode) child adjacent
          ▸ rfl
    | latentPair left right =>
        exact False.elim ((by decide +kernel : forall left right : Fin signature.count,
          ¬ Adjacent graph cut (.observed outcome) (.latentPair left right)) left right adjacent)
  simpa only [endpoint] using ActivePathInput.nodes_eq_pair_of_unique_target_neighbor normal.cutPath distinct unique

end CurrentConditionalFailureSmallPrefixDirection
end Examples
end Causality
end Thesis
