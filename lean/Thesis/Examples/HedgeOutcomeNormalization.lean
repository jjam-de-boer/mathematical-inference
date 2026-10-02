import Thesis.CausalTransport.HedgeOutcomeNormalization
import Thesis.Examples.KernelFailureExtraction

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeAncestralRerooting

open Probability
open CurrentKernelFailureExtraction (partitionGraph)

/-!
# Rerooting repairs a forced-action absorption obstruction

The three-value graph has `A → R → O → Y`, `O → C → Q → Y`, and one
bidirected component on every vertex except `Y`.  Both `A` and `C` are
intervened.  The old large forest keeps `A → R`, `O → C`, and `C → Q`,
with common roots `R,Q` and small set `{R,Q}`.  Its action-free outcome
route from `R` uses `O → Y`, not the old kept edge `O → C`.

Same-map absorption cannot work: absorbing `O` forces its kept child `C`
into the small forest, violating action avoidance.  The new normalization
computes `{R,O,Q}`, keeps `R → O` instead, and makes `O,Q` the common
roots.  No action is absorbed.  Its complete positive countermodel fields
are supplied by the general normalized constructor for the unchanged
query `P(Y | do(A,C))`.

The conditional `P(Y | do(A,C), O)` is also irreducible.  Its installed
conditioner may respond to the rerooted forest, but a prefix omitting `Q`
has an equal full-value denominator in the new pair.  Both public programs
actually fail.  The tests do not identify the changed forest with the
algorithm's extracted child map or claim unrestricted normalization.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def signature : ObservedSignature where
  count := 6
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val = 0 ∧ child.val = 1) ∨ (parent.val = 1 ∧ child.val = 2) ∨
      (parent.val = 2 ∧ (child.val = 3 ∨ child.val = 5)) ∨
      (parent.val = 3 ∧ child.val = 4) ∨ (parent.val = 4 ∧ child.val = 5))
  directed_earlier := by
    intro parent child edge
    have selected := of_decide_eq_true edge
    omega

def graph := partitionGraph signature (fun node => decide (node.val = 5))
def firstAction : Fin signature.count := ⟨0, by decide⟩
def oldFirstRoot : Fin signature.count := ⟨1, by decide⟩
def outerRouteNode : Fin signature.count := ⟨2, by decide⟩
def secondAction : Fin signature.count := ⟨3, by decide⟩
def lastRoot : Fin signature.count := ⟨4, by decide⟩
def outcomeNode : Fin signature.count := ⟨5, by decide⟩

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := fun _ => (by decide : (⟨0, by decide⟩ : Fin 3) ≠ ⟨1, by decide⟩)

def action : NodeSet signature := fun node => decide (node.val = 0 ∨ node.val = 3)
def query : JointKernelQuery signature where
  outcome := NodeSet.singleton outcomeNode
  action := action
  action_outcome_disjoint := (NodeSet.disjointBool_eq_true_iff _ _).mp (by decide +kernel)

def large : NodeSet signature := fun node => decide (node.val ≠ 5)
def small : NodeSet signature := fun node => decide (node.val = 1 ∨ node.val = 4)
def child : ForestChild signature := fun parent => match parent.val with
  | 0 => some oldFirstRoot
  | 2 => some secondAction
  | 3 => some lastRoot
  | _ => none
def roots : NodeSet signature := keptSinks large child

private theorem large_forest : CForest graph large roots child :=
  cForest_of_child graph large child (by decide +kernel) (by decide +kernel)

private theorem small_forest : CForest graph small roots (restrictChild small child) := by
  have sameRoots : keptSinks small (restrictChild small child) = roots :=
    (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)
  rw [← sameRoots]
  exact cForest_of_child graph small (restrictChild small child) (by decide +kernel) (by decide +kernel)

private theorem roots_reach : forall root, roots root = true -> Exists fun outcome =>
    query.outcome outcome = true ∧
      DirectedReachableBy signature (fun parent child => mutilatedDirected signature query.action parent child = true)
        root outcome := by
  intro root selected
  have onlyRoots : forall node : Fin signature.count, roots node = true -> node = oldFirstRoot ∨ node = lastRoot :=
    by decide +kernel
  refine ⟨outcomeNode, by decide +kernel, ?_⟩
  cases onlyRoots root selected with
  | inl same =>
      subst root
      exact .tail (.tail (.refl oldFirstRoot)
        (by decide +kernel : mutilatedDirected signature query.action oldFirstRoot outerRouteNode = true))
        (by decide +kernel : mutilatedDirected signature query.action outerRouteNode outcomeNode = true)
  | inr same =>
      subst root
      exact .tail (.refl lastRoot)
        (by decide +kernel : mutilatedDirected signature query.action lastRoot outcomeNode = true)

noncomputable def witness : HedgeWitness graph query :=
  HedgeWitness.ofForests query large small roots child large_forest small_forest
    (by
      change forall node : Fin signature.count, small node = true -> large node = true
      decide +kernel) (by decide +kernel)
    ((NodeSet.disjointBool_eq_true_iff _ _).mp (by decide +kernel)) roots_reach

/-- The old closure genuinely forces the second action, so this fixture
cannot pass the earlier absorption adapter's avoidance premise. -/
theorem same_map_absorption_forces_action : witness.routeAbsorbedSmall secondAction = true := by decide +kernel
theorem same_map_absorption_avoidance_fails :
    NodeSet.disjointBool witness.routeAbsorbedSmall query.action = false := by decide +kernel

private theorem connected : graph.isSingleCComponent witness.outcomeAncestralSmall = true := by decide +kernel

noncomputable def normalizedWitness : HedgeWitness graph query := witness.normalizeOutcomeAncestry connected

theorem normalized_small_exact : normalizedWitness.small = NodeSet.diff large action :=
  (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)

/-- The former common root `R` now has child `O`, while the old outer row
`O` becomes a root.  Connectivity and avoidance are not achieved by merely
renaming an unchanged forest. -/
theorem rerooted_edges : normalizedWitness.child oldFirstRoot = some outerRouteNode ∧
    normalizedWitness.child outerRouteNode = none := by decide +kernel
theorem rerooted_roots : normalizedWitness.roots =
    (fun node => decide (node.val = 2 ∨ node.val = 4)) :=
  (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)

noncomputable def counterexample : CounterexampleIn (GraphModelClass.positive graph) query :=
  witness.positiveCounterexampleOfOutcomeAncestralSmallConnected rich connected

theorem query_not_identifiable : Not ((GraphModelClass.positive graph).identifiable query) :=
  counterexample.not_identifiable

private def failureTest (result : IdentificationOutcome signature) : Bool :=
  match result with
  | .failed _ => true
  | _ => false

theorem joint_program_fails : failureTest (identifyJointKernel graph query) = true := by decide +kernel

/-! ## An installed conditioner in the newly rooted small forest -/

def conditionalQuery : ConditionalKernelQuery signature where
  outcome := query.outcome
  action := query.action
  condition := NodeSet.singleton outerRouteNode
  action_outcome_disjoint := query.action_outcome_disjoint
  action_condition_disjoint := (NodeSet.disjointBool_eq_true_iff _ _).mp (by decide +kernel)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

noncomputable def conditionalWitness : HedgeWitness graph conditionalQuery.jointNumerator :=
  witness.retargetQuery conditionalQuery.jointNumerator (by decide +kernel) witness.small_avoids_intervention
    (by
      intro root selected
      rcases witness.roots_reach_outcome root selected with ⟨outcome, inOutcome, reaches⟩
      exact ⟨outcome, NodeSet.subset_union_left _ _ outcome inOutcome, reaches⟩)

private theorem conditional_connected : graph.isSingleCComponent conditionalWitness.outcomeAncestralSmall = true :=
  by decide +kernel

noncomputable def conditionalCounterexample :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) conditionalQuery :=
  conditionalWitness.positiveConditionalCounterexampleOfOutcomeAncestralSmallConnectedOfConditionBeforeSmall
    rich conditional_connected lastRoot (by decide +kernel) (by
      change forall node : Fin signature.count, conditionalQuery.condition node = true -> node.val < lastRoot.val
      decide +kernel)

theorem conditional_not_identifiable : Not ((GraphModelClass.positive graph).conditionalIdentifiable conditionalQuery) :=
  conditionalCounterexample.not_identifiable

theorem conditional_no_exchange : conditionalExchangeStep? graph conditionalQuery = none := by decide +kernel
theorem conditional_program_fails : failureTest (identifyConditionalKernel graph conditionalQuery) = true := by decide +kernel

/-! ## Connectivity is a real remaining obligation -/

/-- Keep the same directed graph, but let `A` connect `R,O,C` by
bidirected edges and connect `R` to `Q`.  The large side is connected,
and the old small side `{R,Q}` is connected; after removing actions,
the outcome-ancestral outer vertex `O` is in a separate component. -/
def connectivityObstructedGraph : ObservedGraph signature where
  bidirected := fun left right => decide (left ≠ right ∧
    ((left.val = 0 ∧ right.val < 4) ∨ (right.val = 0 ∧ left.val < 4) ∨
      (left.val = 1 ∧ right.val = 4) ∨ (left.val = 4 ∧ right.val = 1)))
  bidirected_symmetric := by
    intro left right edge
    simpa only [ne_comm, and_comm, or_comm, or_left_comm, or_assoc] using edge
  bidirected_irreflexive := by intro node; simp

noncomputable def connectivityObstructedWitness : HedgeWitness connectivityObstructedGraph query :=
  HedgeWitness.ofForests query large small roots child
    (cForest_of_child _ large child (by decide +kernel) (by decide +kernel))
    (by
      have sameRoots : keptSinks small (restrictChild small child) = roots :=
        (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)
      rw [← sameRoots]
      exact cForest_of_child _ small (restrictChild small child) (by decide +kernel) (by decide +kernel))
    (by
      change forall node : Fin signature.count, small node = true -> large node = true
      decide +kernel) (by decide +kernel)
    ((NodeSet.disjointBool_eq_true_iff _ _).mp (by decide +kernel)) roots_reach

/-- The normalization is not silently treated as a universal hedge
constructor: this valid input fails its remaining connectivity test.
This does not prove that its query has no other countermodel construction. -/
theorem ancestral_small_connectivity_can_fail :
    connectivityObstructedGraph.isSingleCComponent connectivityObstructedWitness.outcomeAncestralSmall = false :=
  by decide +kernel

end HedgeAncestralRerooting
end Examples
end Causality
end Thesis
