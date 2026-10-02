import Thesis.CausalTransport.HedgeSmallAbsorption
import Thesis.Examples.KernelFailureExtraction

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeOuterRouteAbsorption

open Probability
open CurrentKernelFailureExtraction (partitionGraph)

/-!
# Outer-only route vertices absorbed into a checked small forest

The three-value graph has `A → Q → Y` and `R → O → C → Q`.
All vertices except `Y` share a bidirected component.  The supplied large
forest keeps `A → Q`, `O → C`, and `C → Q`; its common roots are `R,Q`.
Initially its small forest is only `{R,Q}`.  The joint query is
`P(Y | do(A))`, whose root route crosses the outer-only rows `O,C`.
The old small-or-outside permission test is explicitly false.

Absorption computes the new small set `{R,O,C,Q}` while retaining the
large side, roots, and original kept map.  Its positive compensated pair
then separates the original queried outcome, not a substitute root query.

For `P(Y | do(A), O)`, routing stops at the conditioner `O`, so `C` is
off the explicit route.  Absorbing route vertices alone would not give a
child-closed forest: `O` still keeps `C`.  The computed kept-descendant
closure includes `C` automatically.  That newly absorbed non-root supplies
the omitted denominator equation in a prefix containing `O`.  The same
newly constructed pair has matching full three-value conditioning kernels
and separates the actual conditional.  Neither endpoint is taken from
the unsupported original outer-update pair.
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
    ((parent.val = 0 ∧ child.val = 4) ∨ (parent.val = 4 ∧ child.val = 5) ∨
      (parent.val = 1 ∧ child.val = 2) ∨ (parent.val = 2 ∧ child.val = 3) ∨
      (parent.val = 3 ∧ child.val = 4))
  directed_earlier := by
    intro parent child edge
    have selected := of_decide_eq_true edge
    omega

def graph := partitionGraph signature (fun node => decide (node.val = 5))
def actionNode : Fin signature.count := ⟨0, by decide⟩
def firstRoot : Fin signature.count := ⟨1, by decide⟩
def outerRouteNode : Fin signature.count := ⟨2, by decide⟩
def retainedChildNode : Fin signature.count := ⟨3, by decide⟩
def lastRoot : Fin signature.count := ⟨4, by decide⟩
def outcomeNode : Fin signature.count := ⟨5, by decide⟩

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := fun _ => (by decide : (⟨0, by decide⟩ : Fin 3) ≠ ⟨1, by decide⟩)

def query : JointKernelQuery signature where
  outcome := NodeSet.singleton outcomeNode
  action := NodeSet.singleton actionNode
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

def large : NodeSet signature := fun node => decide (node.val ≠ 5)
def small : NodeSet signature := fun node => decide (node.val = 1 ∨ node.val = 4)
def child : ForestChild signature := fun parent => match parent.val with
  | 0 => some lastRoot
  | 2 => some retainedChildNode
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
      DirectedReachableBy signature (fun parent child =>
        mutilatedDirected signature query.action parent child = true) root outcome := by
  intro root selected
  have onlyRoots : forall node : Fin signature.count, roots node = true -> node = firstRoot ∨ node = lastRoot :=
    by decide +kernel
  refine ⟨outcomeNode, by decide +kernel, ?_⟩
  cases onlyRoots root selected with
  | inl same =>
      subst root
      exact .tail (.tail (.tail (.tail (.refl firstRoot)
        (by decide +kernel : mutilatedDirected signature query.action firstRoot outerRouteNode = true))
        (by decide +kernel : mutilatedDirected signature query.action outerRouteNode retainedChildNode = true))
        (by decide +kernel : mutilatedDirected signature query.action retainedChildNode lastRoot = true))
        (by decide +kernel : mutilatedDirected signature query.action lastRoot outcomeNode = true)
  | inr same =>
      subst root
      exact .tail (.refl lastRoot) (by decide +kernel : mutilatedDirected signature query.action lastRoot outcomeNode = true)

noncomputable def witness : HedgeWitness graph query :=
  HedgeWitness.ofForests query large small roots child large_forest small_forest
    (by
      change forall node : Fin signature.count, small node = true -> large node = true
      decide +kernel) (by decide +kernel)
    ((NodeSet.disjointBool_eq_true_iff _ _).mp (by decide +kernel)) roots_reach

/-- This is an actual formerly excluded outer route, not an outside-
large readout or an already small vertex renamed for the regression. -/
theorem route_reenters_outer : witness.rootReadoutNodes outerRouteNode = true ∧
    witness.large outerRouteNode = true ∧ witness.small outerRouteNode = false := by decide +kernel

theorem original_routes_not_allowed : Not (forall node, witness.rootReadoutNodes node = true ->
    witness.small node = true ∨ witness.large node = false) := by
  intro allowed
  cases allowed outerRouteNode route_reenters_outer.1 with
  | inl inside => rw [route_reenters_outer.2.2] at inside; cases inside
  | inr outside => rw [route_reenters_outer.2.1] at outside; cases outside

private theorem connected : graph.isSingleCComponent witness.routeAbsorbedSmall = true := by decide +kernel
private theorem avoids : NodeSet.disjointBool witness.routeAbsorbedSmall query.action = true := by decide +kernel

/-- The automatic closure absorbs both original outer rows, but excludes
the action.  No new large-side nodes or new kept edges are invented. -/
theorem absorbed_small_exact : witness.routeAbsorbedSmall = NodeSet.diff witness.large query.action :=
  (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)

noncomputable def absorbedWitness : HedgeWitness graph query := witness.absorbRouteVertices connected avoids

theorem forests_and_routes_retained : absorbedWitness.large = witness.large ∧
    absorbedWitness.child = witness.child ∧ absorbedWitness.roots = witness.roots ∧
      absorbedWitness.rootReadoutNodes = witness.rootReadoutNodes := ⟨rfl, rfl, rfl, rfl⟩

noncomputable def counterexample : CounterexampleIn (GraphModelClass.positive graph) query :=
  witness.positiveCounterexampleOfRouteAbsorption rich connected avoids

theorem query_not_identifiable : Not ((GraphModelClass.positive graph).identifiable query) :=
  counterexample.not_identifiable

/-! ## A responding absorbed conditioner and an off-route kept child -/

def conditionalQuery : ConditionalKernelQuery signature where
  outcome := query.outcome
  action := query.action
  condition := NodeSet.singleton outerRouteNode
  action_outcome_disjoint := query.action_outcome_disjoint
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

noncomputable def conditionalWitness : HedgeWitness graph conditionalQuery.jointNumerator :=
  witness.retargetQuery conditionalQuery.jointNumerator (by decide +kernel) witness.small_avoids_intervention
    (by
      intro root selected
      rcases witness.roots_reach_outcome root selected with ⟨outcome, inOutcome, reaches⟩
      exact ⟨outcome, NodeSet.subset_union_left _ _ outcome inOutcome, reaches⟩)

private theorem conditional_connected : graph.isSingleCComponent conditionalWitness.routeAbsorbedSmall = true := by decide +kernel
private theorem conditional_avoids : NodeSet.disjointBool conditionalWitness.routeAbsorbedSmall conditionalQuery.action = true := by decide +kernel

/-- The original child `C` is off the conditioner-stopped route but is
added by kept-child closure.  It is an originally outer, non-root balancing
vertex; no common root is a queried outcome. -/
theorem off_route_child_absorbed : conditionalWitness.rootReadoutNodes retainedChildNode = false ∧
    conditionalWitness.small retainedChildNode = false ∧ conditionalWitness.roots retainedChildNode = false ∧
    conditionalWitness.child outerRouteNode = some retainedChildNode ∧
    conditionalWitness.routeAbsorbedSmall retainedChildNode = true ∧
    NodeSet.meetsBool conditionalWitness.roots conditionalQuery.outcome = false := by decide +kernel

private theorem condition_before_child : forall node, conditionalQuery.condition node = true -> node.val < retainedChildNode.val :=
  by decide +kernel

noncomputable def conditionalCounterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) conditionalQuery :=
  conditionalWitness.positiveConditionalCounterexampleOfRouteAbsorptionOfConditionBeforeSmall rich
    conditional_connected conditional_avoids retainedChildNode off_route_child_absorbed.2.2.2.2.1 condition_before_child

/-- The matched denominator belongs to the absorbed pair itself.  The
proof does not assert preservation of the old countermodel or observational
equality for the original forbidden outer-only update. -/
theorem conditional_denominator_matches :
    conditionalQuery.jointDenominator.ValueEquivalent conditionalCounterexample.left conditionalCounterexample.right :=
  HedgeWitness.carrierDefectParityModels_carrierFlowReadoutPlan_valueEquivalent_of_parentClosed
      (conditionalWitness.absorbRouteVertices conditional_connected conditional_avoids) rich
      (fun _node => FiniteProbRecord.biasedFlip 1 1 (by decide)) (hedgeCarrierPrefixNodes retainedChildNode)
      (conditionalWitness.carrierFlowParentClosed_prefix retainedChildNode) retainedChildNode
      off_route_child_absorbed.2.2.2.2.1 (by decide +kernel) conditionalQuery.jointDenominator
      (fun node selected => decide_eq_true (condition_before_child node selected))

theorem conditional_query_not_identifiable : Not ((GraphModelClass.positive graph).conditionalIdentifiable conditionalQuery) :=
  conditionalCounterexample.not_identifiable

private def failed (result : IdentificationOutcome signature) : Bool :=
  match result with
  | .failed _ => true
  | _ => false

theorem joint_program_failed : failed (identifyJointKernel graph query) = true := by decide +kernel
theorem conditional_no_exchange : (conditionalExchangeStep? graph conditionalQuery).isNone = true := by decide +kernel
theorem conditional_program_failed : failed (identifyConditionalKernel graph conditionalQuery) = true := by decide +kernel

end HedgeOuterRouteAbsorption
end Examples
end Causality
end Thesis
