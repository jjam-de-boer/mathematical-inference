import Thesis.CausalTransport.HedgeSmallAbsorption

namespace Thesis
namespace Causality

open Probability

/-!
# Rerooting a hedge on action-free outcome ancestors

Keeping an old forest edge is not a requirement of the hedge criterion.
The same-map absorption constructor nevertheless keeps every such edge,
so its child closure may force an intervened vertex into the small forest.
Adding more vertices cannot repair that particular avoidance failure.

This module instead keeps the large vertex set and the original query, but
reconstructs the forest.  Its new small set contains every non-intervened
large vertex that can reach a queried outcome in the incoming-cut graph.
All old small vertices are proved to belong to this set.  The existing finite
`closedForestChild` search chooses small children inside the new small set
and large children inside the large set.  The resulting common roots may
change; all are still action-free ancestors of the original outcome.

Every canonical route of this new hedge is automatically small-or-outside:
its large-side vertices belong to the computed ancestral small set.  Thus
the positive compensated countermodel theorem applies with no avoidance or
old-child-closure premise.  Bidirected connectivity of the computed small
set remains an explicit finite test.  It need not hold for every hedge, so
this is a genuine reduction of the outer-route obstruction, not the general
published completeness theorem.
-/

section Forests

variable {S : ObservedSignature} {G : ObservedGraph S} {q : JointKernelQuery S}

/-- Every old small vertex reaches an original queried outcome without
entering the action.  First follow the old kept forest to one of its common
roots, then use the hedge's root-to-outcome condition.  The strictly later
kept child gives finite recursion without choosing an existential path. -/
theorem HedgeWitness.small_reaches_outcome (w : HedgeWitness G q)
    (node : Fin S.count) (inside : w.small node = true) :
    Exists fun outcome => q.outcome outcome = true ∧
      DirectedReachableBy S (fun parent child => mutilatedDirected S q.action parent child = true) node outcome := by
  cases found : w.child node with
  | none =>
      exact w.roots_reach_outcome node
        ((w.large_forest.roots_exact node).mpr ⟨w.small_subset_large node inside, found⟩)
  | some child =>
      have restricted : restrictChild w.small w.child node = some child :=
        (restrictChild_of_true inside).trans found
      have edge := w.small_forest.child_edge node child restricted
      rcases w.small_reaches_outcome child edge.2.1 with ⟨outcome, selected, reaches⟩
      refine ⟨outcome, selected, DirectedReachableBy.step_left ?_ reaches⟩
      simpa only [mutilatedDirected, w.small_avoids_intervention child edge.2.1,
        Bool.false_eq_true, if_false] using edge.2.2
termination_by S.count - node.val
decreasing_by
  have edge := w.large_forest.child_edge node child (by assumption)
  have later := S.directed_earlier edge.2.2
  omega

/-- A vertex anywhere on the merged readout routes still reaches an
outcome.  Following the selected successor proves this directly, even when
the merge switches from one original root's route to another suffix. -/
theorem HedgeWitness.rootReadoutNodes_reach_outcome (w : HedgeWitness G q)
    (node : Fin S.count) (selected : w.rootReadoutNodes node = true) :
    Exists fun outcome => q.outcome outcome = true ∧
      DirectedReachableBy S (fun parent child => mutilatedDirected S q.action parent child = true) node outcome := by
  cases found : w.rootReadoutSuccessor node with
  | none => exact ⟨node, w.rootReadoutSuccessor_none_is_outcome node selected found, .refl node⟩
  | some child =>
      rcases w.rootReadoutNodes_reach_outcome child (w.rootReadoutSuccessor_nodes found).2 with
        ⟨outcome, inOutcome, reaches⟩
      exact ⟨outcome, inOutcome, DirectedReachableBy.step_left
        (w.rootReadoutSuccessor_mutilatedDirected found) reaches⟩
termination_by S.count - node.val
decreasing_by
  have later := w.rootReadoutSuccessor_earlier (by assumption)
  omega

/-- All action-free outcome ancestors on the unchanged large side.
Reachability uses the complete finite node enumeration and the original
action cut, not a path confined to either old forest. -/
def HedgeWitness.outcomeAncestralSmall (w : HedgeWitness G q) : NodeSet S :=
  fun node => w.large node && (!q.action node &&
    (NodeSet.members q.outcome).any (fun outcome =>
      FiniteReachability.within finBeq (NodeSet.enumerated S)
        (mutilatedDirected S q.action) S.count node outcome))

/-- Exact specification of the computed node set.  The existential occurs
only in this theorem, while the definition itself inspects finite data. -/
theorem HedgeWitness.outcomeAncestralSmall_iff (w : HedgeWitness G q) (node : Fin S.count) :
    w.outcomeAncestralSmall node = true ↔ w.large node = true ∧ q.action node = false ∧
      Exists fun outcome => q.outcome outcome = true ∧
        DirectedReachableBy S (fun parent child => mutilatedDirected S q.action parent child = true) node outcome := by
  constructor
  · intro selected
    have parts := Bool.and_eq_true_iff.mp selected
    have freeReach := Bool.and_eq_true_iff.mp parts.2
    have free : q.action node = false := by
      cases action : q.action node with
      | false => rfl
      | true =>
          have impossible : false = true := by simpa only [action] using freeReach.1
          cases impossible
    rcases List.any_eq_true.mp freeReach.2 with ⟨outcome, listed, reaches⟩
    exact ⟨parts.1, free, outcome,
      (NodeSet.mem_members_iff q.outcome outcome).mp listed,
      directedReachableBy_of_within q.action reaches⟩
  · rintro ⟨inside, free, outcome, selected, reaches⟩
    apply Bool.and_eq_true_iff.mpr
    refine ⟨inside, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
    · rw [free]; rfl
    · exact List.any_eq_true.mpr ⟨outcome, (NodeSet.mem_members_iff q.outcome outcome).mpr selected,
        finiteWithin_of_directedReachableBy reaches⟩

theorem HedgeWitness.outcomeAncestralSmall_subset_large (w : HedgeWitness G q) :
    NodeSet.Subset w.outcomeAncestralSmall w.large :=
  fun node selected => ((w.outcomeAncestralSmall_iff node).mp selected).1

theorem HedgeWitness.outcomeAncestralSmall_avoids_action (w : HedgeWitness G q) :
    NodeSet.Disjoint w.outcomeAncestralSmall q.action :=
  fun node selected => ((w.outcomeAncestralSmall_iff node).mp selected).2.1

/-- The normalization retains every old small vertex, not merely one
selected root.  Its eventual root changes are caused by the new kept edges. -/
theorem HedgeWitness.outcomeAncestralSmall_contains_small (w : HedgeWitness G q) :
    NodeSet.Subset w.small w.outcomeAncestralSmall := by
  intro node selected
  exact (w.outcomeAncestralSmall_iff node).mpr ⟨w.small_subset_large node selected,
    w.small_avoids_intervention node selected, w.small_reaches_outcome node selected⟩

/-- Reconstruct both forests with the existing finite child selector.  Old
large-only successors are not obligations of this new witness. -/
def HedgeWitness.outcomeAncestralChild (w : HedgeWitness G q) : ForestChild S :=
  closedForestChild w.large w.outcomeAncestralSmall

private theorem normalized_roots_small (w : HedgeWitness G q) :
    NodeSet.Subset (keptSinks w.large w.outcomeAncestralChild) w.outcomeAncestralSmall := by
  apply closedForestChild_keptSinks_subset
  intro parent inside outside
  cases found : w.child parent with
  | none =>
      have root := (w.large_forest.roots_exact parent).mpr ⟨inside, found⟩
      have oldSmall := ((w.small_forest.roots_exact parent).mp root).1
      have newSmall := w.outcomeAncestralSmall_contains_small parent oldSmall
      rw [outside] at newSmall
      cases newSmall
  | some child =>
      have edge := w.large_forest.child_edge parent child found
      exact ⟨child, List.mem_filter.mpr ⟨(NodeSet.mem_members_iff w.large child).mpr edge.2.1, edge.2.2⟩⟩

/-- Normalize the hedge under one explicit connectivity test.  Large-side
connectivity, action intersection, and stored action/outcome coordinates
are retained.  Child validity, common roots, action avoidance, and root
reachability are all proved for the newly constructed forests. -/
def HedgeWitness.normalizeOutcomeAncestry (w : HedgeWitness G q)
    (connected : G.isSingleCComponent w.outcomeAncestralSmall = true) : HedgeWitness G q := by
  let child := w.outcomeAncestralChild
  have subset := w.outcomeAncestralSmall_subset_large
  have well := closedForestChild_wellFormed w.large w.outcomeAncestralSmall subset
  have closed := closedForestChild_childClosed w.large w.outcomeAncestralSmall
  have rootsSmall := normalized_roots_small w
  have rootsSame := keptSinks_restrict_eq w.large w.outcomeAncestralSmall child subset closed rootsSmall
  have smallForest : CForest G w.outcomeAncestralSmall (keptSinks w.large child)
      (restrictChild w.outcomeAncestralSmall child) := by
    rw [← rootsSame]
    exact cForest_of_child G _ _ connected (childWellFormed_restrict _ _ child well subset closed)
  exact {
    large := w.large
    small := w.outcomeAncestralSmall
    roots := keptSinks w.large child
    child := child
    large_forest := cForest_of_component_child G _ child w.large_forest.component well
    small_forest := smallForest
    small_subset_large := subset
    large_meets_intervention := w.large_meets_intervention
    small_avoids_intervention := w.outcomeAncestralSmall_avoids_action
    roots_reach_outcome := fun node selected =>
      ((w.outcomeAncestralSmall_iff node).mp (rootsSmall node selected)).2.2
    actionSeed := w.actionSeed
    actionSeed_in_large := w.actionSeed_in_large
    actionSeed_in_action := w.actionSeed_in_action
    outcomeSeed := w.outcomeSeed
    outcomeSeed_in_outcome := w.outcomeSeed_in_outcome }

/-- Every large vertex of any canonical route of the new hedge belongs
to its ancestral small side.  No preservation of the old canonical routes
is needed: all action-free outcome ancestors were included in advance. -/
theorem HedgeWitness.normalizeOutcomeAncestry_routes_allowed (w : HedgeWitness G q)
    (connected : G.isSingleCComponent w.outcomeAncestralSmall = true) :
    forall node, (w.normalizeOutcomeAncestry connected).rootReadoutNodes node = true ->
      (w.normalizeOutcomeAncestry connected).small node = true ∨
        (w.normalizeOutcomeAncestry connected).large node = false := by
  let normalized := w.normalizeOutcomeAncestry connected
  intro node routed
  cases inside : w.large node with
  | false => exact .inr inside
  | true =>
      apply Or.inl
      exact (w.outcomeAncestralSmall_iff node).mpr ⟨inside,
        normalized.rootReadoutNodes_avoids_action node routed,
        normalized.rootReadoutNodes_reach_outcome node routed⟩

end Forests

section Countermodels

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {q : JointKernelQuery S}

/-- Positive countermodels for the original query after outcome-ancestral
rerooting.  Only small-side connectivity is tested: no old-map avoidance
test or preserved-root assumption is passed to the countermodel theorem. -/
noncomputable def HedgeWitness.positiveCounterexampleOfOutcomeAncestralSmallConnected
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (connected : G.isSingleCComponent w.outcomeAncestralSmall = true) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  (w.normalizeOutcomeAncestry connected).positiveCounterexampleOfSmallOrOutsideCarrierFlow rich
    (w.normalizeOutcomeAncestry_routes_allowed connected)

/-- The same normalized witness also supplies conditional countermodels
when a closed coordinate set omits a new small vertex.  Closure is explicitly
checked against the *new* forest and outcome flow; unlike same-map absorption,
rerooting does not preserve the old parent-closure invariant. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfOutcomeAncestralSmallConnectedOfParentClosed
    {query : ConditionalKernelQuery S} (w : HedgeWitness G query.jointNumerator)
    (rich : ObservedSignature.ValueRich S)
    (connected : G.isSingleCComponent w.outcomeAncestralSmall = true)
    (nodes : NodeSet S) (closed : (w.normalizeOutcomeAncestry connected).CarrierFlowParentClosed nodes)
    (balance : Fin S.count) (inside : w.outcomeAncestralSmall balance = true)
    (omitted : nodes balance = false) (conditionWithin : NodeSet.Subset query.condition nodes) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query :=
  (w.normalizeOutcomeAncestry connected).positiveConditionalCounterexampleOfCarrierFlowOfParentClosed rich
    (w.normalizeOutcomeAncestry_routes_allowed connected) nodes closed balance inside omitted conditionWithin

/-- A topological prefix is closed for the new forest automatically.  The
balancing vertex need not be an old root: it belongs to the computed small
set and lies later than all inspected conditioning coordinates. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfOutcomeAncestralSmallConnectedOfConditionBeforeSmall
    {query : ConditionalKernelQuery S} (w : HedgeWitness G query.jointNumerator)
    (rich : ObservedSignature.ValueRich S)
    (connected : G.isSingleCComponent w.outcomeAncestralSmall = true)
    (balance : Fin S.count) (inside : w.outcomeAncestralSmall balance = true)
    (conditionBefore : forall node, query.condition node = true -> node.val < balance.val) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query :=
  (w.normalizeOutcomeAncestry connected).positiveConditionalCounterexampleOfCarrierFlowOfConditionBeforeSmall rich
    (w.normalizeOutcomeAncestry_routes_allowed connected) balance inside conditionBefore

end Countermodels

end Causality
end Thesis
