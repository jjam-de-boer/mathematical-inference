import Thesis.CausalTransport.HedgeConditionalCompensatedReadout
import Thesis.Examples.KernelFailureExtraction

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeConditionalClosedReentry

open Probability
open CurrentKernelFailureExtraction (partitionGraph)

/-!
# Responding conditioners without a queried common root

The three-value graph has `A → Q → Y`, `B → Q`, and `R → E → B`.
The large forest is `{A,R,B,Q}` and keeps `A → Q` and `B → Q`; the
small forest is `{R,B,Q}`.  Its common roots are `R,Q`, neither of which
is the queried outcome `Y`.  The two outside vertices `E,Y` form the
other bidirected component.

For `P(Y | do(A), B)`, canonical routing takes `R → E → B` and
`Q → Y`.  The conditioner `B` is an installed responding small row with
an old kept child.  Thus it is not protected.  The balancing root `Q` is
not a queried outcome and is not unused by the new flow.  Nevertheless,
the prefix strictly before `Q` contains `B` and is parent-closed.  Its
untested small equation makes the actual conditioning kernels agree.

A second query conditions on `E`.  The prefix before the non-root `B`
then suffices: omitted balancing vertices need not even be forest roots.
Both constructions retain the full three-value alphabets and the actual
supported biased priors.  Forests are supplied directly; engine failures
are checked separately rather than asserting an exact extractor choice.
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
      (parent.val = 3 ∧ child.val = 4) ∨ (parent.val = 1 ∧ child.val = 2) ∨
      (parent.val = 2 ∧ child.val = 3))
  directed_earlier := by
    intro parent child edge
    have selected := of_decide_eq_true edge
    omega

def graph := partitionGraph signature (fun node => decide (node.val = 2 ∨ node.val = 5))
def actionNode : Fin signature.count := ⟨0, by decide⟩
def firstRoot : Fin signature.count := ⟨1, by decide⟩
def outsideNode : Fin signature.count := ⟨2, by decide⟩
def internalNode : Fin signature.count := ⟨3, by decide⟩
def lastRoot : Fin signature.count := ⟨4, by decide⟩
def outcomeNode : Fin signature.count := ⟨5, by decide⟩

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := fun _ => (by decide : (⟨0, by decide⟩ : Fin 3) ≠ ⟨1, by decide⟩)

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcomeNode
  action := NodeSet.singleton actionNode
  condition := NodeSet.singleton internalNode
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

def large : NodeSet signature := fun node => decide (node.val ≠ 2 ∧ node.val ≠ 5)
def small : NodeSet signature := fun node => decide (node.val = 1 ∨ node.val = 3 ∨ node.val = 4)
def child : ForestChild signature := fun parent => match parent.val with
  | 0 => some lastRoot
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
    query.jointNumerator.outcome outcome = true ∧
      DirectedReachableBy signature (fun parent child =>
        mutilatedDirected signature query.action parent child = true) root outcome := by
  intro root selected
  have onlyRoots : forall node : Fin signature.count, roots node = true -> node = firstRoot ∨ node = lastRoot :=
    by decide +kernel
  cases onlyRoots root selected with
  | inl same =>
      subst root
      exact ⟨internalNode, by decide +kernel, .tail (.tail (.refl firstRoot)
        (by decide +kernel : mutilatedDirected signature query.action firstRoot outsideNode = true))
        (by decide +kernel : mutilatedDirected signature query.action outsideNode internalNode = true)⟩
  | inr same =>
      subst root
      exact ⟨outcomeNode, by decide +kernel, .tail (.refl lastRoot)
        (by decide +kernel : mutilatedDirected signature query.action lastRoot outcomeNode = true)⟩

noncomputable def witness : HedgeWitness graph query.jointNumerator :=
  HedgeWitness.ofForests query.jointNumerator large small roots child large_forest small_forest
    (by
      change forall node : Fin signature.count, small node = true -> large node = true
      decide +kernel) (by decide +kernel)
    ((NodeSet.disjointBool_eq_true_iff _ _).mp (by decide +kernel)) roots_reach

private theorem allowed : forall node, witness.rootReadoutNodes node = true ->
    witness.small node = true ∨ witness.large node = false := by decide +kernel

private theorem condition_before_root : forall node, query.condition node = true -> node.val < lastRoot.val :=
  by decide +kernel

/-- The old protected-conditioner and queried-root constructions both
fail their geometric tests in this example.  The omitted root also has a
real new-flow child, so the old unused-root marginal cannot be invoked. -/
theorem conditioner_and_routed_root_geometry : witness.smallOutcomeFlowNodes internalNode = true ∧
    witness.carrierFlowProtectedNodes internalNode = false ∧ witness.child internalNode = some lastRoot ∧
    NodeSet.meetsBool witness.roots query.outcome = false ∧
    witness.largeOutcomeFlowSuccessor lastRoot = some outcomeNode := by decide +kernel

theorem condition_not_protected : Not (NodeSet.Subset query.condition witness.carrierFlowProtectedNodes) := by
  intro conditionProtected
  have selected := conditionProtected internalNode (by decide +kernel)
  rw [conditioner_and_routed_root_geometry.2.1] at selected
  cases selected

noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  witness.positiveConditionalCounterexampleOfCarrierFlowOfConditionBeforeSmall rich allowed lastRoot
    (by decide +kernel) condition_before_root

/-- Complete three-value conditioning kernels agree in these exact
positive counterexample endpoints, not just in an unmodified base pair. -/
theorem denominator_matches : query.jointDenominator.ValueEquivalent counterexample.left counterexample.right :=
  witness.carrierDefectParityModels_carrierFlowReadoutPlan_valueEquivalent_of_parentClosed rich
    (fun _node => FiniteProbRecord.biasedFlip 1 1 (by decide)) (hedgeCarrierPrefixNodes lastRoot)
    (witness.carrierFlowParentClosed_prefix lastRoot) lastRoot (by decide +kernel) (by decide +kernel)
    query.jointDenominator (fun node selected => decide_eq_true (condition_before_root node selected))

theorem query_not_identifiable : Not ((GraphModelClass.positive graph).conditionalIdentifiable query) :=
  counterexample.not_identifiable

/-! ## A non-root balancing equation -/

def earlierQuery : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcomeNode
  action := NodeSet.singleton actionNode
  condition := NodeSet.singleton outsideNode
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

private theorem earlier_roots_reach : forall root, witness.roots root = true -> Exists fun outcome =>
    earlierQuery.jointNumerator.outcome outcome = true ∧
      DirectedReachableBy signature (fun parent child =>
        mutilatedDirected signature earlierQuery.action parent child = true) root outcome := by
  intro root selected
  have onlyRoots : forall node : Fin signature.count, witness.roots node = true -> node = firstRoot ∨ node = lastRoot :=
    by decide +kernel
  cases onlyRoots root selected with
  | inl same =>
      subst root
      exact ⟨outsideNode, by decide +kernel, .tail (.refl firstRoot)
        (by decide +kernel : mutilatedDirected signature earlierQuery.action firstRoot outsideNode = true)⟩
  | inr same =>
      subst root
      exact ⟨outcomeNode, by decide +kernel, .tail (.refl lastRoot)
        (by decide +kernel : mutilatedDirected signature earlierQuery.action lastRoot outcomeNode = true)⟩

noncomputable def earlierWitness : HedgeWitness graph earlierQuery.jointNumerator :=
  witness.retargetQuery earlierQuery.jointNumerator (by decide +kernel) witness.small_avoids_intervention earlier_roots_reach

/-- The omitted small vertex is not a common root and has its original
kept child.  Meanwhile the conditioner is an installed outside readout. -/
theorem nonroot_geometry : earlierWitness.small internalNode = true ∧ earlierWitness.roots internalNode = false ∧
    earlierWitness.child internalNode = some lastRoot ∧ earlierWitness.smallOutcomeFlowNodes outsideNode = true ∧
    earlierWitness.carrierFlowProtectedNodes outsideNode = false ∧
    NodeSet.meetsBool earlierWitness.roots earlierQuery.outcome = false := by decide +kernel

noncomputable def earlierCounterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) earlierQuery :=
  earlierWitness.positiveConditionalCounterexampleOfCarrierFlowOfConditionBeforeSmall rich
    (by decide +kernel) internalNode nonroot_geometry.1 (by decide +kernel)

/-- The non-root case matches the full conditioning kernels in its own
actual countermodel pair as well; the earlier query is not substituted by
the first query's denominator or first query's readout plan. -/
theorem earlier_denominator_matches :
    earlierQuery.jointDenominator.ValueEquivalent earlierCounterexample.left earlierCounterexample.right :=
  earlierWitness.carrierDefectParityModels_carrierFlowReadoutPlan_valueEquivalent_of_parentClosed rich
    (fun _node => FiniteProbRecord.biasedFlip 1 1 (by decide)) (hedgeCarrierPrefixNodes internalNode)
    (earlierWitness.carrierFlowParentClosed_prefix internalNode) internalNode nonroot_geometry.1
    (by decide +kernel) earlierQuery.jointDenominator (by
      change forall node : Fin signature.count,
        earlierQuery.jointDenominator.outcome node = true -> hedgeCarrierPrefixNodes internalNode node = true
      decide +kernel)

theorem earlier_query_not_identifiable : Not ((GraphModelClass.positive graph).conditionalIdentifiable earlierQuery) :=
  earlierCounterexample.not_identifiable

/-! ## Actual irreducible failures of the public engines -/

private def failed (result : IdentificationOutcome signature) : Bool :=
  match result with
  | .failed _ => true
  | _ => false

theorem no_exchange : (conditionalExchangeStep? graph query).isNone = true := by decide +kernel
theorem joint_program_failed : failed (identifyJointKernel graph query.jointNumerator) = true := by decide +kernel
theorem conditional_program_failed : failed (identifyConditionalKernel graph query) = true := by decide +kernel
theorem earlier_no_exchange : (conditionalExchangeStep? graph earlierQuery).isNone = true := by decide +kernel
theorem earlier_joint_program_failed : failed (identifyJointKernel graph earlierQuery.jointNumerator) = true := by decide +kernel
theorem earlier_conditional_program_failed : failed (identifyConditionalKernel graph earlierQuery) = true := by decide +kernel

end HedgeConditionalClosedReentry
end Examples
end Causality
end Thesis
