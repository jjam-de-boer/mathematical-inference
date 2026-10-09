import Thesis.CausalTransport.ConditionalFailureFlowBoundary
import Thesis.Examples.ConditionalFailureActivationSelectionGraph

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureFlowBoundary

open PathSpecification HedgeChannelInstallation HedgeChannelEnvironmentInstallation

/-!
# First-queried stopping and the exhaustive Small-source boundary

The first graph has three three-valued vertices `Y,X,R`, with arrows
`Y -> R`, `X -> R` and genuine bidirected pairs `Y <-> R`, `X <-> R`.
For the unchanged query `P(Y | do(X), R)`, the displayed hedge has Small
`Y,R` and root `R`.  The old composed flow sends `Y` into conditioned `R`;
the stored action-root path also starts at `R`.  Neither of those paths
supplies an unconditioned direction under the old policy.

The new policy stops at queried `Y` itself.  Its complete path is a genuine
unconditioned singleton from a Small source different from the action root.
The general arbitrary-forest theorem therefore installs all mandatory Small
rows and supplies a positive full-original-alphabet countermodel.  No model
prior, likelihood table, or conditional probability is evaluated here.

The second check uses the existing genuine collider graph.  Every stopped
Small-source path meets evidence, so the exhaustive classifier returns its
proved hard boundary.  We check the derived Small/outcome disjointness and
retain latest-pivot data; this branch is not misreported as a general parity
construction or as universal conditional completeness.
-/

/-! ## A queried Small source that the original forward policy passes -/

def signature : ObservedSignature where
  count := 3
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (parent.val < 2 ∧ child.val = 2)
  directed_earlier := by intro parent child edge; have parts := of_decide_eq_true edge; omega

def outcomeNode : Fin signature.count := ⟨0, by decide⟩
def actionNode : Fin signature.count := ⟨1, by decide⟩
def conditionNode : Fin signature.count := ⟨2, by decide⟩

def graph : ObservedGraph signature where
  bidirected := fun left right => decide
    ((left.val < 2 ∧ right.val = 2) ∨ (right.val < 2 ∧ left.val = 2))
  bidirected_symmetric := by
    intro left right selected
    exact decide_eq_true ((of_decide_eq_true selected).elim Or.inr Or.inl)
  bidirected_irreflexive := by intro node; apply decide_eq_false; omega

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcomeNode
  action := NodeSet.singleton actionNode
  condition := NodeSet.singleton conditionNode
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := by intro _ same; have values := congrArg Fin.val same; cases values

def selection : HedgeSelection signature where
  large := fun _ => true
  small := NodeSet.union (NodeSet.singleton outcomeNode) (NodeSet.singleton conditionNode)
  child := fun parent => if parent.val < 2 then some conditionNode else none

theorem hedge_tests : hedgeTestsHold graph query.jointNumerator selection = true := by decide +kernel

def witness : HedgeWitness graph query.jointNumerator :=
  hedgeWitness_of_sets graph query.jointNumerator selection hedge_tests

/-- The free queried source is genuinely different from the hedge's stored
root.  The old map forwards it to evidence, whereas the new map stops there. -/
theorem original_and_stopped_routing :
    witness.actionRoot = conditionNode ∧ outcomeNode ≠ witness.actionRoot ∧
    witness.small outcomeNode = true ∧
    witness.smallOutcomeFlowSuccessor outcomeNode = some conditionNode ∧
    witness.conditionalBoundarySuccessor outcomeNode = none := by
  decide +kernel

/-- Even scanning every Small source under the old successor policy would
miss this countermodel family: each complete old path meets conditioned `R`.
The improvement is the certified stopping policy as well as the source scan. -/
theorem old_all_small_paths_conditioned : forall source, forall inside : witness.small source = true,
    (SuccessorPath.ofForest witness.smallOutcomeFlowNodes witness.smallOutcomeFlowSuccessor
      witness.smallOutcomeFlowSuccessor_wellFormed source
      (outcomeFlow_small_subset witness source inside)).nodes.any query.condition = true := by
  decide +kernel

def stoppedPath := witness.conditionalBoundaryPath outcomeNode original_and_stopped_routing.2.2.1

/-- Singleton shape follows from the general complete-path certificates;
the regression does not repeatedly evaluate the bounded trace search. -/
theorem stopped_path_nodes : stoppedPath.nodes = [outcomeNode] :=
  stoppedPath.nodes_eq_singleton_of_source_stopped original_and_stopped_routing.2.2.2.2

private theorem stopped_path_unconditioned :
    forall child, child ∈ stoppedPath.nodes -> query.condition child = false := by
  intro child member
  rw [stopped_path_nodes] at member
  have same : child = outcomeNode := List.mem_singleton.mp member
  subst child
  exact query.outcome_condition_disjoint outcomeNode (by decide)

/-- The actual general forest theorem keeps the full Small phase `Y,R`.
It derives the outcome mask and direction; none is assumed from a numerical
calculation of this example's conditional probabilities. -/
def parity : ConditionalParityWitness witness
    (LinearSignal.ofSuccessor witness.conditionalBoundarySuccessor)
    (LinearSignal.ofSuccessor witness.conditionalBoundarySuccessor) :=
  .ofSuccessorPath witness witness.smallOutcomeFlowNodes witness.conditionalBoundarySuccessor
    witness.conditionalBoundarySuccessor_wellFormed (outcomeFlow_small_subset witness)
    (outcomeFlow_avoids_action witness) witness.conditionalBoundarySinks_queried
    outcomeNode original_and_stopped_routing.2.2.1 stoppedPath stopped_path_unconditioned

/-- Both models are positive on the complete original three-valued graph,
have the same full observational law, and differ on the unchanged query. -/
noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  conditionalCounterexampleOfParity witness rich
    (.ofSuccessor witness.conditionalBoundarySuccessor)
    (.ofSuccessor witness.conditionalBoundarySuccessor) parity

theorem query_not_identifiable : ¬ (GraphModelClass.positive graph).conditionalIdentifiable query :=
  counterexample.not_identifiable

private def counterexampleCase {left : Type _} {right : Type _} : Sum left right -> Bool
  | .inl _ => true
  | .inr _ => false

/-- Only the finite outer tag is reduced.  The actual returned semantic
branch is backed by the independently constructed countermodel above. -/
theorem queried_small_source_returns_counterexample :
    counterexampleCase (witness.conditionalCounterexampleOrSmallFlowBoundary rich) = true := by
  decide +kernel

/-! ## The genuine conditioned branch remains an explicit hard boundary -/

namespace ConditionedCollider

open CurrentConditionalFailureActivationSelection

/-- All three original Small sources are checked, including the collider
and both conditioned roots.  No caller-supplied all-sinks flag is used. -/
def boundary : ConditionedSmallFlowBoundary CurrentConditionalFailureActivationSelection.witness where
  encounters_condition := by decide +kernel

theorem all_sources_return_boundary :
    counterexampleCase (CurrentConditionalFailureActivationSelection.witness.conditionalCounterexampleOrSmallFlowBoundary
      CurrentConditionalFailureActivationSelection.rich) = false := by
  decide +kernel

/-- This disjointness is a conclusion of the exhaustive hard boundary,
not an added restriction on the original hedge or terminal query. -/
theorem small_avoids_outcome : NodeSet.Disjoint CurrentConditionalFailureActivationSelection.witness.small
    CurrentConditionalFailureActivationSelection.query.outcome := boundary.small_avoids_outcome

/-- The returned hard boundary also provides the actual latest reachable
conditioner from the hedge's stored root, through the generic finite search. -/
def latestPivot : LatestConditionalPivot CurrentConditionalFailureActivationSelection.graph
    CurrentConditionalFailureActivationSelection.query CurrentConditionalFailureActivationSelection.witness.actionRoot :=
  boundary.latestPivot CurrentConditionalFailureActivationSelection.witness.actionRoot
    CurrentConditionalFailureActivationSelection.witness.actionRoot_in_small

end ConditionedCollider

end CurrentConditionalFailureFlowBoundary
end Examples
end Causality
end Thesis
