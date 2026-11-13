import Thesis.CausalTransport.ConditionalFailureTraceConnectivity
import Thesis.Examples.ConditionalFailureIncidenceDirection
import Thesis.Examples.ConditionalFailureCoreIncidence

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureIncidenceConnectivity

open Probability FiniteBooleanInteraction PathSpecification
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation

/-!
# Whole actual approach and trace connections on genuine conditional hedges

The outside-Small-pivot fixture has the literal mandatory approach `U,R,P`.
The general local edge theorem lifts both actual causal steps to the tested
incidence graph, and every listed row connects back to original Small source
`U`.  Thus the actual outcome incidence at outside-Small `P` reaches Small
at the original observed-count bound, without a manually supplied basis
column, a guessed short route, or evaluation of opaque normalization.

The collider fixture has complete actual traces inside Small.  Its real
pruned union, opaque normal form and hard-boundary certificate exercise the
universal trace-edge and trace-to-collider-head results even at that overlap.
No disjoint auxiliary domain or duplicate background installation is used.

These are clients of the universal whole-approach and whole-trace theorems.
They do not replace the missing terminal argument that connects an arbitrary
constructed outcome component to a genuine mandatory approach contact.
-/

namespace OutsideSmallPivot

open CurrentConditionalFailureSmallPrefixDirection

private theorem source_in_small : witness.small source = true := by decide +kernel

private theorem pivot_visited : pivotNode ∈
    (normal.forkApproachPath boundary pivot forest source source_in_small).nodes := by
  change pivotNode ∈ CurrentConditionalFailureForkApproach.approach.nodes
  rw [CurrentConditionalFailureForkApproach.actual_path]
  decide +kernel

/-- Both genuine steps of the actual complete prefix are incidence
edges; the receiving evidence row is included in the same literal list. -/
theorem actual_two_approach_edges :
    normal.forkPairIncidence boundary pivot forest source commonRoot = true ∧
      normal.forkPairIncidence boundary pivot forest commonRoot pivotNode = true := by
  have consecutive := normal.forkApproachPath_incidence_consecutive boundary pivot forest source source_in_small
  change Consecutive _ CurrentConditionalFailureForkApproach.approach.nodes at consecutive
  rw [CurrentConditionalFailureForkApproach.actual_path] at consecutive
  exact ⟨consecutive.1, consecutive.2.1⟩

/-- The universal whole-prefix theorem connects outside-Small `P` back
to original Small `U`.  It is not necessary to replace that source by the
intermediate Small root or supply a manually selected two-edge walk. -/
theorem actual_pivot_reaches_source :
    FiniteReachability.Reachable (normal.forkPairIncidence boundary pivot forest) pivotNode source :=
  normal.forkApproachPath_member_reaches_source boundary pivot forest source source_in_small pivotNode pivot_visited

/-- The receiving pivot is genuinely in the computed all-Small prefix
union, although its original Small-membership test is false. -/
theorem actual_pivot_contact : normal.forkApproachNodes boundary pivot forest pivotNode = true :=
  normal.forkApproachPath_retained boundary pivot forest source source_in_small pivotNode pivot_visited

/-- The actual outcome scan returns `P`, so the universal starting-contact
theorem proves the complete finite Small search at the unchanged bound. -/
theorem actual_connection_at_original_bound : normal.forkOutcomeReachesSmallTest boundary pivot forest signature.count = true := by
  apply normal.forkOutcomeReachesSmallTest_of_starting_approach boundary pivot forest
  rw [CurrentConditionalFailureIncidenceDirection.actual_starting_row]
  exact actual_pivot_contact

/-- The original-label positive countermodels follow from the general
whole-approach connection, rather than a fixture's separately proved phase
gap or its one-edge search result from the earlier direction regression. -/
noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  conditionalCounterexampleOfForkIncidenceReachability witness rich boundary pivot normal forest
    signature.count actual_connection_at_original_bound

theorem query_not_identifiable : ¬ (GraphModelClass.positive graph).conditionalIdentifiable query :=
  counterexample.not_identifiable

end OutsideSmallPivot

namespace SmallOverlap

open CurrentConditionalFailureActivationSelection
open CurrentConditionalFailureCoreIncidence.SmallOverlap

/-- Every real trace transmitter is recognized by the actual installed
pair graph, even though its row is already a mandatory Small mechanism. -/
theorem actual_trace_incidence_edge {parent next : Fin signature.count}
    (selected : normal.activationTraceNodes retainedPivot cutForest parent = true)
    (edge : normal.activationTraceSuccessor retainedPivot cutForest parent = some next) :
    normal.forkPairIncidence boundary retainedPivot cutForest parent next = true :=
  normal.activationTrace_incidence_edge boundary retainedPivot cutForest selected edge

/-- The opaque actual trace union supplies a genuine original collider
head connection for every selected row.  The auxiliary policy's irrelevant
ancestors do not enter this conclusion or the installed row selection. -/
theorem actual_trace_reaches_head (node : Fin signature.count)
    (selected : normal.activationTraceNodes retainedPivot cutForest node = true) :
    Exists fun collider : Fin signature.count => normal.colliderSeeds collider = true ∧ normal.pathHeads collider = true ∧
      FiniteReachability.Reachable (normal.forkPairIncidence boundary retainedPivot cutForest) node collider :=
  normal.activationTraceNodes_reaches_head boundary retainedPivot cutForest node selected

/-- Every actual trace row is also a genuine mandatory approach contact
in this fixture.  Small overlap is proved by the structural normal-form
theorem, not by executing its exhaustive path search. -/
theorem actual_trace_is_approach_contact (node : Fin signature.count)
    (selected : normal.activationTraceNodes retainedPivot cutForest node = true) :
    normal.forkApproachNodes boundary retainedPivot cutForest node = true :=
  boundary.small_subset_absorbingNodes _ _ node (normal_trace_union_inside_small node selected)

end SmallOverlap
end CurrentConditionalFailureIncidenceConnectivity
end Examples
end Causality
end Thesis
