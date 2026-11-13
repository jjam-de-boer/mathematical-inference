import Thesis.CausalTransport.ConditionalFailureTraceConnectivity

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S} {query : ConditionalKernelQuery S}

/-!
# The first conditioned Small approach has a genuine path/trace/fork contact

A retained conditioner alone does not say that its normalized interaction is
connected to the mandatory Small routing.  Here the pivot is the literal first
conditioned endpoint of an actual Small-source approach.  The fork-aware
prefix ends at its first combined interaction contact on that same old list.

That contact cannot be an unrelated extra conditioner: the original complete
approach stops at its first queried row, so a conditioned contact must be its
own endpoint/pivot.  The exact incoming-cut path makes that pivot a real head.
Every other combined contact is therefore a genuine normalized path head,
an actual pruned activation trace row, or an omitted normalized fork.

The contact is truly retained by the complete mandatory approach union,
including zero-edge contacts and contacts outside Small.  The existing
whole-approach and whole-trace theorems finish its route back to Small.
Accordingly, if all normalized heads are connected to the actual outcome
incidence, the complete original-count Small search succeeds without another
contact, parity, row coverage or outcome-freedom flag.

This proves the connected-head branch of the terminal reduction.  It does
not assume that arbitrary retained pivots work, or prove that all heads are
connected when a retained fork cancels its preceding read.  The remaining
normalized-path argument is supplied by `ConditionalFailureHeadConnectivity`:
it reaches a genuine approach contact at such a barrier or derives this
connected-head branch from the actual geometry.
-/

namespace FirstConditionedSmallApproach

variable {w : HedgeWitness graph query.jointNumerator}
    (boundary : ConditionedSmallFlowBoundary w) (approach : FirstConditionedSmallApproach w)
    (normal : ConditionalBackdoorPathNormalForm graph query approach.pivot.node)
    (forest : ConditionalCutColliderActivationForest query approach.pivot.node)

/-- The receiving endpoint of the actual fork-aware prefix from this
original Small source.  The original complete approach is not replaced by
a newly selected route or a later reachable conditioner. -/
def incidenceContact : Fin S.count :=
  (normal.forkApproachPath boundary approach.pivot forest approach.source approach.source_in_small).endpoint

/-- The computed contact belongs to the actual complete prefix union,
even if its original Small-membership test is false or a fork later resumes. -/
theorem incidenceContact_retained :
    normal.forkApproachNodes boundary approach.pivot forest
      (approach.incidenceContact boundary normal forest) = true :=
  normal.forkApproachPath_retained boundary approach.pivot forest approach.source approach.source_in_small _
    (List.mem_of_getLast? (normal.forkApproachPath boundary approach.pivot forest approach.source approach.source_in_small).finishes)

/-- The same contact is on the original complete first-conditioned list.
Complete stopped-path determinism identifies that list with the boundary's
canonical output; the proof does not evaluate either finite route search. -/
theorem incidenceContact_visited_original :
    approach.incidenceContact boundary normal forest ∈ approach.path.nodes := by
  have receives : NodeSet.Subset query.condition (normal.forkAbsorptionTargets approach.pivot forest) := fun row selected =>
    NodeSet.subset_union_left _ _ row (NodeSet.subset_union_right _ _ row selected)
  have visited := boundary.interactionStopPath_subset_boundary
    (normal.forkAbsorptionTargets approach.pivot forest) receives approach.source approach.source_in_small
    (approach.incidenceContact boundary normal forest)
    (List.mem_of_getLast? (normal.forkApproachPath boundary approach.pivot forest approach.source approach.source_in_small).finishes)
  rw [approach.path.nodes_eq_of_same_source (w.conditionalBoundaryPath approach.source approach.source_in_small)]
  exact visited

/-- Original full-query outcome avoidance survives the computed first
contact, including its receiving endpoint.  The approach ends at a
conditioner, not at an omitted or newly invented outcome. -/
theorem incidenceContact_outcome_free : query.outcome (approach.incidenceContact boundary normal forest) = false :=
  approach.outcome_free _ (approach.incidenceContact_visited_original boundary normal forest)

/-- The real first combined contact is a path head, a real activation
trace row, or an omitted normalized fork.  A conditioner-only contact is
the actual first pivot and hence a genuine incoming path head. -/
theorem incidenceContact_head_or_trace_or_fork :
    normal.pathHeads (approach.incidenceContact boundary normal forest) = true ∨
      normal.activationTraceNodes approach.pivot forest (approach.incidenceContact boundary normal forest) = true ∨
      normal.cutPath.forkNodes (approach.incidenceContact boundary normal forest) = true := by
  have target := normal.forkApproachPath_endpoint_target boundary approach.pivot forest approach.source approach.source_in_small
  change normal.forkAbsorptionTargets approach.pivot forest (approach.incidenceContact boundary normal forest) = true at target
  rcases Bool.or_eq_true_iff.mp target with core | fork
  · rcases Bool.or_eq_true_iff.mp core with activation | conditioned
    · rcases Bool.or_eq_true_iff.mp activation with head | trace
      · exact Or.inl head
      · exact Or.inr (Or.inl trace)
    · have same := approach.conditioned_member_eq_endpoint _
        (approach.incidenceContact_visited_original boundary normal forest) conditioned
      change approach.incidenceContact boundary normal forest = approach.pivot.node at same
      apply Or.inl
      rw [same]
      exact (normal.pathDirection_source_odd approach.pivot.selected).1
  · exact Or.inr (Or.inr fork)

/-- Connected actual normalized heads close every genuine first-contact
case at the original finite bound.  Trace contacts are connected to their
own collider heads; a retained fork contact is connected to its actual
following head, never by an invented edge to its canceled preceding head.
The connected-head premise is a graph proof obligation, not a theorem of
arbitrary retained-pivot membership or a published terminal-readiness field. -/
theorem forkOutcomeReachesSmallTest_of_pathHeads_connected
    (headsConnected : forall head, normal.pathHeads head = true ->
      FiniteReachability.Reachable (normal.forkPairIncidence boundary approach.pivot forest)
        (normal.forkOutcomeIncidenceRow boundary approach.pivot forest) head) :
    normal.forkOutcomeReachesSmallTest boundary approach.pivot forest S.count = true := by
  let contact := approach.incidenceContact boundary normal forest
  have retained := approach.incidenceContact_retained boundary normal forest
  apply normal.forkOutcomeReachesSmallTest_of_approach_contact boundary approach.pivot forest contact retained
  rcases approach.incidenceContact_head_or_trace_or_fork boundary normal forest with head | trace | fork
  · exact headsConnected contact head
  · rcases normal.activationTraceNodes_reaches_head boundary approach.pivot forest contact trace with
      ⟨collider, _seed, head, toCollider⟩
    exact LinearSignal.pairIncidence_reachable_trans _ _ _ _ (headsConnected collider head)
      (LinearSignal.pairIncidence_reachable_swap _ _ _ _ toCollider)
  · rcases normal.retainedFork_incidence_edge boundary approach.pivot forest contact fork retained with ⟨next, head, edge⟩
    have reverseEdge := (normal.forkPairIncidence_swap boundary approach.pivot forest next contact).trans edge
    exact LinearSignal.pairIncidence_reachable_trans _ _ _ _ (headsConnected next head)
      (FiniteReachability.Reachable.prepend reverseEdge (FiniteReachability.Reachable.refl _ contact))

end FirstConditionedSmallApproach
end Causality
end Thesis
