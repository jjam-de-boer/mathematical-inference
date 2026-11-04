import Thesis.Causality.CausalAbstraction
import Thesis.Causality.Identification

namespace Thesis.Causality
open Probability

/-!
Cluster-local queries pull outcome and action node sets back to unions of
micro clusters. Locality of the assignment map transports outcome events.
This is a syntactic/semantic locality statement, not identification over a
whole graph class: exactness of one pair of SCMs does not provide a lift of
all observationally equivalent macro models to equivalent micro models.
-/

namespace FiniteCausalCoarseGraining

theorem microNodes_disjoint (coarsening : FiniteCausalCoarseGraining micro coarse)
    (left right : NodeSet coarse) (disjoint : NodeSet.Disjoint left right) :
    NodeSet.Disjoint (coarsening.microNodes left) (coarsening.microNodes right) := by
  intro member onLeft
  cases onRight : coarsening.microNodes right member with
  | false => rfl
  | true =>
    obtain ⟨first, firstSelected⟩ := (finAny_eq_true_iff _).mp onLeft
    obtain ⟨second, secondSelected⟩ := (finAny_eq_true_iff _).mp onRight
    have firstParts := Bool.and_eq_true_iff.mp firstSelected
    have secondParts := Bool.and_eq_true_iff.mp secondSelected
    by_cases same : first = second
    · subst second
      have excluded := disjoint first firstParts.1
      rw [secondParts.1] at excluded
      cases excluded
    · have excluded := coarsening.cluster_disjoint first second same member firstParts.2
      rw [secondParts.2] at excluded
      cases excluded

/-- Pull both query node sets back to entire observed-node clusters. -/
def pullbackQuery (coarsening : FiniteCausalCoarseGraining micro coarse)
    (query : JointKernelQuery coarse) : JointKernelQuery micro where
  outcome := coarsening.microNodes query.outcome
  action := coarsening.microNodes query.action
  action_outcome_disjoint := coarsening.microNodes_disjoint _ _ query.action_outcome_disjoint

/-- Explicit τ-locality for a supplied fine/coarse query pair. -/
def PullsBackQuery (coarsening : FiniteCausalCoarseGraining micro coarse)
    (fineQuery : JointKernelQuery micro) (coarseQuery : JointKernelQuery coarse) : Prop :=
  fineQuery.outcome = coarsening.microNodes coarseQuery.outcome ∧
  fineQuery.action = coarsening.microNodes coarseQuery.action

theorem pullbackQuery_local (coarsening : FiniteCausalCoarseGraining micro coarse)
    (query : JointKernelQuery coarse) : coarsening.PullsBackQuery (coarsening.pullbackQuery query) query :=
  ⟨rfl, rfl⟩

/-- Every event local to the macro outcome pulls back to an event local
to the union of its micro clusters, including nonlinear aggregation. -/
theorem pullback_event_local (coarsening : FiniteCausalCoarseGraining micro coarse)
    (nodes : NodeSet coarse) (event : Event coarse.Assignment)
    (localEvent : EventDependsOnlyOn nodes event) :
    EventDependsOnlyOn (coarsening.microNodes nodes) (fun state => event (coarsening.assignmentMap state)) := by
  intro first second agree
  apply localEvent
  intro node selected
  apply coarsening.coordinate_local node first second
  intro member inCluster
  apply agree member
  exact (finAny_eq_true_iff _).mpr ⟨node, Bool.and_eq_true_iff.mpr ⟨selected, inCluster⟩⟩

end FiniteCausalCoarseGraining
end Thesis.Causality
