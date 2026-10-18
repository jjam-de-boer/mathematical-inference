import Thesis.Causality.LatentRootGrouping
import Thesis.Examples.HiddenDAGCollapse

namespace Thesis.Causality.Examples.LatentRootGrouping

open Probability HiddenDAGCollapse

/-!
# Group a genuine three-child hidden cause after eliminating a hidden relay

The original five-node native fixture has observational zeros and a shared
root reaching three observed children, one through an internal hidden relay.
Compose its proved collapse with the new grouped root-model constructor.
All interventions and events are compared with the original native record;
no canonical two-child compatibility hypothesis can be supplied or is needed.
The explicit common group is still incident to all three children.
-/

def grouped := model.toLatentRootSCM.cliqueGroupedModel projection.observedGraph
  (fun left right => model.toLatentRootSCM_projectedGraph left right)

theorem fixed_root_count : grouped.latent.count = projection.observedGraph.cliqueRootCount := rfl

theorem projected_graph_exact (left right : Fin signature.count) :
    grouped.latent.projectedBidirected left right = projection.observedGraph.bidirected left right :=
  model.toLatentRootSCM.cliqueGroupedModel_projectedGraph projection.observedGraph
    (fun first second => model.toLatentRootSCM_projectedGraph first second) left right

theorem every_interventional_event (intervention : HardIntervention signature) (event : Event signature.Assignment) :
    QProb.Equiv (grouped.interventionalValue intervention.value event) (model.interventionalValue intervention event) := by
  have preserved := model.toLatentRootSCM.cliqueGroupedModel_interventionalValue projection.observedGraph
    (fun left right => model.toLatentRootSCM_projectedGraph left right) intervention.value event
  rw [model.toLatentRootSCM_interventionalValue] at preserved
  exact preserved

theorem every_observational_event (event : Event signature.Assignment) :
    QProb.Equiv (grouped.observationalValue event) (model.observationalValue event) := by
  have preserved := model.toLatentRootSCM.cliqueGroupedModel_observationalValue projection.observedGraph
    (fun left right => model.toLatentRootSCM_projectedGraph left right) event
  rw [model.toLatentRootSCM_observationalValue] at preserved
  exact preserved

theorem observational_zero_retained : (grouped.observationalValue (fun assignment => assignment y)).num = 0 :=
  (QProb.equiv_num_zero_iff (every_observational_event _)).mpr observational_y_true_zero

theorem nonzero_intervention_retained :
    QProb.Equiv (grouped.interventionalValue forceXFalse.value (fun assignment => assignment y)) ⟨1, 2, by decide⟩ :=
  QProb.equiv_trans (every_interventional_event forceXFalse _) interventional_y_true_half

def sharedGroup : Fin projection.observedGraph.cliqueRootCount :=
  model.toLatentRootSCM.cliqueGroupOwner projection.observedGraph
    (fun left right => model.toLatentRootSCM_projectedGraph left right) u

theorem sharedGroup_incident (child : Fin signature.count) :
    grouped.latent.incident sharedGroup child = model.toLatentRootSCM.latent.incident u child :=
  congrFun (model.toLatentRootSCM.cliqueGroupOwner_mask projection.observedGraph
    (fun left right => model.toLatentRootSCM_projectedGraph left right) u) child

/-- Grouping retains the shared source as one permitted three-child input;
it does not silently turn the model into independent pair-root form. -/
theorem grouped_not_canonical : ¬ grouped.IsCanonicalSemiMarkovian := by
  intro canonical
  have atX : grouped.latent.incident sharedGroup x = true :=
    (sharedGroup_incident x).trans shared_root_three_children.1
  have atY : grouped.latent.incident sharedGroup y = true :=
    (sharedGroup_incident y).trans shared_root_three_children.2.1
  have atZ : grouped.latent.incident sharedGroup z = true :=
    (sharedGroup_incident z).trans shared_root_three_children.2.2
  rcases canonical sharedGroup x y z atX atY atZ with same | same | same
  · exact (by decide : x ≠ y) same
  · exact (by decide : x ≠ z) same
  · exact (by decide : y ≠ z) same

end Thesis.Causality.Examples.LatentRootGrouping
