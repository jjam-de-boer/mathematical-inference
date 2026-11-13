import Thesis.CausalTransport.ProjectionTemplateRepresentation
import Thesis.Examples.HiddenDAGCollapse
import Thesis.Examples.HiddenDAGMultivaluedPresentation

namespace Thesis.Causality.Examples.ProjectionTemplateRepresentation

open Probability

/-!
# Projection-wide native and finite-template coverage regressions

The original hidden-relay fixture and the three-valued finite-population
fixture have different full hidden graphs. Each enters the actual model
domain at its observed projection, without a fixed hidden topology or a
caller-supplied simulation interface. Its clique representative preserves
every intervention and event. Its finite structural representative preserves
the entire observational law and the explicitly retained targets.

The relay check retains a factual zero and a nonzero causal effect after
eliminating an internal hidden node and grouping a three-child shared root.
The multivalued check retains the whole count law, not just a Boolean
readout, and permits forcing a declared value that has observational mass
zero. Supported conditioning keeps the original positive causal evidence.

No large structural catalogue is evaluated here. Membership is supplied by
the constructive general theorem. The irreducible representation boundaries
prevent interface elaboration from expanding the source-compression program;
their bodies are still checked normally, with no resource-limit increase.
-/

namespace HiddenRelay

open HiddenDAGCollapse

def original : ProjectedHiddenDAGModel projection.observedGraph :=
  .ofModel model (fun _ _ => rfl)

def native : FiniteHiddenDAGSCM signature projection.observedGraph.cliqueRootProjection :=
  original.cliqueRepresentative

theorem every_interventional_event (intervention : HardIntervention signature) (event : Event signature.Assignment) :
    QProb.Equiv (native.interventionalValue intervention event) (model.interventionalValue intervention event) :=
  original.cliqueRepresentative_interventionalValue intervention event

theorem native_observational_zero : (native.observationalValue (fun values => values y)).num = 0 :=
  (QProb.equiv_num_zero_iff (original.cliqueRepresentative_observationalValue _)).mpr observational_y_true_zero

theorem native_causal_half :
    QProb.Equiv (native.interventionalValue forceXFalse (fun values => values y)) ⟨1, 2, by decide⟩ :=
  QProb.equiv_trans (every_interventional_event forceXFalse _) interventional_y_true_half

def target : NativeProbabilityQuery signature := ⟨forceXFalse, fun values => values y⟩

@[irreducible] def represented : Causality.ProjectionTemplateRepresentation original [target] :=
  original.projectionTemplateRepresentation [target]

theorem catalogue_member : represented.template ∈ projection.observedGraph.cliqueRootProjection.hiddenDAG.nativeTemplateCatalogue
    (FiniteHiddenDAGSCM.representationNodeBound projection.observedGraph.cliqueRootProjection 1)
    (FiniteHiddenDAGSCM.representationSourceBound signature 1) := represented.listed

theorem all_observed_events (event : Event signature.Assignment) :
    QProb.Equiv (represented.model.observationalValue event) (model.observationalValue event) := represented.observational event

theorem selected_effect : QProb.Equiv (represented.model.interventionalValue forceXFalse (fun values => values y))
    (model.interventionalValue forceXFalse (fun values => values y)) := represented.preserved target List.mem_cons_self

theorem represented_observational_zero : (represented.model.observationalValue (fun values => values y)).num = 0 :=
  (QProb.equiv_num_zero_iff (all_observed_events _)).mpr observational_y_true_zero

theorem represented_causal_half :
    QProb.Equiv (represented.model.interventionalValue forceXFalse (fun values => values y)) ⟨1, 2, by decide⟩ :=
  QProb.equiv_trans selected_effect interventional_y_true_half

/-- The standalone instance is in the same original-graph domain. It does
not merely live in an unproved surrogate class with the right probabilities. -/
def standaloneMember : ProjectedHiddenDAGModel projection.observedGraph := represented.asProjectedModel

@[irreducible] def conditionalRepresentation (intervention : HardIntervention signature) (evidence event : Event signature.Assignment) :
    Causality.ProjectionTemplateRepresentation original
      [⟨intervention, fun values => evidence values && event values⟩, ⟨intervention, evidence⟩] :=
  original.projectionTemplateRepresentation _

theorem arbitrary_supported_conditional (intervention : HardIntervention signature) (evidence event : Event signature.Assignment)
    (supported : (model.interventionalDist intervention).EventPositive evidence) :
    let retained := conditionalRepresentation intervention evidence event
    let evidenceListed : (⟨intervention, evidence⟩ : NativeProbabilityQuery signature) ∈
        [⟨intervention, fun values => evidence values && event values⟩, ⟨intervention, evidence⟩] :=
      List.mem_cons_of_mem _ List.mem_cons_self
    QProb.Equiv
      (((retained.model.interventionalDist intervention).conditionOn evidence
        ((retained.query_eventPositive_iff ⟨intervention, evidence⟩ evidenceListed).mpr supported)).probVal event)
      (((model.interventionalDist intervention).conditionOn evidence supported).probVal event) := by
  dsimp only
  exact (conditionalRepresentation intervention evidence event).conditionOn_probVal intervention evidence event
    List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) supported

end HiddenRelay

namespace Multivalued

open HiddenDAGMultivaluedPresentation

def original : ProjectedHiddenDAGModel projection.observedGraph :=
  .ofModel model (fun _ _ => rfl)

def native : FiniteHiddenDAGSCM signature projection.observedGraph.cliqueRootProjection :=
  original.cliqueRepresentative

theorem every_interventional_event (intervention : HardIntervention signature) (event : Event signature.Assignment) :
    QProb.Equiv (native.interventionalValue intervention event) (model.interventionalValue intervention event) :=
  original.cliqueRepresentative_interventionalValue intervention event

theorem entire_count_law (intervention : HardIntervention signature) (unforced : intervention.value y = none) (event : Event Nat) :
    QProb.Equiv (native.interventionalValue intervention (fun values => event (readValue (values y)))) (counts.record.probVal event) :=
  QProb.equiv_trans (every_interventional_event intervention _) (interventional_y_event intervention unforced event)

theorem native_null_observation :
    QProb.Equiv (native.observationalValue (fun values => decide (readValue (values y) = 2))) QProb.zero :=
  QProb.equiv_trans (original.cliqueRepresentative_observationalValue _) null_observed_y

theorem native_null_intervention :
    QProb.Equiv (native.interventionalValue ((HardIntervention.empty signature).set y nullCode)
      (fun values => decide (readValue (values y) = 2))) QProb.one :=
  QProb.equiv_trans (every_interventional_event _ _) do_y_null_probability_one

def nullTarget : NativeProbabilityQuery signature :=
  ⟨(HardIntervention.empty signature).set y nullCode, fun values => decide (readValue (values y) = 2)⟩

@[irreducible] def represented : Causality.ProjectionTemplateRepresentation original [nullTarget] :=
  original.projectionTemplateRepresentation [nullTarget]

theorem catalogue_member : represented.template ∈ projection.observedGraph.cliqueRootProjection.hiddenDAG.nativeTemplateCatalogue
    (FiniteHiddenDAGSCM.representationNodeBound projection.observedGraph.cliqueRootProjection 1)
    (FiniteHiddenDAGSCM.representationSourceBound signature 1) := represented.listed

theorem entire_observational_count_law (event : Event Nat) :
    QProb.Equiv (represented.model.observationalValue (fun values => event (readValue (values y)))) (counts.record.probVal event) :=
  QProb.equiv_trans (represented.observational _) (observational_y_event event)

theorem represented_null_observation :
    QProb.Equiv (represented.model.observationalValue (fun values => decide (readValue (values y) = 2))) QProb.zero :=
  QProb.equiv_trans (represented.observational _) null_observed_y

theorem represented_null_intervention :
    QProb.Equiv (represented.model.interventionalValue ((HardIntervention.empty signature).set y nullCode)
      (fun values => decide (readValue (values y) = 2))) QProb.one :=
  QProb.equiv_trans (represented.preserved nullTarget List.mem_cons_self) do_y_null_probability_one

end Multivalued
end Thesis.Causality.Examples.ProjectionTemplateRepresentation
