import Thesis.CausalTransport.HiddenDAGNativeTemplateRepresentation
import Thesis.Examples.HiddenDAGFiniteRepresentation
import Thesis.Examples.HiddenDAGMultivaluedPresentation

namespace Thesis.Causality.Examples.HiddenDAGNativeTemplates

open Probability

/-!
# Standalone native coverage with hidden relays and null observed targets

The five-node fixture exercises the uniform full-DAG coverage constructor,
not a caller-supplied transfer interface. Its explicit finite catalogue entry
and rational factors instantiate a native model without a base-model argument.
The original whole observed law and retained effect are preserved.

The multivalued fixture separately tests all-intervention encoding of an
actual rational finite-population distribution. Three public values remain
available; the null value two stays null factually and has mass one when
forced. The regression retains the full count law and supported conditionals,
not merely a Boolean summary. Large structural catalogues are never evaluated
by a decision tactic: membership follows from the general coverage proofs.
-/

namespace HiddenRelay

open HiddenDAGCollapse HiddenDAGSourceCompression

def represented : FiniteHiddenDAGSCM.NativeTemplateRepresentation original [target] :=
  original.nativeTemplateRepresentation [target]

/-- The constructor takes finite structural data and rational factors only. -/
def replay : FiniteHiddenDAGSCM signature projection :=
  represented.template.model (P := projection) represented.factors

theorem catalogue_member : represented.template ∈ fullGraph.nativeTemplateCatalogue
    (FiniteHiddenDAGSCM.representationNodeBound projection 1)
    (FiniteHiddenDAGSCM.representationSourceBound signature 1) := represented.listed

theorem all_observed_events (event : Event signature.Assignment) :
    QProb.Equiv (replay.observationalValue event) (original.observationalValue event) := represented.observational event

theorem selected_effect : QProb.Equiv (replay.interventionalValue target.intervention target.event)
    (original.interventionalValue target.intervention target.event) := represented.preserved target List.mem_cons_self

open HiddenDAGCompactSources

/-- Keep interface elaboration from unfolding five-source compression.
The executable constructor body is still checked and no limit is raised. -/
@[irreducible] def conditionalRepresentation (intervention : HardIntervention signature) (evidence event : Event signature.Assignment) :
    FiniteHiddenDAGSCM.NativeTemplateRepresentation original (conditionalTargets intervention evidence event) :=
  original.nativeTemplateRepresentation (conditionalTargets intervention evidence event)

theorem arbitrary_supported_conditional (intervention : HardIntervention signature) (evidence event : Event signature.Assignment)
    (supported : (original.interventionalDist intervention).EventPositive evidence) :
    let retained := conditionalRepresentation intervention evidence event
    let evidenceListed : (⟨intervention, evidence⟩ : NativeProbabilityQuery signature) ∈ conditionalTargets intervention evidence event :=
      List.mem_cons_of_mem _ List.mem_cons_self
    QProb.Equiv
      (((retained.model.interventionalDist intervention).conditionOn evidence
        ((retained.query_eventPositive_iff ⟨intervention, evidence⟩ evidenceListed).mpr supported)).probVal event)
      (((original.interventionalDist intervention).conditionOn evidence supported).probVal event) := by
  dsimp only
  exact (conditionalRepresentation intervention evidence event).conditionOn_probVal intervention evidence event
    List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) supported

end HiddenRelay

namespace Multivalued

open HiddenDAGMultivaluedPresentation

def sourceCodes (_node : Fin projection.hiddenDAG.count) : ValueEquivalence (Fin witness.card) (Fin witness.card) :=
  ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def template := model.nativeTemplate (fun _ => witness.card) (fun _ => witness.card) (fun _ => conversion) sourceCodes
def factors := model.nativeTemplateFactors (fun _ => witness.card) sourceCodes
def replay : FiniteHiddenDAGSCM signature projection := template.model (P := projection) factors

theorem every_interventional_event (intervention : HardIntervention signature) (event : Event signature.Assignment) :
    QProb.Equiv (replay.interventionalValue intervention event) (model.interventionalValue intervention event) :=
  model.nativeTemplateModel_interventionalValue (fun _ => witness.card) (fun _ => witness.card)
    (fun _ => conversion) sourceCodes intervention event

theorem entire_count_law (intervention : HardIntervention signature) (unforced : intervention.value y = none) (event : Event Nat) :
    QProb.Equiv (replay.interventionalValue intervention (fun values => event (readValue (values y)))) (counts.record.probVal event) :=
  QProb.equiv_trans (every_interventional_event intervention _) (interventional_y_event intervention unforced event)

theorem supported_conditionals (intervention : HardIntervention signature) (evidence event : Event signature.Assignment)
    (supported : (model.interventionalDist intervention).EventPositive evidence) :
    QProb.Equiv
      (((replay.interventionalDist intervention).conditionOn evidence
        ((model.nativeTemplateModel_eventPositive_iff (fun _ => witness.card) (fun _ => witness.card)
          (fun _ => conversion) sourceCodes intervention evidence).mpr supported)).probVal event)
      (((model.interventionalDist intervention).conditionOn evidence supported).probVal event) :=
  model.nativeTemplateModel_conditionOn_probVal (fun _ => witness.card) (fun _ => witness.card)
    (fun _ => conversion) sourceCodes intervention evidence event supported

theorem null_observation_retained :
    QProb.Equiv (replay.observationalValue (fun values => decide (readValue (values y) = 2))) QProb.zero :=
  QProb.equiv_trans (model.nativeTemplateModel_observationalValue (fun _ => witness.card) (fun _ => witness.card)
    (fun _ => conversion) sourceCodes _) null_observed_y

theorem null_intervention_still_permitted :
    QProb.Equiv (replay.interventionalValue ((HardIntervention.empty signature).set y nullCode)
      (fun values => decide (readValue (values y) = 2))) QProb.one :=
  QProb.equiv_trans (every_interventional_event _ _) do_y_null_probability_one

end Multivalued
end Thesis.Causality.Examples.HiddenDAGNativeTemplates
