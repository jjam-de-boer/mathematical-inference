import Thesis.CausalTransport.HiddenDAGSourcePresentation
import Thesis.Examples.HiddenDAGMultivaluedPresentation
import Thesis.Examples.HiddenDAGSourceCompression

namespace Thesis.Causality.Examples.HiddenDAGSourcePresentation

open Probability

/-!
# Finite source codes are private, not restrictions on observed values

The three-valued native fixture has a permitted but factually null observed
value two. Its private sources have only two atom occurrences. Presenting
those sources therefore reduces each private alphabet from three values to
two codes, while every observed value and every intervention target stays
available. All-event and supported-conditional theorems use the actual new
native evaluator and canonical product prior.

A second symbolic regression uses the existing five-node hidden graph with
a hidden relay and a shared three-child ancestor. This checks that the
adapter does not secretly assume observed-only graphs or pairwise roots.
Its duplicate source occurrences are retained as sampling codes, not exposed
as new observable labels. No large source cube is reduced in the kernel.
-/

namespace Multivalued

open HiddenDAGMultivaluedPresentation

def presentations (node : Fin projection.hiddenDAG.count) := (model.factor node).atomPresentation
def presented := model.presentSources presentations

theorem two_private_codes (node : Fin projection.hiddenDAG.count) : (presentations node).card = 2 := by
  change coded.record.atoms.length = 2
  decide +kernel

theorem private_alphabet_strictly_smaller (node : Fin projection.hiddenDAG.count) :
    (presented.noiseEnumeration node).length < (model.noiseEnumeration node).length := by
  change (List.finRange (presentations node).card).length < (List.finRange witness.card).length
  rw [List.length_finRange, List.length_finRange, two_private_codes, domain_card]
  decide

theorem observed_values_unchanged (node : Fin projection.hiddenDAG.count) :
    presented.nodeEnumeration node = model.nodeEnumeration node := rfl

theorem every_intervention_event (intervention : HardIntervention signature) (event : Event signature.Assignment) :
    QProb.Equiv (presented.interventionalValue intervention event) (model.interventionalValue intervention event) :=
  model.presentSources_interventionalValue presentations intervention event

/-- The complete three-valued count law survives the smaller private
alphabets; this is not merely a Boolean readout of the count. -/
theorem count_law (intervention : HardIntervention signature) (unforced : intervention.value y = none) (event : Event Nat) :
    QProb.Equiv (presented.interventionalValue intervention (fun values => event (readValue (values y))))
      (counts.record.probVal event) :=
  QProb.equiv_trans (every_intervention_event intervention _)
    (interventional_y_event intervention unforced event)

theorem supported_conditionals (intervention : HardIntervention signature) (evidence event : Event signature.Assignment)
    (supported : (model.interventionalDist intervention).EventPositive evidence) :
    QProb.Equiv
      (((presented.interventionalDist intervention).conditionOn evidence
        ((model.presentSources_eventPositive_iff presentations intervention evidence).mpr supported)).probVal event)
      (((model.interventionalDist intervention).conditionOn evidence supported).probVal event) :=
  model.presentSources_conditionOn_probVal presentations intervention evidence event supported

theorem null_observation_retained :
    QProb.Equiv (presented.observationalValue (fun values => decide (readValue (values y) = 2))) QProb.zero :=
  QProb.equiv_trans (model.presentSources_observationalValue presentations _) null_observed_y

theorem null_intervention_still_valid :
    QProb.Equiv (presented.interventionalValue ((HardIntervention.empty signature).set y nullCode)
      (fun values => decide (readValue (values y) = 2))) QProb.one :=
  QProb.equiv_trans (every_intervention_event _ _) do_y_null_probability_one

end Multivalued

namespace HiddenRelay

open HiddenDAGCollapse

def original := HiddenDAGSourceCompression.original
def presentations (node : Fin fullGraph.count) := (original.factor node).atomPresentation
def presented := original.presentSources presentations

theorem unit_simulation (intervention : HardIntervention signature) (codes : presented.NoiseAssignment) :
    presented.evalObserved intervention codes = original.evalObserved intervention (FiniteProduct.decodePresentation presentations codes) :=
  original.presentSources_evalObserved presentations intervention codes

theorem every_observed_event (event : Event signature.Assignment) :
    QProb.Equiv (presented.observationalValue event) (original.observationalValue event) :=
  original.presentSources_observationalValue presentations event

theorem every_intervention_event (intervention : HardIntervention signature) (event : Event signature.Assignment) :
    QProb.Equiv (presented.interventionalValue intervention event) (original.interventionalValue intervention event) :=
  original.presentSources_interventionalValue presentations intervention event

theorem actual_source_independence
    (events : (node : Fin fullGraph.count) → presented.Noise node → Bool) :
    QProb.Equiv (presented.prior.probVal (FiniteProduct.rectangularEvent fullGraph.count presented.Noise events))
      (FiniteProduct.qProduct fullGraph.count (fun node => (presented.factor node).probVal (events node))) :=
  presented.product_law events

end HiddenRelay
end Thesis.Causality.Examples.HiddenDAGSourcePresentation
