import Thesis.CausalTransport.HiddenDAGValuePresentation
import Thesis.Examples.HiddenDAGReachableValues

namespace Thesis.Causality.Examples.HiddenDAGValuePresentation

open Probability HiddenDAGCollapse

/-!
# Native finite hidden values preserve retained causal laws

The five-node relay tests simulation across a hidden descendant of an observed
intervened parent. Both retained interventions preserve their entire records,
not just the event that motivated source compression. Arbitrary other actions
are deliberately not asserted preserved.

The three-valued fixture separately tests the observed coding boundary: its
null value remains an intervention target and every permitted observed value
has a two-sided code conversion. These tests use symbolic theorem applications,
not expansion of an exponential noise cube or a larger computation limit.
-/

def actions := HiddenDAGReachableValues.actions
def presented := model.retainedValueModel actions

theorem finite_node_types (node : Fin fullGraph.count) :
    presented.NodeValue node = Fin (model.valueWitness actions node).card := rfl

theorem private_sources_unchanged (node : Fin fullGraph.count) : presented.factor node = model.factor node := rfl

theorem forced_unit_readout (noise : model.NoiseAssignment) :
    presented.evalObserved forceXFalse noise = model.evalObserved forceXFalse noise :=
  model.retainedValueModel_evalObserved actions forceXFalse (List.mem_cons_of_mem _ List.mem_cons_self) noise

theorem forced_whole_record : presented.interventionalDist forceXFalse = model.interventionalDist forceXFalse :=
  model.retainedValueModel_interventionalDist actions forceXFalse (List.mem_cons_of_mem _ List.mem_cons_self)

theorem factual_whole_record : presented.observationalDist = model.observationalDist :=
  model.retainedValueModel_observationalDist actions

/-- Every additional retained intervention has the same full conditional
law wherever the original evidence was supported. -/
theorem supported_conditional (evidence event : Event signature.Assignment)
    (supported : (model.interventionalDist forceXFalse).EventPositive evidence) :
    QProb.Equiv
      (((presented.interventionalDist forceXFalse).conditionOn evidence
        ((model.retainedValueModel_eventPositive_iff actions forceXFalse
          (List.mem_cons_of_mem _ List.mem_cons_self) evidence).mpr supported)).probVal event)
      (((model.interventionalDist forceXFalse).conditionOn evidence supported).probVal event) :=
  model.retainedValueModel_conditionOn_probVal actions forceXFalse
    (List.mem_cons_of_mem _ List.mem_cons_self) evidence event supported

theorem observed_cardinality_exact (index : Fin signature.count) :
    (model.valueWitness actions (projection.hiddenDAG.observedNode index)).card = 2 :=
  model.retainedObservedEquiv_card actions index

namespace NullObserved

open HiddenDAGMultivaluedPresentation

def forceNull := (HardIntervention.empty HiddenDAGMultivaluedPresentation.signature).set HiddenDAGMultivaluedPresentation.y nullCode
def requested : List (HardIntervention HiddenDAGMultivaluedPresentation.signature) := [forceNull]
def presented := model.retainedValueModel requested

theorem all_observed_values_retained (index : Fin HiddenDAGMultivaluedPresentation.signature.count)
    (value : HiddenDAGMultivaluedPresentation.signature.Value index) :
    (presented.observedEquiv index).forward ((presented.observedEquiv index).backward value) = value :=
  (presented.observedEquiv index).forward_backward value

theorem observed_cardinality_still_three (index : Fin HiddenDAGMultivaluedPresentation.signature.count) :
    (model.valueWitness requested (projection.hiddenDAG.observedNode index)).card = 3 := by
  rw [model.retainedObservedEquiv_card requested index]
  change (List.finRange witness.card).length = 3
  rw [List.length_finRange, domain_card]

theorem factual_null_stays_null :
    QProb.Equiv (presented.observationalValue (fun values => decide (readValue (values y) = 2))) QProb.zero := by
  change QProb.Equiv (presented.observationalDist.probVal _) QProb.zero
  rw [model.retainedValueModel_observationalDist requested]
  exact null_observed_y

theorem forcing_null_still_has_probability_one :
    QProb.Equiv (presented.interventionalValue forceNull (fun values => decide (readValue (values y) = 2))) QProb.one := by
  rw [model.retainedValueModel_interventionalValue requested forceNull (List.mem_cons_of_mem _ List.mem_cons_self)]
  exact do_y_null_probability_one

end NullObserved
end Thesis.Causality.Examples.HiddenDAGValuePresentation
