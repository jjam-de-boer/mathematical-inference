import Thesis.CausalTransport.HiddenDAGFiniteRepresentation
import Thesis.Examples.HiddenDAGCompactSources

namespace Thesis.Causality.Examples.HiddenDAGFiniteRepresentation

open Probability HiddenDAGCollapse HiddenDAGSourceCompression

/-!
# A bounded representative of an actual hidden relay

Retain the five-node original graph, its three-child hidden ancestor and its
non-root hidden relay. The package constructs bounded private alphabets and
bounded hidden endogenous alphabets simultaneously, preserving all factual
events and the requested effect. Observed values retain their exact declared
cardinalities. All checks use the construction interfaces rather than unfolding
the concrete source-compression recursion or enumerating the full value tables.

The generic conditional regression also composes both coding steps with the
existing compression that retains an arbitrary joint event and its evidence.
It checks the actual conditioned native record, not just a bare quotient.
-/

def represented := withObservation.finiteModel

theorem actual_private_alphabet (node : Fin fullGraph.count) :
    represented.Noise node = Fin (withObservation.codeCard node) := withObservation.finiteModel_noise node

theorem actual_endogenous_alphabet (node : Fin fullGraph.count) :
    represented.NodeValue node = Fin (withObservation.codeModel.valueWitness withObservation.retainedActions node).card :=
  withObservation.finiteModel_nodeValue node

theorem bounded_hidden_values (node : Fin fullGraph.count) (hidden : fullGraph.hidden node = true) :
    (withObservation.codeModel.valueWitness withObservation.retainedActions node).card ≤
      2 * (signature.assignmentEnumeration.length + 1 + 1) ^ 5 :=
  withObservation.finiteModel_hidden_bound node hidden

theorem exact_observed_cardinality (index : Fin signature.count) :
    (withObservation.codeModel.valueWitness withObservation.retainedActions (fullGraph.observedNode index)).card = 2 :=
  withObservation.finiteModel_observed_card index

theorem all_factual_events (event : Event signature.Assignment) :
    QProb.Equiv (represented.observationalValue event) (original.observationalValue event) :=
  withObservation.finiteModel_observational event

theorem target_preserved : QProb.Equiv (represented.interventionalValue target.intervention target.event)
    (original.interventionalValue target.intervention target.event) :=
  withObservation.finiteModel_preserved target List.mem_cons_self

/-- Exercise the uniform constructor's type, not just a caller-supplied
record that postulates the preservation obligations as external fields. -/
def witness : FiniteHiddenDAGSCM.BoundedRepresentation original [target] :=
  original.boundedRepresentation [target]

theorem constructor_retains_entire_observed_law (event : Event signature.Assignment) :
    QProb.Equiv (witness.model.observationalValue event) (original.observationalValue event) := witness.observational event

open HiddenDAGCompactSources

theorem arbitrary_supported_conditional (intervention : HardIntervention signature) (evidence event : Event signature.Assignment)
    (supported : (original.interventionalDist intervention).EventPositive evidence) :
    let retained := conditionalCompression intervention evidence event
    let evidenceListed : (⟨intervention, evidence⟩ : NativeProbabilityQuery signature) ∈ conditionalTargets intervention evidence event :=
      List.mem_cons_of_mem _ List.mem_cons_self
    QProb.Equiv
      (((retained.finiteModel.interventionalDist intervention).conditionOn evidence
        ((retained.finiteModel_eventPositive_iff ⟨intervention, evidence⟩ evidenceListed).mpr supported)).probVal event)
      (((original.interventionalDist intervention).conditionOn evidence supported).probVal event) := by
  dsimp only
  exact (conditionalCompression intervention evidence event).finiteModel_conditionOn_probVal intervention evidence event
    List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) supported

end Thesis.Causality.Examples.HiddenDAGFiniteRepresentation
