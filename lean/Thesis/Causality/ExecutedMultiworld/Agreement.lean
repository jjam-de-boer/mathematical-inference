import Thesis.Causality.ExecutedMultiworld.FromEmpty

namespace Thesis
namespace Causality

open Probability

/-! Eventwise and query-level agreement of the two independently executed routes. -/

/-! ## Agreement of the two independently executed routes -/

variable {S : ObservedSignature} {mode : CausalMode S}
  {event : CounterfactualEvent S} {query : CounterfactualQuery S}

theorem executedRoutes_endpoint_eval_agree
    (fromFactual : ExecutedOccurrenceConstruction mode event)
    (fromEmpty : FromEmptyExecutedOccurrenceConstruction mode event)
    (assignment : mode.record.model.latent.Assignment) :
    fromFactual.coordinates.untransportObserved
        (fromFactual.target.record.model.eval
          (fromFactual.endpointAssignment assignment)) =
      fromEmpty.coordinates.untransportObserved
        (fromEmpty.target.record.model.eval
          (fromEmpty.endpointAssignment assignment)) := by
  rw [fromFactual.endpoint_eval, fromEmpty.endpoint_eval]
  rw [AtomicIntervention.SameCoordinates.untransportObserved_transportObserved]
  rw [AtomicIntervention.SameCoordinates.untransportObserved_transportObserved]

/--
The independently executed from-factual and from-empty routes assign the same
probability to every occurrence-world event, not only to a query's designated
numerator and denominator.
-/
theorem executedRoutes_eventProbability_equiv
    (fromFactual : ExecutedOccurrenceConstruction mode event)
    (fromEmpty : FromEmptyExecutedOccurrenceConstruction mode event)
    (predicate : fromFactual.World.Assignment -> Bool) :
    QProb.Equiv
      (fromFactual.endpointRecord.observedValue
        (fromFactual.endpointEvent predicate))
      (fromEmpty.endpointRecord.observedValue
        (fromEmpty.endpointEvent predicate)) := by
  exact QProb.equiv_trans
    (fromFactual.endpointRecord_observedValue predicate)
    (QProb.equiv_symm
      (fromEmpty.endpointRecord_observedValue predicate))

theorem executedRoutes_denominator_equiv
    (fromFactual :
      ExecutedOccurrenceConstruction mode query.combinedEvent)
    (fromEmpty :
      FromEmptyExecutedOccurrenceConstruction mode query.combinedEvent) :
    QProb.Equiv fromFactual.denominator fromEmpty.denominator :=
  QProb.equiv_trans fromFactual.denominator_equiv
    (QProb.equiv_symm fromEmpty.denominator_equiv)

theorem executedRoutes_numerator_equiv
    (fromFactual :
      ExecutedOccurrenceConstruction mode query.combinedEvent)
    (fromEmpty :
      FromEmptyExecutedOccurrenceConstruction mode query.combinedEvent) :
    QProb.Equiv fromFactual.numerator fromEmpty.numerator :=
  QProb.equiv_trans fromFactual.numerator_equiv
    (QProb.equiv_symm fromEmpty.numerator_equiv)

end Causality
end Thesis
