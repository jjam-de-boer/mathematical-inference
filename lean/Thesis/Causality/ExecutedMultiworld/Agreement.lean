import Thesis.Causality.ExecutedMultiworld.FromFactual
import Thesis.Causality.ExecutedMultiworld.FromEmpty

namespace Thesis
namespace Causality

open Probability

/-!
Eventwise and query-level agreement of the two independently executed routes.

`FromFactual` starts from a factual source mode, whereas `FromEmpty` obtains
an endpoint by literal root/node creation whose evaluator and event
probabilities agree after coordinate transport.  Their dependent signatures
need not be definitionally equal, so every comparison first transports observed
assignments back through the route's `coordinates` witness. The file proves
pointwise evaluator agreement and then derives event, numerator, denominator,
and full partial-result agreement.
-/

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
numerator and denominator.  Both sides are first reduced to the same reference
event probability by their respective endpoint-record theorems.
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

/-- The two routes therefore have extensionally equal evidence probabilities. -/
theorem executedRoutes_denominator_equiv
    (fromFactual :
      ExecutedOccurrenceConstruction mode query.combinedEvent)
    (fromEmpty :
      FromEmptyExecutedOccurrenceConstruction mode query.combinedEvent) :
    QProb.Equiv fromFactual.denominator fromEmpty.denominator :=
  QProb.equiv_trans fromFactual.denominator_equiv
    (QProb.equiv_symm fromEmpty.denominator_equiv)

/-- The two routes likewise have extensionally equal queried-event probabilities. -/
theorem executedRoutes_numerator_equiv
    (fromFactual :
      ExecutedOccurrenceConstruction mode query.combinedEvent)
    (fromEmpty :
      FromEmptyExecutedOccurrenceConstruction mode query.combinedEvent) :
    QProb.Equiv fromFactual.numerator fromEmpty.numerator :=
  QProb.equiv_trans fromFactual.numerator_equiv
    (QProb.equiv_symm fromEmpty.numerator_equiv)

/--
The two executed routes give equivalent partial conditional-query results,
including the unsupported case.
-/
noncomputable def executedRoutes_denote_equivalent
    (fromFactual :
      ExecutedOccurrenceConstruction mode query.combinedEvent)
    (fromEmpty :
      FromEmptyExecutedOccurrenceConstruction mode query.combinedEvent) :
    ProbabilityResult.Equivalent fromFactual.denote fromEmpty.denote :=
  ProbabilityResult.trans fromFactual.semanticAgreement
    (ProbabilityResult.symm fromEmpty.semanticAgreement)

end Causality
end Thesis
