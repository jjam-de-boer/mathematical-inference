import Thesis.Causality.ExecutedMultiworld.Configuration

namespace Thesis
namespace Causality

open Probability

/-!
Route-independent endpoint interface for an executed occurrence multiworld.

This interface deliberately compares endpoints extensionally.  A route need
only supply its final record, the transport from reference occurrence
coordinates, and the theorem that every occurrence-world predicate has the
reference joint probability.  The shared query definitions below then give
the same numerator, denominator, and conditional-denotation layer to both
from-factual and from-empty executions.
-/

structure MultiworldEndpoint (M : ExactModel S)
    (event : CounterfactualEvent S) where
  signature : ObservedSignature
  record : CausalEpistemicRecord signature
  coordinates : AtomicIntervention.SameCoordinates
    (OccurrenceMultiworld.Encoding.signature (M.occurrenceMultiworld event))
    signature
  eventAt : ((M.occurrenceMultiworld event).Assignment -> Bool) ->
    signature.Assignment -> Bool
  observedValue : forall predicate,
    QProb.Equiv (record.observedValue (eventAt predicate))
      ((M.occurrenceMultiworld event).jointDist.probVal predicate)

namespace MultiworldEndpoint

noncomputable def denominator
    (query : CounterfactualQuery S)
    (endpoint : MultiworldEndpoint M query.combinedEvent) : QProb :=
  endpoint.record.observedValue
    (endpoint.eventAt
      (query.combinedConditionPredicate (M.occurrenceMultiworld query.combinedEvent)))

noncomputable def numerator
    (query : CounterfactualQuery S)
    (endpoint : MultiworldEndpoint M query.combinedEvent) : QProb :=
  endpoint.record.observedValue
    (endpoint.eventAt
      (query.combinedNumeratorPredicate (M.occurrenceMultiworld query.combinedEvent)))

noncomputable def denote
    (query : CounterfactualQuery S)
    (endpoint : MultiworldEndpoint M query.combinedEvent) :
    ProbabilityResult.Result :=
  ProbabilityResult.divide (some (numerator query endpoint))
    (some (denominator query endpoint))

theorem denominator_equiv
    (query : CounterfactualQuery S)
    (endpoint : MultiworldEndpoint M query.combinedEvent) :
    QProb.Equiv (denominator query endpoint) (query.denominator M) := by
  exact QProb.equiv_trans
    (endpoint.observedValue
      (query.combinedConditionPredicate
        (M.occurrenceMultiworld query.combinedEvent)))
    (QProb.equiv_trans
      (FiniteProbRecord.map_probVal M.prior
        (M.occurrenceMultiworld query.combinedEvent).eval
        (query.combinedConditionPredicate
          (M.occurrenceMultiworld query.combinedEvent)))
      (FiniteProbRecord.probVal_congr M.prior _ _
        (fun assignment =>
          query.combinedConditionPredicate_eval
            (M.occurrenceMultiworld query.combinedEvent) assignment)))

theorem numerator_equiv
    (query : CounterfactualQuery S)
    (endpoint : MultiworldEndpoint M query.combinedEvent) :
    QProb.Equiv (numerator query endpoint) (query.numerator M) := by
  exact QProb.equiv_trans
    (endpoint.observedValue
      (query.combinedNumeratorPredicate
        (M.occurrenceMultiworld query.combinedEvent)))
    (QProb.equiv_trans
      (FiniteProbRecord.map_probVal M.prior
        (M.occurrenceMultiworld query.combinedEvent).eval
        (query.combinedNumeratorPredicate
          (M.occurrenceMultiworld query.combinedEvent)))
      (FiniteProbRecord.probVal_congr M.prior _ _
        (fun assignment =>
          query.combinedNumeratorPredicate_eval
            (M.occurrenceMultiworld query.combinedEvent) assignment)))

noncomputable def semanticAgreement
    (query : CounterfactualQuery S)
    (endpoint : MultiworldEndpoint M query.combinedEvent) :
    ProbabilityResult.Equivalent (denote query endpoint) (query.denote M) :=
  ProbabilityResult.divide_congr
    (.value (numerator_equiv query endpoint))
    (.value (denominator_equiv query endpoint))

end MultiworldEndpoint

end Causality
end Thesis
