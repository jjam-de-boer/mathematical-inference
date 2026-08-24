import Thesis.Causality.Multiworld
import Thesis.Causality.Structural.Atomic

namespace Thesis
namespace Causality

open Probability

/-!
Route-independent endpoint interface for an executed occurrence multiworld.

This interface deliberately compares endpoints extensionally. An endpoint
records its final causal record and a transport from the reference occurrence
coordinates. Its event interpretation is required to be exactly the reference
predicate pulled back along that transport, and its probability certificate
identifies every such coordinate-transported image with the reference joint
probability. The shared query definitions below then give the same numerator,
denominator, and conditional-denotation layer to both from-factual and
from-empty executions.
-/

/--
An endpoint record together with its coordinate-induced images of reference
occurrence-world events and their probability-agreement certificate.
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
  eventAt_coordinates : forall predicate assignment,
    eventAt predicate assignment =
      predicate
        (OccurrenceMultiworld.Encoding.decodeAssignment
          (M.occurrenceMultiworld event)
          (coordinates.untransportObserved assignment))
  observedValue : forall predicate,
    QProb.Equiv (record.observedValue (eventAt predicate))
      ((M.occurrenceMultiworld event).jointDist.probVal predicate)

namespace MultiworldEndpoint

/--
Any two endpoints agree on the coordinate-transported images of every
reference occurrence-world event.
-/
theorem eventProbability_equiv
    (left right : MultiworldEndpoint M event)
    (predicate : (M.occurrenceMultiworld event).Assignment -> Bool) :
    QProb.Equiv
      (left.record.observedValue (left.eventAt predicate))
      (right.record.observedValue (right.eventAt predicate)) :=
  QProb.equiv_trans (left.observedValue predicate)
    (QProb.equiv_symm (right.observedValue predicate))

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

/-- Any two endpoints over one query agree on its evidence probability. -/
theorem pair_denominator_equiv
    (query : CounterfactualQuery S)
    (left right : MultiworldEndpoint M query.combinedEvent) :
    QProb.Equiv (denominator query left) (denominator query right) :=
  QProb.equiv_trans (denominator_equiv query left)
    (QProb.equiv_symm (denominator_equiv query right))

/-- Any two endpoints over one query agree on its numerator probability. -/
theorem pair_numerator_equiv
    (query : CounterfactualQuery S)
    (left right : MultiworldEndpoint M query.combinedEvent) :
    QProb.Equiv (numerator query left) (numerator query right) :=
  QProb.equiv_trans (numerator_equiv query left)
    (QProb.equiv_symm (numerator_equiv query right))

/-- Any two endpoints over one query have equivalent complete partial results. -/
noncomputable def pair_denote_equivalent
    (query : CounterfactualQuery S)
    (left right : MultiworldEndpoint M query.combinedEvent) :
    ProbabilityResult.Equivalent (denote query left) (denote query right) :=
  ProbabilityResult.trans (semanticAgreement query left)
    (ProbabilityResult.symm (semanticAgreement query right))

end MultiworldEndpoint

end Causality
end Thesis
