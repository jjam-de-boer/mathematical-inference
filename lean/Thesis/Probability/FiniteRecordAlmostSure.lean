import Thesis.Probability.FiniteRecord

namespace Thesis
namespace Probability
namespace FiniteProbRecord

/-!
# Equality on a probability-one finite event

A finite record may contain zero-weight atoms and repeated labels.  Equality
of two events on a probability-one event therefore need not be literal
pointwise equality on every listed atom.  The lemmas here discard only the
zero-weight exceptions, by induction on natural weights.  They neither choose
a positive atom nor assume an arbitrary proposition is decidable.

This is the probability bridge for almost-sure SCM consistency: an action
already factual throughout the positive-mass population changes no event
probability, even if it changes a mechanism at a zero-weight unit.
-/

/-- Agreement on an event carrying the complete mass suffices for equality
of event masses.  In the false branch the full-mass equation forces the head
weight to zero; it does not force the evidence to hold at that label. -/
theorem eventMass_congr_on_full_event (atoms : List (Ω × Nat))
    (evidence left right : Event Ω)
    (full : eventMass atoms evidence = totalMass atoms)
    (agree : forall value, evidence value = true → left value = right value) :
    eventMass atoms left = eventMass atoms right := by
  induction atoms with
  | nil => rfl
  | cons atom atoms inductionHypothesis =>
      rcases atom with ⟨value, weight⟩
      cases selected : evidence value with
      | false =>
          have bounded := eventMass_le_totalMass atoms evidence
          have equation : eventMass atoms evidence = weight + totalMass atoms := by
            simpa only [eventMass, totalMass, selected, Bool.false_eq_true, if_false] using full
          have zero : weight = 0 := by omega
          have tailFull : eventMass atoms evidence = totalMass atoms := by omega
          simp only [eventMass, zero, Nat.zero_add,
            inductionHypothesis tailFull]
          cases left value <;> cases right value <;> rfl
      | true =>
          have tailFull : eventMass atoms evidence = totalMass atoms := by
            have equation : weight + eventMass atoms evidence = weight + totalMass atoms := by
              simpa only [eventMass, totalMass, selected, if_true] using full
            exact Nat.add_left_cancel equation
          simp only [eventMass, agree value selected,
            inductionHypothesis tailFull]

/-- Probability one is expressed by rational equivalence, not by equality
of unreduced fraction records.  The same record supplies both denominators. -/
theorem probVal_congr_on_probability_one (record : FiniteProbRecord Ω)
    (evidence left right : Event Ω)
    (full : QProb.Equiv (record.probVal evidence) QProb.one)
    (agree : forall value, evidence value = true → left value = right value) :
    QProb.Equiv (record.probVal left) (record.probVal right) := by
  have mass : eventMass record.atoms evidence = record.den := by
    simpa only [QProb.Equiv, probVal, QProb.one, Nat.mul_one, Nat.one_mul] using full
  have same := eventMass_congr_on_full_event record.atoms evidence left right
    (mass.trans record.total_mass.symm) agree
  change eventMass record.atoms left * record.den = eventMass record.atoms right * record.den
  rw [same]

end FiniteProbRecord
end Probability
end Thesis
