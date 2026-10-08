import Thesis.Probability.BooleanNoise
import Thesis.Probability.FiniteProductReindex

namespace Thesis
namespace Probability
namespace FiniteProbRecord

/-!
# Independent finite noise under unchanged source evidence

Routing a conditional signal is not justified by the unconditional XOR-channel
theorem alone.  The evidence must first be shown not to inspect the newly
installed noise.  Conditioning an actual independent product on such source
evidence leaves that noise independent of the *conditioned* source record.

The product identity below retains arbitrary mixed output events.  It is
proved at natural weighted-mass level, with repeated labels and zero weights
allowed.  Each source uses its own supported evidence mass; no equality of
the left and right conditioning denominators is required.  The XOR corollary
then applies the existing biased-channel cancellation to those actual
conditioned records.  A causal readout must separately prove that its real
evaluation preserves the evidence and realizes this independent product.
-/

/-- Source-only evidence stays supported after adjoining an arbitrary
independent record.  No supported noise atom is chosen: its whole positive
total mass integrates out. -/
theorem product_evidence_right_positive (left : FiniteProbRecord Ω)
    (right : FiniteProbRecord X) (evidence : Event X)
    (supported : right.EventPositive evidence) :
    (left.product right).EventPositive (fun pair => evidence pair.2) :=
  (QProb.equiv_num_pos_iff (left.product_probVal_right right evidence)).mpr supported

/-- Conditioning a product on right-factor evidence retains independence
for every mixed event.  This is an all-event identity, not a rectangular
shortcut that would be insufficient for a noisy readout event. -/
theorem product_conditionOn_right_probVal (left : FiniteProbRecord Ω)
    (right : FiniteProbRecord X) (evidence : Event X)
    (supported : right.EventPositive evidence) (event : Event (Ω × X)) :
    QProb.Equiv
      (((left.product right).conditionOn (fun pair => evidence pair.2)
        (left.product_evidence_right_positive right evidence supported)).probVal event)
      ((left.product (right.conditionOn evidence supported)).probVal event) := by
  have numerator : eventMass (weightedCartesian left.atoms (right.atoms.filter (fun atom => evidence atom.1))) event =
      eventMass (weightedCartesian left.atoms right.atoms) (fun pair => evidence pair.2 && event pair) := by
    rw [eventMass_weightedCartesian_bind, eventMass_weightedCartesian_bind]
    simp only [eventMass_filter_event]
  have denominator : eventMass (weightedCartesian left.atoms right.atoms) (fun pair => evidence pair.2) =
      left.den * eventMass right.atoms evidence := by
    have rectangular := eventMass_weightedCartesian left.atoms right.atoms topEvent evidence
    simp only [topEvent, Bool.true_and, eventMass_top, left.total_mass] at rectangular
    exact rectangular
  simp only [product, conditionOn, probVal, QProb.Equiv]
  rw [eventMass_filter_event (weightedCartesian left.atoms right.atoms)
    (fun pair => evidence pair.2) event, ← numerator, denominator]

/-- The noise-first conditional output is exactly the independent channel
of the genuinely conditioned source.  The same evidence can have different
probabilities in separately presented models. -/
theorem xorChannel_conditionOn_noise_first_probVal (source : FiniteProbRecord Ω)
    (signal evidence : Event Ω) (supported : source.EventPositive evidence)
    (noise : FiniteProbRecord Bool) (event : Event Bool) :
    QProb.Equiv
      (((noise.product source).conditionOn (fun pair => evidence pair.2)
        (noise.product_evidence_right_positive source evidence supported)).probVal
        (fun pair => event (Bool.xor (signal pair.2) pair.1)))
      (((source.conditionOn evidence supported).xorChannel signal noise).probVal event) :=
  QProb.equiv_trans
    (noise.product_conditionOn_right_probVal source evidence supported
      (fun pair => event (Bool.xor (signal pair.2) pair.1)))
    (QProb.equiv_trans
      (noise.product_swap_probVal (source.conditionOn evidence supported)
        (fun pair => event (Bool.xor (signal pair.2) pair.1)))
      (QProb.equiv_symm (((source.conditionOn evidence supported).product noise).map_probVal
        (fun pair => Bool.xor (signal pair.1) pair.2) event)))

end FiniteProbRecord
end Probability
end Thesis
