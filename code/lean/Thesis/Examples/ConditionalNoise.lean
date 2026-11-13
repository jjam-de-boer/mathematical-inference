import Thesis.Probability.ConditionalNoise

namespace Thesis
namespace Probability
namespace Examples
namespace ConditionalNoiseRegression

/-!
# Unequal-context checks for conditioned independent readout noise

These small exact records check the normalized calculation used by the actual
SCM routing theorem.  The source evidences have probabilities `1/2` and `1/5`,
so the conditioned product denominators are genuinely different.  Repeated
labels and a zero-weight atom are retained, rather than replaced by a common
uniform table.  The all-event transport theorem is checked independently of
the exact fractions, and fair-noise erasure records the bias boundary.
-/

def leftSource : FiniteProbRecord (Bool × Bool) where
  atoms := [((false, true), 1), ((false, true), 1), ((true, true), 1),
    ((true, false), 3), ((false, false), 0)]
  den := 6
  den_pos := by decide
  total_mass := rfl

def rightSource : FiniteProbRecord (Bool × Bool) where
  atoms := [((false, true), 1), ((true, true), 1), ((false, false), 8)]
  den := 10
  den_pos := by decide
  total_mass := rfl

def noise : FiniteProbRecord Bool := FiniteProbRecord.biasedFlip 1 1 (by decide)

theorem left_supported : leftSource.EventPositive (fun value => value.2) := by decide +kernel
theorem right_supported : rightSource.EventPositive (fun value => value.2) := by decide +kernel

def leftConditionedProduct := (noise.product leftSource).conditionOn (fun pair => pair.2.2)
  (noise.product_evidence_right_positive leftSource (fun value => value.2) left_supported)

def rightConditionedProduct := (noise.product rightSource).conditionOn (fun pair => pair.2.2)
  (noise.product_evidence_right_positive rightSource (fun value => value.2) right_supported)

theorem context_probabilities :
    QProb.Equiv (leftSource.probVal (fun value => value.2)) ⟨1, 2, by decide⟩ ∧
    QProb.Equiv (rightSource.probVal (fun value => value.2)) ⟨1, 5, by decide⟩ := by decide +kernel

theorem actual_conditioned_denominators : leftConditionedProduct.den = 9 ∧ rightConditionedProduct.den = 6 := by decide +kernel

theorem left_output_true : QProb.Equiv
    (leftConditionedProduct.probVal (fun pair => Bool.xor pair.2.1 pair.1)) ⟨4, 9, by decide⟩ := by decide +kernel

theorem left_output_false : QProb.Equiv
    (leftConditionedProduct.probVal (fun pair => !(Bool.xor pair.2.1 pair.1))) ⟨5, 9, by decide⟩ := by decide +kernel

theorem right_output_true : QProb.Equiv
    (rightConditionedProduct.probVal (fun pair => Bool.xor pair.2.1 pair.1)) ⟨1, 2, by decide⟩ := by decide +kernel

/-- The theorem transports arbitrary output events, not just the numerical
true-bit check above.  In particular, the false output and a certain event
retain their own normalized meanings. -/
theorem left_all_events (event : Event Bool) : QProb.Equiv
    (leftConditionedProduct.probVal (fun pair => event (Bool.xor pair.2.1 pair.1)))
    (((leftSource.conditionOn (fun value => value.2) left_supported).xorChannel
      (fun value => value.1) noise).probVal event) :=
  leftSource.xorChannel_conditionOn_noise_first_probVal (fun value => value.1)
    (fun value => value.2) left_supported noise event

theorem source_gap_reflected : Not (QProb.Equiv
    (((leftSource.conditionOn (fun value => value.2) left_supported).xorChannel (fun value => value.1) noise).probVal id)
    (((rightSource.conditionOn (fun value => value.2) right_supported).xorChannel (fun value => value.1) noise).probVal id)) := by
  intro equal
  have sourceEqual := (FiniteProbRecord.xorChannel_probVal_equiv_iff_of_bias
    (leftSource.conditionOn _ left_supported) (fun value => value.1)
    (rightSource.conditionOn _ right_supported) (fun value => value.1)
    noise 1 (by decide) (by decide +kernel)).mp equal
  have different : Not (QProb.Equiv
    ((leftSource.conditionOn (fun value => value.2) left_supported).probVal (fun value => value.1))
    ((rightSource.conditionOn (fun value => value.2) right_supported).probVal (fun value => value.1))) := by decide +kernel
  exact different sourceEqual

/-- Full-support fair noise still erases this genuine conditional gap.  It
cannot be substituted for the supported biased noise in a countermodel step. -/
def fairNoise : FiniteProbRecord Bool where
  atoms := [(false, 1), (true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

theorem balanced_noise_erases_gap : QProb.Equiv
    (((leftSource.conditionOn (fun value => value.2) left_supported).xorChannel (fun value => value.1) fairNoise).probVal id)
    (((rightSource.conditionOn (fun value => value.2) right_supported).xorChannel (fun value => value.1) fairNoise).probVal id) :=
  FiniteProbRecord.xorChannel_probVal_equiv_of_balanced
    (leftSource.conditionOn _ left_supported) (fun value => value.1)
    (rightSource.conditionOn _ right_supported) (fun value => value.1) fairNoise (by decide +kernel)

end ConditionalNoiseRegression
end Examples
end Probability
end Thesis
