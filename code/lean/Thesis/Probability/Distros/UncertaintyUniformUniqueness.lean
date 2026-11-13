import Thesis.Probability.Distros.UncertaintyUniform
import Thesis.Probability.ExactLogSeparation

namespace Thesis.Probability.UncertaintyMeasure
open ProbabilityVector

private def bit : ExactLog := ExactLog.log (PositiveRatio.ofNat 2 (by decide))

private theorem bit_succ (n : Nat) :
    ExactLog.scaleNat (n + 1) bit = ExactLog.add (ExactLog.scaleNat n bit) bit := by
  apply ExactLog.ext
  · apply PositiveRatio.ext <;> simp [bit, ExactLog.scaleNat, ExactLog.log, ExactLog.add,
      PositiveRatio.ofNat, PositiveRatio.pow, PositiveRatio.mul, Nat.pow_succ]
  · rfl

private theorem power_bracket (measure : UncertaintyMeasure) (n k : Nat) (positive : 0 < n) :
    ExactLog.LE (ExactLog.scaleNat (n ^ k).log2 bit)
      (ExactLog.scaleNat k (measure.value (uniform n positive))) ∧
    ExactLog.LE (ExactLog.scaleNat k (measure.value (uniform n positive)))
      (ExactLog.scaleNat ((n ^ k).log2 + 1) bit) := by
  have twoPower (exponent : Nat) : ExactLog.Equiv
      (measure.value (uniform (2 ^ exponent) (Nat.pow_pos (by decide)))) (ExactLog.scaleNat exponent bit) :=
    ExactLog.equiv_trans (measure.uniform_pow 2 exponent (by decide)) (ExactLog.scaleNat_congr exponent measure.fair)
  have first := measure.uniform_mono (2 ^ (n ^ k).log2) (n ^ k)
    (Nat.pow_pos (by decide)) (Nat.pow_pos positive) (Nat.log2_self_le (Nat.ne_of_gt (Nat.pow_pos positive)))
  have second := measure.uniform_mono (n ^ k) (2 ^ ((n ^ k).log2 + 1))
    (Nat.pow_pos positive) (Nat.pow_pos (by decide)) (Nat.le_of_lt Nat.lt_log2_self)
  exact ⟨(ExactLog.le_congr (twoPower _) (measure.uniform_pow n k positive)).mp first,
    (ExactLog.le_congr (measure.uniform_pow n k positive) (twoPower _)).mp second⟩

/-- Every pair of admissible measures agrees on uniform finite choices.
The proof uses only grouping, uniform ordering, fair-bit normalization and
the proved Archimedean separation of the exact logarithmic value space. -/
theorem uniform_unique (first second : UncertaintyMeasure) (n : Nat) (positive : 0 < n) :
    ExactLog.Equiv (first.value (uniform n positive)) (second.value (uniform n positive)) := by
  have ordered (left right : UncertaintyMeasure) :
      ExactLog.LE (left.value (uniform n positive)) (right.value (uniform n positive)) := by
    apply ExactLog.le_of_multiples_le_add_one
    intro k
    have lower := (power_bracket right n k positive).1
    have upper := (power_bracket left n k positive).2
    rw [bit_succ] at upper
    exact ExactLog.le_trans upper ((ExactLog.add_le_add_right_iff _ _ bit).mpr lower)
  exact (ExactLog.equiv_iff_le _ _).mpr ⟨ordered first second, ordered second first⟩

/-- The uniform logarithm formula is a conclusion of the uncertainty
requirements, not an assumption about an arbitrary measure. -/
theorem uniform_log (measure : UncertaintyMeasure) (n : Nat) (positive : 0 < n) :
    ExactLog.Equiv (measure.value (uniform n positive)) (ExactLog.log (PositiveRatio.ofNat n positive)) :=
  ExactLog.equiv_trans (measure.uniform_unique UncertaintyMeasure.shannon n positive) (ProbabilityVector.uniform_entropy n positive)

end Thesis.Probability.UncertaintyMeasure
