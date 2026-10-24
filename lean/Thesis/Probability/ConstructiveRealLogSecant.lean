import Thesis.Probability.RationalLogSecant
import Thesis.Probability.ConstructiveRealDyadicCauchy
import Thesis.Probability.ConstructiveRealCauchyOrder

namespace Thesis.Probability.RationalLogSecant
open ConstructiveReal RationalGeometricSeries

/-- Right logarithmic secants at the explicitly dyadic steps `2⁻ⁿ`. -/
def dyadic (n : Nat) : ExactLog := slope (2 ^ n) (Nat.pow_pos (by decide))

def realValue (n : Nat) : ConstructiveReal := (dyadic n).interpret

theorem realValue_mono (first second : Nat) (ordered : first ≤ second) :
    LE (realValue first) (realValue second) :=
  ExactLog.interpret_mono (slope_mono _ _ _ _ (Nat.pow_le_pow_right (by decide) ordered))

/-- The exact logarithm estimate supplies a dyadic real step certificate.
The bound is deliberately rounded up from `2⁻⁽ⁿ⁺¹⁾` to `2⁻ⁿ`. -/
theorem realValue_step (n : Nat) : Within (envelope 1 n) (realValue n) (realValue (n + 1)) := by
  have estimate := slope_double_upper (2 ^ n) (Nat.pow_pos (by decide))
  have index : 2 * 2 ^ n = 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  simp only [index] at estimate
  have transferred := ExactLog.interpret_mono estimate
  have represented := ExactLog.interpret_add (dyadic n)
    (ExactLog.ofSignedRatio (⟨1, 2 ^ (n + 1), by decide, Nat.pow_pos (by decide)⟩ : PositiveRatio).toSignedRatio)
  have right := equiv_trans represented (add_congr (equiv_refl _) (ExactLog.interpret_ofSignedRatio _))
  have smaller : QProb.LE (⟨1, 2 ^ (n + 1), Nat.pow_pos (by decide)⟩ : QProb) (envelope 1 n) := by
    change 1 * 2 ^ n ≤ 1 * 2 ^ (n + 1)
    simp only [Nat.one_mul, Nat.pow_succ]
    omega
  have errorOrder := (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr smaller)
  have upper : LE (realValue (n + 1)) (add (realValue n) (ofSignedRatio (envelope 1 n).toSignedRatio)) :=
    le_trans ((le_congr (equiv_refl _) right).mp transferred) (add_le_add (le_refl _) errorOrder)
  exact ⟨le_trans (realValue_mono n (n + 1) (by omega)) ((within_refl (envelope 1 n) (realValue (n + 1))).1), upper⟩

/-- Effective convergence of right secants follows from their proved finite
step estimates, not from an assumed differentiability or completeness axiom. -/
def sequence : RealCauchySequence := RealCauchySequence.ofDyadicSteps realValue 1 realValue_step

/-- A candidate logarithm derivative coefficient at one, constructed with
certified rational enclosures. Identifying it as the derivative still requires
controlling arbitrary increments, including negative ones. -/
def limit : ConstructiveReal := sequence.limit

theorem remainder (n : Nat) : Within (envelope 2 n) (realValue n) limit :=
  RealCauchySequence.ofDyadicSteps_remainder realValue 1 realValue_step n

theorem realValue_zero : Equiv (realValue 0) one :=
  equiv_trans (ExactLog.interpret_congr (show ExactLog.Equiv (dyadic 0) (ExactLog.ofSignedRatio SignedRatio.one) from by decide +kernel))
    (ExactLog.interpret_ofSignedRatio SignedRatio.one)

/-- The constructed coefficient is bounded away from zero, so its positive
reciprocal is available without an arbitrary-real sign decision. -/
theorem one_le_limit : LE one limit := by
  apply RealCauchySequence.le_limit sequence one
  intro n
  exact (le_congr realValue_zero (equiv_refl _)).mp (realValue_mono 0 n (Nat.zero_le _))

theorem limit_le_three : LE limit (ofSignedRatio ⟨3, 1, by decide⟩) := by
  have bounded := (remainder 0).2
  have collect : Equiv (add (realValue 0) (ofSignedRatio (envelope 2 0).toSignedRatio))
      (ofSignedRatio ⟨3, 1, by decide⟩) :=
    equiv_trans (add_congr realValue_zero (equiv_refl _))
      (equiv_trans (ofSignedRatio_add _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)))
  exact (le_congr (equiv_refl _) collect).mp bounded


/-- Every positive rational secant lies below the constructed limit. The
late dyadic step is selected from the rational denominator, with no search
or choice of a real comparison witness. -/
theorem offsetSlope_le_limit (step : PositiveRatio) : LE (offsetSlope step).interpret limit := by
  have eventual := RealCauchySequence.limit_le_limit_of_tail
    (RealCauchySequence.constant (offsetSlope step).interpret) sequence step.den (by
      intro n later
      have size : PositiveRatio.LE (⟨1, 2 ^ n, by decide, Nat.pow_pos (by decide)⟩ : PositiveRatio) step := by
        change 1 * step.den ≤ step.num * 2 ^ n
        rw [Nat.one_mul]
        exact Nat.le_trans (Nat.le_trans later (Nat.le_of_lt Nat.lt_two_pow_self))
          (Nat.le_mul_of_pos_left _ step.num_pos)
      have compared := offsetSlope_antitone _ step size
      rw [offsetSlope_unit] at compared
      exact ExactLog.interpret_mono compared)
  exact (le_congr (RealCauchySequence.constant_limit _) (equiv_refl _)).mp eventual

/-- Uniform control of every positive rational secant whose step is at
most the selected dyadic step. This is the squeeze needed for right-hand
first variation, not merely convergence along the dyadic sequence. -/
theorem offsetSlope_within (step : PositiveRatio) (n : Nat)
    (small : PositiveRatio.LE step (⟨1, 2 ^ n, by decide, Nat.pow_pos (by decide)⟩ : PositiveRatio)) :
    Within (envelope 2 n) (offsetSlope step).interpret limit := by
  have below := offsetSlope_le_limit step
  have compared := offsetSlope_antitone step _ small
  rw [offsetSlope_unit] at compared
  have lower : LE (realValue n) (offsetSlope step).interpret := ExactLog.interpret_mono compared
  exact ⟨le_trans below ((within_refl (envelope 2 n) limit).1),
    le_trans (remainder n).2 (add_le_add lower (le_refl _))⟩

end Thesis.Probability.RationalLogSecant
