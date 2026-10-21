import Thesis.Probability.Distros.EntropyUniform
import Thesis.Probability.ExactLogConvex
import Thesis.Probability.FiniteBernoulli

namespace Thesis.Probability

/-- A finite algebraic logarithm bound for a small complement decrement.
It is an intermediate estimate for continuity at probability zero. -/
theorem log_inverse_complement_bound (den m : Nat) (denLarge : 1 < den) (mPositive : 0 < m)
    (bounded : 2 * m ≤ den) :
    ExactLog.LE (ExactLog.log ⟨den, den - 1, Nat.lt_trans Nat.zero_lt_one denLarge, Nat.sub_pos_of_lt denLarge⟩)
      (ExactLog.divideNat (ExactLog.log (PositiveRatio.ofNat 2 (by decide))) m mPositive) := by
  simpa only [ExactLog.LE, ExactLog.log, ExactLog.divideNat, PositiveRatio.LE, PositiveRatio.toQProb,
    QProb.LE, PositiveRatio.pow, PositiveRatio.ofNat, Nat.one_mul, Nat.mul_one, Nat.pow_one, Nat.one_pow] using
    FiniteBernoulli.half_power den m (Nat.lt_trans Nat.zero_lt_one denLarge) bounded

namespace ExactLog

private theorem power_mono_exponent (x : PositiveRatio) (positive : x.den ≤ x.num)
    {a b : Nat} (bounded : a ≤ b) : PositiveRatio.LE (x.pow a) (x.pow b) := by
  obtain ⟨gap, rfl⟩ := Nat.exists_eq_add_of_le bounded
  change x.num ^ a * x.den ^ (a + gap) ≤ x.num ^ (a + gap) * x.den ^ a
  rw [Nat.pow_add, Nat.pow_add]
  have power := Nat.pow_le_pow_left positive gap
  have scaled := Nat.mul_le_mul_left (x.num ^ a * x.den ^ a) power
  simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using scaled

/-- Increasing a nonnegative rational coefficient preserves order when the
exact logarithm value itself is nonnegative. -/
theorem scaleRatio_weight_mono {p q : QProb} (bounded : QProb.LE p q) (x : ExactLog)
    (nonnegative : LE zero x) : LE (scaleRatio p x) (scaleRatio q x) := by
  have argument : x.argument.den ≤ x.argument.num := by
    change PositiveRatio.LE (PositiveRatio.one.pow x.degree) (x.argument.pow 1) at nonnegative
    rw [PositiveRatio.one_pow, PositiveRatio.pow_one] at nonnegative
    simpa only [PositiveRatio.LE, PositiveRatio.toQProb, PositiveRatio.one, QProb.LE, Nat.one_mul, Nat.mul_one] using nonnegative
  change PositiveRatio.LE ((x.argument.pow p.num).pow (x.degree * q.den))
    ((x.argument.pow q.num).pow (x.degree * p.den))
  rw [← PositiveRatio.pow_mul, ← PositiveRatio.pow_mul]
  apply power_mono_exponent x.argument argument
  have scaled := Nat.mul_le_mul_right x.degree bounded
  simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using scaled

end ExactLog
end Thesis.Probability
