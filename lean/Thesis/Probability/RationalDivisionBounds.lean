import Thesis.Probability.RationalNorm

namespace Thesis.Probability.SignedRatio

/-- Dividing by a positive natural does not increase rational magnitude. -/
theorem magnitude_divideNat_le (value : SignedRatio) (n : Nat) (positive : 0 < n) :
    QProb.LE (divideNat value n positive).magnitude value.magnitude := by
  change value.num.natAbs * value.den ≤ value.num.natAbs * (value.den * n)
  simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_right (value.num.natAbs * value.den) positive

end Thesis.Probability.SignedRatio
