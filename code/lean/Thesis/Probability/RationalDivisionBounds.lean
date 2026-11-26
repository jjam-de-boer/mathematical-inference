import Thesis.Probability.RationalNorm

/-!
# Magnitude estimates for division by a positive natural

For a signed rational, division by n has exactly the original magnitude
multiplied by 1/n. Positivity of n is explicit, so n=0 is outside this
operation rather than assigned a fallback value. The weaker contraction
bound follows by cross multiplication on natural numerator magnitudes.
Both results respect unreduced rational presentations.
-/

namespace Thesis.Probability.SignedRatio

/-- Dividing by a positive natural does not increase rational magnitude. -/
theorem magnitude_divideNat_le (value : SignedRatio) (n : Nat) (positive : 0 < n) :
    QProb.LE (divideNat value n positive).magnitude value.magnitude := by
  change value.num.natAbs * value.den ≤ value.num.natAbs * (value.den * n)
  simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_right (value.num.natAbs * value.den) positive

/-- The exact magnitude identity retains the divisor for sharper estimates. -/
theorem magnitude_divideNat (value : SignedRatio) (n : Nat) (positive : 0 < n) :
    QProb.Equiv (divideNat value n positive).magnitude (QProb.mul value.magnitude ⟨1, n, positive⟩) := by
  simp only [QProb.Equiv, magnitude, divideNat, QProb.mul, Nat.mul_one]

end Thesis.Probability.SignedRatio
