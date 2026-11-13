import Thesis.Probability.RationalApproximation
import Thesis.Probability.QProbOrder

namespace Thesis.Probability.QProb

theorem mul_le_mul {a b c d : QProb} (first : LE a b) (second : LE c d) : LE (mul a c) (mul b d) := by
  have multiplied := Nat.mul_le_mul first second
  simpa only [LE, mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using multiplied

end Thesis.Probability.QProb

namespace Thesis.Probability.SignedRatio

/-- Exact magnitude as an unreduced nonnegative rational. -/
def magnitude (value : SignedRatio) : QProb := ⟨value.num.natAbs, value.den, value.den_pos⟩

theorem magnitude_congr {a b : SignedRatio} (same : Equiv a b) : QProb.Equiv a.magnitude b.magnitude := by
  have absolute := congrArg Int.natAbs same
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using absolute

theorem magnitude_neg (value : SignedRatio) : QProb.Equiv (neg value).magnitude value.magnitude := by
  simp only [QProb.Equiv, magnitude, neg, Int.natAbs_neg]

theorem magnitude_mul (a b : SignedRatio) : QProb.Equiv (mul a b).magnitude (QProb.mul a.magnitude b.magnitude) := by
  simp only [QProb.Equiv, magnitude, mul, QProb.mul, Int.natAbs_mul]

theorem magnitude_add (a b : SignedRatio) : QProb.LE (add a b).magnitude (QProb.add a.magnitude b.magnitude) := by
  have numerator := Int.natAbs_add_le (a.num * (b.den : Int)) (b.num * (a.den : Int))
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at numerator
  exact Nat.mul_le_mul_right (a.den * b.den) numerator

theorem le_magnitude (value : SignedRatio) : LE value value.magnitude.toSignedRatio := by
  apply (le_iff_cross _ _).mpr
  exact Int.mul_le_mul_of_nonneg_right Int.le_natAbs (Int.natCast_nonneg value.den)

theorem neg_le_magnitude (value : SignedRatio) : LE (neg value) value.magnitude.toSignedRatio := by
  have bounded := le_magnitude (neg value)
  have same := QProb.toSignedRatio_congr (magnitude_neg value)
  exact (le_congr (equiv_refl _) same).mp bounded

/-- A magnitude bound is equivalent to the two signed bounds. Comparisons
remain finite integer comparisons, including at zero. -/
theorem magnitude_le_iff (value : SignedRatio) (bound : QProb) :
    QProb.LE value.magnitude bound ↔ LE value bound.toSignedRatio ∧ LE (neg value) bound.toSignedRatio := by
  constructor
  · intro bounded
    have lifted := (toSignedRatio_le_iff _ _).mpr bounded
    exact ⟨le_trans (le_magnitude value) lifted, le_trans (neg_le_magnitude value) lifted⟩
  · intro bounded
    have forward := (le_iff_cross _ _).mp bounded.1
    have backward := (le_iff_cross _ _).mp bounded.2
    change value.num.natAbs * bound.den ≤ bound.num * value.den
    rw [← Int.ofNat_le, Int.natCast_mul, Int.natCast_mul]
    rcases Int.natAbs_eq value.num with positive | negative
    · rw [← positive]
      exact forward
    · have absolute : (value.num.natAbs : Int) = -value.num := by
        have doubled := congrArg (fun number : Int => -number) negative
        simpa only [Int.neg_neg] using doubled.symm
      rw [absolute]
      exact backward

/-- Two-sided distance bounds can be supplied as ordinary signed bounds. -/
theorem magnitude_sub_le_iff (a b : SignedRatio) (bound : QProb) :
    QProb.LE (sub a b).magnitude bound ↔
      LE a (add b bound.toSignedRatio) ∧ LE b (add a bound.toSignedRatio) := by
  rw [magnitude_le_iff]
  exact and_congr
    ((sub_le_iff_le_add a b bound.toSignedRatio).trans
      (le_congr (equiv_refl _) (add_comm _ _)))
    ((le_congr (neg_sub a b) (equiv_refl _)).trans
      ((sub_le_iff_le_add b a bound.toSignedRatio).trans
        (le_congr (equiv_refl _) (add_comm _ _))))

theorem magnitude_sub_symm (a b : SignedRatio) : QProb.Equiv (sub a b).magnitude (sub b a).magnitude :=
  QProb.equiv_trans (QProb.equiv_symm (magnitude_neg (sub a b))) (magnitude_congr (neg_sub a b))

/-- The triangle inequality for finite signed-rational approximation error. -/
theorem magnitude_sub_triangle (a b c : SignedRatio) :
    QProb.LE (sub a c).magnitude (QProb.add (sub a b).magnitude (sub b c).magnitude) :=
  QProb.le_congr (QProb.equiv_symm (magnitude_congr (sub_split a b c)))
    (QProb.equiv_refl _) (magnitude_add _ _)

/-- Absolute error vanishes exactly when the rational values agree. -/
theorem magnitude_zero_iff (value : SignedRatio) : QProb.Equiv value.magnitude QProb.zero ↔ Equiv value zero := by
  simp only [QProb.Equiv, magnitude, QProb.zero, Nat.mul_one, Nat.zero_mul, equiv_zero_iff, Int.natAbs_eq_zero]

/-- Algebraic splitting used by product-error certificates. -/
theorem product_difference (a b c d : SignedRatio) :
    Equiv (sub (mul a b) (mul c d)) (add (mul (sub a c) b) (mul c (sub b d))) := by
  simp only [Equiv, sub, mul, add, neg, Int.natCast_mul, Int.mul_add,
    Int.mul_neg, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  omega

/-- Finite product error is bounded by the two input errors and magnitudes. -/
theorem magnitude_product_difference (a b c d : SignedRatio) :
    QProb.LE (sub (mul a b) (mul c d)).magnitude
      (QProb.add (QProb.mul (sub a c).magnitude b.magnitude) (QProb.mul c.magnitude (sub b d).magnitude)) :=
  QProb.le_congr (QProb.equiv_symm (magnitude_congr (product_difference a b c d)))
    (QProb.add_congr (magnitude_mul _ _) (magnitude_mul _ _)) (magnitude_add _ _)

theorem product_error_bound (a b c d : SignedRatio) (firstError secondError firstSize secondSize : QProb)
    (first : QProb.LE (sub a c).magnitude firstError) (second : QProb.LE (sub b d).magnitude secondError)
    (sizeFirst : QProb.LE c.magnitude firstSize) (sizeSecond : QProb.LE b.magnitude secondSize) :
    QProb.LE (sub (mul a b) (mul c d)).magnitude
      (QProb.add (QProb.mul firstError secondSize) (QProb.mul firstSize secondError)) :=
  QProb.le_trans (magnitude_product_difference a b c d)
    (QProb.add_le_add (QProb.mul_le_mul first sizeSecond) (QProb.mul_le_mul sizeFirst second))

end Thesis.Probability.SignedRatio
