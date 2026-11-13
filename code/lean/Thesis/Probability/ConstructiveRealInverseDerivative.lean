import Thesis.Probability.ConstructiveDerivativeChain
import Thesis.Probability.ConstructiveDerivativeWithin
import Thesis.Probability.ConstructiveRealInverseBounds

namespace Thesis.Probability.ConstructiveReal

private theorem inverse_radius_error_le (lower epsilon radius : PositiveRatio)
    (small : PositiveRatio.LE radius (epsilon.divideNat (lower.den ^ 3) (Nat.pow_pos lower.den_pos))) :
    QProb.LE (inverseRadiusError lower radius) (QProb.mul epsilon.toQProb radius.toQProb) := by
  have scaled : QProb.LE (QProb.mul radius.toQProb (QProb.ofNat (lower.den ^ 3))) epsilon.toQProb :=
    QProb.le_congr (QProb.equiv_refl _) (PositiveRatio.divide_mul epsilon _ (Nat.pow_pos lower.den_pos))
      (QProb.mul_le_mul small (QProb.le_refl _))
  exact QProb.le_congr (QProb.equiv_symm (QProb.mul_assoc _ _ _)) (QProb.mul_comm _ _)
    (QProb.mul_le_mul (QProb.le_refl radius.toQProb) scaled)

/-- Reciprocal differentiation on the supplied positive half-line. The slope
is the negative inverse square and the modulus comes from the proved
quadratic error bound. Membership remains explicit at every nearby argument. -/
def positiveInverse_hasDerivativeWithinAt (point : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) point) :
    HasDerivativeWithinAt (fun y => LE (ofSignedRatio lower.toSignedRatio) y)
      (fun y admitted => y.positiveInverse lower admitted) point bounded
      (neg (mul (point.positiveInverse lower bounded) (point.positiveInverse lower bounded))) where
  modulus epsilon := epsilon.divideNat (lower.den ^ 3) (Nat.pow_pos lower.den_pos)
  remainder epsilon radius small y admitted close :=
    within_mono (positiveInverse_first_variation point y lower radius bounded admitted close)
      (inverse_radius_error_le lower epsilon radius small)

/-- Reciprocal-affine differentiation retains the positive denominator
domain. Zero and negative affine factors are allowed whenever the supplied
point and nearby arguments satisfy that domain. -/
def inverse_affine_hasDerivativeWithinAt (point factor offset : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) (add (mul point factor) offset)) :
    HasDerivativeWithinAt (fun y => LE (ofSignedRatio lower.toSignedRatio) (add (mul y factor) offset))
      (fun y admitted => (add (mul y factor) offset).positiveInverse lower admitted) point bounded
      (neg (mul factor (mul ((add (mul point factor) offset).positiveInverse lower bounded)
        ((add (mul point factor) offset).positiveInverse lower bounded)))) :=
  ((HasDerivativeAt.affine point factor offset).chainWithin (positiveInverse_hasDerivativeWithinAt _ lower bounded)).slope_congr
    (mul_neg _ _)

end Thesis.Probability.ConstructiveReal
