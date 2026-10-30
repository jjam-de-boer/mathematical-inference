import Thesis.Probability.ConstructiveUniformDerivative
import Thesis.Probability.ConstructiveRealUniformBounds
import Thesis.Probability.ConstructiveRealExpDerivative
import Thesis.Probability.ConstructiveRealInverseDerivative

namespace Thesis.Probability.ConstructiveReal

/-- Exponential first variation with one computed modulus for any explicitly
bounded domain. The underlying rational Taylor remainder is transferred at
both actual arguments, with the supplied shared approximation bound. -/
def exp_uniformDerivative (domain : ConstructiveReal → Prop) (bound : Nat)
    (bounded : ∀ x, domain x → ∀ precision, PositiveRatio.LE precision PositiveRatio.one →
      QProb.LE (x.rationalApproximation.value precision).magnitude (QProb.ofNat bound)) :
    UniformDerivativeWithin domain (fun x _ => x.exp) (fun x _ => x.exp) where
  congr _ _ _ _ same := exp_congr same
  modulus epsilon := epsilon.divideNat (RationalTaylorExponential.uniformSumBound bound)
    (RationalTaylorExponential.uniformSumBound_pos _)
  remainder epsilon radius small x hx y hy close := by
    let k := RationalTaylorExponential.uniformSumBound bound
    have scaled : QProb.LE (QProb.mul radius.toQProb (QProb.ofNat k)) epsilon.toQProb :=
      QProb.le_congr (QProb.equiv_refl _) (PositiveRatio.divide_mul epsilon k (RationalTaylorExponential.uniformSumBound_pos _))
        (QProb.mul_le_mul small (QProb.le_refl _))
    have half : QProb.LE (⟨k, 2, by decide⟩ : QProb) (QProb.ofNat k) := by
      change k * 1 ≤ k * 2
      simpa only [Nat.mul_one] using Nat.le_mul_of_pos_right k (by decide : 0 < 2)
    have error := QProb.le_trans (QProb.mul_le_mul (QProb.le_refl (QProb.mul radius.toQProb radius.toQProb)) half)
      (QProb.le_congr (QProb.equiv_symm (QProb.mul_assoc _ _ _)) (QProb.mul_comm _ _)
        (QProb.mul_le_mul (QProb.le_refl radius.toQProb) scaled))
    exact within_mono (exp_first_variation_radius x y bound radius close (bounded x hx) (bounded y hy)) error

/-- Reciprocal first variation is uniform on its explicit positive half-line.
The modulus depends on the rational floor and is independent of the point. -/
def positiveInverse_uniformDerivative (lower : PositiveRatio) :
    UniformDerivativeWithin (fun x => LE (ofSignedRatio lower.toSignedRatio) x)
      (fun x admitted => x.positiveInverse lower admitted)
      (fun x admitted => neg (mul (x.positiveInverse lower admitted) (x.positiveInverse lower admitted))) where
  congr _ _ hx hy same := positiveInverse_congr same lower lower hx hy
  modulus epsilon := epsilon.divideNat (lower.den ^ 3) (Nat.pow_pos lower.den_pos)
  remainder epsilon radius small x hx y hy close :=
    (positiveInverse_hasDerivativeWithinAt x lower hx).remainder epsilon radius small y hy close

/-- Fixed interval bounds on the signed reciprocal slope, suitable for
uniform composition. No comparison of the reciprocal with zero is decided. -/
theorem inverseSlope_bounds (x : ConstructiveReal) (lower : PositiveRatio)
    (positive : LE (ofSignedRatio lower.toSignedRatio) x) :
    let inverse := x.positiveInverse lower positive
    let bound := ofSignedRatio (QProb.ofNat lower.den).toSignedRatio
    LE (neg (mul bound bound)) (neg (mul inverse inverse)) ∧ LE (neg (mul inverse inverse)) zero := by
  let inverse := x.positiveInverse lower positive
  have squared := square_le_square (x.positiveInverse_nonnegative lower positive) (x.positiveInverse_upper lower positive)
  exact ⟨(neg_le_neg_iff _ _).mpr squared,
    (le_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))).mp
      ((neg_le_neg_iff zero (mul inverse inverse)).mpr (square_nonnegative inverse))⟩

def inverseSlopeMagnitudeBound (lower : PositiveRatio) : Nat :=
  let bound := ofSignedRatio (QProb.ofNat lower.den).toSignedRatio
  intervalMagnitudeBound (neg (mul bound bound)) zero

theorem inverseSlope_magnitude_bounded (x : ConstructiveReal) (lower : PositiveRatio)
    (positive : LE (ofSignedRatio lower.toSignedRatio) x) (precision : PositiveRatio)
    (fine : PositiveRatio.LE precision PositiveRatio.one) :
    QProb.LE ((neg (mul (x.positiveInverse lower positive) (x.positiveInverse lower positive))).rationalApproximation.value precision).magnitude
      (QProb.ofNat (inverseSlopeMagnitudeBound lower)) :=
  magnitude_bounded_of_interval _ _ _ (inverseSlope_bounds x lower positive).1 (inverseSlope_bounds x lower positive).2 precision fine

end Thesis.Probability.ConstructiveReal
