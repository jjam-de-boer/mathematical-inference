import Thesis.Probability.ConstructiveRealExpVariation
import Thesis.Probability.ConstructiveRealSquareBounds

namespace Thesis.Probability.ConstructiveReal

/-- Rational error advertised by the real exponential's quadratic remainder
on an interval with the supplied natural bound. -/
def expRadiusError (bound : Nat) (radius : PositiveRatio) : QProb :=
  QProb.mul (QProb.mul radius.toQProb radius.toQProb) ⟨RationalTaylorExponential.uniformSumBound bound, 2, by decide⟩

theorem exp_first_variation_radius (x y : ConstructiveReal) (bound : Nat) (radius : PositiveRatio)
    (close : Within radius.toQProb x y)
    (boundedX : ∀ precision, PositiveRatio.LE precision PositiveRatio.one →
      QProb.LE (x.rationalApproximation.value precision).magnitude (QProb.ofNat bound))
    (boundedY : ∀ precision, PositiveRatio.LE precision PositiveRatio.one →
      QProb.LE (y.rationalApproximation.value precision).magnitude (QProb.ofNat bound)) :
    Within (expRadiusError bound radius) y.exp (expLinear x y) := by
  let c : QProb := ⟨RationalTaylorExponential.uniformSumBound bound, 2, by decide⟩
  have positive : LE zero (ofSignedRatio c.toSignedRatio) :=
    (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr (QProb.zero_le c))
  have scaled := mul_le_mul_nonnegative_right positive (within_square close)
  have embedded : Equiv
      (mul (ofSignedRatio (QProb.mul radius.toQProb radius.toQProb).toSignedRatio) (ofSignedRatio c.toSignedRatio))
      (ofSignedRatio (expRadiusError bound radius).toSignedRatio) := by
    rw [expRadiusError, QProb.toSignedRatio_mul]
    exact ofSignedRatio_mul _ _
  exact withinReal_mono (exp_first_variation_bounded x y bound boundedX boundedY)
    ((le_congr (equiv_refl _) embedded).mp scaled)

/-- One fixed bound controls all fine rational approximants in the unit
neighborhood of this real presentation. It is computed, not an extra premise. -/
def expLocalBound (x : ConstructiveReal) : Nat := x.rationalApproximation.magnitudeBound + 3

theorem exp_first_variation_local (x y : ConstructiveReal) (radius : PositiveRatio)
    (small : PositiveRatio.LE radius PositiveRatio.one) (close : Within radius.toQProb x y) :
    Within (expRadiusError x.expLocalBound radius) y.exp (expLinear x y) := by
  apply exp_first_variation_radius x y x.expLocalBound radius close
  · intro precision fine
    apply QProb.le_trans (x.rationalApproximation.magnitude_bounded precision fine)
    change x.rationalApproximation.magnitudeBound * 1 ≤ (x.rationalApproximation.magnitudeBound + 3) * 1
    omega
  · intro precision fine
    exact RegularRationalApproximation.magnitude_bounded_near y.rationalApproximation x.rationalApproximation
      ((within_congr y.rationalApproximation_limit x.rationalApproximation_limit).mpr (within_symm (within_mono close small))) precision fine

end Thesis.Probability.ConstructiveReal
