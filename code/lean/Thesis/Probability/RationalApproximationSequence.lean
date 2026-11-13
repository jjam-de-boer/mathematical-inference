import Thesis.Probability.RegularRationalAlgebra
import Thesis.Probability.ConstructiveRealCauchy

namespace Thesis.Probability.RegularRationalApproximation

/-- Sample a regular rational approximation at reciprocal-natural accuracies.
The resulting Cauchy modulus is explicit and does not select indices from an
existential convergence assertion. -/
def sequence (approximation : RegularRationalApproximation) : RationalCauchySequence where
  value n := approximation.value (PositiveRatio.unitPrecision n)
  modulus precision := precision.half.den
  cauchy precision n m left right := by
    have error := approximation.error_bound (PositiveRatio.unitPrecision n) (PositiveRatio.unitPrecision m)
    have small := QProb.le_trans error (QProb.le_congr (QProb.equiv_refl _) precision.half_sum
      (QProb.add_le_add (PositiveRatio.unitPrecision_le _ n left) (PositiveRatio.unitPrecision_le _ m right)))
    exact ((SignedRatio.magnitude_sub_le_iff _ _ _).mp small).1

theorem sequence_limit (approximation : RegularRationalApproximation) :
    ConstructiveReal.Equiv approximation.sequence.limit approximation.limit := by
  apply ConstructiveReal.equiv_trans (ConstructiveReal.equiv_symm approximation.sequence.toReal_limit)
  apply RealCauchySequence.limit_unique _ _ (fun precision => precision.den)
  intro precision n later
  exact ConstructiveReal.within_mono (ConstructiveReal.within_symm (approximation.limit_within (PositiveRatio.unitPrecision n)))
    (PositiveRatio.unitPrecision_le precision n later)

end Thesis.Probability.RegularRationalApproximation

namespace Thesis.Probability.ConstructiveReal

/-- A canonical effective sequence of rational values converging to a real
presentation. This approximates analytic values, not coordinates of a law
subject to exact linear constraints. -/
def rationalSequence (x : ConstructiveReal) : RealCauchySequence := x.rationalApproximation.sequence.toReal

theorem rationalSequence_limit (x : ConstructiveReal) : Equiv x.rationalSequence.limit x :=
  equiv_trans x.rationalApproximation.sequence.toReal_limit
    (equiv_trans x.rationalApproximation.sequence_limit x.rationalApproximation_limit)

end Thesis.Probability.ConstructiveReal
