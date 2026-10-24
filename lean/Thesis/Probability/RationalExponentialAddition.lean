import Thesis.Probability.RationalTaylorProduct
import Thesis.Probability.ConstructiveRealProductLimits

namespace Thesis.Probability.RationalExponential
open ConstructiveReal RationalGeometricSeries

/-- The natural exponential addition law follows from finite Taylor
convolution and a certified vanishing corner error. The argument applies to
all signed rational inputs and assumes no infinite rearrangement theorem. -/
theorem exp_add (a b : SignedRatio) : Equiv (exp (SignedRatio.add a b)) (mul (exp a) (exp b)) := by
  let boundA := a.magnitude.naturalUpper
  let boundB := b.magnitude.naturalUpper
  let coefficient := RationalTaylorExponential.geometricCoefficient boundA * RationalTaylorExponential.geometricCoefficient boundB
  let first := (sequence a).toReal.mul (sequence b).toReal
  let second := (sequence (SignedRatio.add a b)).toReal
  have finite (n : Nat) : Within (QProb.scale (n * n) (envelope coefficient n)) (first.value n) (second.value n) := by
    have estimate := RationalTaylorExponential.partial_product_error a b boundA boundB n
      a.magnitude.le_naturalUpper b.magnitude.le_naturalUpper
    have embedded := (within_ofSignedRatio_iff _ _ _).mpr estimate
    exact (within_congr (equiv_symm (ofSignedRatio_mul _ _)) (equiv_refl _)).mp embedded
  have limits : Equiv first.limit second.limit := by
    apply first.limit_unique second.limit (fun precision => max (squareEnvelopeModulus coefficient precision.half)
      (second.modulus precision.half.half.half))
    intro precision n later
    have close := within_mono (finite n) (square_envelope_small coefficient precision.half n (Nat.le_trans (Nat.le_max_left _ _) later))
    exact within_triangle_halves precision close (second.tail_within precision.half n (Nat.le_trans (Nat.le_max_right _ _) later))
  have productLimit : Equiv first.limit (mul (exp a) (exp b)) :=
    equiv_trans (RealCauchySequence.mul_limit _ _) (mul_congr (sequence a).toReal_limit (sequence b).toReal_limit)
  exact equiv_trans (equiv_symm (sequence (SignedRatio.add a b)).toReal_limit) (equiv_trans (equiv_symm limits) productLimit)

end Thesis.Probability.RationalExponential
