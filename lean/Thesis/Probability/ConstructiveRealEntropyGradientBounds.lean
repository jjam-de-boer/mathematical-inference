import Thesis.Probability.ConstructiveRealUniformBounds
import Thesis.Probability.ConstructiveRealEntropyFirstVariation
import Thesis.Probability.ConstructiveRealLogOrder

namespace Thesis.Probability.ConstructiveReal

/-- Fixed endpoint bounds for the bit-entropy gradient on a positive part
of the unit interval. They do not depend on the real presentation of x. -/
theorem entropyBitGradient_bounds (x : ConstructiveReal) (lower : PositiveRatio)
    (inside : entropyPositiveDomain lower x) :
    LE (neg (ofSignedRatio ⟨3, 1, by decide⟩)) (entropyBitGradient x lower inside.1) ∧
      LE (entropyBitGradient x lower inside.1)
        (neg ((ofSignedRatio lower.toSignedRatio).positiveLog2 lower (le_refl _))) := by
  let logarithm := x.positiveLog2 lower inside.1
  have coefficientPositive : LE zero RationalLogSecant.limit :=
    le_trans ((ofSignedRatio_le_iff _ _).mpr (by decide +kernel)) RationalLogSecant.one_le_limit
  have sumUpper : LE (add logarithm RationalLogSecant.limit) (ofSignedRatio ⟨3, 1, by decide⟩) :=
    (le_congr (equiv_refl _) (zero_add _)).mp
      (add_le_add (positiveLog2_nonpositive x lower inside.1 inside.2) RationalLogSecant.limit_le_three)
  have logLower := positiveLog2_mono (ofSignedRatio lower.toSignedRatio) x lower lower (le_refl _) inside.1 inside.1
  have sumLower : LE ((ofSignedRatio lower.toSignedRatio).positiveLog2 lower (le_refl _))
      (add logarithm RationalLogSecant.limit) :=
    le_trans logLower ((le_congr (add_zero logarithm) (equiv_refl _)).mp (add_le_add (le_refl logarithm) coefficientPositive))
  exact ⟨(neg_le_neg_iff _ _).mpr sumUpper, (neg_le_neg_iff _ _).mpr sumLower⟩

def entropyGradientMagnitudeBound (lower : PositiveRatio) : Nat :=
  intervalMagnitudeBound (neg (ofSignedRatio ⟨3, 1, by decide⟩))
    (neg ((ofSignedRatio lower.toSignedRatio).positiveLog2 lower (le_refl _)))

/-- A computable common bound for fine approximants of all entropy slopes
in the supplied positive cube. This supplies the outer bound in the uniform
chain rule without a pointwise-dependent radius. -/
theorem entropyBitGradient_magnitude_bounded (x : ConstructiveReal) (lower : PositiveRatio)
    (inside : entropyPositiveDomain lower x) (precision : PositiveRatio)
    (fine : PositiveRatio.LE precision PositiveRatio.one) :
    QProb.LE ((entropyBitGradient x lower inside.1).rationalApproximation.value precision).magnitude
      (QProb.ofNat (entropyGradientMagnitudeBound lower)) :=
  magnitude_bounded_of_interval _ _ _ (entropyBitGradient_bounds x lower inside).1
    (entropyBitGradient_bounds x lower inside).2 precision fine

end Thesis.Probability.ConstructiveReal
