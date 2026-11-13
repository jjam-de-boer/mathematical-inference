import Thesis.Probability.ConstructiveRealLogLimits
import Thesis.Probability.ConstructiveRealProductLimits

namespace Thesis.Probability.ConstructiveReal

/-- Positive-rational multiplication agrees with its real embedding. -/
theorem ofPositiveRatio_mul (a b : PositiveRatio) :
    Equiv (mul (ofSignedRatio a.toSignedRatio) (ofSignedRatio b.toSignedRatio)) (ofSignedRatio (a.mul b).toSignedRatio) := by
  change Equiv _ (ofSignedRatio (QProb.mul a.toQProb b.toQProb).toSignedRatio)
  rw [QProb.toSignedRatio_mul]
  exact ofSignedRatio_mul _ _

/-- The product domain's positive lower bound is proved from the supplied
input bounds; it is not an unexplained positivity obligation. -/
theorem mul_positive_lower (x y : ConstructiveReal) (lowerX lowerY : PositiveRatio)
    (boundedX : LE (ofSignedRatio lowerX.toSignedRatio) x) (boundedY : LE (ofSignedRatio lowerY.toSignedRatio) y) :
    LE (ofSignedRatio (lowerX.mul lowerY).toSignedRatio) (mul x y) := by
  have firstPositive : LE zero (ofSignedRatio lowerX.toSignedRatio) :=
    (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr lowerX.signed_nonnegative)
  have secondPositive : LE zero y := le_trans
    ((ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr lowerY.signed_nonnegative)) boundedY
  exact (le_congr (ofPositiveRatio_mul lowerX lowerY) (equiv_refl _)).mp
    (mul_le_mul boundedX boundedY firstPositive secondPositive)

/-- The logarithm product law for arbitrary positive real presentations.
The proof transfers the exact rational law through effective product and
logarithm limits, with all domain lower bounds constructed explicitly. -/
theorem positiveLog2_mul (x y : ConstructiveReal) (lowerX lowerY : PositiveRatio)
    (boundedX : LE (ofSignedRatio lowerX.toSignedRatio) x) (boundedY : LE (ofSignedRatio lowerY.toSignedRatio) y) :
    Equiv ((mul x y).positiveLog2 (lowerX.mul lowerY) (mul_positive_lower x y lowerX lowerY boundedX boundedY))
      (add (x.positiveLog2 lowerX boundedX) (y.positiveLog2 lowerY boundedY)) := by
  let first := x.positiveSequence lowerX boundedX
  let second := y.positiveSequence lowerY boundedY
  let product := first.mul second
  let lower := lowerX.mul lowerY
  have positive : ∀ n, LE (ofSignedRatio lower.toSignedRatio) (product.value n) := fun n =>
    mul_positive_lower _ _ lowerX lowerY (x.positiveSequence_lower lowerX boundedX n) (y.positiveSequence_lower lowerY boundedY n)
  let logs := product.mapLog2 lower positive
  let sum := (x.logSequence lowerX boundedX).add (y.logSequence lowerY boundedY)
  have pointwise (n : Nat) : Equiv (logs.value n) (sum.value n) := by
    let a := x.positiveCenter lowerX (PositiveRatio.unitPrecision n)
    let b := y.positiveCenter lowerY (PositiveRatio.unitPrecision n)
    have represented : Equiv (product.value n) (ofSignedRatio (a.mul b).toSignedRatio) := ofPositiveRatio_mul a b
    have rationalBound : LE (ofSignedRatio lower.toSignedRatio) (ofSignedRatio (a.mul b).toSignedRatio) :=
      (le_congr (equiv_refl _) represented).mp (positive n)
    exact equiv_trans (positiveLog2_congr represented lower lower (positive n) rationalBound)
      (equiv_trans (positiveLog2_ofPositiveRatio (a.mul b) lower rationalBound) (rationalLog2_mul a b))
  have productLimit : Equiv product.limit (mul x y) :=
    equiv_trans (RealCauchySequence.mul_limit first second)
      (mul_congr (x.positiveSequence_limit lowerX boundedX) (y.positiveSequence_limit lowerY boundedY))
  have actualLimit : Equiv logs.limit
      ((mul x y).positiveLog2 lower (mul_positive_lower x y lowerX lowerY boundedX boundedY)) :=
    equiv_trans (RealCauchySequence.mapLog2_limit product lower positive)
      (positiveLog2_congr productLimit lower lower (product.le_limit _ positive) (mul_positive_lower x y lowerX lowerY boundedX boundedY))
  exact equiv_trans (equiv_symm actualLimit)
    (equiv_trans (RealCauchySequence.limit_congr logs sum pointwise) (RealCauchySequence.add_limit _ _))

end Thesis.Probability.ConstructiveReal
