import Thesis.Probability.ConstructiveRealLogSecant
import Thesis.Probability.ConstructiveRealDistanceAlgebra
import Thesis.Probability.ConstructiveRealRationalScaling

namespace Thesis.Probability.RationalLogSecant
open ConstructiveReal RationalGeometricSeries

private theorem cancel_secant (step : PositiveRatio) :
    Equiv (mul (ofSignedRatio step.toSignedRatio) (offsetSlope step).interpret)
      (rationalLog2 (offsetPoint step)) := by
  have canceled : ExactLog.Equiv (ExactLog.scaleRatio step.toQProb (offsetSlope step))
      (ExactLog.log (offsetPoint step)) := by
    rw [offsetSlope, ExactLog.scaleRatio_mul]
    have unit : QProb.Equiv (QProb.mul step.toQProb step.inv.toQProb) QProb.one := PositiveRatio.mul_inv step
    exact ExactLog.equiv_trans (ExactLog.scaleRatio_weight_congr unit _) (by
      rw [ExactLog.scaleRatio_one]; exact ExactLog.equiv_refl _)
  exact equiv_trans (equiv_symm (equiv_trans (ExactLog.interpret_scaleRatio _ _)
    (scaleRatio_mul _ _))) (ExactLog.interpret_congr canceled)

/-- A proved right first-variation bound for every positive rational
increment below a dyadic radius. The coefficient is constructed from the
existing logarithm; no derivative formula is assumed. -/
theorem right_variation_dyadic (step : PositiveRatio) (n : Nat)
    (small : PositiveRatio.LE step (⟨1, 2 ^ n, by decide, Nat.pow_pos (by decide)⟩ : PositiveRatio)) :
    Within (QProb.mul step.toQProb (envelope 2 n)) (rationalLog2 (offsetPoint step))
      (mul (ofSignedRatio step.toSignedRatio) limit) :=
  (within_congr (cancel_secant step) (equiv_refl _)).mp
    ((within_mul_positive_iff step _ _ _).mpr (offsetSlope_within step n small))

/-- A computable radius for the right first variation with requested
linear error coefficient. Only the rational denominator selects the index. -/
def rightModulus (precision : PositiveRatio) : PositiveRatio :=
  ⟨1, 2 ^ ((2 * precision.den).log2 + 1), by decide, Nat.pow_pos (by decide)⟩

/-- The error in `log₂(1+h) = c h + o(h)` is at most `epsilon*h` for
all positive rational `h` inside the explicit radius. Zero and negative
increments and the extension to real arguments are separate steps. -/
theorem right_variation (precision step : PositiveRatio) (small : PositiveRatio.LE step (rightModulus precision)) :
    Within (QProb.mul precision.toQProb step.toQProb) (rationalLog2 (offsetPoint step))
      (mul (ofSignedRatio step.toSignedRatio) limit) := by
  have estimate := right_variation_dyadic step ((2 * precision.den).log2 + 1) small
  have unitBound := envelope_small 1 precision ((2 * precision.den).log2 + 1) (by simp only [Nat.mul_one]; exact Nat.le_refl _)
  exact within_mono estimate (QProb.le_congr (QProb.equiv_refl _) (QProb.mul_comm _ _)
    (QProb.mul_le_mul (QProb.le_refl _) unitBound))

end Thesis.Probability.RationalLogSecant
