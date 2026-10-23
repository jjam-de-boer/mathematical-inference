import Thesis.Probability.ConstructiveRealLogarithm
import Thesis.Probability.ConstructiveRealCauchyStability

namespace Thesis.Probability.ConstructiveReal

/-- A certified uniform continuity modulus for the real logarithm on an
explicit positive half-line. The spare half of the input radius absorbs the
rational enclosure errors before passage to the limit. -/
theorem positiveLog2_within (x y : ConstructiveReal) (lower : PositiveRatio)
    (boundedX : LE (ofSignedRatio lower.toSignedRatio) x) (boundedY : LE (ofSignedRatio lower.toSignedRatio) y)
    (precision : PositiveRatio)
    (close : Within (lower.logInputPrecision precision).half.toQProb x y) :
    Within precision.toQProb (x.positiveLog2 lower boundedX) (y.positiveLog2 lower boundedY) := by
  let delta := lower.logInputPrecision precision
  apply RealCauchySequence.limit_within_of_tail _ _ _ delta.half.half.den
  intro n later
  let unit := PositiveRatio.unitPrecision n
  have first := within_triangle (within_symm (x.positiveCenter_within lower boundedX unit)) close
  have combined := within_triangle first (y.positiveCenter_within lower boundedY unit)
  have errors := (within_ofSignedRatio_iff _ _ _).mp combined
  have unitBound := PositiveRatio.unitPrecision_le delta.half.half n later
  have enlarged := QProb.add_le_add (QProb.add_le_add unitBound (QProb.le_refl delta.half.toQProb)) unitBound
  have collected : QProb.Equiv
      (QProb.add (QProb.add delta.half.half.toQProb delta.half.toQProb) delta.half.half.toQProb) delta.toQProb :=
    QProb.equiv_trans (QProb.add_congr (QProb.add_comm _ _) (QProb.equiv_refl _))
      (QProb.equiv_trans (QProb.add_assoc _ _ _)
        (QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl _) delta.half.half_sum) delta.half_sum))
  have small := QProb.le_trans errors (QProb.le_congr (QProb.equiv_refl _) collected enlarged)
  exact rationalLog2_within lower _ _ precision (x.positiveCenter_lower lower _) (y.positiveCenter_lower lower _) small

end Thesis.Probability.ConstructiveReal
