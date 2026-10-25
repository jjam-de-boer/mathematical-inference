import Thesis.Probability.ConstructiveRealEntropy
import Thesis.Probability.ConstructiveRealCauchyStability

namespace Thesis.Probability.ConstructiveReal

/-- Uniform entropy continuity on the closed unit interval. Half of the
rational input radius is reserved for the two rational enclosure errors.
In particular the certificate also applies across the zero boundary. -/
theorem realEntropyTerm_within (x y : ConstructiveReal)
    (nonnegativeX : LE zero x) (nonnegativeY : LE zero y) (boundedX : LE x one) (boundedY : LE y one)
    (precision : PositiveRatio)
    (close : Within (entropyInputPrecision precision).half.toQProb x y) :
    Within precision.toQProb (x.realEntropyTerm nonnegativeX boundedX) (y.realEntropyTerm nonnegativeY boundedY) := by
  let delta := entropyInputPrecision precision
  apply RealCauchySequence.limit_within_of_tail _ _ _ delta.half.half.den
  intro n later
  let unit := PositiveRatio.unitPrecision n
  have first := within_triangle (within_symm (x.unitCenter_within nonnegativeX unit)) close
  have combined := within_triangle first (y.unitCenter_within nonnegativeY unit)
  have errors := (within_ofSignedRatio_iff _ _ _).mp combined
  have unitBound := PositiveRatio.unitPrecision_le delta.half.half n later
  have enlarged := QProb.add_le_add (QProb.add_le_add unitBound (QProb.le_refl delta.half.toQProb)) unitBound
  have collected : QProb.Equiv
      (QProb.add (QProb.add delta.half.half.toQProb delta.half.toQProb) delta.half.half.toQProb) delta.toQProb :=
    QProb.equiv_trans (QProb.add_congr (QProb.add_comm _ _) (QProb.equiv_refl _))
      (QProb.equiv_trans (QProb.add_assoc _ _ _)
        (QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl _) delta.half.half_sum) delta.half_sum))
  have small := QProb.le_trans errors (QProb.le_congr (QProb.equiv_refl _) collected enlarged)
  exact rationalEntropyTerm_within precision _ _ (x.unitCenter_bounded nonnegativeX boundedX unit)
    (y.unitCenter_bounded nonnegativeY boundedY unit) small

end Thesis.Probability.ConstructiveReal
