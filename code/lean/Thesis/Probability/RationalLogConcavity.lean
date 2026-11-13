import Thesis.Probability.RationalAMGMMean
import Thesis.Probability.ExactLogLinear

namespace Thesis.Probability

/-- The undivided weighted form is convenient for secant comparisons. -/
theorem rational_log_pair_weighted (a b mean : PositiveRatio) (left right : Nat)
    (bounded : QProb.LE (QProb.add (QProb.scale left a.toQProb) (QProb.scale right b.toQProb))
      (QProb.scale (left + right) mean.toQProb)) :
    ExactLog.LE (ExactLog.add (ExactLog.scaleNat left (ExactLog.log a)) (ExactLog.scaleNat right (ExactLog.log b)))
      (ExactLog.scaleNat (left + right) (ExactLog.log mean)) := by
  let items := [(a, left), (b, right)]
  have sum : QProb.Equiv (RationalAMGM.weightedSum items)
      (QProb.add (QProb.scale left a.toQProb) (QProb.scale right b.toQProb)) :=
    QProb.add_congr (QProb.equiv_refl _) (QProb.add_zero _)
  have arithmetic : QProb.LE (RationalAMGM.weightedSum items)
      (QProb.scale (RationalAMGM.totalWeight items) mean.toQProb) := by
    simp only [items, RationalAMGM.totalWeight, Nat.add_zero]
    exact QProb.le_congr (QProb.equiv_symm sum) (QProb.equiv_refl _) bounded
  simpa only [ExactLog.LE, ExactLog.add, ExactLog.scaleNat, ExactLog.log,
    PositiveRatio.pow_one, Nat.mul_one, Nat.one_mul, items, RationalAMGM.weightedProduct,
    RationalAMGM.totalWeight, PositiveRatio.mul_one, Nat.add_zero] using
      RationalAMGM.weightedProduct_le_mean items mean arithmetic

/-- Concavity of the exact rational logarithm, proved from finite weighted
AM–GM. Zero coefficients are included; only the normalization denominator
must be positive. No logarithm formula or derivative is a premise. -/
theorem rational_log_pair_concavity (a b mean : PositiveRatio) (left right : Nat) (positive : 0 < left + right)
    (bounded : QProb.LE (QProb.add (QProb.scale left a.toQProb) (QProb.scale right b.toQProb))
      (QProb.scale (left + right) mean.toQProb)) :
    ExactLog.LE
      (ExactLog.divideNat (ExactLog.add (ExactLog.scaleNat left (ExactLog.log a)) (ExactLog.scaleNat right (ExactLog.log b)))
        (left + right) positive) (ExactLog.log mean) := by
  let items := [(a, left), (b, right)]
  have sum : QProb.Equiv (RationalAMGM.weightedSum items) (QProb.add (QProb.scale left a.toQProb) (QProb.scale right b.toQProb)) :=
    QProb.add_congr (QProb.equiv_refl _) (QProb.add_zero _)
  have arithmetic : QProb.LE (RationalAMGM.weightedSum items) (QProb.scale (RationalAMGM.totalWeight items) mean.toQProb) := by
    simp only [items, RationalAMGM.totalWeight, Nat.add_zero]
    exact QProb.le_congr (QProb.equiv_symm sum) (QProb.equiv_refl _) bounded
  have estimate := RationalAMGM.weightedProduct_le_mean items mean arithmetic
  simpa only [ExactLog.LE, ExactLog.divideNat, ExactLog.add, ExactLog.scaleNat, ExactLog.log,
    PositiveRatio.pow_one, Nat.mul_one, Nat.one_mul, items, RationalAMGM.weightedProduct, RationalAMGM.totalWeight,
    PositiveRatio.mul_one, Nat.add_zero] using estimate

end Thesis.Probability
