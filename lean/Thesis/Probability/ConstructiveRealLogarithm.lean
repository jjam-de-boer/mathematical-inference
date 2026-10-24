import Thesis.Probability.RationalLogContinuity
import Thesis.Probability.ConstructiveRealReciprocal

namespace Thesis.Probability.ConstructiveReal

theorem rationalLog2_congr {a b : PositiveRatio} (same : PositiveRatio.Equiv a b) : Equiv (rationalLog2 a) (rationalLog2 b) :=
  ExactLog.interpret_congr ((ExactLog.log_equiv_log_iff _ _).mpr same)

/-- Positive rational approximations give an effective sequence of logarithm
values. The Cauchy modulus comes from the finite Bernoulli power estimate. -/
def logSequence (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) : RealCauchySequence where
  value n := rationalLog2 (x.positiveCenter lower (PositiveRatio.unitPrecision n))
  modulus precision := (lower.logInputPrecision precision).half.den
  cauchy precision n m left right := by
    have errors := (x.positiveApproximation lower bounded).error_bound (PositiveRatio.unitPrecision n) (PositiveRatio.unitPrecision m)
    have smaller := QProb.add_le_add (PositiveRatio.unitPrecision_le _ n left) (PositiveRatio.unitPrecision_le _ m right)
    have close := QProb.le_trans errors (QProb.le_congr (QProb.equiv_refl _) (PositiveRatio.half_sum _) smaller)
    exact rationalLog2_within lower _ _ precision (x.positiveCenter_lower lower _) (x.positiveCenter_lower lower _) close

/-- Base-two logarithm of a general real with a supplied positive rational
lower bound. Rational atom weights are unchanged. -/
def positiveLog2 (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) : ConstructiveReal := (x.logSequence lower bounded).limit

/-- The real logarithm has an explicit error bound from a sufficiently late
certified rational input approximation. -/
theorem positiveLog2_tail (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) (precision : PositiveRatio) (n : Nat)
    (later : (x.logSequence lower bounded).modulus precision.half.half ≤ n) :
    Within precision.toQProb (rationalLog2 (x.positiveCenter lower (PositiveRatio.unitPrecision n))) (x.positiveLog2 lower bounded) :=
  (x.logSequence lower bounded).tail_within precision n later

/-- The new logarithm agrees with the previous certified logarithm of every
positive rational argument. -/
theorem positiveLog2_ofPositiveRatio (value lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) (ofSignedRatio value.toSignedRatio)) :
    Equiv ((ofSignedRatio value.toSignedRatio).positiveLog2 lower bounded) (rationalLog2 value) := by
  apply RealCauchySequence.limit_unique _ _ (fun _ => 0)
  intro precision n _
  have lowerRational := (SignedRatio.toSignedRatio_le_iff _ _).mp ((ofSignedRatio_le_iff _ _).mp bounded)
  have same := rationalLog2_congr (positiveCenter_ofPositiveRatio value lower (PositiveRatio.unitPrecision n) lowerRational)
  exact (within_congr same (equiv_refl _)).mpr (within_refl precision.toQProb (rationalLog2 value))

/-- The logarithm is independent of real presentations and of the positive
lower-bound witness, even though those choices change its evaluation schedule. -/
theorem positiveLog2_congr {x y : ConstructiveReal} (same : Equiv x y) (lowerX lowerY : PositiveRatio)
    (boundedX : LE (ofSignedRatio lowerX.toSignedRatio) x) (boundedY : LE (ofSignedRatio lowerY.toSignedRatio) y) :
    Equiv (x.positiveLog2 lowerX boundedX) (y.positiveLog2 lowerY boundedY) := by
  let common := if PositiveRatio.LE lowerX lowerY then lowerX else lowerY
  have lowerBounds : PositiveRatio.LE common lowerX ∧ PositiveRatio.LE common lowerY := by
    by_cases ordered : PositiveRatio.LE lowerX lowerY
    · simp only [common, if_pos ordered]
      exact ⟨PositiveRatio.le_refl _, ordered⟩
    · simp only [common, if_neg ordered]
      exact ⟨(PositiveRatio.le_total lowerX lowerY).resolve_left ordered, PositiveRatio.le_refl _⟩
  have compareTerms (precision : PositiveRatio) (n : Nat)
      (later : (common.logInputPrecision precision).half.den ≤ n) :
      Within precision.toQProb ((x.logSequence lowerX boundedX).value n) ((y.logSequence lowerY boundedY).value n) := by
    let unit := PositiveRatio.unitPrecision n
    have first := (within_congr (equiv_refl _) same).mp (within_symm (x.positiveCenter_within lowerX boundedX unit))
    have between := within_triangle first (y.positiveCenter_within lowerY boundedY unit)
    have errors := (within_ofSignedRatio_iff _ _ _).mp between
    have unitBound := PositiveRatio.unitPrecision_le (common.logInputPrecision precision).half n later
    have small := QProb.le_trans errors (QProb.le_congr (QProb.equiv_refl _) (PositiveRatio.half_sum _)
      (QProb.add_le_add unitBound unitBound))
    exact rationalLog2_within common _ _ precision
      (PositiveRatio.le_trans lowerBounds.1 (x.positiveCenter_lower lowerX unit))
      (PositiveRatio.le_trans lowerBounds.2 (y.positiveCenter_lower lowerY unit)) small
  apply RealCauchySequence.limit_unique _ _ (fun precision => max (common.logInputPrecision precision.half).half.den
    ((y.logSequence lowerY boundedY).modulus precision.half.half.half))
  intro precision n later
  exact within_triangle_halves precision
    (compareTerms precision.half n (Nat.le_trans (Nat.le_max_left _ _) later))
    ((y.logSequence lowerY boundedY).tail_within precision.half n (Nat.le_trans (Nat.le_max_right _ _) later))

end Thesis.Probability.ConstructiveReal
