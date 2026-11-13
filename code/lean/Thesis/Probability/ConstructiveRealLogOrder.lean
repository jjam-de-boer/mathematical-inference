import Thesis.Probability.ConstructiveRealLogContinuity

namespace Thesis.Probability.ConstructiveReal

/-- The constructed logarithm preserves closed order. Positive lower-bound
witnesses on the two inputs may differ. The proof uses one-sided finite
logarithm bounds and effective limits, without deciding real order. -/
theorem positiveLog2_mono (x y : ConstructiveReal) (lowerX lowerY : PositiveRatio)
    (boundedX : LE (ofSignedRatio lowerX.toSignedRatio) x) (boundedY : LE (ofSignedRatio lowerY.toSignedRatio) y)
    (compared : LE x y) : LE (x.positiveLog2 lowerX boundedX) (y.positiveLog2 lowerY boundedY) := by
  apply le_of_forall_rational_error
  intro precision
  let first := x.logSequence lowerX boundedX
  let second := y.logSequence lowerY boundedY
  have termOrder (n : Nat) (later : (lowerY.logInputPrecision precision).den ≤ n) :
      LE (first.value n) ((second.add (RealCauchySequence.constant (ofSignedRatio precision.toSignedRatio))).value n) := by
    let unit := PositiveRatio.unitPrecision n
    have close := le_trans (x.positiveCenter_le lowerX boundedX unit)
      (le_trans compared (y.positiveCenter_within lowerY boundedY unit).1)
    have enlarged := le_trans close (add_le_add (le_refl _)
      ((ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr (PositiveRatio.unitPrecision_le _ n later))))
    have rational := (ofSignedRatio_le_iff _ _).mp
      ((le_congr (equiv_refl _) (ofSignedRatio_add _ _)).mp enlarged)
    exact rationalLog2_le_add_of_close lowerY _ _ precision (y.positiveCenter_lower lowerY unit) rational
  have limits := RealCauchySequence.limit_le_limit_of_tail first
    (second.add (RealCauchySequence.constant (ofSignedRatio precision.toSignedRatio)))
    (lowerY.logInputPrecision precision).den termOrder
  have sumLimit : Equiv
      (second.add (RealCauchySequence.constant (ofSignedRatio precision.toSignedRatio))).limit
      (add second.limit (ofSignedRatio precision.toSignedRatio)) :=
    equiv_trans (RealCauchySequence.add_limit second _)
    (add_congr (equiv_refl _) (RealCauchySequence.constant_limit _))
  exact (le_congr (equiv_refl _) sumLimit).mp limits

theorem positiveLog2_one (lower : PositiveRatio) (bounded : LE (ofSignedRatio lower.toSignedRatio) one) :
    Equiv (one.positiveLog2 lower bounded) zero :=
  equiv_trans (positiveLog2_ofPositiveRatio PositiveRatio.one lower bounded) (ExactLog.interpret_ofSignedRatio SignedRatio.zero)

/-- The usual sign conclusions follow from the value at one and monotonicity. -/
theorem positiveLog2_nonnegative (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) (aboveOne : LE one x) : LE zero (x.positiveLog2 lower bounded) :=
  (le_congr (positiveLog2_one PositiveRatio.one (le_refl one)) (equiv_refl _)).mp
    (positiveLog2_mono one x PositiveRatio.one lower (le_refl one) bounded aboveOne)

theorem positiveLog2_nonpositive (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) (belowOne : LE x one) : LE (x.positiveLog2 lower bounded) zero :=
  (le_congr (equiv_refl _) (positiveLog2_one PositiveRatio.one (le_refl one))).mp
    (positiveLog2_mono x one lower PositiveRatio.one bounded (le_refl one) belowOne)

end Thesis.Probability.ConstructiveReal
