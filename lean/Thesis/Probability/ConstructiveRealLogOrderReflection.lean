import Thesis.Probability.ConstructiveRealLogOrder

namespace Thesis.Probability.ConstructiveReal

/-- The real logarithm reflects closed order. For each pair of rational
endpoints, a refused endpoint comparison makes both endpoints positive.
Monotonicity then places their exact rational logarithms in the asserted
order, which the faithful exact-log interpretation reflects back. The only
comparisons decided here are comparisons of rational endpoints. -/
theorem positiveLog2_reflects_order (x y : ConstructiveReal) (lowerX lowerY : PositiveRatio)
    (boundedX : LE (ofSignedRatio lowerX.toSignedRatio) x) (boundedY : LE (ofSignedRatio lowerY.toSignedRatio) y)
    (compared : LE (x.positiveLog2 lowerX boundedX) (y.positiveLog2 lowerY boundedY)) : LE x y := by
  intro first second
  let a := (x.enclose first).lower
  let b := (y.enclose second).upper
  by_cases endpoints : SignedRatio.LE a b
  · exact endpoints
  · have reverse : SignedRatio.LE b a := (SignedRatio.le_total a b).resolve_left endpoints
    have bLower : SignedRatio.LE lowerY.toSignedRatio b :=
      (ofSignedRatio_le_iff _ _).mp (le_trans boundedY (y.upper_bound second))
    have aLower := SignedRatio.le_trans bLower reverse
    let pa := PositiveRatio.ofSignedPositive a (SignedRatio.positive_of_lower lowerY a aLower)
    let pb := PositiveRatio.ofSignedPositive b (SignedRatio.positive_of_lower lowerY b bLower)
    have aSame : SignedRatio.Equiv pa.toSignedRatio a := PositiveRatio.ofSignedPositive_value _ _
    have bSame : SignedRatio.Equiv pb.toSignedRatio b := PositiveRatio.ofSignedPositive_value _ _
    have aBound : LE (ofSignedRatio lowerY.toSignedRatio) (ofSignedRatio pa.toSignedRatio) :=
      (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.le_congr (SignedRatio.equiv_refl _) aSame).mpr aLower)
    have bBound : LE (ofSignedRatio lowerY.toSignedRatio) (ofSignedRatio pb.toSignedRatio) :=
      (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.le_congr (SignedRatio.equiv_refl _) bSame).mpr bLower)
    have aBelow : LE (ofSignedRatio pa.toSignedRatio) x :=
      (le_congr ((ofSignedRatio_equiv_iff _ _).mpr aSame) (equiv_refl x)).mpr (x.lower_bound first)
    have bAbove : LE y (ofSignedRatio pb.toSignedRatio) :=
      (le_congr (equiv_refl y) ((ofSignedRatio_equiv_iff _ _).mpr bSame)).mpr (y.upper_bound second)
    have chained := le_trans (positiveLog2_mono _ x lowerY lowerX aBound boundedX aBelow)
      (le_trans compared (positiveLog2_mono y _ lowerY lowerY boundedY bBound bAbove))
    have rational : LE (rationalLog2 pa) (rationalLog2 pb) :=
      (le_congr (positiveLog2_ofPositiveRatio pa lowerY aBound) (positiveLog2_ofPositiveRatio pb lowerY bBound)).mp chained
    have exactOrder := (ExactLog.interpret_le_iff (ExactLog.log pa) (ExactLog.log pb)).mp rational
    have inputs := (ExactLog.log_le_log_iff pa pb).mp exactOrder
    exact (SignedRatio.le_congr aSame bSame).mp ((SignedRatio.toSignedRatio_le_iff pa.toQProb pb.toQProb).mpr inputs)

theorem positiveLog2_le_iff (x y : ConstructiveReal) (lowerX lowerY : PositiveRatio)
    (boundedX : LE (ofSignedRatio lowerX.toSignedRatio) x) (boundedY : LE (ofSignedRatio lowerY.toSignedRatio) y) :
    LE (x.positiveLog2 lowerX boundedX) (y.positiveLog2 lowerY boundedY) ↔ LE x y :=
  ⟨positiveLog2_reflects_order x y lowerX lowerY boundedX boundedY,
    positiveLog2_mono x y lowerX lowerY boundedX boundedY⟩

/-- Logarithm equality on positive real domains determines the input value. -/
theorem positiveLog2_equiv_iff (x y : ConstructiveReal) (lowerX lowerY : PositiveRatio)
    (boundedX : LE (ofSignedRatio lowerX.toSignedRatio) x) (boundedY : LE (ofSignedRatio lowerY.toSignedRatio) y) :
    Equiv (x.positiveLog2 lowerX boundedX) (y.positiveLog2 lowerY boundedY) ↔ Equiv x y :=
  and_congr (positiveLog2_le_iff x y lowerX lowerY boundedX boundedY)
    (positiveLog2_le_iff y x lowerY lowerX boundedY boundedX)

end Thesis.Probability.ConstructiveReal
