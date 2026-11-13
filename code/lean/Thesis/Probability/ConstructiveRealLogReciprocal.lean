import Thesis.Probability.ConstructiveRealLogMultiplication
import Thesis.Probability.ConstructiveRealBounds

namespace Thesis.Probability.ConstructiveReal

/-- A computable candidate lower bound for the reciprocal, derived from a
positive natural upper bound of the original real presentation. -/
def positiveInverseLower (x : ConstructiveReal) : PositiveRatio :=
  (PositiveRatio.ofNat x.naturalUpper x.naturalUpper_pos).inv

/-- The reciprocal's positive-domain certificate is constructed, rather
than being an extra premise of the logarithm inverse law. -/
theorem positiveInverse_lower (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) :
    LE (ofSignedRatio x.positiveInverseLower.toSignedRatio) (x.positiveInverse lower bounded) := by
  let size := PositiveRatio.ofNat x.naturalUpper x.naturalUpper_pos
  let factor := ofSignedRatio size.toSignedRatio
  have compared := mul_le_mul_nonnegative_right (x.positiveInverse_nonnegative lower bounded) x.le_naturalUpper
  have oneBound : LE one (mul factor (x.positiveInverse lower bounded)) :=
    (le_congr (x.mul_positiveInverse lower bounded) (equiv_refl _)).mp compared
  have canceled : Equiv (mul factor (ofSignedRatio size.inv.toSignedRatio)) one :=
    equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (PositiveRatio.signed_mul_inv size))
  have multiplied := (le_congr canceled (equiv_refl _)).mpr oneBound
  exact (mul_le_mul_positive_iff factor size (le_refl factor) _ _).mp multiplied

/-- The general real logarithm inverse law, with the inverse's positive
lower bound computed automatically from the original input. -/
theorem positiveLog2_positiveInverse (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) :
    Equiv ((x.positiveInverse lower bounded).positiveLog2 x.positiveInverseLower (x.positiveInverse_lower lower bounded))
      (neg (x.positiveLog2 lower bounded)) := by
  let inverse := x.positiveInverse lower bounded
  have inverseBound := x.positiveInverse_lower lower bounded
  have productLog := positiveLog2_mul x inverse lower x.positiveInverseLower bounded inverseBound
  have zeroLog := equiv_trans
    (positiveLog2_congr (x.mul_positiveInverse lower bounded) (lower.mul x.positiveInverseLower) PositiveRatio.one
      (mul_positive_lower x inverse lower x.positiveInverseLower bounded inverseBound) (le_refl one))
    (positiveLog2_one PositiveRatio.one (le_refl one))
  exact neg_unique _ _ (equiv_trans (equiv_symm productLog) zeroLog)

/-- Division is interpreted as multiplication by the constructed positive
reciprocal; all domain witnesses in the logarithm quotient law are proved. -/
theorem positiveLog2_quotient (x y : ConstructiveReal) (lowerX lowerY : PositiveRatio)
    (boundedX : LE (ofSignedRatio lowerX.toSignedRatio) x) (boundedY : LE (ofSignedRatio lowerY.toSignedRatio) y) :
    Equiv ((mul x (y.positiveInverse lowerY boundedY)).positiveLog2 (lowerX.mul y.positiveInverseLower)
      (mul_positive_lower x _ lowerX y.positiveInverseLower boundedX (y.positiveInverse_lower lowerY boundedY)))
      (sub (x.positiveLog2 lowerX boundedX) (y.positiveLog2 lowerY boundedY)) :=
  equiv_trans (positiveLog2_mul x _ lowerX y.positiveInverseLower boundedX (y.positiveInverse_lower lowerY boundedY))
    (add_congr (equiv_refl _) (y.positiveLog2_positiveInverse lowerY boundedY))

end Thesis.Probability.ConstructiveReal
