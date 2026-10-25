import Thesis.Probability.ConstructiveRealNaturalLog
import Thesis.Probability.ConstructiveRealLogOrderReflection

namespace Thesis.Probability.ConstructiveReal

/-- Natural logarithm equality also determines positive real inputs. The
proved bit/natural unit conversion reduces this to bit-logarithm separation. -/
theorem positiveLn_equiv_iff (x y : ConstructiveReal) (lowerX lowerY : PositiveRatio)
    (boundedX : LE (ofSignedRatio lowerX.toSignedRatio) x) (boundedY : LE (ofSignedRatio lowerY.toSignedRatio) y) :
    Equiv (x.positiveLn lowerX boundedX) (y.positiveLn lowerY boundedY) ↔ Equiv x y := by
  constructor
  · intro same
    have binary : Equiv (x.positiveLog2 lowerX boundedX) (y.positiveLog2 lowerY boundedY) :=
      equiv_trans (positiveLog2_from_positiveLn x lowerX boundedX)
        (equiv_trans (mul_congr same (equiv_refl RationalLogSecant.limit))
          (equiv_symm (positiveLog2_from_positiveLn y lowerY boundedY)))
    exact (positiveLog2_equiv_iff x y lowerX lowerY boundedX boundedY).mp binary
  · intro same
    exact positiveLn_congr same lowerX lowerY boundedX boundedY


/-- Natural logarithms preserve and reflect order with their proved positive
unit factor; the rational lower-bound witnesses may differ between inputs. -/
theorem positiveLn_le_iff (x y : ConstructiveReal) (lowerX lowerY : PositiveRatio)
    (boundedX : LE (ofSignedRatio lowerX.toSignedRatio) x) (boundedY : LE (ofSignedRatio lowerY.toSignedRatio) y) :
    LE (x.positiveLn lowerX boundedX) (y.positiveLn lowerY boundedY) ↔ LE x y := by
  calc
    _ ↔ LE (mul lnTwo (x.positiveLog2 lowerX boundedX)) (mul lnTwo (y.positiveLog2 lowerY boundedY)) :=
      le_congr (mul_comm (x.positiveLog2 lowerX boundedX) lnTwo) (mul_comm (y.positiveLog2 lowerY boundedY) lnTwo)
    _ ↔ LE (x.positiveLog2 lowerX boundedX) (y.positiveLog2 lowerY boundedY) :=
      mul_le_mul_positive_iff lnTwo RationalLogSecant.limit.positiveInverseLower lnTwo_lower _ _
    _ ↔ LE x y := positiveLog2_le_iff x y lowerX lowerY boundedX boundedY

/-- The exponential of the natural logarithm recovers every positive input.
This direction uses proved logarithm injectivity; it is not inferred merely
from the already proved opposite composition. -/
theorem exp_positiveLn (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) : Equiv (exp (x.positiveLn lower bounded)) x :=
  (positiveLn_equiv_iff _ x (x.positiveLn lower bounded).expLower lower
    (x.positiveLn lower bounded).exp_lower bounded).mp (positiveLn_exp (x.positiveLn lower bounded))

/-- Natural Taylor exponentials preserve and reflect closed real order.
The proof uses logarithm order reflection and the independently identified
positive unit coefficient, with no arbitrary-real comparison procedure. -/
theorem exp_le_exp_iff (x y : ConstructiveReal) : LE x.exp y.exp ↔ LE x y := by
  calc
    _ ↔ LE x.expLog2 y.expLog2 := (positiveLog2_le_iff x.exp y.exp x.expLower y.expLower x.exp_lower y.exp_lower).symm
    _ ↔ LE (mul x RationalLogSecant.limit) (mul y RationalLogSecant.limit) :=
      le_congr (expLog2_value x) (expLog2_value y)
    _ ↔ LE (mul RationalLogSecant.limit x) (mul RationalLogSecant.limit y) :=
      le_congr (mul_comm x RationalLogSecant.limit) (mul_comm y RationalLogSecant.limit)
    _ ↔ LE x y := mul_le_mul_positive_iff RationalLogSecant.limit PositiveRatio.one RationalLogSecant.one_le_limit x y

theorem exp_equiv_iff (x y : ConstructiveReal) : Equiv x.exp y.exp ↔ Equiv x y :=
  and_congr (exp_le_exp_iff x y) (exp_le_exp_iff y x)

end Thesis.Probability.ConstructiveReal
