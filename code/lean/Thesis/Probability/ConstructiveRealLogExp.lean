import Thesis.Probability.ConstructiveRealExpPositive
import Thesis.Probability.ConstructiveRealLogReciprocal
import Thesis.Probability.ConstructiveRealAdditiveMap

namespace Thesis.Probability.ConstructiveReal

/-- The base-two logarithm of the Taylor exponential is defined at every
real input using the proved, computed positive lower bound of exp(x). -/
def expLog2 (x : ConstructiveReal) : ConstructiveReal := x.exp.positiveLog2 x.expLower x.exp_lower

theorem expLog2_congr {x y : ConstructiveReal} (same : Equiv x y) : Equiv x.expLog2 y.expLog2 :=
  positiveLog2_congr (exp_congr same) x.expLower y.expLower x.exp_lower y.exp_lower

theorem expLog2_add (x y : ConstructiveReal) : Equiv (add x y).expLog2 (add x.expLog2 y.expLog2) :=
  equiv_trans (positiveLog2_congr (exp_add x y) (add x y).expLower (x.expLower.mul y.expLower)
    (add x y).exp_lower (mul_positive_lower x.exp y.exp x.expLower y.expLower x.exp_lower y.exp_lower))
    (positiveLog2_mul x.exp y.exp x.expLower y.expLower x.exp_lower y.exp_lower)

def expLog2Additive : AdditiveMap where
  value := expLog2
  map_equiv := expLog2_congr
  map_add := expLog2_add

theorem expLog2_zero : Equiv zero.expLog2 zero := expLog2Additive.map_zero

theorem expLog2_neg (x : ConstructiveReal) : Equiv (neg x).expLog2 (neg x.expLog2) := expLog2Additive.map_neg x

/-- The log-exponential composite is linear on every signed rational. Its
unit coefficient is still identified with the derived logarithm slope later. -/
theorem expLog2_ofSignedRatio (q : SignedRatio) :
    Equiv (ofSignedRatio q).expLog2 (mul (ofSignedRatio q) one.expLog2) := expLog2Additive.map_rational q

end Thesis.Probability.ConstructiveReal
