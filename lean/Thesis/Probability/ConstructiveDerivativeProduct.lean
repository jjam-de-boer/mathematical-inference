import Thesis.Probability.ConstructiveDerivativeWithinProduct
import Thesis.Probability.ConstructiveDerivativeChain

namespace Thesis.Probability.ConstructiveReal.HasDerivativeAt
open ConstructiveReal

/-- Effective product rule, using the shared domain-relative proof. All
constituent moduli are computed; variable factors need no separately assumed
neighborhood bounds. The original full-space statement is unchanged. -/
def mul {f g : ConstructiveReal → ConstructiveReal} {point sf sg : ConstructiveReal}
    (first : HasDerivativeAt f point sf) (second : HasDerivativeAt g point sg) :
    HasDerivativeAt (fun y => ConstructiveReal.mul (f y) (g y)) point
      (ConstructiveReal.add (ConstructiveReal.mul sf (g point)) (ConstructiveReal.mul (f point) sg)) :=
  ((first.restrict (fun _ => True) True.intro).mul (second.restrict (fun _ => True) True.intro)).unrestrict (fun _ => True.intro)

end Thesis.Probability.ConstructiveReal.HasDerivativeAt
