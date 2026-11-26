import Thesis.Probability.ConstructiveDerivativeWithinProduct
import Thesis.Probability.ConstructiveDerivativeChain

/-!
# Full-space Leibniz rule from the shared domain-relative construction

Two effective derivative certificates yield the product slope
`sf * g(point) + f(point) * sg`. The wrapper restricts both functions to
the always-admitted domain, applies the proved partial-domain product
rule, and removes that trivial restriction.

All accuracy schedules are constructed from the input certificates and
the actual basepoint data. Variable factors need no separately supplied
neighborhood bound or sign assumption, and the residual formulation also
covers zero increments.
-/

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
