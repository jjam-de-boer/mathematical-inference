import Thesis.Probability.ConstructiveDerivativeWithinChain
import Thesis.Probability.ConstructiveDerivativeSquare
import Thesis.Probability.ConstructiveDerivativeProductIdentity

namespace Thesis.Probability.ConstructiveReal.HasDerivativeWithinAt
open ConstructiveReal

/-- The quantitative product rule on an explicit domain. Polarization reuses
the exact square remainder and the same checked polynomial identities as
the full-space rule. No off-domain function values are requested. -/
def mul {domain : ConstructiveReal → Prop} {f g : ∀ x, domain x → ConstructiveReal}
    {point sf sg : ConstructiveReal} {inside : domain point}
    (first : HasDerivativeWithinAt domain f point inside sf) (second : HasDerivativeWithinAt domain g point inside sg) :
    HasDerivativeWithinAt domain (fun y admitted => ConstructiveReal.mul (f y admitted) (g y admitted)) point inside
      (ConstructiveReal.add (ConstructiveReal.mul sf (g point inside)) (ConstructiveReal.mul (f point inside) sg)) := by
  let sumSquared := (first.add second).chain (square_hasDerivativeAt (ConstructiveReal.add (f point inside) (g point inside)))
  let diffSquared := (first.add second.neg).chain (square_hasDerivativeAt (ConstructiveReal.sub (f point inside) (g point inside)))
  let combined := (sumSquared.add diffSquared.neg).mul_constant (ofSignedRatio derivativeProductQuarter)
  exact (combined.function_congr (fun y admitted => derivative_product_value_identity (f y admitted) (g y admitted))).slope_congr
    (derivative_product_slope_identity (f point inside) (g point inside) sf sg)

end Thesis.Probability.ConstructiveReal.HasDerivativeWithinAt
