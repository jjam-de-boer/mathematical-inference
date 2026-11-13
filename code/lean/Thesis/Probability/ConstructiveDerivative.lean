import Thesis.Probability.ConstructiveRealRing
import Thesis.Probability.RationalPrecision

namespace Thesis.Probability.ConstructiveReal

/-- Effective real differentiability in a residual form: on every supplied
rational radius `r` below the computed modulus, the error in the linear
approximation is at most `epsilon * r`. Quantification is over all real nearby
inputs and all positive rational radii bounding their distance. This avoids
both division by a possibly zero increment and any real sign/equality decision.
The modulus is data, rather than an existential index selected by choice. -/
structure HasDerivativeAt (function : ConstructiveReal → ConstructiveReal) (point slope : ConstructiveReal) where
  modulus : PositiveRatio → PositiveRatio
  remainder : ∀ epsilon radius : PositiveRatio, PositiveRatio.LE radius (modulus epsilon) →
    ∀ nearby : ConstructiveReal, Within radius.toQProb point nearby →
      Within (QProb.mul epsilon.toQProb radius.toQProb) (function nearby)
        (add (function point) (mul (sub nearby point) slope))

end Thesis.Probability.ConstructiveReal
