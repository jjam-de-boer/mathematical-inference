import Thesis.Probability.ConstructiveRealRing
import Thesis.Probability.RationalPrecision

/-!
# Differentiability as computable linear-remainder control

`HasDerivativeAt` stores a rational accuracy modulus and proves a residual
bound for every positive rational radius below it. The bound applies to
all real inputs within that radius, including a zero increment, and scales
the error by `epsilon * radius`. No quotient by the actual increment is
formed and no equality or sign of arbitrary reals is decided.

The modulus is supplied computational data. Later algebra and composition
rules transform this data, so a derivative certificate carries an effective
approximation guarantee rather than only an existential limit statement.
-/

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
