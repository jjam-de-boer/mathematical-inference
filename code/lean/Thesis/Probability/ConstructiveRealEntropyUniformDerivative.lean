import Thesis.Probability.ConstructiveRealUniformLogarithm
import Thesis.Probability.ConstructiveRealEntropyVariation

namespace Thesis.Probability.ConstructiveReal

/-- The uniform entropy first-variation certificate is inhabited by the
implemented entropy. A single radius schedule applies to every point in the
supplied positive part of [0,1], including either endpoint of that domain. -/
def realEntropyTerm_uniformDerivative (lower : PositiveRatio) :
    UniformDerivativeWithin (entropyPositiveDomain lower)
      (fun x admitted => x.realEntropyTerm (entropyPositiveNonnegative lower x admitted) admitted.2)
      (fun x admitted => neg (add (x.positiveLog2 lower admitted.1) RationalLogSecant.limit)) where
  congr x y hx hy same := realEntropyTerm_congr same (entropyPositiveNonnegative lower x hx) (entropyPositiveNonnegative lower y hy) hx.2 hy.2
  modulus := entropyVariationModulus lower
  remainder epsilon radius small x hx y hy close := realEntropyTerm_uniform_first_variation x y lower hx hy epsilon radius small close

/-- Squaring has a global uniform quadratic remainder, even on domains
whose real sign or equality predicates are not decidable. -/
def square_uniformDerivative (domain : ConstructiveReal → Prop) :
    UniformDerivativeWithin domain (fun x _ => mul x x) (fun x _ => add x x) where
  congr _ _ _ _ same := mul_congr same same
  modulus epsilon := epsilon
  remainder _epsilon radius small x _ y _ close :=
    within_mono (square_first_variation x y radius close) (QProb.mul_le_mul small (QProb.le_refl _))

end Thesis.Probability.ConstructiveReal
