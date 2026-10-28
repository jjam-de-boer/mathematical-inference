import Thesis.Probability.ConstructiveDerivativeLocalDomain
import Thesis.Probability.ConstructiveRealNaturalLog
import Thesis.Probability.ConstructiveRealInverseDerivative

namespace Thesis.Probability.ConstructiveReal.HasDerivativeAt
open ConstructiveReal

/-- Differentiate a globally positive analytic function using its computed
point-dependent lower certificates. A fixed local half-floor supplies the
chain-rule domain; congruence then restores the actual total function.
No positivity comparison is decided and no uniform global floor is assumed. -/
def positiveLn {f : ConstructiveReal → ConstructiveReal} {point slope : ConstructiveReal}
    (derivative : HasDerivativeAt f point slope)
    (lower : ConstructiveReal → PositiveRatio)
    (positive : ∀ y, LE (ofSignedRatio (lower y).toSignedRatio) (f y)) :
    HasDerivativeAt (fun y => (f y).positiveLn (lower y) (positive y)) point
      (mul slope ((f point).positiveInverse (lower point) (positive point))) := by
  let fixed := (lower point).half
  have inside : LE (ofSignedRatio fixed.toSignedRatio) (f point) :=
    positive_half_lower _ _ (lower point) (positive point) (within_refl _ _)
  let chained := derivative.chainWithin (positiveLn_hasDerivativeWithinAt (f point) fixed inside)
  have admitted := derivative.positive_near (lower point) (positive point)
  let total := chained.toLocalTotal (fun y => (f y).positiveLn (lower y) (positive y))
    (derivative.positiveRadius (lower point)) admitted
    (positiveLn_congr (equiv_refl _) fixed (lower point) inside (positive point))
    (fun y close => positiveLn_congr (equiv_refl _) fixed (lower y) (admitted y close) (positive y))
  exact total.slope_congr (mul_congr (equiv_refl _)
    (positiveInverse_congr (equiv_refl _) fixed (lower point) inside (positive point)))

/-- The corresponding reciprocal rule retains the same effective local
positivity control and computes the negative inverse-square slope. -/
def positiveInverse {f : ConstructiveReal → ConstructiveReal} {point slope : ConstructiveReal}
    (derivative : HasDerivativeAt f point slope)
    (lower : ConstructiveReal → PositiveRatio)
    (positive : ∀ y, LE (ofSignedRatio (lower y).toSignedRatio) (f y)) :
    HasDerivativeAt (fun y => (f y).positiveInverse (lower y) (positive y)) point
      (mul slope (ConstructiveReal.neg (mul ((f point).positiveInverse (lower point) (positive point))
        ((f point).positiveInverse (lower point) (positive point))))) := by
  let fixed := (lower point).half
  have inside : LE (ofSignedRatio fixed.toSignedRatio) (f point) :=
    positive_half_lower _ _ (lower point) (positive point) (within_refl _ _)
  let chained := derivative.chainWithin (positiveInverse_hasDerivativeWithinAt (f point) fixed inside)
  have admitted := derivative.positive_near (lower point) (positive point)
  let total := chained.toLocalTotal (fun y => (f y).positiveInverse (lower y) (positive y))
    (derivative.positiveRadius (lower point)) admitted
    (positiveInverse_congr (equiv_refl _) fixed (lower point) inside (positive point))
    (fun y close => positiveInverse_congr (equiv_refl _) fixed (lower y) (admitted y close) (positive y))
  have same := positiveInverse_congr (equiv_refl (f point)) fixed (lower point) inside (positive point)
  exact total.slope_congr (mul_congr (equiv_refl _) (neg_congr (mul_congr same same)))

end Thesis.Probability.ConstructiveReal.HasDerivativeAt
