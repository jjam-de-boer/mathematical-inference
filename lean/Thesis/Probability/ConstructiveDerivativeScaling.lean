import Thesis.Probability.ConstructiveDerivativeAlgebra
import Thesis.Probability.ConstructiveDerivativeWithinScaling

namespace Thesis.Probability.ConstructiveReal.HasDerivativeAt
open ConstructiveReal

/-- Differentiation commutes with multiplication by any fixed analytic value.
A rational input modulus is computed from the fixed factor's enclosure bound. -/
def mul_constant {f : ConstructiveReal → ConstructiveReal} {point slope : ConstructiveReal}
    (derivative : HasDerivativeAt f point slope) (factor : ConstructiveReal) :
    HasDerivativeAt (fun y => mul (f y) factor) point (mul slope factor) :=
  ((derivative.restrict (fun _ => True) True.intro).mul_constant factor).unrestrict (fun _ => True.intro)

/-- Affine real maps have the expected derivative, including zero factors. -/
def affine (point factor offset : ConstructiveReal) :
    HasDerivativeAt (fun y => ConstructiveReal.add (mul y factor) offset) point factor :=
  (((identity point).mul_constant factor).add (constant point offset)).slope_congr
    (equiv_trans (add_congr (one_mul factor) (equiv_refl _)) (add_zero _))

/-- A fixed local Lipschitz constant computed from the derivative's slope. -/
def localLipschitzConstant {f : ConstructiveReal → ConstructiveReal} {point slope : ConstructiveReal}
    (_derivative : HasDerivativeAt f point slope) : Nat := slope.rationalApproximation.magnitudeBound + 1

theorem localLipschitzConstant_pos {f : ConstructiveReal → ConstructiveReal} {point slope : ConstructiveReal}
    (derivative : HasDerivativeAt f point slope) : 0 < derivative.localLipschitzConstant := Nat.zero_lt_succ _

/-- Differentiability supplies a local Lipschitz bound at the point, with an
explicit radius threshold. This provides the domain control for composition. -/
theorem local_within {f : ConstructiveReal → ConstructiveReal} {point slope : ConstructiveReal}
    (derivative : HasDerivativeAt f point slope) (radius : PositiveRatio)
    (small : PositiveRatio.LE radius (derivative.modulus PositiveRatio.one)) (y : ConstructiveReal)
    (close : Within radius.toQProb point y) :
    Within (QProb.mul radius.toQProb (QProb.ofNat derivative.localLipschitzConstant)) (f y) (f point) :=
  (derivative.restrict (fun _ => True) True.intro).local_within radius small y True.intro close

end Thesis.Probability.ConstructiveReal.HasDerivativeAt
