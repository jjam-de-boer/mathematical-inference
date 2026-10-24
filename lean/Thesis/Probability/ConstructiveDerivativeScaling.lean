import Thesis.Probability.ConstructiveDerivativeAlgebra
import Thesis.Probability.ConstructiveRealDistanceScaling

namespace Thesis.Probability.ConstructiveReal.HasDerivativeAt
open ConstructiveReal

/-- Differentiation commutes with multiplication by any fixed analytic value.
A rational input modulus is computed from the fixed factor's enclosure bound. -/
def mul_constant {f : ConstructiveReal → ConstructiveReal} {point slope : ConstructiveReal}
    (derivative : HasDerivativeAt f point slope) (factor : ConstructiveReal) :
    HasDerivativeAt (fun y => mul (f y) factor) point (mul slope factor) where
  modulus epsilon := derivative.modulus (epsilon.divideNat factor.rationalApproximation.magnitudeBound
    (by unfold RegularRationalApproximation.magnitudeBound; omega))
  remainder epsilon radius small y close := by
    have compared := within_mul_right (derivative.remainder _ radius small y close) factor
    have collected : QProb.Equiv
        (QProb.mul (QProb.mul
          (epsilon.divideNat factor.rationalApproximation.magnitudeBound (by unfold RegularRationalApproximation.magnitudeBound; omega)).toQProb radius.toQProb)
          (QProb.ofNat factor.rationalApproximation.magnitudeBound))
        (QProb.mul epsilon.toQProb radius.toQProb) := by
      simp only [QProb.Equiv, QProb.mul, QProb.ofNat, PositiveRatio.toQProb, PositiveRatio.divideNat, Nat.mul_one]
      ac_rfl
    have linear : Equiv (mul (ConstructiveReal.add (f point) (mul (sub y point) slope)) factor)
        (ConstructiveReal.add (mul (f point) factor) (mul (sub y point) (mul slope factor))) :=
      equiv_trans (add_mul _ _ _) (add_congr (equiv_refl _) (mul_assoc _ _ _))
    exact (within_congr (equiv_refl _) linear).mp
      (within_mono compared (QProb.le_congr (QProb.equiv_refl _) collected (QProb.le_refl _)))

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
    Within (QProb.mul radius.toQProb (QProb.ofNat derivative.localLipschitzConstant)) (f y) (f point) := by
  have product := (within_congr (equiv_refl _) (zero_mul slope)).mp (within_mul_right (within_increment close) slope)
  have translated := (within_congr (equiv_refl _) (add_zero (f point))).mp
    ((within_add_left_iff _ (f point) _ _).mpr product)
  have compared := within_triangle (derivative.remainder PositiveRatio.one radius small y close) translated
  have collected : QProb.Equiv
      (QProb.add (QProb.mul PositiveRatio.one.toQProb radius.toQProb)
        (QProb.mul radius.toQProb (QProb.ofNat slope.rationalApproximation.magnitudeBound)))
      (QProb.mul radius.toQProb (QProb.ofNat derivative.localLipschitzConstant)) := by
    simp only [QProb.Equiv, QProb.mul, QProb.add, QProb.ofNat, PositiveRatio.one, PositiveRatio.toQProb,
      localLipschitzConstant, Nat.mul_one, Nat.one_mul, Nat.mul_add, Nat.add_mul]
    ac_rfl
  exact within_mono compared (QProb.le_congr (QProb.equiv_refl _) collected (QProb.le_refl _))

end Thesis.Probability.ConstructiveReal.HasDerivativeAt
