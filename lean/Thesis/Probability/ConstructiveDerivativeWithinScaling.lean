import Thesis.Probability.ConstructiveDerivativeWithin
import Thesis.Probability.ConstructiveRealDistanceScaling

namespace Thesis.Probability.ConstructiveReal.HasDerivativeWithinAt
open ConstructiveReal

/-- Multiplication by a fixed analytic value preserves domain-relative
differentiation and computes its error modulus from a rational size bound. -/
def mul_constant {domain : ConstructiveReal → Prop} {f : ∀ x, domain x → ConstructiveReal}
    {point slope : ConstructiveReal} {inside : domain point}
    (derivative : HasDerivativeWithinAt domain f point inside slope) (factor : ConstructiveReal) :
    HasDerivativeWithinAt domain (fun y admitted => mul (f y admitted) factor) point inside (mul slope factor) where
  modulus epsilon := derivative.modulus (epsilon.divideNat factor.rationalApproximation.magnitudeBound
    (by unfold RegularRationalApproximation.magnitudeBound; omega))
  remainder epsilon radius small y admitted close := by
    have compared := within_mul_right (derivative.remainder _ radius small y admitted close) factor
    have collected : QProb.Equiv
        (QProb.mul (QProb.mul
          (epsilon.divideNat factor.rationalApproximation.magnitudeBound (by unfold RegularRationalApproximation.magnitudeBound; omega)).toQProb radius.toQProb)
          (QProb.ofNat factor.rationalApproximation.magnitudeBound))
        (QProb.mul epsilon.toQProb radius.toQProb) := by
      simp only [QProb.Equiv, QProb.mul, QProb.ofNat, PositiveRatio.toQProb, PositiveRatio.divideNat, Nat.mul_one]
      ac_rfl
    have linear : Equiv (mul (add (f point inside) (mul (sub y point) slope)) factor)
        (add (mul (f point inside) factor) (mul (sub y point) (mul slope factor))) :=
      equiv_trans (add_mul _ _ _) (add_congr (equiv_refl _) (mul_assoc _ _ _))
    exact (within_congr (equiv_refl _) linear).mp
      (within_mono compared (QProb.le_congr (QProb.equiv_refl _) collected (QProb.le_refl _)))

/-- A fixed local Lipschitz constant computed from the derivative's slope. -/
def localLipschitzConstant {domain : ConstructiveReal → Prop} {f : ∀ x, domain x → ConstructiveReal} {point slope : ConstructiveReal} {inside : domain point}
    (_derivative : HasDerivativeWithinAt domain f point inside slope) : Nat := slope.rationalApproximation.magnitudeBound + 1

theorem localLipschitzConstant_pos {domain : ConstructiveReal → Prop} {f : ∀ x, domain x → ConstructiveReal} {point slope : ConstructiveReal} {inside : domain point}
    (derivative : HasDerivativeWithinAt domain f point inside slope) : 0 < derivative.localLipschitzConstant := Nat.zero_lt_succ _

/-- Differentiability supplies a local Lipschitz bound at the point, with an
explicit radius threshold. This provides the domain control for composition. -/
theorem local_within {domain : ConstructiveReal → Prop} {f : ∀ x, domain x → ConstructiveReal} {point slope : ConstructiveReal} {inside : domain point}
    (derivative : HasDerivativeWithinAt domain f point inside slope) (radius : PositiveRatio)
    (small : PositiveRatio.LE radius (derivative.modulus PositiveRatio.one)) (y : ConstructiveReal) (admitted : domain y)
    (close : Within radius.toQProb point y) :
    Within (QProb.mul radius.toQProb (QProb.ofNat derivative.localLipschitzConstant)) (f y admitted) (f point inside) := by
  have product := (within_congr (equiv_refl _) (zero_mul slope)).mp (within_mul_right (within_increment close) slope)
  have translated := (within_congr (equiv_refl _) (add_zero (f point inside))).mp
    ((within_add_left_iff _ (f point inside) _ _).mpr product)
  have compared := within_triangle (derivative.remainder PositiveRatio.one radius small y admitted close) translated
  have collected : QProb.Equiv
      (QProb.add (QProb.mul PositiveRatio.one.toQProb radius.toQProb)
        (QProb.mul radius.toQProb (QProb.ofNat slope.rationalApproximation.magnitudeBound)))
      (QProb.mul radius.toQProb (QProb.ofNat derivative.localLipschitzConstant)) := by
    simp only [QProb.Equiv, QProb.mul, QProb.add, QProb.ofNat, PositiveRatio.one, PositiveRatio.toQProb,
      localLipschitzConstant, Nat.mul_one, Nat.one_mul, Nat.mul_add, Nat.add_mul]
    ac_rfl
  exact within_mono compared (QProb.le_congr (QProb.equiv_refl _) collected (QProb.le_refl _))

end Thesis.Probability.ConstructiveReal.HasDerivativeWithinAt
