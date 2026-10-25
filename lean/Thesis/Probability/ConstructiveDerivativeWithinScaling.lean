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

end Thesis.Probability.ConstructiveReal.HasDerivativeWithinAt
