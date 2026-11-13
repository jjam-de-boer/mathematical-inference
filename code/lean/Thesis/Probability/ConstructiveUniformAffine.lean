import Thesis.Probability.ConstructiveUniformDerivative

namespace Thesis.Probability.ConstructiveReal.UniformDerivativeWithin
open ConstructiveReal

def function_congr {domain : ConstructiveReal → Prop} {first second slope : ∀ x, domain x → ConstructiveReal}
    (derivative : UniformDerivativeWithin domain first slope)
    (same : ∀ x hx, Equiv (first x hx) (second x hx)) : UniformDerivativeWithin domain second slope where
  congr x y hx hy equivalent := equiv_trans (equiv_symm (same x hx))
    (equiv_trans (derivative.congr x y hx hy equivalent) (same y hy))
  modulus := derivative.modulus
  remainder epsilon radius small x hx y hy close :=
    (within_congr (same y hy) (add_congr (same x hx) (equiv_refl _))).mp
      (derivative.remainder epsilon radius small x hx y hy close)

def constant (domain : ConstructiveReal → Prop) (value : ConstructiveReal) :
    UniformDerivativeWithin domain (fun _ _ => value) (fun _ _ => zero) where
  congr _ _ _ _ _ := equiv_refl value
  modulus _ := PositiveRatio.one
  remainder epsilon radius small x hx y hy close :=
    (HasDerivativeWithinAt.constant x hx value).remainder epsilon radius small y hy close

/-- Finite uniform certificates combine with an explicitly computed joint
modulus. Slopes may vary over the domain; no compactness principle is used. -/
def listSum {domain : ConstructiveReal → Prop} (indices : List ι)
    (functions slopes : ι → ∀ x, domain x → ConstructiveReal)
    (derivatives : ∀ i, UniformDerivativeWithin domain (functions i) (slopes i)) :
    UniformDerivativeWithin domain
      (fun x hx => ConstructiveReal.listSum (indices.map (fun i => functions i x hx)))
      (fun x hx => ConstructiveReal.listSum (indices.map (fun i => slopes i x hx))) :=
  match indices with
  | [] => constant domain zero
  | i :: rest => (derivatives i).add (listSum rest functions slopes derivatives)

private theorem affine_increment (factor offset x y : ConstructiveReal) :
    Equiv (sub (ConstructiveReal.add (mul y factor) offset) (ConstructiveReal.add (mul x factor) offset))
      (mul (sub y x) factor) :=
  equiv_trans (add_congr (equiv_refl _) (neg_add _ _))
    (equiv_trans (add_four _ _ _ _) (equiv_trans (add_congr (equiv_refl _) (add_neg offset))
      (equiv_trans (add_zero _) (equiv_symm (sub_mul y x factor)))))

/-- Affine pullback of a uniform derivative. The affine increment is exact,
so a global rational magnitude bound on its fixed factor suffices even when
the outer slope is unbounded. The domain is supplied explicitly and may
include endpoints. Negative and zero affine factors are allowed. -/
def affine_pullback {source target : ConstructiveReal → Prop}
    {function slope : ∀ x, target x → ConstructiveReal}
    (derivative : UniformDerivativeWithin target function slope)
    (factor offset : ConstructiveReal)
    (admitted : ∀ x, source x → target (ConstructiveReal.add (mul x factor) offset)) :
    UniformDerivativeWithin source
      (fun x hx => function (ConstructiveReal.add (mul x factor) offset) (admitted x hx))
      (fun x hx => mul factor (slope (ConstructiveReal.add (mul x factor) offset) (admitted x hx))) where
  congr x y hx hy same := derivative.congr _ _ (admitted x hx) (admitted y hy)
    (add_congr (mul_congr same (equiv_refl _)) (equiv_refl _))
  modulus epsilon :=
    let count := factor.rationalApproximation.magnitudeBound
    have positive : 0 < count := by unfold count RegularRationalApproximation.magnitudeBound; omega
    (derivative.modulus (epsilon.divideNat count positive)).divideNat count positive
  remainder epsilon radius small x hx y hy close := by
    let count := factor.rationalApproximation.magnitudeBound
    have positive : 0 < count := by unfold count RegularRationalApproximation.magnitudeBound; omega
    let precision := epsilon.divideNat count positive
    let imageRadius := PositiveRatio.mul radius (PositiveRatio.ofNat count positive)
    have imageSmall : PositiveRatio.LE imageRadius (derivative.modulus precision) :=
      QProb.le_congr (QProb.equiv_refl _) (PositiveRatio.divide_mul (derivative.modulus precision) count positive)
        (QProb.mul_le_mul small (QProb.le_refl (QProb.ofNat count)))
    have changed := within_mul_right close factor
    have translated := (within_add_left_iff _ offset _ _).mpr changed
    have imageClose : Within imageRadius.toQProb (ConstructiveReal.add (mul x factor) offset)
        (ConstructiveReal.add (mul y factor) offset) :=
      (within_congr (add_comm _ _) (add_comm _ _)).mp translated
    have estimate := derivative.remainder precision imageRadius imageSmall _ (admitted x hx) _ (admitted y hy) imageClose
    have collected : QProb.Equiv (QProb.mul precision.toQProb imageRadius.toQProb)
        (QProb.mul epsilon.toQProb radius.toQProb) := by
      simp only [precision, imageRadius, PositiveRatio.mul, PositiveRatio.ofNat, PositiveRatio.divideNat,
        PositiveRatio.toQProb, QProb.Equiv, QProb.mul, Nat.mul_one]
      ac_rfl
    have linear := mul_congr (affine_increment factor offset x y)
      (equiv_refl (slope (ConstructiveReal.add (mul x factor) offset) (admitted x hx)))
    exact (within_congr (equiv_refl _) (add_congr (equiv_refl _)
      (equiv_trans linear (mul_assoc _ _ _)))).mp
      (within_mono estimate (QProb.le_congr (QProb.equiv_refl _) collected (QProb.le_refl _)))

end Thesis.Probability.ConstructiveReal.UniformDerivativeWithin
