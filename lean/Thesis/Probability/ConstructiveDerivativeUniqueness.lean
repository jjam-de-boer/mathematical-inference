import Thesis.Probability.ConstructiveDerivativeAlgebra
import Thesis.Probability.ConstructiveRealDistanceAlgebra

namespace Thesis.Probability.ConstructiveReal.HasDerivativeAt
open ConstructiveReal

/-- Derivatives are unique up to real value equivalence. The proof samples a
computed positive rational step shared by the two moduli, so the derivative
specification cannot certify arbitrary incompatible slopes. -/
theorem unique {f : ConstructiveReal → ConstructiveReal} {point sf sg : ConstructiveReal}
    (first : HasDerivativeAt f point sf) (second : HasDerivativeAt f point sg) : Equiv sf sg := by
  apply equiv_of_within_all
  intro epsilon
  let a := first.modulus epsilon.half
  let b := second.modulus epsilon.half
  let radius := if PositiveRatio.LE a b then a else b
  have bounds : PositiveRatio.LE radius a ∧ PositiveRatio.LE radius b := by
    by_cases ordered : PositiveRatio.LE a b
    · simp only [radius, if_pos ordered]
      exact ⟨PositiveRatio.le_refl _, ordered⟩
    · simp only [radius, if_neg ordered]
      exact ⟨(PositiveRatio.le_total a b).resolve_left ordered, PositiveRatio.le_refl _⟩
  let nearby := ConstructiveReal.add point (ofSignedRatio radius.toSignedRatio)
  have close := within_positive_shift point radius
  have compared := within_triangle (within_symm (first.remainder epsilon.half radius bounds.1 nearby close))
    (second.remainder epsilon.half radius bounds.2 nearby close)
  have collected : QProb.Equiv
      (QProb.add (QProb.mul epsilon.half.toQProb radius.toQProb) (QProb.mul epsilon.half.toQProb radius.toQProb))
      (QProb.mul radius.toQProb epsilon.toQProb) :=
    QProb.equiv_trans (QProb.equiv_symm (QProb.add_mul_distrib _ _ _))
      (QProb.equiv_trans (QProb.mul_congr epsilon.half_sum (QProb.equiv_refl _)) (QProb.mul_comm _ _))
  have linear (slope : ConstructiveReal) : Equiv
      (ConstructiveReal.add (f point) (mul (sub nearby point) slope))
      (ConstructiveReal.add (f point) (mul (ofSignedRatio radius.toSignedRatio) slope)) :=
    add_congr (equiv_refl _) (mul_congr (positive_shift_increment point radius) (equiv_refl _))
  have translated := (within_add_left_iff _ (f point) _ _).mp
    ((within_congr (linear sf) (linear sg)).mp
      (within_mono compared (QProb.le_congr (QProb.equiv_refl _) collected (QProb.le_refl _))))
  exact (within_mul_positive_iff radius epsilon.toQProb sf sg).mp translated

/-- Changing a point's real presentation preserves differentiability when
the function values at the two presentations agree. The effective modulus
and slope are retained. -/
def point_congr {f : ConstructiveReal → ConstructiveReal} {point point' slope : ConstructiveReal}
    (derivative : HasDerivativeAt f point slope) (samePoint : Equiv point point') (sameValue : Equiv (f point) (f point')) :
    HasDerivativeAt f point' slope where
  modulus := derivative.modulus
  remainder epsilon radius small y close :=
    (within_congr (equiv_refl _) (add_congr sameValue
      (mul_congr (add_congr (equiv_refl _) (neg_congr samePoint)) (equiv_refl _)))).mp
        (derivative.remainder epsilon radius small y ((within_congr samePoint (equiv_refl _)).mpr close))

end Thesis.Probability.ConstructiveReal.HasDerivativeAt
