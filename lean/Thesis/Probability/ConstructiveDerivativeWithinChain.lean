import Thesis.Probability.ConstructiveDerivativeWithinAlgebra
import Thesis.Probability.ConstructiveDerivativeWithinScaling

namespace Thesis.Probability.ConstructiveReal.HasDerivativeWithinAt
open ConstructiveReal

private def commonLower (a b : PositiveRatio) : PositiveRatio := if PositiveRatio.LE a b then a else b
private theorem commonLower_bounds (a b : PositiveRatio) :
    PositiveRatio.LE (commonLower a b) a ∧ PositiveRatio.LE (commonLower a b) b := by
  by_cases ordered : PositiveRatio.LE a b
  · simp only [commonLower, if_pos ordered]
    exact ⟨PositiveRatio.le_refl _, ordered⟩
  · simp only [commonLower, if_neg ordered]
    exact ⟨(PositiveRatio.le_total a b).resolve_left ordered, PositiveRatio.le_refl _⟩

/-- Effective composition on an explicit source domain. Its supplied image
certificate guarantees that the outer function is defined; neither domain
needs decidable membership or a total extension. -/
def chainWithin {source target : ConstructiveReal → Prop} {f : ∀ x, source x → ConstructiveReal}
    {g : ∀ x, target x → ConstructiveReal} {point sf sg : ConstructiveReal}
    {inside : source point} {imageInside : target (f point inside)}
    (first : HasDerivativeWithinAt source f point inside sf)
    (second : HasDerivativeWithinAt target g (f point inside) imageInside sg)
    (admitted : ∀ y supplied, target (f y supplied)) :
    HasDerivativeWithinAt source (fun y supplied => g (f y supplied) (admitted y supplied)) point inside (mul sf sg) where
  modulus epsilon :=
    let l := first.localLipschitzConstant
    let m := sg.rationalApproximation.magnitudeBound
    let inner := epsilon.half.divideNat m (by unfold m RegularRationalApproximation.magnitudeBound; omega)
    let outer := epsilon.half.divideNat l first.localLipschitzConstant_pos
    commonLower (first.modulus PositiveRatio.one)
      (commonLower (first.modulus inner) ((second.modulus outer).divideNat l first.localLipschitzConstant_pos))
  remainder epsilon radius small y supplied close := by
    let l := first.localLipschitzConstant
    let m := sg.rationalApproximation.magnitudeBound
    have positiveM : 0 < m := by unfold m RegularRationalApproximation.magnitudeBound; omega
    let inner := epsilon.half.divideNat m positiveM
    let outer := epsilon.half.divideNat l first.localLipschitzConstant_pos
    let rho := PositiveRatio.mul radius (PositiveRatio.ofNat l first.localLipschitzConstant_pos)
    have outerBounds := commonLower_bounds (first.modulus PositiveRatio.one)
      (commonLower (first.modulus inner) ((second.modulus outer).divideNat l first.localLipschitzConstant_pos))
    have innerBounds := commonLower_bounds (first.modulus inner) ((second.modulus outer).divideNat l first.localLipschitzConstant_pos)
    have threshold := PositiveRatio.le_trans small outerBounds.2
    have inputChange := first.local_within radius (PositiveRatio.le_trans small outerBounds.1) y supplied close
    have imageSmall : PositiveRatio.LE rho (second.modulus outer) :=
      QProb.le_congr (QProb.equiv_refl _) (PositiveRatio.divide_mul (second.modulus outer) l first.localLipschitzConstant_pos)
        (QProb.mul_le_mul (PositiveRatio.le_trans threshold innerBounds.2) (QProb.le_refl (QProb.ofNat l)))
    have outerRemainder := second.remainder outer rho imageSmall (f y supplied) (admitted y supplied) (within_symm inputChange)
    have innerRemainder := first.remainder inner radius (PositiveRatio.le_trans threshold innerBounds.1) y supplied close
    have increment := (within_congr (equiv_refl _) (add_sub_cancel (f point inside) (mul (sub y point) sf))).mp
      ((within_sub_right_iff _ (f point inside) _ _).mpr innerRemainder)
    have scaled := within_mul_right increment sg
    have translated := (within_add_left_iff _ (g (f point inside) imageInside) _ _).mpr scaled
    have linear : Equiv
        (ConstructiveReal.add (g (f point inside) imageInside) (mul (mul (sub y point) sf) sg))
        (ConstructiveReal.add (g (f point inside) imageInside) (mul (sub y point) (mul sf sg))) :=
      add_congr (equiv_refl _) (mul_assoc _ _ _)
    have compared := within_triangle outerRemainder ((within_congr (equiv_refl _) linear).mp translated)
    have innerError : QProb.Equiv
        (QProb.mul (QProb.mul inner.toQProb radius.toQProb) (QProb.ofNat m))
        (QProb.mul epsilon.half.toQProb radius.toQProb) := by
      simp only [inner, PositiveRatio.divideNat, PositiveRatio.toQProb, QProb.Equiv, QProb.mul, QProb.ofNat, Nat.mul_one]
      ac_rfl
    have outerError : QProb.Equiv (QProb.mul outer.toQProb rho.toQProb)
        (QProb.mul epsilon.half.toQProb radius.toQProb) := by
      simp only [outer, rho, PositiveRatio.mul, PositiveRatio.ofNat, PositiveRatio.divideNat,
        PositiveRatio.toQProb, QProb.Equiv, QProb.mul, Nat.mul_one]
      ac_rfl
    have collected := QProb.equiv_trans (QProb.add_congr outerError innerError)
      (QProb.equiv_trans (QProb.equiv_symm (QProb.add_mul_distrib _ _ _))
        (QProb.mul_congr epsilon.half_sum (QProb.equiv_refl _)))
    exact within_mono compared (QProb.le_congr (QProb.equiv_refl _) collected (QProb.le_refl _))

/-- Composition with a total outer function keeps the original source domain. -/
def chain {source : ConstructiveReal → Prop} {f : ∀ x, source x → ConstructiveReal}
    {g : ConstructiveReal → ConstructiveReal} {point sf sg : ConstructiveReal} {inside : source point}
    (first : HasDerivativeWithinAt source f point inside sf) (second : HasDerivativeAt g (f point inside) sg) :
    HasDerivativeWithinAt source (fun y supplied => g (f y supplied)) point inside (mul sf sg) :=
  first.chainWithin (second.restrict (fun _ => True) True.intro) (fun _ _ => True.intro)

end Thesis.Probability.ConstructiveReal.HasDerivativeWithinAt
