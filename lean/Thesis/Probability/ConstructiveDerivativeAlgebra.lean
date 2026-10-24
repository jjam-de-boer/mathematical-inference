import Thesis.Probability.ConstructiveDerivative
import Thesis.Probability.ConstructiveRealDifferenceLimits

namespace Thesis.Probability.ConstructiveReal.HasDerivativeAt
open ConstructiveReal

/-- Equivalent slopes preserve the same effective accuracy modulus. -/
def slope_congr {f : ConstructiveReal → ConstructiveReal} {point slope slope' : ConstructiveReal}
    (derivative : HasDerivativeAt f point slope) (same : Equiv slope slope') : HasDerivativeAt f point slope' where
  modulus := derivative.modulus
  remainder epsilon radius small y close :=
    (within_congr (equiv_refl _) (add_congr (equiv_refl _) (mul_congr (equiv_refl _) same))).mp
      (derivative.remainder epsilon radius small y close)

def function_congr {f g : ConstructiveReal → ConstructiveReal} {point slope : ConstructiveReal}
    (derivative : HasDerivativeAt f point slope) (same : ∀ x, Equiv (f x) (g x)) : HasDerivativeAt g point slope where
  modulus := derivative.modulus
  remainder epsilon radius small y close :=
    (within_congr (same y) (add_congr (same point) (equiv_refl _))).mp
      (derivative.remainder epsilon radius small y close)

/-- Constants have zero derivative, including the empty finite sum. -/
def constant (point value : ConstructiveReal) : HasDerivativeAt (fun _ => value) point zero where
  modulus _ := PositiveRatio.one
  remainder epsilon radius _ y _ := by
    have same : Equiv (add value (mul (sub y point) zero)) value :=
      equiv_trans (add_congr (equiv_refl _) (mul_zero _)) (add_zero _)
    exact (within_congr (equiv_refl _) (equiv_symm same)).mp (within_refl _ value)

/-- Identity has derivative one. The certificate also covers zero increments. -/
def identity (point : ConstructiveReal) : HasDerivativeAt (fun y => y) point one where
  modulus _ := PositiveRatio.one
  remainder epsilon radius _ y _ := by
    have same : Equiv (add point (mul (sub y point) one)) y :=
      equiv_trans (add_congr (equiv_refl _) (mul_one _))
        (equiv_trans (add_comm _ _) (equiv_trans (add_assoc _ _ _)
          (equiv_trans (add_congr (equiv_refl _) (equiv_trans (add_comm _ _) (add_neg point))) (add_zero _))))
    exact (within_congr (equiv_refl _) (equiv_symm same)).mp (within_refl _ y)

private def commonLower (a b : PositiveRatio) : PositiveRatio := if PositiveRatio.LE a b then a else b

private theorem commonLower_bounds (a b : PositiveRatio) :
    PositiveRatio.LE (commonLower a b) a ∧ PositiveRatio.LE (commonLower a b) b := by
  by_cases ordered : PositiveRatio.LE a b
  · simp only [commonLower, if_pos ordered]
    exact ⟨PositiveRatio.le_refl _, ordered⟩
  · simp only [commonLower, if_neg ordered]
    exact ⟨(PositiveRatio.le_total a b).resolve_left ordered, PositiveRatio.le_refl _⟩

/-- Finite addition has the sum derivative, with a jointly computed modulus. -/
def add {f g : ConstructiveReal → ConstructiveReal} {point sf sg : ConstructiveReal}
    (first : HasDerivativeAt f point sf) (second : HasDerivativeAt g point sg) :
    HasDerivativeAt (fun y => ConstructiveReal.add (f y) (g y)) point (ConstructiveReal.add sf sg) where
  modulus epsilon := commonLower (first.modulus epsilon.half) (second.modulus epsilon.half)
  remainder epsilon radius small y close := by
    have bounds := commonLower_bounds (first.modulus epsilon.half) (second.modulus epsilon.half)
    have compared := within_add
      (first.remainder epsilon.half radius (PositiveRatio.le_trans small bounds.1) y close)
      (second.remainder epsilon.half radius (PositiveRatio.le_trans small bounds.2) y close)
    have collected : QProb.Equiv
        (QProb.add (QProb.mul epsilon.half.toQProb radius.toQProb) (QProb.mul epsilon.half.toQProb radius.toQProb))
        (QProb.mul epsilon.toQProb radius.toQProb) :=
      QProb.equiv_trans (QProb.equiv_symm (QProb.add_mul_distrib _ _ _))
        (QProb.mul_congr epsilon.half_sum (QProb.equiv_refl _))
    have linear : Equiv
        (ConstructiveReal.add (ConstructiveReal.add (f point) (mul (sub y point) sf))
          (ConstructiveReal.add (g point) (mul (sub y point) sg)))
        (ConstructiveReal.add (ConstructiveReal.add (f point) (g point)) (mul (sub y point) (ConstructiveReal.add sf sg))) :=
      equiv_trans (add_four _ _ _ _) (add_congr (equiv_refl _) (equiv_symm (mul_add _ _ _)))
    exact (within_congr (equiv_refl _) linear).mp
      (within_mono compared (QProb.le_congr (QProb.equiv_refl _) collected (QProb.le_refl _)))

def neg {f : ConstructiveReal → ConstructiveReal} {point slope : ConstructiveReal}
    (derivative : HasDerivativeAt f point slope) : HasDerivativeAt (fun y => ConstructiveReal.neg (f y)) point (ConstructiveReal.neg slope) where
  modulus := derivative.modulus
  remainder epsilon radius small y close := by
    have compared := within_neg (derivative.remainder epsilon radius small y close)
    have linear : Equiv (ConstructiveReal.neg (ConstructiveReal.add (f point) (mul (sub y point) slope)))
        (ConstructiveReal.add (ConstructiveReal.neg (f point)) (mul (sub y point) (ConstructiveReal.neg slope))) :=
      equiv_trans (neg_add _ _) (add_congr (equiv_refl _) (equiv_symm (mul_neg _ _)))
    exact (within_congr (equiv_refl _) linear).mp compared

/-- Differentiation commutes with any supplied finite sum. Empty lists and
repeated indices use their actual sum semantics; no index is selected by choice. -/
def listSum (indices : List ι) (f : ι → ConstructiveReal → ConstructiveReal) (slopes : ι → ConstructiveReal) (point : ConstructiveReal)
    (derivatives : ∀ index, HasDerivativeAt (f index) point (slopes index)) :
    HasDerivativeAt (fun y => ConstructiveReal.listSum (indices.map (fun index => f index y))) point
      (ConstructiveReal.listSum (indices.map slopes)) :=
  match indices with
  | [] => constant point zero
  | index :: rest => (derivatives index).add (listSum rest f slopes point derivatives)

end Thesis.Probability.ConstructiveReal.HasDerivativeAt
