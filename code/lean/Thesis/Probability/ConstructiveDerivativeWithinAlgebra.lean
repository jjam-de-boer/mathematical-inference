import Thesis.Probability.ConstructiveDerivativeWithin
import Thesis.Probability.ConstructiveRealDifferenceLimits

namespace Thesis.Probability.ConstructiveReal.HasDerivativeWithinAt
open ConstructiveReal

/-- Restrict an analytic certificate using a supplied domain inclusion,
without deciding membership or defining the function outside its domain. -/
def restrict {domain : ConstructiveReal → Prop} {f : ∀ x, domain x → ConstructiveReal}
    {point slope : ConstructiveReal} {inside : domain point}
    (derivative : HasDerivativeWithinAt domain f point inside slope)
    (smaller : ConstructiveReal → Prop) (admittedPoint : smaller point) (included : ∀ x, smaller x → domain x) :
    HasDerivativeWithinAt smaller (fun x admitted => f x (included x admitted)) point admittedPoint slope where
  modulus := derivative.modulus
  remainder epsilon radius small y admitted close := derivative.remainder epsilon radius small y (included y admitted) close

def function_congr {domain : ConstructiveReal → Prop} {f g : ∀ x, domain x → ConstructiveReal}
    {point slope : ConstructiveReal} {inside : domain point}
    (derivative : HasDerivativeWithinAt domain f point inside slope) (same : ∀ x admitted, Equiv (f x admitted) (g x admitted)) :
    HasDerivativeWithinAt domain g point inside slope where
  modulus := derivative.modulus
  remainder epsilon radius small y admitted close :=
    (within_congr (same y admitted) (add_congr (same point inside) (equiv_refl _))).mp
      (derivative.remainder epsilon radius small y admitted close)

/-- Constants have zero derivative on every explicitly supplied domain. -/
def constant {domain : ConstructiveReal → Prop} (point : ConstructiveReal) (inside : domain point) (value : ConstructiveReal) :
    HasDerivativeWithinAt domain (fun _ _ => value) point inside zero where
  modulus _ := PositiveRatio.one
  remainder epsilon radius _ y _ _ := by
    have same : Equiv (ConstructiveReal.add value (mul (sub y point) zero)) value :=
      equiv_trans (add_congr (equiv_refl _) (mul_zero _)) (add_zero _)
    exact (within_congr (equiv_refl _) (equiv_symm same)).mp (within_refl _ value)

private def commonLower (a b : PositiveRatio) : PositiveRatio := if PositiveRatio.LE a b then a else b
private theorem commonLower_bounds (a b : PositiveRatio) :
    PositiveRatio.LE (commonLower a b) a ∧ PositiveRatio.LE (commonLower a b) b := by
  by_cases ordered : PositiveRatio.LE a b
  · simp only [commonLower, if_pos ordered]
    exact ⟨PositiveRatio.le_refl _, ordered⟩
  · simp only [commonLower, if_neg ordered]
    exact ⟨(PositiveRatio.le_total a b).resolve_left ordered, PositiveRatio.le_refl _⟩

/-- Addition computes a common modulus on the original explicit domain. -/
def add {domain : ConstructiveReal → Prop} {f g : ∀ x, domain x → ConstructiveReal}
    {point sf sg : ConstructiveReal} {inside : domain point}
    (first : HasDerivativeWithinAt domain f point inside sf) (second : HasDerivativeWithinAt domain g point inside sg) :
    HasDerivativeWithinAt domain (fun y admitted => ConstructiveReal.add (f y admitted) (g y admitted)) point inside (ConstructiveReal.add sf sg) where
  modulus epsilon := commonLower (first.modulus epsilon.half) (second.modulus epsilon.half)
  remainder epsilon radius small y admitted close := by
    have bounds := commonLower_bounds (first.modulus epsilon.half) (second.modulus epsilon.half)
    have compared := within_add
      (first.remainder epsilon.half radius (PositiveRatio.le_trans small bounds.1) y admitted close)
      (second.remainder epsilon.half radius (PositiveRatio.le_trans small bounds.2) y admitted close)
    have collected : QProb.Equiv
        (QProb.add (QProb.mul epsilon.half.toQProb radius.toQProb) (QProb.mul epsilon.half.toQProb radius.toQProb))
        (QProb.mul epsilon.toQProb radius.toQProb) :=
      QProb.equiv_trans (QProb.equiv_symm (QProb.add_mul_distrib _ _ _))
        (QProb.mul_congr epsilon.half_sum (QProb.equiv_refl _))
    have linear : Equiv
        (ConstructiveReal.add (ConstructiveReal.add (f point inside) (mul (sub y point) sf))
          (ConstructiveReal.add (g point inside) (mul (sub y point) sg)))
        (ConstructiveReal.add (ConstructiveReal.add (f point inside) (g point inside)) (mul (sub y point) (ConstructiveReal.add sf sg))) :=
      equiv_trans (add_four _ _ _ _) (add_congr (equiv_refl _) (equiv_symm (mul_add _ _ _)))
    exact (within_congr (equiv_refl _) linear).mp
      (within_mono compared (QProb.le_congr (QProb.equiv_refl _) collected (QProb.le_refl _)))

def neg {domain : ConstructiveReal → Prop} {f : ∀ x, domain x → ConstructiveReal}
    {point slope : ConstructiveReal} {inside : domain point}
    (derivative : HasDerivativeWithinAt domain f point inside slope) :
    HasDerivativeWithinAt domain (fun y admitted => ConstructiveReal.neg (f y admitted)) point inside (ConstructiveReal.neg slope) where
  modulus := derivative.modulus
  remainder epsilon radius small y admitted close := by
    have compared := within_neg (derivative.remainder epsilon radius small y admitted close)
    have linear : Equiv (ConstructiveReal.neg (ConstructiveReal.add (f point inside) (mul (sub y point) slope)))
        (ConstructiveReal.add (ConstructiveReal.neg (f point inside)) (mul (sub y point) (ConstructiveReal.neg slope))) :=
      equiv_trans (neg_add _ _) (add_congr (equiv_refl _) (equiv_symm (mul_neg _ _)))
    exact (within_congr (equiv_refl _) linear).mp compared

/-- Finite sums retain the same explicit domain, with computed joint error
control. Empty lists and repeated indices use their actual sum semantics. -/
def listSum {domain : ConstructiveReal → Prop} (indices : List ι)
    (f : ι → ∀ x, domain x → ConstructiveReal) (slopes : ι → ConstructiveReal)
    (point : ConstructiveReal) (inside : domain point)
    (derivatives : ∀ index, HasDerivativeWithinAt domain (f index) point inside (slopes index)) :
    HasDerivativeWithinAt domain (fun y admitted => ConstructiveReal.listSum (indices.map (fun index => f index y admitted)))
      point inside (ConstructiveReal.listSum (indices.map slopes)) :=
  match indices with
  | [] => constant point inside zero
  | index :: rest => (derivatives index).add (listSum rest f slopes point inside derivatives)

end Thesis.Probability.ConstructiveReal.HasDerivativeWithinAt
