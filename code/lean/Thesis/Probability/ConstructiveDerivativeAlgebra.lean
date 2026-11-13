import Thesis.Probability.ConstructiveDerivativeWithinAlgebra

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
    (derivative : HasDerivativeAt f point slope) (same : ∀ x, Equiv (f x) (g x)) : HasDerivativeAt g point slope :=
  ((derivative.restrict (fun _ => True) True.intro).function_congr (fun x _ => same x)).unrestrict (fun _ => True.intro)

/-- Constants have zero derivative, including the empty finite sum. -/
def constant (point value : ConstructiveReal) : HasDerivativeAt (fun _ => value) point zero :=
  (HasDerivativeWithinAt.constant (domain := fun _ => True) point True.intro value).unrestrict (fun _ => True.intro)

/-- Identity has derivative one. The certificate also covers zero increments. -/
def identity (point : ConstructiveReal) : HasDerivativeAt (fun y => y) point one where
  modulus _ := PositiveRatio.one
  remainder epsilon radius _ y _ := by
    have same : Equiv (add point (mul (sub y point) one)) y :=
      equiv_trans (add_congr (equiv_refl _) (mul_one _))
        (equiv_trans (add_comm _ _) (equiv_trans (add_assoc _ _ _)
          (equiv_trans (add_congr (equiv_refl _) (equiv_trans (add_comm _ _) (add_neg point))) (add_zero _))))
    exact (within_congr (equiv_refl _) (equiv_symm same)).mp (within_refl _ y)

/-- Finite addition uses the same computed domain-relative rule. -/
def add {f g : ConstructiveReal → ConstructiveReal} {point sf sg : ConstructiveReal}
    (first : HasDerivativeAt f point sf) (second : HasDerivativeAt g point sg) :
    HasDerivativeAt (fun y => ConstructiveReal.add (f y) (g y)) point (ConstructiveReal.add sf sg) :=
  ((first.restrict (fun _ => True) True.intro).add (second.restrict (fun _ => True) True.intro)).unrestrict (fun _ => True.intro)

def neg {f : ConstructiveReal → ConstructiveReal} {point slope : ConstructiveReal}
    (derivative : HasDerivativeAt f point slope) : HasDerivativeAt (fun y => ConstructiveReal.neg (f y)) point (ConstructiveReal.neg slope) :=
  (derivative.restrict (fun _ => True) True.intro).neg.unrestrict (fun _ => True.intro)

/-- Differentiation commutes with any supplied finite sum. Empty lists and
repeated indices use their actual sum semantics; no index is selected by choice. -/
def listSum (indices : List ι) (f : ι → ConstructiveReal → ConstructiveReal) (slopes : ι → ConstructiveReal) (point : ConstructiveReal)
    (derivatives : ∀ index, HasDerivativeAt (f index) point (slopes index)) :
    HasDerivativeAt (fun y => ConstructiveReal.listSum (indices.map (fun index => f index y))) point
      (ConstructiveReal.listSum (indices.map slopes)) :=
  (HasDerivativeWithinAt.listSum (domain := fun _ => True) indices (fun index y _ => f index y) slopes point True.intro
    (fun index => (derivatives index).restrict (fun _ => True) True.intro)).unrestrict (fun _ => True.intro)

end Thesis.Probability.ConstructiveReal.HasDerivativeAt
