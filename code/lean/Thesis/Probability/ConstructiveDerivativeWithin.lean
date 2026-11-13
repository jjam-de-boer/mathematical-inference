import Thesis.Probability.ConstructiveDerivative

namespace Thesis.Probability.ConstructiveReal

/-- Effective differentiation for a function with an explicit domain. Nearby
arguments carry domain proofs, so positive reciprocals and logarithms need no
total extension across zero. Domain-relative differentiation alone does not
assert uniqueness on an isolated domain or a full-space derivative. -/
structure HasDerivativeWithinAt (domain : ConstructiveReal → Prop)
    (function : ∀ x, domain x → ConstructiveReal) (point : ConstructiveReal) (inside : domain point) (slope : ConstructiveReal) where
  modulus : PositiveRatio → PositiveRatio
  remainder : ∀ epsilon radius : PositiveRatio, PositiveRatio.LE radius (modulus epsilon) →
    ∀ nearby : ConstructiveReal, ∀ admitted : domain nearby, Within radius.toQProb point nearby →
      Within (QProb.mul epsilon.toQProb radius.toQProb) (function nearby admitted)
        (add (function point inside) (mul (sub nearby point) slope))

namespace HasDerivativeWithinAt

def slope_congr {domain : ConstructiveReal → Prop} {f : ∀ x, domain x → ConstructiveReal}
    {point slope slope' : ConstructiveReal} {inside : domain point}
    (derivative : HasDerivativeWithinAt domain f point inside slope) (same : Equiv slope slope') :
    HasDerivativeWithinAt domain f point inside slope' where
  modulus := derivative.modulus
  remainder epsilon radius small y admitted close :=
    (within_congr (equiv_refl _) (add_congr (equiv_refl _) (mul_congr (equiv_refl _) same))).mp
      (derivative.remainder epsilon radius small y admitted close)

/-- A domain-relative certificate becomes a full-space derivative when
membership is supplied for every argument. No membership test is inferred. -/
def unrestrict {domain : ConstructiveReal → Prop} {f : ∀ x, domain x → ConstructiveReal}
    {point slope : ConstructiveReal} {inside : domain point}
    (derivative : HasDerivativeWithinAt domain f point inside slope) (admitted : ∀ y, domain y) :
    HasDerivativeAt (fun y => f y (admitted y)) point slope where
  modulus := derivative.modulus
  remainder epsilon radius small y close := derivative.remainder epsilon radius small y (admitted y) close

end HasDerivativeWithinAt

/-- A full-space derivative restricts to any supplied domain containing its
point. No decidability of membership is needed. -/
def HasDerivativeAt.restrict {f : ConstructiveReal → ConstructiveReal} {point slope : ConstructiveReal}
    (derivative : HasDerivativeAt f point slope) (domain : ConstructiveReal → Prop) (inside : domain point) :
    HasDerivativeWithinAt domain (fun y _ => f y) point inside slope where
  modulus := derivative.modulus
  remainder epsilon radius small y _ close := derivative.remainder epsilon radius small y close

end Thesis.Probability.ConstructiveReal
