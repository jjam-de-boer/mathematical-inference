import Thesis.Probability.ConstructiveRealInverseDerivative
import Thesis.Probability.ConstructiveRealExpDerivative

namespace Thesis.Examples.ConstructiveInverseDerivative
open Probability ConstructiveReal

example (point : ConstructiveReal) (lower : PositiveRatio) (bounded : LE (ofSignedRatio lower.toSignedRatio) point) :
    HasDerivativeWithinAt (fun y => LE (ofSignedRatio lower.toSignedRatio) y)
      (fun y admitted => y.positiveInverse lower admitted) point bounded
      (neg (mul (point.positiveInverse lower bounded) (point.positiveInverse lower bounded))) :=
  positiveInverse_hasDerivativeWithinAt point lower bounded

/-- Zero increments remain covered without testing equality of reals. -/
example (point : ConstructiveReal) (lower : PositiveRatio) (bounded : LE (ofSignedRatio lower.toSignedRatio) point)
    (epsilon radius : PositiveRatio)
    (small : PositiveRatio.LE radius ((positiveInverse_hasDerivativeWithinAt point lower bounded).modulus epsilon)) :
    Within (QProb.mul epsilon.toQProb radius.toQProb) (point.positiveInverse lower bounded) (inverseLinear point point lower bounded) :=
  (positiveInverse_hasDerivativeWithinAt point lower bounded).remainder epsilon radius small point bounded (within_refl _ point)

/-- Restriction of a full-space derivative does not require deciding domain
membership. The proof is supplied for each admitted argument. -/
example (domain : ConstructiveReal → Prop) (point : ConstructiveReal) (inside : domain point) :
    HasDerivativeWithinAt domain (fun y _ => y.exp) point inside point.exp :=
  (exp_hasDerivativeAt point).restrict domain inside

private def lower : PositiveRatio := ⟨1, 2, by decide, by decide⟩
private theorem oneBound : LE (ofSignedRatio lower.toSignedRatio) one := (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
private theorem inverseOne : Equiv (one.positiveInverse lower oneBound) one :=
  inverse_unique one _ one (mul_positiveInverse one lower oneBound) (one_mul one)

example : HasDerivativeWithinAt (fun y => LE (ofSignedRatio lower.toSignedRatio) y)
    (fun y admitted => y.positiveInverse lower admitted) one oneBound (neg one) :=
  (positiveInverse_hasDerivativeWithinAt one lower oneBound).slope_congr
    (neg_congr (equiv_trans (mul_congr inverseOne inverseOne) (one_mul one)))

/-- A concrete negative increment inside the positive domain satisfies the
computed modulus. The exact quadratic remainder bounds the analytic outputs. -/
private def epsilon : PositiveRatio := ⟨1, 10, by decide, by decide⟩
private def radius : PositiveRatio := ⟨1, 80, by decide, by decide⟩
private def nearby : ConstructiveReal := ofSignedRatio ⟨159, 160, by decide⟩
private theorem nearbyBound : LE (ofSignedRatio lower.toSignedRatio) nearby := (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
example : Within (⟨1, 800, by decide⟩ : QProb) (nearby.positiveInverse lower nearbyBound) (inverseLinear one nearby lower oneBound) :=
  (positiveInverse_hasDerivativeWithinAt one lower oneBound).remainder epsilon radius (by decide +kernel) nearby nearbyBound
    ((within_ofSignedRatio_iff _ _ _).mpr (by decide +kernel))

/-- Zero is excluded by the stated domain premise, rather than receiving an
arbitrary inverse value. -/
example (admitted : LE (ofSignedRatio lower.toSignedRatio) zero) : False :=
  (by decide +kernel : ¬ SignedRatio.LE lower.toSignedRatio SignedRatio.zero) ((ofSignedRatio_le_iff _ _).mp admitted)

/-- Partial outer functions retain their domain after composition. -/
example (f : ConstructiveReal → ConstructiveReal) (domain : ConstructiveReal → Prop)
    (g : ∀ x, domain x → ConstructiveReal) (point sf sg : ConstructiveReal) (inside : domain (f point))
    (first : HasDerivativeAt f point sf) (second : HasDerivativeWithinAt domain g (f point) inside sg) :
    HasDerivativeWithinAt (fun y => domain (f y)) (fun y admitted => g (f y) admitted) point inside (mul sf sg) :=
  first.chainWithin second

example (point factor offset : ConstructiveReal) (bound : PositiveRatio)
    (bounded : LE (ofSignedRatio bound.toSignedRatio) (add (mul point factor) offset)) :
    HasDerivativeWithinAt (fun y => LE (ofSignedRatio bound.toSignedRatio) (add (mul y factor) offset))
      (fun y admitted => (add (mul y factor) offset).positiveInverse bound admitted) point bounded
      (neg (mul factor (mul ((add (mul point factor) offset).positiveInverse bound bounded)
        ((add (mul point factor) offset).positiveInverse bound bounded)))) :=
  inverse_affine_hasDerivativeWithinAt point factor offset bound bounded

/-- Removing a domain condition requires an explicit proof for every input. -/
example (domain : ConstructiveReal → Prop) (f : ∀ x, domain x → ConstructiveReal)
    (point slope : ConstructiveReal) (inside : domain point)
    (derivative : HasDerivativeWithinAt domain f point inside slope) (admitted : ∀ y, domain y) :
    HasDerivativeAt (fun y => f y (admitted y)) point slope := derivative.unrestrict admitted

end Thesis.Examples.ConstructiveInverseDerivative
