import Thesis.Probability.ConstructiveRealEntropyDerivative

namespace Thesis.Examples.ConstructiveEntropyDerivative
open Probability ConstructiveReal

/-- A positive domain can be arbitrary. Product and chain rules never
request values or decide membership outside that domain. -/
example {domain : ConstructiveReal → Prop} {f g : ∀ x, domain x → ConstructiveReal}
    {point sf sg : ConstructiveReal} {inside : domain point}
    (first : HasDerivativeWithinAt domain f point inside sf) (second : HasDerivativeWithinAt domain g point inside sg) :
    HasDerivativeWithinAt domain (fun y admitted => mul (f y admitted) (g y admitted)) point inside
      (add (mul sf (g point inside)) (mul (f point inside) sg)) := first.mul second

/-- The natural-unit entropy slope at probability one is exactly -1,
with any supplied valid positive lower bound. The derivative is relative to
the closed unit interval here, so no endpoint uniqueness is inferred. -/
example (lower : PositiveRatio) (positive : LE (ofSignedRatio lower.toSignedRatio) one) :
    HasDerivativeWithinAt (entropyPositiveDomain lower)
      (fun y admitted => y.naturalEntropyTerm (entropyPositiveNonnegative lower y admitted) admitted.2)
      one ⟨positive, le_refl one⟩ (neg one) :=
  (naturalEntropyTerm_hasDerivativeWithinAt one lower ⟨positive, le_refl one⟩).slope_congr
    (neg_congr (equiv_trans (add_congr (positiveLn_one lower positive) (equiv_refl one)) (zero_add one)))

/-- Repeated summands contribute their actual multiplicity. A domain-relative
empty sum needs no positive point or real equality decision. -/
example (domain : ConstructiveReal → Prop) (point : ConstructiveReal) (inside : domain point) :
    HasDerivativeWithinAt domain (fun _ _ => zero) point inside zero :=
  HasDerivativeWithinAt.listSum ([] : List Nat) (fun _ _ _ => zero) (fun _ => zero) point inside
    (fun _ => HasDerivativeWithinAt.constant point inside zero)

example (point : ConstructiveReal) (lower : PositiveRatio) (inside : entropyPositiveDomain lower point) :
    HasDerivativeWithinAt (entropyPositiveDomain lower)
      (fun y admitted => add (y.naturalEntropyTerm (entropyPositiveNonnegative lower y admitted) admitted.2)
        (y.naturalEntropyTerm (entropyPositiveNonnegative lower y admitted) admitted.2))
      point inside (add (neg (add (point.positiveLn lower inside.1) one)) (neg (add (point.positiveLn lower inside.1) one))) :=
  (naturalEntropyTerm_hasDerivativeWithinAt point lower inside).add
    (naturalEntropyTerm_hasDerivativeWithinAt point lower inside)

end Thesis.Examples.ConstructiveEntropyDerivative
