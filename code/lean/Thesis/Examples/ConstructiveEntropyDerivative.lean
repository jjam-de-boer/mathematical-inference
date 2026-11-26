import Thesis.Probability.ConstructiveRealEntropyDerivative

/-!
# Domain-relative differentiation of natural entropy

The scalar entropy derivative is used only on the supplied domain with a
positive rational lower bound and upper bound one. At probability one its
slope simplifies to `-1` using the proved logarithm-of-one identity. This is
a derivative relative to the closed domain; it does not assert unrestricted
derivative uniqueness at that endpoint.

The remaining fixtures exercise products on arbitrary proof-indexed domains,
the empty finite sum, and two identical entropy summands. Domain admission
proofs travel with every argument, so no function is evaluated outside its
domain and no real-valued membership test is introduced.
-/

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
