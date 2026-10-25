import Thesis.Probability.ConstructiveDerivativeWithinChain
import Thesis.Probability.ConstructiveDerivativeScaling

namespace Thesis.Probability.ConstructiveReal.HasDerivativeAt
open ConstructiveReal

/-- Full inner differentiation uses the general domain-relative chain rule
on the exact source domain where the outer value is admitted. -/
def chainWithin {f : ConstructiveReal → ConstructiveReal} {domain : ConstructiveReal → Prop}
    {g : ∀ x, domain x → ConstructiveReal} {point sf sg : ConstructiveReal} {inside : domain (f point)}
    (first : HasDerivativeAt f point sf) (second : HasDerivativeWithinAt domain g (f point) inside sg) :
    HasDerivativeWithinAt (fun y => domain (f y)) (fun y admitted => g (f y) admitted) point inside (mul sf sg) :=
  (first.restrict (fun y => domain (f y)) inside).chainWithin second (fun _ admitted => admitted)

/-- Full-space composition is the unrestricted case of the same computed
chain rule. The public derivative statement and its effective guarantees are
unchanged. -/
def chain {f g : ConstructiveReal → ConstructiveReal} {point sf sg : ConstructiveReal}
    (first : HasDerivativeAt f point sf) (second : HasDerivativeAt g (f point) sg) :
    HasDerivativeAt (fun y => g (f y)) point (mul sf sg) :=
  (first.chainWithin (second.restrict (fun _ => True) True.intro)).unrestrict (fun _ => True.intro)

end Thesis.Probability.ConstructiveReal.HasDerivativeAt
