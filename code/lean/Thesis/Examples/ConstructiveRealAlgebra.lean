import Thesis.Probability.ConstructiveRealRing

namespace Thesis.Examples.ConstructiveRealAlgebra
open Probability

example (x y z : ConstructiveReal) :
    ConstructiveReal.Equiv (ConstructiveReal.mul (ConstructiveReal.mul x y) z) (ConstructiveReal.mul x (ConstructiveReal.mul y z)) :=
  ConstructiveReal.mul_assoc x y z
example (x y z : ConstructiveReal) :
    ConstructiveReal.Equiv (ConstructiveReal.mul x (ConstructiveReal.add y z))
      (ConstructiveReal.add (ConstructiveReal.mul x y) (ConstructiveReal.mul x z)) := ConstructiveReal.mul_add x y z
example (x y : ConstructiveReal) :
    ConstructiveReal.Equiv (ConstructiveReal.mul x (ConstructiveReal.neg y)) (ConstructiveReal.neg (ConstructiveReal.mul x y)) :=
  ConstructiveReal.mul_neg x y
example (x y : ConstructiveReal) :
    ConstructiveReal.Equiv (ConstructiveReal.sub x y) ConstructiveReal.zero ↔ ConstructiveReal.Equiv x y :=
  ConstructiveReal.sub_equiv_zero_iff x y

/-- The new algebra retains a nontrivial real value space. -/
example : ¬ ConstructiveReal.Equiv ConstructiveReal.one ConstructiveReal.zero := by
  intro collapsed
  have impossible : ¬ SignedRatio.Equiv SignedRatio.one SignedRatio.zero := by decide +kernel
  exact impossible ((ConstructiveReal.ofSignedRatio_equiv_iff _ _).mp collapsed)

/-- Real powers agree with the existing exact signed-rational monomials. -/
example : ConstructiveReal.Equiv
    (ConstructiveReal.pow (ConstructiveReal.ofSignedRatio ⟨3, 2, by decide⟩) 3)
    (ConstructiveReal.ofSignedRatio ⟨27, 8, by decide⟩) :=
  ConstructiveReal.equiv_trans (ConstructiveReal.ofSignedRatio_power _ _)
    ((ConstructiveReal.ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel))

example (x : ConstructiveReal) (m n : Nat) :
    ConstructiveReal.Equiv (ConstructiveReal.pow x (m + n)) (ConstructiveReal.mul (ConstructiveReal.pow x m) (ConstructiveReal.pow x n)) :=
  ConstructiveReal.pow_add x m n
example (x : ConstructiveReal) (values : List ConstructiveReal) :
    ConstructiveReal.Equiv (ConstructiveReal.mul x (ConstructiveReal.listSum values))
      (ConstructiveReal.listSum (values.map (ConstructiveReal.mul x))) := ConstructiveReal.mul_listSum x values

end Thesis.Examples.ConstructiveRealAlgebra
