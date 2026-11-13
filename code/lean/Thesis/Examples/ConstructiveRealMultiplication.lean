import Thesis.Probability.ConstructiveRealMultiplication
import Thesis.Probability.ExactLogInterpretation

namespace Thesis.Examples.ConstructiveRealMultiplication
open Probability

private def a : SignedRatio := ⟨-3, 4, by decide⟩
private def b : SignedRatio := ⟨7, 6, by decide⟩
private def precision : PositiveRatio := ⟨1, 100, by decide, by decide⟩
private def product : ConstructiveReal := ConstructiveReal.mul (ConstructiveReal.ofSignedRatio a) (ConstructiveReal.ofSignedRatio b)

/-- Actual enclosures of a negative rational product are computed correctly. -/
example : SignedRatio.LE ⟨-88, 100, by decide⟩ (product.enclose precision).lower := by decide +kernel
example : SignedRatio.LE (product.enclose precision).upper ⟨-87, 100, by decide⟩ := by decide +kernel
example : ConstructiveReal.Equiv product (ConstructiveReal.ofSignedRatio ⟨-7, 8, by decide⟩) :=
  ConstructiveReal.equiv_trans (ConstructiveReal.ofSignedRatio_mul a b)
    ((ConstructiveReal.ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel))

/-- Rescaling an input changes its stored magnitude bound and precision
schedule, but cannot change the product's value. -/
example : ConstructiveReal.Equiv
    (ConstructiveReal.mul (ConstructiveReal.ofSignedRatio ⟨2, 4, by decide⟩) (ConstructiveReal.ofSignedRatio ⟨-4, 8, by decide⟩))
    (ConstructiveReal.mul (ConstructiveReal.ofSignedRatio ⟨3, 6, by decide⟩) (ConstructiveReal.ofSignedRatio ⟨-3, 6, by decide⟩)) :=
  ConstructiveReal.mul_congr
    ((ConstructiveReal.ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel))
    ((ConstructiveReal.ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel))

example (x y : ConstructiveReal) : ConstructiveReal.Equiv (ConstructiveReal.mul x y) (ConstructiveReal.mul y x) := ConstructiveReal.mul_comm x y
example (x : ConstructiveReal) : ConstructiveReal.Equiv (ConstructiveReal.mul x ConstructiveReal.zero) ConstructiveReal.zero := ConstructiveReal.mul_zero x
example (x : ConstructiveReal) : ConstructiveReal.Equiv (ConstructiveReal.mul x ConstructiveReal.one) x := ConstructiveReal.mul_one x
example (x x' y y' : ConstructiveReal) (first : ConstructiveReal.Equiv x x') (second : ConstructiveReal.Equiv y y') :
    ConstructiveReal.Equiv (ConstructiveReal.mul x y) (ConstructiveReal.mul x' y') := ConstructiveReal.mul_congr first second

example : ConstructiveReal.Equiv
    (ConstructiveReal.mul (ExactLog.log ⟨3, 1, by decide, by decide⟩).interpret ConstructiveReal.one)
    (ExactLog.log ⟨3, 1, by decide, by decide⟩).interpret := ConstructiveReal.mul_one _

example (x y : ConstructiveReal) (bounded : ∀ error : PositiveRatio, ConstructiveReal.Within error.toQProb x y) :
    ConstructiveReal.Equiv x y := ConstructiveReal.equiv_of_within_all x y bounded

end Thesis.Examples.ConstructiveRealMultiplication
