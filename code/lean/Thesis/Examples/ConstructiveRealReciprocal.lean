import Thesis.Probability.ConstructiveRealReciprocal
import Thesis.Probability.ExactLogInterpretation

namespace Thesis.Examples.ConstructiveRealReciprocal
open Probability

example (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio lower.toSignedRatio) x) :
    ConstructiveReal.Equiv (ConstructiveReal.mul x (x.positiveInverse lower bounded)) ConstructiveReal.one :=
  x.mul_positiveInverse lower bounded

example (x y : ConstructiveReal) (same : ConstructiveReal.Equiv x y) (first second : PositiveRatio)
    (firstBound : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio first.toSignedRatio) x)
    (secondBound : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio second.toSignedRatio) y) :
    ConstructiveReal.Equiv (x.positiveInverse first firstBound) (y.positiveInverse second secondBound) :=
  ConstructiveReal.positiveInverse_congr same first second firstBound secondBound

example (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio lower.toSignedRatio) x) (a b : ConstructiveReal) :
    ConstructiveReal.LE (ConstructiveReal.mul x a) (ConstructiveReal.mul x b) ↔ ConstructiveReal.LE a b :=
  x.mul_le_mul_positive_iff lower bounded a b

private def third : PositiveRatio := ⟨1, 3, by decide, by decide⟩
private def twoThirds : ConstructiveReal := ConstructiveReal.ofSignedRatio ⟨2, 3, by decide⟩
private theorem third_lower : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio third.toSignedRatio) twoThirds :=
  (ConstructiveReal.ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
private def inverseTwoThirds : ConstructiveReal := twoThirds.positiveInverse third third_lower

example : ConstructiveReal.Equiv inverseTwoThirds (ConstructiveReal.ofSignedRatio ⟨3, 2, by decide⟩) :=
  ConstructiveReal.ofPositiveRatio_inverse ⟨2, 3, by decide, by decide⟩ third third_lower

/-- The algorithm computes an enclosure of 3/2 at the requested precision. -/
private def precision : PositiveRatio := ⟨1, 100, by decide, by decide⟩
example : SignedRatio.LE ⟨149, 100, by decide⟩ (inverseTwoThirds.enclose precision).lower := by decide +kernel
example : SignedRatio.LE (inverseTwoThirds.enclose precision).upper ⟨151, 100, by decide⟩ := by decide +kernel

/-- An irrational real with a certified positive rational lower bound is
also in the domain; the inverse is not asserted to be rational. -/
private def logThree : ConstructiveReal := (ExactLog.log ⟨3, 1, by decide, by decide⟩).interpret
private theorem logThree_lower : ConstructiveReal.LE ConstructiveReal.one logThree := by
  have exactBound : ExactLog.LE (ExactLog.ofSignedRatio SignedRatio.one) (ExactLog.log ⟨3, 1, by decide, by decide⟩) := by decide +kernel
  exact (ConstructiveReal.le_congr (ExactLog.interpret_ofSignedRatio _) (ConstructiveReal.equiv_refl _)).mp
    (ExactLog.interpret_mono exactBound)

example : ConstructiveReal.Equiv (ConstructiveReal.mul logThree (logThree.positiveInverse PositiveRatio.one logThree_lower))
    ConstructiveReal.one := logThree.mul_positiveInverse PositiveRatio.one logThree_lower
example : ConstructiveReal.LE ConstructiveReal.zero (logThree.positiveInverse PositiveRatio.one logThree_lower) :=
  logThree.positiveInverse_nonnegative PositiveRatio.one logThree_lower

/-- A positive-domain certificate for zero cannot be manufactured. -/
example : ¬ ConstructiveReal.LE (ConstructiveReal.ofSignedRatio third.toSignedRatio) ConstructiveReal.zero := by
  intro impossible
  exact (show ¬ SignedRatio.LE third.toSignedRatio SignedRatio.zero from by decide +kernel)
    ((ConstructiveReal.ofSignedRatio_le_iff _ _).mp impossible)

end Thesis.Examples.ConstructiveRealReciprocal
