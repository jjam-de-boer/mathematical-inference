import Thesis.Probability.ConstructiveRealLogReciprocal

/-!
# Base-two logarithm laws with transported positive witnesses

Passage to a logarithmic limit requires one positive rational floor for
every term of the supplied real Cauchy sequence. Product and quotient laws
retain separate floors for their inputs and construct the appropriate
floor for the resulting argument. A reciprocal's own positive lower bound
is computed from an enclosure and then carried into its logarithm.

The concrete reference is `log2(3)`, whose lower bound one comes from an
exact-log certificate. Its reciprocal illustrates that the reciprocal-log
identity applies to analytic values, with a constructed unit-numerator
rational lower witness and positive denominator. No logarithm at zero is
defined and no equality decision on arbitrary real inputs is needed.
-/

namespace Thesis.Examples.ConstructiveRealLogLaws
open Probability

example (sequence : RealCauchySequence) (lower : PositiveRatio)
    (bounded : ∀ n, ConstructiveReal.LE (ConstructiveReal.ofSignedRatio lower.toSignedRatio) (sequence.value n)) :
    ConstructiveReal.Equiv (sequence.mapLog2 lower bounded).limit
      (sequence.limit.positiveLog2 lower (sequence.le_limit _ bounded)) := sequence.mapLog2_limit lower bounded

example (x y : ConstructiveReal) (first second : PositiveRatio)
    (firstBound : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio first.toSignedRatio) x)
    (secondBound : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio second.toSignedRatio) y) :
    ConstructiveReal.Equiv ((ConstructiveReal.mul x y).positiveLog2 (first.mul second)
      (ConstructiveReal.mul_positive_lower x y first second firstBound secondBound))
      (ConstructiveReal.add (x.positiveLog2 first firstBound) (y.positiveLog2 second secondBound)) :=
  ConstructiveReal.positiveLog2_mul x y first second firstBound secondBound

example (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio lower.toSignedRatio) x) :
    ConstructiveReal.LE (ConstructiveReal.ofSignedRatio x.positiveInverseLower.toSignedRatio) (x.positiveInverse lower bounded) :=
  x.positiveInverse_lower lower bounded

example (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio lower.toSignedRatio) x) :
    ConstructiveReal.Equiv ((x.positiveInverse lower bounded).positiveLog2 x.positiveInverseLower (x.positiveInverse_lower lower bounded))
      (ConstructiveReal.neg (x.positiveLog2 lower bounded)) := x.positiveLog2_positiveInverse lower bounded

example (x y : ConstructiveReal) (first second : PositiveRatio)
    (firstBound : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio first.toSignedRatio) x)
    (secondBound : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio second.toSignedRatio) y) :
    ConstructiveReal.Equiv ((ConstructiveReal.mul x (y.positiveInverse second secondBound)).positiveLog2 (first.mul y.positiveInverseLower)
      (ConstructiveReal.mul_positive_lower x _ first y.positiveInverseLower firstBound (y.positiveInverse_lower second secondBound)))
      (ConstructiveReal.sub (x.positiveLog2 first firstBound) (y.positiveLog2 second secondBound)) :=
  ConstructiveReal.positiveLog2_quotient x y first second firstBound secondBound

private def logThree : ConstructiveReal := ConstructiveReal.rationalLog2 ⟨3, 1, by decide, by decide⟩
private theorem logThree_lower : ConstructiveReal.LE ConstructiveReal.one logThree := by
  have exactBound : ExactLog.LE (ExactLog.ofSignedRatio SignedRatio.one) (ExactLog.log ⟨3, 1, by decide, by decide⟩) := by decide +kernel
  exact (ConstructiveReal.le_congr (ExactLog.interpret_ofSignedRatio _) (ConstructiveReal.equiv_refl _)).mp
    (ExactLog.interpret_mono exactBound)

/-- The positive lower bound of an irrational reciprocal is constructed
from an enclosure, then used by the general logarithm inverse law. -/
example : ConstructiveReal.Equiv
    ((logThree.positiveInverse PositiveRatio.one logThree_lower).positiveLog2 logThree.positiveInverseLower
      (logThree.positiveInverse_lower PositiveRatio.one logThree_lower))
    (ConstructiveReal.neg (logThree.positiveLog2 PositiveRatio.one logThree_lower)) :=
  logThree.positiveLog2_positiveInverse PositiveRatio.one logThree_lower

example : logThree.positiveInverseLower.num = 1 := rfl
example : 0 < logThree.positiveInverseLower.den := logThree.positiveInverseLower.den_pos

end Thesis.Examples.ConstructiveRealLogLaws
