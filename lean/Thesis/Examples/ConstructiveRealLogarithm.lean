import Thesis.Probability.ConstructiveRealLogContinuity

namespace Thesis.Examples.ConstructiveRealLogarithm
open Probability

example (x y : ConstructiveReal) (same : ConstructiveReal.Equiv x y) (first second : PositiveRatio)
    (firstBound : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio first.toSignedRatio) x)
    (secondBound : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio second.toSignedRatio) y) :
    ConstructiveReal.Equiv (x.positiveLog2 first firstBound) (y.positiveLog2 second secondBound) :=
  ConstructiveReal.positiveLog2_congr same first second firstBound secondBound

example (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio lower.toSignedRatio) x) (precision : PositiveRatio) (n : Nat)
    (later : (x.logSequence lower bounded).modulus precision.half.half ≤ n) :
    ConstructiveReal.Within precision.toQProb
      (ConstructiveReal.rationalLog2 (x.positiveCenter lower (PositiveRatio.unitPrecision n))) (x.positiveLog2 lower bounded) :=
  x.positiveLog2_tail lower bounded precision n later

/-- The same explicit modulus applies to general positive real inputs. -/
example (x y : ConstructiveReal) (lower precision : PositiveRatio)
    (boundedX : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio lower.toSignedRatio) x)
    (boundedY : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio lower.toSignedRatio) y)
    (close : ConstructiveReal.Within (lower.logInputPrecision precision).half.toQProb x y) :
    ConstructiveReal.Within precision.toQProb (x.positiveLog2 lower boundedX) (y.positiveLog2 lower boundedY) :=
  ConstructiveReal.positiveLog2_within x y lower boundedX boundedY precision close

private def half : PositiveRatio := ⟨1, 2, by decide, by decide⟩
private def threeHalves : PositiveRatio := ⟨3, 2, by decide, by decide⟩
private def rationalInput : ConstructiveReal := ConstructiveReal.ofSignedRatio threeHalves.toSignedRatio
private theorem lowerBound : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio half.toSignedRatio) rationalInput :=
  (ConstructiveReal.ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
private def logarithm : ConstructiveReal := rationalInput.positiveLog2 half lowerBound

example : ConstructiveReal.Equiv logarithm (ConstructiveReal.rationalLog2 threeHalves) :=
  ConstructiveReal.positiveLog2_ofPositiveRatio threeHalves half lowerBound

/-- The extension computes certified enclosures, not merely a symbolic
postulate identifying the new real logarithm with the rational one. -/
private def precision : PositiveRatio := ⟨1, 16, by decide, by decide⟩
example : SignedRatio.LE ⟨1, 2, by decide⟩ (logarithm.enclose precision).lower := by decide +kernel
example : SignedRatio.LE (logarithm.enclose precision).upper ⟨3, 4, by decide⟩ := by decide +kernel

private def logThree : ConstructiveReal := ConstructiveReal.rationalLog2 ⟨3, 1, by decide, by decide⟩
private theorem logThree_lower : ConstructiveReal.LE ConstructiveReal.one logThree := by
  have exactBound : ExactLog.LE (ExactLog.ofSignedRatio SignedRatio.one) (ExactLog.log ⟨3, 1, by decide, by decide⟩) := by decide +kernel
  exact (ConstructiveReal.le_congr (ExactLog.interpret_ofSignedRatio _) (ConstructiveReal.equiv_refl _)).mp
    (ExactLog.interpret_mono exactBound)

/-- The input may itself be an irrational analytic value. -/
example (precision : PositiveRatio) :
    ConstructiveReal.LE (ConstructiveReal.ofSignedRatio ((logThree.positiveLog2 PositiveRatio.one logThree_lower).enclose precision).lower)
      (logThree.positiveLog2 PositiveRatio.one logThree_lower) := ConstructiveReal.lower_bound _ _

end Thesis.Examples.ConstructiveRealLogarithm
