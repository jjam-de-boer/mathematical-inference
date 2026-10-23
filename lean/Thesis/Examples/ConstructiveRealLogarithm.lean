import Thesis.Probability.ConstructiveRealLogOrder

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

example (x y : ConstructiveReal) (first second : PositiveRatio)
    (firstBound : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio first.toSignedRatio) x)
    (secondBound : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio second.toSignedRatio) y)
    (compared : ConstructiveReal.LE x y) :
    ConstructiveReal.LE (x.positiveLog2 first firstBound) (y.positiveLog2 second secondBound) :=
  ConstructiveReal.positiveLog2_mono x y first second firstBound secondBound compared

example : ConstructiveReal.Equiv (ConstructiveReal.one.positiveLog2 PositiveRatio.one (ConstructiveReal.le_refl _))
    ConstructiveReal.zero := ConstructiveReal.positiveLog2_one _ _

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

private def quarter : PositiveRatio := ⟨1, 4, by decide, by decide⟩
private theorem half_lower : ConstructiveReal.LE (ConstructiveReal.ofSignedRatio quarter.toSignedRatio)
    (ConstructiveReal.ofSignedRatio half.toSignedRatio) :=
  (ConstructiveReal.ofSignedRatio_le_iff _ _).mpr (by decide +kernel)

/-- A negative logarithm is represented and proved with the same general
construction; it is not restricted to inputs at least one. -/
example : ConstructiveReal.Equiv ((ConstructiveReal.ofSignedRatio half.toSignedRatio).positiveLog2 quarter half_lower)
    (ConstructiveReal.ofSignedRatio ⟨-1, 1, by decide⟩) :=
  ConstructiveReal.equiv_trans (ConstructiveReal.positiveLog2_ofPositiveRatio half quarter half_lower)
    (ConstructiveReal.equiv_trans (ExactLog.interpret_congr
      (show ExactLog.Equiv (ExactLog.log half) (ExactLog.ofSignedRatio ⟨-1, 1, by decide⟩) from by decide +kernel))
      (ExactLog.interpret_ofSignedRatio _))

end Thesis.Examples.ConstructiveRealLogarithm
