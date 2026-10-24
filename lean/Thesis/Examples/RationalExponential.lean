import Thesis.Probability.RationalExponential

namespace Thesis.Examples.RationalExponential
open Probability

example (x : SignedRatio) (n : Nat) (after : Probability.RationalExponential.offset x ≤ n) :
    ConstructiveReal.Within
      (RationalGeometricSeries.envelope (2 * Probability.RationalExponential.tailBound x) (n - Probability.RationalExponential.offset x))
      (ConstructiveReal.ofSignedRatio (RationalGeometricSeries.partialSum (Probability.RationalTaylorExponential.term x) n))
      (Probability.RationalExponential.exp x) := Probability.RationalExponential.remainder x n after

example (x : SignedRatio) (small : QProb.LE x.magnitude ⟨1, 2, by decide⟩) :
    ConstructiveReal.Equiv (Probability.RationalExponential.exp x) (Probability.RationalTaylorExponential.expSmall x small) :=
  Probability.RationalExponential.exp_eq_small x small

example : ConstructiveReal.Equiv (Probability.RationalExponential.exp SignedRatio.zero) ConstructiveReal.one :=
  Probability.RationalExponential.exp_zero

/-- The natural magnitude bound uses the represented quotient, including
when a rational argument has a large unreduced numerator. -/
example : (⟨1000, 1000, by decide⟩ : QProb).naturalUpper = 2 := by decide +kernel
example : Probability.RationalExponential.offset ⟨1000, 1000, by decide⟩ = Probability.RationalExponential.offset ⟨1, 1, by decide⟩ := by decide +kernel
example : ConstructiveReal.Equiv (Probability.RationalExponential.exp ⟨1000, 1000, by decide⟩)
    (Probability.RationalExponential.exp ⟨1, 1, by decide⟩) := Probability.RationalExponential.exp_congr (by decide +kernel)

private def precision : PositiveRatio := ⟨1, 100, by decide, by decide⟩
private def e : ConstructiveReal := Probability.RationalExponential.exp ⟨1, 1, by decide⟩
private def inverseE : ConstructiveReal := Probability.RationalExponential.exp ⟨-1, 1, by decide⟩
private def expTwo : ConstructiveReal := Probability.RationalExponential.exp ⟨2, 1, by decide⟩

/-- Actual certified enclosures beyond the earlier small-argument domain. -/
example : SignedRatio.LE ⟨271, 100, by decide⟩ (e.enclose precision).lower := by decide +kernel
example : SignedRatio.LE (e.enclose precision).upper ⟨273, 100, by decide⟩ := by decide +kernel
example : SignedRatio.LE ⟨36, 100, by decide⟩ (inverseE.enclose precision).lower := by decide +kernel
example : SignedRatio.LE (inverseE.enclose precision).upper ⟨38, 100, by decide⟩ := by decide +kernel
example : SignedRatio.LE ⟨738, 100, by decide⟩ (expTwo.enclose precision).lower := by decide +kernel
example : SignedRatio.LE (expTwo.enclose precision).upper ⟨740, 100, by decide⟩ := by decide +kernel

end Thesis.Examples.RationalExponential
