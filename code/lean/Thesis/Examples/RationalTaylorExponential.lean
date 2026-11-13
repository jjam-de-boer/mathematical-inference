import Thesis.Probability.RationalTaylorExponential

namespace Thesis.Examples.RationalTaylorExponential
open Probability

example (terms : Nat → SignedRatio) (coefficient : Nat)
    (bounded : ∀ n, QProb.LE (terms n).magnitude (RationalGeometricSeries.envelope coefficient n)) (n : Nat) :
    ConstructiveReal.Within (RationalGeometricSeries.envelope (2 * coefficient) n)
      (ConstructiveReal.ofSignedRatio (RationalGeometricSeries.partialSum terms n))
      (RationalGeometricSeries.sequence terms coefficient bounded).limit := RationalGeometricSeries.remainder terms coefficient bounded n

example (x : SignedRatio) (small : QProb.LE x.magnitude ⟨1, 2, by decide⟩) (n : Nat) :
    ConstructiveReal.Within (RationalGeometricSeries.envelope 2 n)
      (ConstructiveReal.ofSignedRatio (RationalGeometricSeries.partialSum (Probability.RationalTaylorExponential.term x) n))
      (Probability.RationalTaylorExponential.expSmall x small) := Probability.RationalTaylorExponential.expSmall_remainder x small n

example : ConstructiveReal.Equiv (Probability.RationalTaylorExponential.expSmall SignedRatio.zero (by decide)) ConstructiveReal.one :=
  Probability.RationalTaylorExponential.expSmall_zero

example : SignedRatio.Equiv (Probability.RationalTaylorExponential.term ⟨1, 2, by decide⟩ 3) ⟨1, 48, by decide⟩ := by decide +kernel
example : SignedRatio.Equiv (Probability.RationalTaylorExponential.term ⟨-1, 2, by decide⟩ 3) ⟨-1, 48, by decide⟩ := by decide +kernel

example : ConstructiveReal.Equiv (Probability.RationalTaylorExponential.expSmall ⟨1, 2, by decide⟩ (by decide))
    (Probability.RationalTaylorExponential.expSmall ⟨2, 4, by decide⟩ (by decide)) :=
  Probability.RationalTaylorExponential.expSmall_congr (by decide +kernel) (by decide) (by decide)

/-- The series constructions compute certified enclosures on both sides of
zero, rather than assuming an exponential value or a Taylor remainder. -/
private def precision : PositiveRatio := ⟨1, 100, by decide, by decide⟩
private def positive : ConstructiveReal := Probability.RationalTaylorExponential.expSmall ⟨1, 2, by decide⟩ (by decide)
private def negative : ConstructiveReal := Probability.RationalTaylorExponential.expSmall ⟨-1, 2, by decide⟩ (by decide)

example : SignedRatio.LE ⟨164, 100, by decide⟩ (positive.enclose precision).lower := by decide +kernel
example : SignedRatio.LE (positive.enclose precision).upper ⟨166, 100, by decide⟩ := by decide +kernel
example : SignedRatio.LE ⟨60, 100, by decide⟩ (negative.enclose precision).lower := by decide +kernel
example : SignedRatio.LE (negative.enclose precision).upper ⟨62, 100, by decide⟩ := by decide +kernel

/-- Zero domination remains a valid series certificate and gives a zero
remainder at every truncation. -/
example (n : Nat) : ConstructiveReal.Within (RationalGeometricSeries.envelope 0 n)
    (ConstructiveReal.ofSignedRatio (RationalGeometricSeries.partialSum (fun _ => SignedRatio.zero) n))
    (RationalGeometricSeries.sequence (fun _ => SignedRatio.zero) 0 (fun k => by change 0 * 2 ^ k ≤ 0 * 1; simp only [Nat.zero_mul, Nat.le_refl])).limit :=
  RationalGeometricSeries.remainder _ 0 (fun k => by change 0 * 2 ^ k ≤ 0 * 1; simp only [Nat.zero_mul, Nat.le_refl]) n

end Thesis.Examples.RationalTaylorExponential
