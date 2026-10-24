import Thesis.Probability.ConstructiveRealExponential

namespace Thesis.Examples.ConstructiveRealExponential
open Probability

/-- Uniform interval estimates include radius zero and do not depend on a
particular rational argument presentation or Taylor truncation. -/
example (n : Nat) : QProb.LE (RationalGeometricSeries.normSum (RationalTaylorExponential.coefficient 0) 0 n)
    (QProb.ofNat 2) := RationalTaylorExponential.coefficient_sum_bound 0 n

example : RationalTaylorExponential.uniformSumBound 1 = 16 := by decide +kernel
example : RationalTaylorExponential.uniformSumBound 2 = 486 := by decide +kernel

example (x y : SignedRatio) (bound : Nat)
    (boundedX : QProb.LE x.magnitude (QProb.ofNat bound)) (boundedY : QProb.LE y.magnitude (QProb.ofNat bound)) :
    ConstructiveReal.Within
      (QProb.mul (SignedRatio.sub x y).magnitude (QProb.ofNat (RationalTaylorExponential.uniformSumBound bound)))
      (Probability.RationalExponential.exp x) (Probability.RationalExponential.exp y) :=
  Probability.RationalExponential.exp_within x y bound boundedX boundedY

example (x : ConstructiveReal) (precision : PositiveRatio) (n : Nat)
    (later : x.expSequence.modulus precision.half.half ≤ n) :
    ConstructiveReal.Within precision.toQProb
      (Probability.RationalExponential.exp (x.rationalApproximation.value (PositiveRatio.unitPrecision n))) x.exp :=
  x.exp_tail precision n later

example (x : SignedRatio) : ConstructiveReal.Equiv
    (ConstructiveReal.exp (ConstructiveReal.ofSignedRatio x)) (Probability.RationalExponential.exp x) :=
  ConstructiveReal.exp_ofSignedRatio x

example : ConstructiveReal.Equiv (ConstructiveReal.exp ConstructiveReal.zero) ConstructiveReal.one := ConstructiveReal.exp_zero

/-- Equal real values may have different enclosures and computed continuity
schedules; exponentiation respects their value equivalence. -/
example (x : ConstructiveReal) : ConstructiveReal.Equiv
    (ConstructiveReal.exp (ConstructiveReal.add x ConstructiveReal.zero)) x.exp :=
  ConstructiveReal.exp_congr (ConstructiveReal.add_zero x)

example : ConstructiveReal.Equiv (ConstructiveReal.exp (ConstructiveReal.ofSignedRatio ⟨-1000, 1000, by decide⟩))
    (Probability.RationalExponential.exp ⟨-1, 1, by decide⟩) :=
  ConstructiveReal.equiv_trans (ConstructiveReal.exp_ofSignedRatio _)
    (Probability.RationalExponential.exp_congr (by decide +kernel))

end Thesis.Examples.ConstructiveRealExponential
