import Thesis.Probability.ExactLogEnclosure

namespace Thesis.Examples.ExactLog
open Probability

private def three : PositiveRatio := ⟨3, 1, by decide, by decide⟩
private def threeHalves : PositiveRatio := ⟨3, 2, by decide, by decide⟩
private def oneBit : Probability.ExactLog := Probability.ExactLog.ofSignedRatio ⟨1, 1, by decide⟩

/-- A nontrivial root presentation agrees exactly with one bit. -/
example : Probability.ExactLog.Equiv ⟨⟨4, 1, by decide, by decide⟩, 2, by decide⟩ oneBit := by decide +kernel

/-- Certified comparisons around an irrational logarithm use only integer powers. -/
example : Probability.ExactLog.LE (Probability.ExactLog.ofSignedRatio ⟨3, 2, by decide⟩) (Probability.ExactLog.log three) ∧
    Probability.ExactLog.LE (Probability.ExactLog.log three) (Probability.ExactLog.ofSignedRatio ⟨8, 5, by decide⟩) := by decide +kernel

/-- Equivalent unreduced arguments and degree rescaling preserve the value. -/
example : Probability.ExactLog.Equiv
    (Probability.ExactLog.rescale (Probability.ExactLog.log threeHalves) 3 (by decide))
    (Probability.ExactLog.log ⟨6, 4, by decide, by decide⟩) := by decide +kernel

/-- Negative bits are exact values, rather than clipped probability weights. -/
example : Probability.ExactLog.Equiv
    (Probability.ExactLog.neg (Probability.ExactLog.ofSignedRatio ⟨3, 2, by decide⟩))
    (Probability.ExactLog.ofSignedRatio ⟨-3, 2, by decide⟩) := by decide +kernel

/-- Executed bisection encloses log₂(3) in [49/32, 52/32], width 3/32 < 1/8. -/
private def threeBounds := Probability.ExactLog.enclose (Probability.ExactLog.log three) ⟨1, 8, by decide⟩ (by decide)
example : threeBounds.lower = 49 ∧ threeBounds.width = 3 ∧ threeBounds.den = 32 := by decide +kernel
example : Probability.ExactLog.LE (Probability.ExactLog.ofSignedRatio ⟨49, 32, by decide⟩) (Probability.ExactLog.log three) ∧
    Probability.ExactLog.LE (Probability.ExactLog.log three) (Probability.ExactLog.ofSignedRatio ⟨52, 32, by decide⟩) :=
  ⟨threeBounds.lower_bound, threeBounds.upper_bound⟩

/-- The total error guarantee also applies below zero, at nonunit degrees,
and to arbitrarily presented positive rational tolerances. -/
example (x : Probability.ExactLog) (epsilon : QProb) (positive : 0 < epsilon.num) :
    ∃ interval : Probability.ExactLog.Enclosure x epsilon,
      interval.width * epsilon.den < epsilon.num * interval.den :=
  ⟨Probability.ExactLog.enclose x epsilon positive, (Probability.ExactLog.enclose x epsilon positive).width_lt⟩

end Thesis.Examples.ExactLog
